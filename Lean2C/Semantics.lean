import Lean2C.C
import ZlibF.Runtime.CAbi
import ZlibF.Runtime.LibcCString

/-!
# Operational semantics for `Lean2C.CSource`

Total, fuel-indexed C99 LP64 operational semantics for the source-level C AST
(`Lean2C.CSource`). Undefined behavior (`C.Fault.ub`) models C99 constraints:
* shift counts negative or `>= width` (`32` / `64`), plus signed left-shift overflow;
* division or modulo by zero, and signed `INT_MIN / -1`, `INT_MIN % -1`;
* signed integer arithmetic overflow on `+`, `-`, `*` (`i32` / `i64`);
* null, dangling, read-only, or out-of-bounds memory loads, stores, and pointer arithmetic;
* unsigned `+`, `-`, `*` wrap modulo `2^32` or `2^64` per C99 §6.2.5/9.
-/

namespace Lean2C.Semantics
open Lean2C.CSource C
set_option autoImplicit false

/-- Runtime C values on LP64 (`char` 8-bit, `short` 16-bit, `int` 32-bit, `long` / pointers 64-bit). -/
inductive CVal where
  | bool (v : Bool)
  | u8 (v : UInt8)
  | u16 (v : UInt16)
  | u32 (v : UInt32)
  | u64 (v : UInt64)
  | i32 (v : Int32)
  | i64 (v : Int64)
  | ptr (v : C.BPtr)
  | functionPtr (v : FnPtr)
  /-- Identity of an automatic z_stream object in the local environment. -/
  | streamLocal (ref : ZStreamRef)
  /-- An addressable automatic stream, with the byte address of its reserved member. -/
  | streamWithReserved (ref : ZStreamRef) (address : BPtr)
  /-- Array-to-pointer decay of a static array of pointers to string literals. -/
  | stringTable (entries : Array String)
  | void
  deriving DecidableEq, Inhabited

@[simp] def CVal.streamRef? : CVal → Option ZStreamRef
  | .streamLocal r | .streamWithReserved r _ => some r
  | _ => none

/-- Association-list environment for C variables and macro constants. -/
abbrev CEnv := List (String × CVal)

def CEnv.lookup (env : CEnv) (name : String) : Option CVal :=
  match env with
  | [] => none
  | (k, v) :: rest => if k == name then some v else CEnv.lookup rest name

def CEnv.set (env : CEnv) (name : String) (v : CVal) : CEnv :=
  match env with
  | [] => [(name, v)]
  | (k, old) :: rest => if k == name then (k, v) :: rest else (k, old) :: CEnv.set rest name v

@[simp] theorem CEnv.lookup_cons_same (env : CEnv) (name : String) (v : CVal) :
    CEnv.lookup ((name, v) :: env) name = some v := by
  simp [CEnv.lookup]

@[simp] theorem CEnv.lookup_cons_ne (env : CEnv) {k name : String} (hne : (k == name) = false) (v : CVal) :
    CEnv.lookup ((k, v) :: env) name = CEnv.lookup env name := by
  simp [CEnv.lookup, hne]

@[simp] theorem CEnv.lookup_set_same (env : CEnv) (name : String) (v : CVal) :
    CEnv.lookup (CEnv.set env name v) name = some v := by
  induction env with
  | nil => simp [CEnv.set]
  | cons hd tl ih =>
    rcases hd with ⟨k, old⟩
    by_cases hk : k = name
    · subst hk; simp [CEnv.set]
    · have hne : (k == name) = false := beq_false_of_ne hk
      simp [CEnv.set, hne, ih]

theorem CEnv.lookup_set_ne (env : CEnv) {name x : String} (hne : name ≠ x) (v : CVal) :
    CEnv.lookup (CEnv.set env x v) name = CEnv.lookup env name := by
  induction env with
  | nil => simp [CEnv.set, beq_false_of_ne (Ne.symm hne)]
  | cons hd tl ih =>
    rcases hd with ⟨k, old⟩
    by_cases hkx : k = x
    · subst hkx
      simp [CEnv.set, beq_false_of_ne (Ne.symm hne)]
    · by_cases hkn : k = name
      · subst hkn
        have h1 : (k == x) = false := beq_false_of_ne hkx
        simp [CEnv.set, h1]
      · have h1 : (k == x) = false := beq_false_of_ne hkx
        have h2 : (k == name) = false := beq_false_of_ne hkn
        simp [CEnv.set, h1, h2, ih]

/-- C99 truthiness of a scalar or pointer value. -/
def CVal.toBool? : CVal → Option Bool
  | .bool b => some b
  | .u8 x => some (x != 0)
  | .u16 x => some (x != 0)
  | .u32 x => some (x != 0)
  | .u64 x => some (x != 0)
  | .i32 x => some (x != 0)
  | .i64 x => some (x != 0)
  | .ptr p => some (p != .null)
  | .functionPtr p => some (p != .null)
  | .stringTable _ => some true
  | .streamLocal _ | .streamWithReserved .. => none
  | .void => none

/-- Exact mathematical integer value of a scalar C value. -/
def CVal.toInt? : CVal → Option Int
  | .bool b => some (if b then 1 else 0)
  | .u8 x => some (Int.ofNat x.toNat)
  | .u16 x => some (Int.ofNat x.toNat)
  | .u32 x => some (Int.ofNat x.toNat)
  | .u64 x => some (Int.ofNat x.toNat)
  | .i32 x => some x.toInt
  | .i64 x => some x.toInt
  | _ => none

/-- Bit width of an integer `Ty` on LP64. -/
def bitWidth? : Ty → Option Nat
  | .bool => some 1
  | .u8 => some 8
  | .u16 => some 16
  | .u32 => some 32
  | .i32 => some 32
  | .u64 => some 64
  | .i64 => some 64
  | _ => none

/-- Construct a `CVal` from an integer at target C type using LP64 two's-complement conversion. -/
def ofIntForTy (ty : Ty) (z : Int) : Except Fault CVal :=
  match ty with
  | .bool => .ok (.bool (z != 0))
  | .u8 => .ok (.u8 (UInt8.ofInt z))
  | .u16 => .ok (.u16 (UInt16.ofInt z))
  | .u32 => .ok (.u32 (UInt32.ofInt z))
  | .u64 => .ok (.u64 (UInt64.ofInt z))
  | .i32 => .ok (.i32 (Int32.ofInt z))
  | .i64 => .ok (.i64 (Int64.ofInt z))
  | _ => .error (.ub s!"unsupported scalar target type {ty.render}")

/-- Construct a non-negative numeric literal. -/
def evalNum (ty : Ty) (n : Nat) : Except Fault CVal :=
  match ty with
  | .bool => .ok (.bool (n != 0))
  | .u8 => .ok (.u8 (UInt8.ofNat n))
  | .u16 => .ok (.u16 (UInt16.ofNat n))
  | .u32 => .ok (.u32 (UInt32.ofNat n))
  | .i32 =>
    if n < 2^31 then .ok (.i32 (Int32.ofNat n))
    else .error (.ub s!"signed int32 literal out of range: {n}")
  | .u64 => .ok (.u64 (UInt64.ofNat n))
  | .i64 =>
    if n < 2^63 then .ok (.i64 (Int64.ofNat n))
    else .error (.ub s!"signed int64 literal out of range: {n}")
  | _ => .error (.ub s!"numeric literal cannot have type {ty.render}")

/-- C99 type cast between scalar or pointer values. -/
def evalCast (ty : Ty) (v : CVal) : Except Fault CVal :=
  match ty, v with
  | .void, _ => .ok .void
  | .ptr _, .ptr p => .ok (.ptr p)
  | .ptr _, .u64 0 => .ok (.ptr .null)
  | .ptr _, .i32 0 => .ok (.ptr .null)
  | .ptr _, .i64 0 => .ok (.ptr .null)
  | .named "alloc_func", .i32 0 | .named "free_func", .i32 0 => .ok (.functionPtr .null)
  | .named "alloc_func", .functionPtr p | .named "free_func", .functionPtr p => .ok (.functionPtr p)
  | .bool, _ =>
    match v.toBool? with
    | some b => .ok (.bool b)
    | none => .error (.ub "invalid cast to _Bool")
  | _, _ =>
    match v.toInt? with
    | some z => ofIntForTy ty z
    | none => .error (.ub s!"cannot cast value to {ty.render}")

def inSignedRange (width : Nat) (z : Int) : Bool :=
  let half : Int := Int.ofNat (2 ^ (width - 1))
  decide (-half ≤ z) && decide (z < half)

/-- Checked signed result on `i32` / `i64`: faults on C99 signed integer overflow. -/
def checkedSigned (ty : Ty) (z : Int) : Except Fault CVal :=
  match ty with
  | .i32 =>
    if inSignedRange 32 z then .ok (.i32 (Int32.ofInt z))
    else .error (.ub "signed 32-bit integer overflow")
  | .i64 =>
    if inSignedRange 64 z then .ok (.i64 (Int64.ofInt z))
    else .error (.ub "signed 64-bit integer overflow")
  | _ => .error (.ub "expected signed integer type")

/-- Relational comparison under C99 usual arithmetic conversions. -/
def evalRelOp (op : String) (lv rv : CVal) : Except Fault CVal := do
  let some lz := lv.toInt? | .error (.ub s!"non-scalar LHS in {op}")
  let some rz := rv.toInt? | .error (.ub s!"non-scalar RHS in {op}")
  let res := match lv, rv with
    | .u64 x, .u64 y =>
      match op with
      | "<" => x < y | "<=" => x <= y | ">" => y < x | ">=" => y <= x
      | "==" => x == y | _ => x != y
    | .u32 x, .u32 y =>
      match op with
      | "<" => x < y | "<=" => x <= y | ">" => y < x | ">=" => y <= x
      | "==" => x == y | _ => x != y
    | .i64 x, .i64 y =>
      match op with
      | "<" => x < y | "<=" => x <= y | ">" => y < x | ">=" => y <= x
      | "==" => x == y | _ => x != y
    | .i32 x, .i32 y =>
      match op with
      | "<" => x < y | "<=" => x <= y | ">" => y < x | ">=" => y <= x
      | "==" => x == y | _ => x != y
    | .u64 x, _ =>
      let y := UInt64.ofInt rz
      match op with
      | "<" => x < y | "<=" => x <= y | ">" => y < x | ">=" => y <= x
      | "==" => x == y | _ => x != y
    | _, .u64 y =>
      let x := UInt64.ofInt lz
      match op with
      | "<" => x < y | "<=" => x <= y | ">" => y < x | ">=" => y <= x
      | "==" => x == y | _ => x != y
    | .u32 x, _ =>
      let y := UInt32.ofInt rz
      match op with
      | "<" => x < y | "<=" => x <= y | ">" => y < x | ">=" => y <= x
      | "==" => x == y | _ => x != y
    | _, .u32 y =>
      let x := UInt32.ofInt lz
      match op with
      | "<" => x < y | "<=" => x <= y | ">" => y < x | ">=" => y <= x
      | "==" => x == y | _ => x != y
    | _, _ =>
      match op with
      | "<" => lz < rz | "<=" => lz ≤ rz | ">" => rz < lz | ">=" => rz ≤ lz
      | "==" => lz == rz | _ => lz != rz
  return .bool res

/-- Shift operators (`<<`, `>>`) with strict C99 width check (`0 ≤ rhs < width`) and signed left-shift check. -/
def evalShiftOp (ty : Ty) (op : String) (lv rv : CVal) : Except Fault CVal := do
  let some width := bitWidth? ty | .error (.ub s!"shift with invalid result type {ty.render}")
  let effWidth := if width < 32 then 32 else width
  let some shiftInt := rv.toInt? | .error (.ub "non-integer shift count")
  if shiftInt < 0 || Int.ofNat effWidth ≤ shiftInt then
    .error (.ub s!"C99 shift count {shiftInt} out of bounds for width {effWidth}")
  else
    let k := shiftInt.toNat
    match ty with
    | .u32 =>
      let .u32 x ← evalCast .u32 lv | .error (.ub "invalid shift LHS")
      return .u32 (if op == "<<" then x <<< UInt32.ofNat k else x >>> UInt32.ofNat k)
    | .u64 =>
      let .u64 x ← evalCast .u64 lv | .error (.ub "invalid shift LHS")
      return .u64 (if op == "<<" then x <<< UInt64.ofNat k else x >>> UInt64.ofNat k)
    | .i32 =>
      let .i32 x ← evalCast .i32 lv | .error (.ub "invalid shift LHS")
      if op == "<<" then
        if x.toInt < 0 then .error (.ub "C99 left shift of negative signed int")
        else return ← checkedSigned .i32 (x.toInt * Int.ofNat (2 ^ k))
      else
        return .i32 (Int32.ofInt (x.toInt / Int.ofNat (2 ^ k)))
    | .i64 =>
      let .i64 x ← evalCast .i64 lv | .error (.ub "invalid shift LHS")
      if op == "<<" then
        if x.toInt < 0 then .error (.ub "C99 left shift of negative signed long")
        else return ← checkedSigned .i64 (x.toInt * Int.ofNat (2 ^ k))
      else
        return .i64 (Int64.ofInt (x.toInt / Int.ofNat (2 ^ k)))
    | _ => .error (.ub s!"shift result type {ty.render} not promoted")

/-- Element size in bytes for the pinned LP64 scalar types. -/
def elementBytes : Ty → Option Nat
  | .bool | .u8 | .named "char" => some 1
  | .u16 => some 2
  | .u32 | .i32 => some 4
  | .u64 | .i64 | .ptr _ => some 8
  | _ => none

/-- C subscripts count elements while addresses in the byte heap count bytes. -/
def indexAddress (ty : Ty) (p : BPtr) (index : Int) : M BPtr := fun h => do
  let some width := elementBytes ty | .error (.ub s!"unsupported element size for {ty.render}")
  let .ref r start := p | .error (.ub "arithmetic on a null pointer")
  let some bytes := Space.get h r | .error (.ub "arithmetic on a dangling pointer")
  if start > bytes.size then .error (.ub "pointer outside its object")
  p.add (index * (width : Int)) h

/-- Pointer subtraction is measured in elements of the common array. Check the
range of the element count before converting it to the target's ptrdiff_t. -/
def elementDifference (ty : Ty) (p q : BPtr) : M Int64 := fun h => do
  let some width := elementBytes ty | .error (.ub s!"unsupported element size for {ty.render}")
  let .ref r i := p | .error (.ub (if q == .null then "subtraction of a null pointer"
                                   else "difference of a null pointer and another pointer"))
  let .ref other j := q | .error (.ub "difference of a null pointer and another pointer")
  if r != other then .error (.ub "difference of pointers into different objects")
  let some bytes := Space.get h r | .error (.ub "difference of dangling pointers")
  if i > bytes.size || j > bytes.size then .error (.ub "pointer outside its object")
  let distance := (i : Int) - (j : Int)
  if distance % (width : Int) != 0 then .error (.ub "difference is not a whole number of elements")
  let count := distance / (width : Int)
  if inSignedRange 64 count then return (Int64.ofInt count, h)
  else .error (.ub "pointer difference is not a ptrdiff_t")

/-- The typed operand determines the unit of pointer arithmetic, including subtraction
whose result type is a signed integer. -/
def pointerElement (left right : Value) : Ty :=
  match left.type, right.type with
  | .ptr ty, _ | _, .ptr ty => ty
  | _, _ => .u8

/-- Pointer binary operations (`+`, `-`, `==`, `!=`) against the live `Heap`. -/
def evalPtrOp (op : String) (lv rv : CVal) (h : C.Heap) (element : Ty := .u8) : Except Fault CVal := do
  match lv, op, rv with
  | .ptr p, "==", .ptr q => return .bool (p == q)
  | .ptr p, "!=", .ptr q => return .bool (p != q)
  | .ptr p, "==", .u64 0 | .ptr p, "==", .i32 0 | .ptr p, "==", .i64 0
  | .u64 0, "==", .ptr p | .i32 0, "==", .ptr p | .i64 0, "==", .ptr p =>
    return .bool (p == .null)
  | .ptr p, "!=", .u64 0 | .ptr p, "!=", .i32 0 | .ptr p, "!=", .i64 0
  | .u64 0, "!=", .ptr p | .i32 0, "!=", .ptr p | .i64 0, "!=", .ptr p =>
    return .bool (p != .null)
  | .ptr p, "-", .ptr q =>
    let (d, _) ← elementDifference element p q h
    return .i64 d
  | .ptr p, "+", v | v, "+", .ptr p =>
    let some off := v.toInt? | .error (.ub "pointer addition with non-integer")
    let (p', _) ← indexAddress element p off h
    return .ptr p'
  | .ptr p, "-", v =>
    let some off := v.toInt? | .error (.ub "pointer subtraction with non-integer")
    let (p', _) ← indexAddress element p (-off) h
    return .ptr p'
  | _, _, _ => .error (.ub s!"unsupported pointer operator {op}")

/-- C99 LP64 binary operator semantics on already-evaluated operands. -/
def evalBinOp (ty : Ty) (op : String) (lv rv : CVal) (h : C.Heap := C.Heap.empty)
    (element : Ty := .u8) :
    Except Fault CVal := do
  if lv matches .ptr _ || rv matches .ptr _ then
    return ← evalPtrOp op lv rv h element
  if ["<", "<=", ">", ">=", "==", "!="].contains op then
    return ← evalRelOp op lv rv
  if op == "<<" || op == ">>" then
    return ← evalShiftOp ty op lv rv
  let l' ← evalCast ty lv
  let r' ← evalCast ty rv
  match l', r' with
  | .u32 x, .u32 y =>
    match op with
    | "+" => return .u32 (x + y)
    | "-" => return .u32 (x - y)
    | "*" => return .u32 (x * y)
    | "/" => if y == 0 then .error (.ub "u32 division by zero") else return .u32 (x / y)
    | "%" => if y == 0 then .error (.ub "u32 modulo by zero") else return .u32 (x % y)
    | "&" => return .u32 (x &&& y)
    | "|" => return .u32 (x ||| y)
    | "^" => return .u32 (x ^^^ y)
    | _ => .error (.ub s!"unsupported u32 operator {op}")
  | .u64 x, .u64 y =>
    match op with
    | "+" => return .u64 (x + y)
    | "-" => return .u64 (x - y)
    | "*" => return .u64 (x * y)
    | "/" => if y == 0 then .error (.ub "u64 division by zero") else return .u64 (x / y)
    | "%" => if y == 0 then .error (.ub "u64 modulo by zero") else return .u64 (x % y)
    | "&" => return .u64 (x &&& y)
    | "|" => return .u64 (x ||| y)
    | "^" => return .u64 (x ^^^ y)
    | _ => .error (.ub s!"unsupported u64 operator {op}")
  | .i32 x, .i32 y =>
    let xi := x.toInt
    let yi := y.toInt
    match op with
    | "&" => return .i32 (x &&& y)
    | "|" => return .i32 (x ||| y)
    | "^" => return .i32 (x ^^^ y)
    | "+" => return ← checkedSigned .i32 (xi + yi)
    | "-" => return ← checkedSigned .i32 (xi - yi)
    | "*" => return ← checkedSigned .i32 (xi * yi)
    | "/" =>
      if yi == 0 then .error (.ub "i32 division by zero")
      else return ← checkedSigned .i32 (Int.tdiv xi yi)
    | "%" =>
      if yi == 0 then .error (.ub "i32 modulo by zero")
      else if xi == -(Int.ofNat (2^31)) && yi == -1 then .error (.ub "i32 modulo overflow")
      else return .i32 (Int32.ofInt (Int.tmod xi yi))
    | _ => .error (.ub s!"unsupported i32 operator {op}")
  | .i64 x, .i64 y =>
    let xi := x.toInt
    let yi := y.toInt
    match op with
    | "&" => return .i64 (x &&& y)
    | "|" => return .i64 (x ||| y)
    | "^" => return .i64 (x ^^^ y)
    | "+" => return ← checkedSigned .i64 (xi + yi)
    | "-" => return ← checkedSigned .i64 (xi - yi)
    | "*" => return ← checkedSigned .i64 (xi * yi)
    | "/" =>
      if yi == 0 then .error (.ub "i64 division by zero")
      else return ← checkedSigned .i64 (Int.tdiv xi yi)
    | "%" =>
      if yi == 0 then .error (.ub "i64 modulo by zero")
      else if xi == -(Int.ofNat (2^63)) && yi == -1 then .error (.ub "i64 modulo overflow")
      else return .i64 (Int64.ofInt (Int.tmod xi yi))
    | _ => .error (.ub s!"unsupported i64 operator {op}")
  | .u8 x, .u8 y =>
    match op with
    | "+" => return .u8 (x + y) | "-" => return .u8 (x - y) | "*" => return .u8 (x * y)
    | "&" => return .u8 (x &&& y) | "|" => return .u8 (x ||| y) | "^" => return .u8 (x ^^^ y)
    | _ => .error (.ub s!"unsupported u8 operator {op}")
  | .u16 x, .u16 y =>
    match op with
    | "+" => return .u16 (x + y) | "-" => return .u16 (x - y) | "*" => return .u16 (x * y)
    | "&" => return .u16 (x &&& y) | "|" => return .u16 (x ||| y) | "^" => return .u16 (x ^^^ y)
    | _ => .error (.ub s!"unsupported u16 operator {op}")
  | _, _ => .error (.ub s!"unsupported binary operator {op} on {ty.render}")

/-- Read a scalar value from `Heap` through `BPtr`. -/
def readHeap (ty : Ty) (p : C.BPtr) (h : C.Heap) : Except Fault CVal := do
  match ty with
  | .u8 =>
    let (v, _) ← C.load8 p h
    return .u8 v
  | .u64 =>
    if ByteAddress.value h p % 8 != 0 then .error (.ub "misaligned unsigned long load")
    let (v, _) ← C.load64 p h
    return .u64 v
  | _ => .error (.ub s!"unsupported heap load type {ty.render}")

/-- Store a scalar value into `Heap` through `BPtr`. -/
def writeHeap (ty : Ty) (p : C.BPtr) (v : CVal) (h : C.Heap) : Except Fault C.Heap := do
  match ty with
  | .u8 =>
    let .u8 b ← evalCast .u8 v | .error (.ub "expected byte value")
    let (_, h') ← C.store8 p b h
    return h'
  | .u64 =>
    if ByteAddress.value h p % 8 != 0 then .error (.ub "misaligned unsigned long store")
    let .u64 w ← evalCast .u64 v | .error (.ub "expected u64 value")
    let (_, h') ← C.store64 p w h
    return h'
  | _ => .error (.ub s!"unsupported heap store type {ty.render}")

/-- Subscript a static pointer table in elements. The literals have the addresses
assigned by the model's read-only string pool. -/
def readStringSlot (entries : Array String) (index : Int) : M CVal := do
  if index < 0 then ub "string table index below zero"
  let some text := entries[index.toNat]? | ub "string table index past the end"
  return .ptr (← strLitRef text)

def readStreamCount (ref : ZStreamRef) (field : String) : M UInt32 := do
  let z ← ldZStream (some ref)
  match field with
  | "avail_in" => return z.avail_in
  | "avail_out" => return z.avail_out
  | _ => ub "unsupported unsigned z_stream field"

def writeStreamCount (ref : ZStreamRef) (field : String) (n : UInt32) : M Unit := do
  let z ← ldZStream (some ref)
  match field with
  | "avail_in" => stZStream (some ref) {z with avail_in := n}
  | "avail_out" => stZStream (some ref) {z with avail_out := n}
  | _ => ub "unsupported unsigned z_stream field"

/-- Typed assignments to the fields of a local stream in the buffer utilities. -/
def writeStreamField (ref : ZStreamRef) (field : String) (v : CVal) : M Unit :=
  match v with
  | .u32 n => writeStreamCount ref field n
  | _ => do
    let z ← ldZStream (some ref)
    match field, v with
    | "next_in", .ptr p => stZStream (some ref) {z with next_in := p}
    | "next_out", .ptr p => stZStream (some ref) {z with next_out := p}
    | "opaque", .ptr p => stZStream (some ref) {z with «opaque» := p}
    | "zalloc", .functionPtr p => stZStream (some ref) {z with zalloc := p}
    | "zfree", .functionPtr p => stZStream (some ref) {z with zfree := p}
    | _, _ => ub "unsupported z_stream assignment"

@[simp] theorem writeStreamField_u32 (ref : ZStreamRef) (field : String) (v : UInt32) :
    writeStreamField ref field (.u32 v) = writeStreamCount ref field v := rfl

/-- Table of C functions lowered to `Lean2C.CSource` (`(params, stmts)`). -/
abbrev FnTable := String → Option (List (String × Ty) × List Stmt)

/-- Outcome of executing C statements. -/
inductive StmtOutcome where
  | next (env : CEnv) (h : C.Heap)
  | ret (val : CVal) (h : C.Heap)
  | brk (env : CEnv) (h : C.Heap)
  | fault (f : Fault)

/-- Default C constants emitted as macro `#define` identifiers by `Lean2C.Lower`. -/
def defaultCGlobals : CEnv :=
  [ ("BASE", .u64 65521)
  , ("NMAX", .u64 5552)
  , ("Z_OK", .i32 0)
  , ("Z_STREAM_END", .i32 1)
  , ("Z_NEED_DICT", .i32 2)
  , ("Z_ERRNO", .i32 (-1))
  , ("Z_STREAM_ERROR", .i32 (-2))
  , ("Z_DATA_ERROR", .i32 (-3))
  , ("Z_MEM_ERROR", .i32 (-4))
  , ("Z_BUF_ERROR", .i32 (-5))
  , ("Z_VERSION_ERROR", .i32 (-6))
  , ("Z_NULL", .i32 0)
  , ("OS_CODE", .u64 3)
  ]

def bindParams (params : List (String × Ty)) (vals : List CVal) : Except Fault CEnv :=
  match params, vals with
  | [], [] => .ok []
  | (n, t) :: ps, v :: vs => do
    let cv ← evalCast t v
    let rest ← bindParams ps vs
    return (n, cv) :: rest
  | _, _ => .error (.ub "parameter count mismatch")

mutual

/-- Evaluate a `CSource.Value`, returning the value, updated environment, and heap. -/
def evalValue (fns : FnTable) (globals : CEnv) (fuel : Nat) (env : CEnv) (h : C.Heap) (v : Value) :
    Except Fault (CVal × CEnv × C.Heap) :=
  match v with
  | .var _ name =>
    match env.lookup name with
    | some val => .ok (val, env, h)
    | none =>
      match globals.lookup name with
      | some val => .ok (val, env, h)
      | none => .error (.ub s!"unbound variable {name}")
  | .num ty n => do
    let val ← evalNum ty n
    return (val, env, h)
  | .cast ty arg => do
    let (av, env1, h1) ← evalValue fns globals fuel env h arg
    let res ← evalCast ty av
    return (res, env1, h1)
  | .op ty op lhs rhs => do
    if op == "&&" then
      let (lv, env1, h1) ← evalValue fns globals fuel env h lhs
      match lv.toBool? with
      | some false => return (.bool false, env1, h1)
      | some true =>
        let (rv, env2, h2) ← evalValue fns globals fuel env1 h1 rhs
        match rv.toBool? with
        | some b => return (.bool b, env2, h2)
        | none => .error (.ub "non-boolean RHS in &&")
      | none => .error (.ub "non-boolean LHS in &&")
    else if op == "||" then
      let (lv, env1, h1) ← evalValue fns globals fuel env h lhs
      match lv.toBool? with
      | some true => return (.bool true, env1, h1)
      | some false =>
        let (rv, env2, h2) ← evalValue fns globals fuel env1 h1 rhs
        match rv.toBool? with
        | some b => return (.bool b, env2, h2)
        | none => .error (.ub "non-boolean RHS in ||")
      | none => .error (.ub "non-boolean LHS in ||")
    else
      let (lv, env1, h1) ← evalValue fns globals fuel env h lhs
      let (rv, env2, h2) ← evalValue fns globals fuel env1 h1 rhs
      let res ← evalBinOp ty op lv rv h2 (pointerElement lhs rhs)
      return (res, env2, h2)
  | .choose cond yes no => do
    let (cv, env1, h1) ← evalValue fns globals fuel env h cond
    match cv.toBool? with
    | some true => evalValue fns globals fuel env1 h1 yes
    | some false => evalValue fns globals fuel env1 h1 no
    | none => .error (.ub "non-boolean ternary condition")
  | .load ty ptrExpr => do
    let (pv, env1, h1) ← evalValue fns globals fuel env h ptrExpr
    match pv with
    | .ptr p =>
      let val ← readHeap ty p h1
      return (val, env1, h1)
    | _ => .error (.ub "dereference of non-pointer")
  | .index ty ptrExpr offExpr => do
    let (pv, env1, h1) ← evalValue fns globals fuel env h ptrExpr
    let (ov, env2, h2) ← evalValue fns globals fuel env1 h1 offExpr
    match pv, ov.toInt? with
    | .stringTable entries, some off =>
      if ty != .ptr .u8 && ty != .ptr (.named "char") then
        .error (.ub "string table element has incompatible type")
      else
        let (val, h3) ← readStringSlot entries off h2
        return (val, env2, h3)
    | .ptr p, some off =>
      let (p', h3) ← indexAddress ty p off h2
      let val ← readHeap ty p' h3
      return (val, env2, h3)
    | _, _ => .error (.ub "invalid pointer index")
  | .addr (.field .u64 (.var (.named "z_stream") name) "reserved") =>
    match env.lookup name with
    | some (.streamWithReserved _ address) => .ok (.ptr address, env, h)
    | _ => .error (.ub "missing address for z_stream.reserved")
  | .field (.ptr .u8) (.var (.named "z_stream") name) "next_out" => do
    let some ref := (env.lookup name).bind CVal.streamRef? | .error (.ub "expected local z_stream object")
    let (stream, h') ← ldZStream (some ref) h
    return (.ptr stream.next_out, env, h')
  | .field .u32 (.var (.named "z_stream") name) member => do
    let some ref := (env.lookup name).bind CVal.streamRef? | .error (.ub "expected local z_stream object")
    let (n, h') ← readStreamCount ref member h
    return (.u32 n, env, h')
  | .postDec (.var ty name) => do
    let some cur := env.lookup name | .error (.ub s!"unbound variable {name}")
    let dec ← evalBinOp ty "-" cur (.i32 1) h
    return (cur, env.set name dec, h)
  | .preDec (.var ty name) => do
    let some cur := env.lookup name | .error (.ub s!"unbound variable {name}")
    let dec ← evalBinOp ty "-" cur (.i32 1) h
    return (dec, env.set name dec, h)
  | .call _ name args => do
    let (argVals, env1, h1) ← evalArgs fns globals fuel env h args
    match fuel with
    | 0 => .error .outOfFuel
    | fuel' + 1 =>
      match fns name with
      | some (params, body) =>
        if argVals.length ≠ params.length then
          .error (.ub s!"arity mismatch calling {name}")
        else
          let calleeEnv ← bindParams params argVals
          match execStmts fns globals fuel' calleeEnv h1 body with
          | .ret rv h2 => return (rv, env1, h2)
          | .next _ h2 => return (.void, env1, h2)
          | .brk _ _ => .error (.ub s!"uncaught break in {name}")
          | .fault f => .error f
      | none => .error (.ub s!"unknown function {name}")
  | _ => .error (.ub "unsupported expression form")
termination_by (fuel, sizeOf v)

def evalArgs (fns : FnTable) (globals : CEnv) (fuel : Nat) (env : CEnv) (h : C.Heap)
    (args : List Value) : Except Fault (List CVal × CEnv × C.Heap) :=
  match args with
  | [] => .ok ([], env, h)
  | a :: rest => do
    let (av, env1, h1) ← evalValue fns globals fuel env h a
    let (rvs, env2, h2) ← evalArgs fns globals fuel env1 h1 rest
    return (av :: rvs, env2, h2)
termination_by (fuel, sizeOf args)

/-- Execute a single `CSource.Stmt`. Loops (`while`, `do-while`) consume one unit of `fuel` per iteration. -/
def execStmt (fns : FnTable) (globals : CEnv) (fuel : Nat) (env : CEnv) (h : C.Heap) (s : Stmt) :
    StmtOutcome :=
  match s with
  | .decl _ name none => .next (env.set name .void) h
  | .decl ty name (some initExpr) =>
    match evalValue fns globals fuel env h initExpr with
    | .error f => .fault f
    | .ok (iv, env1, h1) =>
      match evalCast ty iv with
      | .error f => .fault f
      | .ok cv => .next (env1.set name cv) h1
  | .assign (.var ty name) rhs =>
    match evalValue fns globals fuel env h rhs with
    | .error f => .fault f
    | .ok (rv, env1, h1) =>
      match evalCast ty rv with
      | .error f => .fault f
      | .ok cv => .next (env1.set name cv) h1
  | .assign (.field ty (.var (.named "z_stream") name) member) rhs =>
    match (env.lookup name).bind CVal.streamRef? with
    | some ref =>
      match evalValue fns globals fuel env h rhs with
      | .error fault => .fault fault
      | .ok (value, env1, h1) =>
        match evalCast ty value with
        | .ok converted =>
          match writeStreamField ref member converted h1 with
          | .ok (_, h2) => .next env1 h2
          | .error fault => .fault fault
        | .error fault => .fault fault
    | _ => .fault (.ub "expected local z_stream object")
  | .assign (.load ty ptrExpr) rhs =>
    match evalValue fns globals fuel env h ptrExpr with
    | .error f => .fault f
    | .ok (pv, env1, h1) =>
      match evalValue fns globals fuel env1 h1 rhs with
      | .error f => .fault f
      | .ok (rv, env2, h2) =>
        match pv with
        | .ptr p =>
          match writeHeap ty p rv h2 with
          | .error f => .fault f
          | .ok h3 => .next env2 h3
        | _ => .fault (.ub "store through non-pointer")
  | .assign (.index ty ptrExpr offExpr) rhs =>
    match evalValue fns globals fuel env h ptrExpr with
    | .error f => .fault f
    | .ok (pv, env1, h1) =>
      match evalValue fns globals fuel env1 h1 offExpr with
      | .error f => .fault f
      | .ok (ov, env2, h2) =>
        match evalValue fns globals fuel env2 h2 rhs with
        | .error f => .fault f
        | .ok (rv, env3, h3) =>
          match pv, ov.toInt? with
          | .ptr p, some off =>
            match indexAddress ty p off h3 with
            | .error f => .fault f
            | .ok (p', h4) =>
              match writeHeap ty p' rv h4 with
              | .error f => .fault f
              | .ok h5 => .next env3 h5
          | _, _ => .fault (.ub "indexed store through invalid pointer")
  | .assign _ _ => .fault (.ub "unsupported assignment place")
  | .eval expr =>
    match evalValue fns globals fuel env h expr with
    | .error f => .fault f
    | .ok (_, env1, h1) => .next env1 h1
  | .ret expr =>
    match evalValue fns globals fuel env h expr with
    | .error f => .fault f
    | .ok (rv, _, h1) => .ret rv h1
  | .branch cond yes no =>
    match evalValue fns globals fuel env h cond with
    | .error f => .fault f
    | .ok (cv, env1, h1) =>
      match cv.toBool? with
      | some true => execStmts fns globals fuel env1 h1 yes
      | some false => execStmts fns globals fuel env1 h1 no
      | none => .fault (.ub "non-boolean branch condition")
  | .stop => .brk env h
  | .loop cond body =>
    match fuel with
    | 0 => .fault .outOfFuel
    | fuel' + 1 =>
      match evalValue fns globals fuel' env h cond with
      | .error f => .fault f
      | .ok (cv, env1, h1) =>
        match cv.toBool? with
        | none => .fault (.ub "non-boolean while condition")
        | some false => .next env1 h1
        | some true =>
          match execStmts fns globals fuel' env1 h1 body with
          | .next env2 h2 => execStmt fns globals fuel' env2 h2 (.loop cond body)
          | .brk env2 h2 => .next env2 h2
          | .ret rv h2 => .ret rv h2
          | .fault f => .fault f
  | .doLoop body cond =>
    match fuel with
    | 0 => .fault .outOfFuel
    | fuel' + 1 =>
      match execStmts fns globals fuel' env h body with
      | .next env1 h1 =>
        match evalValue fns globals fuel' env1 h1 cond with
        | .error f => .fault f
        | .ok (cv, env2, h2) =>
          match cv.toBool? with
          | none => .fault (.ub "non-boolean do-while condition")
          | some false => .next env2 h2
          | some true => execStmt fns globals fuel' env2 h2 (.doLoop body cond)
      | .brk env1 h1 => .next env1 h1
      | .ret rv h1 => .ret rv h1
      | .fault f => .fault f
termination_by (fuel, sizeOf s)

def execStmts (fns : FnTable) (globals : CEnv) (fuel : Nat) (env : CEnv) (h : C.Heap)
    (ss : List Stmt) : StmtOutcome :=
  match ss with
  | [] => .next env h
  | s :: rest =>
    match execStmt fns globals fuel env h s with
    | .next env1 h1 => execStmts fns globals fuel env1 h1 rest
    | .brk env1 h1 => .brk env1 h1
    | .ret rv h1 => .ret rv h1
    | .fault f => .fault f
termination_by (fuel, sizeOf ss)

end

/-- Run a lowered C function (`(params, body)`) on concrete argument values and initial heap. -/
def runCFn (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (fn : List (String × Ty) × List Stmt) (args : List CVal) (h : C.Heap) : StmtOutcome :=
  match bindParams fn.1 args with
  | .error f => .fault f
  | .ok initEnv => execStmts fns globals fuel initEnv h fn.2

end Lean2C.Semantics
