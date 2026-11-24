import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Address
import ZlibF.Runtime.ControlFlow

/-!
# Runtime: pure C ABI surface annotations

`@[reducible]` / `abbrev` type wrappers over `ZlibF.Runtime.Schema` types.
Every wrapper is definitionally equal to its underlying Lean type, so existing
safety proofs remain unchanged while `Lean2C` derives C signatures, pointer
qualifiers, linkage, globals, and stack storage purely from Lean types.
-/

namespace C

/-- The first byte of a C string literal, including the terminating byte of `""`. -/
def literalFirstByte (s : String) : UInt8 := s.toUTF8[0]?.getD 0

/-- Pointer qualifiers over `BPtr`, `WPtr`, `CodePtr`, and `UPtr`. -/
abbrev ConstBPtr := BPtr
abbrev CStr := BPtr
abbrev ConstCStr := BPtr
abbrev VoidPtr := BPtr
abbrev ConstVoidPtr := BPtr
abbrev ConstWPtr := WPtr
abbrev ConstCodePtr := CodePtr
abbrev ConstCtDataPtr := CtDataPtr
abbrev ConstIPtr := IPtr
abbrev ConstUPtr := UPtr

/-- Out/in-out pointer conventions. -/
abbrev PtrU32 := BPtr
abbrev PtrU64 := BPtr
abbrev OutCodePtr := CodePtr
abbrev OutUInt32 := UInt32
abbrev OutInt32 := BPtr

/-- Scalar C ABI aliases. -/
abbrev ZOffT := Int64
abbrev ZOff64T := Int64
abbrev CodeType := UInt32
abbrev ZCrcT := UInt32
abbrev ZWordT := UInt32

/-- Automatic (stack) storage type markers. -/
abbrev StackStream := ZStreamPtr
abbrev StackScalar64 := BPtr
abbrev StackScalar32 := BPtr
abbrev StackByte := BPtr

/-- Field address helper: equal to `fallback` in Lean, lowered as `(unsigned char *)(&<base>.<field>)` in C. -/
abbrev stackAddr {α β : Type} (_base : α) (_field : String) (fallback : β) : β := fallback

/-- Read-only word table pointer (`const unsigned short *`) backed by an `Array UInt16` in Lean. -/
abbrev ConstWTable := Array UInt16

/-- Function linkage and external C symbol annotations. -/
abbrev CExport (α : Type) := α
abbrev CExportAs (_cname : String) (α : Type) := α
abbrev CHidden (α : Type) := α
abbrev CHiddenAs (_cname : String) (α : Type) := α
abbrev CStatic (α : Type) := α
abbrev CStaticAs (_cname : String) (α : Type) := α
abbrev CStaticInline (α : Type) := α
abbrev COrder (_order : Nat) (α : Type) := α

/-- Source operand order for a pointer comparison, using the checked same-object relation. -/
def Ptr.gt {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) : M Bool := Ptr.lt q p

/-- The lowest-addressed byte of an unsigned integer on the pinned little-endian target. -/
def firstByte32 (word : UInt32) : UInt8 := word.toUInt8

/-- Read the four-byte representation of an unsigned word on the little-endian target. -/
def memcpyLoad32 (p : ConstBPtr) : M UInt32 := do
  let mut w : UInt32 := 0
  for i in [0:4] do
    let b ← index8 p i
    w := w ||| (b.toUInt32 <<< (8 * i).toUInt32)
  pure w

/-- `zmemcpy(&v, p, 8)`: unaligned 8-byte little-endian read (`memcpy(&v, p, 8)` in C). -/
def memcpyLoad64 (p : ConstBPtr) : M UInt64 := do
  let b0 ← index8 p 0
  let b1 ← index8 p 1
  let b2 ← index8 p 2
  let b3 ← index8 p 3
  let b4 ← index8 p 4
  let b5 ← index8 p 5
  let b6 ← index8 p 6
  let b7 ← index8 p 7
  pure (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
    (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56))

/-- `zmemcpy(dst, &v, 8)`: unaligned 8-byte little-endian store (`memcpy(dst, &v, 8)` in C). -/
def memcpyStore64 (dst : BPtr) (v : UInt64) : M Unit := do
  store8 dst (v &&& 0xff).toUInt8
  store8 (← dst.add 1) ((v >>> 8) &&& 0xff).toUInt8
  store8 (← dst.add 2) ((v >>> 16) &&& 0xff).toUInt8
  store8 (← dst.add 3) ((v >>> 24) &&& 0xff).toUInt8
  store8 (← dst.add 4) ((v >>> 32) &&& 0xff).toUInt8
  store8 (← dst.add 5) ((v >>> 40) &&& 0xff).toUInt8
  store8 (← dst.add 6) ((v >>> 48) &&& 0xff).toUInt8
  store8 (← dst.add 7) ((v >>> 56) &&& 0xff).toUInt8

/-- Global constant and function-local static constant table annotations. -/
abbrev CGlobalConstStr (α : Type) := α
abbrev CGlobalConstStrArray (α : Type) := α
abbrev CLocalConst (α : Type) := α

/-- `*(int *)p` -/
def load32 (p : BPtr) : M Int32 := do
  let b0 ← index8 p 0; let b1 ← index8 p 1; let b2 ← index8 p 2; let b3 ← index8 p 3
  return (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)).toInt32

/-- `*(int *)p = v` -/
def store32 (p : BPtr) (v : Int32) : M Unit := do
  let u := v.toUInt32
  store8 (← p.add 0) u.toUInt8
  store8 (← p.add 1) (u >>> 8).toUInt8
  store8 (← p.add 2) (u >>> 16).toUInt8
  store8 (← p.add 3) (u >>> 24).toUInt8

/-- Store through an `unsigned *` into modeled byte storage on the pinned
    x86-64 ABI. The low address bits include the origin of embedded arrays. -/
def storeU32 (p : PtrU32) (v : UInt32) : M Unit := fun h =>
  if ByteAddress.value h p % 4 == 0 then store32 p v.toInt32 h
  else .error (.ub "misaligned unsigned int store")

/-- Aligned scalar accesses in byte storage on the pinned ABI. -/
def loadU32 (p : PtrU32) : M UInt32 := fun h =>
  if ByteAddress.value h p % 4 == 0 then (do return (← load32 p).toUInt32 : M UInt32) h
  else .error (.ub "misaligned unsigned int load")

def storeI32 (p : OutInt32) (v : Int32) : M Unit := fun h =>
  if ByteAddress.value h p % 4 == 0 then store32 p v h
  else .error (.ub "misaligned int store")

/-- An unsigned output parameter may name a byte-backed word or a counter
    embedded in a live gzip or inflate state. -/
inductive UInt32Cell where
  | bytes (p : BPtr)
  | gzHave (p : GzStatePtr)
  | inflateHave (p : InflateStatePtr)

def UInt32Cell.read : UInt32Cell → M UInt32
  | .bytes p => do return (← load32 p).toUInt32
  | .gzHave p => do return (← ldGzState p).x.«have»
  | .inflateHave p => do return (← ldInflateState p).«have»

def UInt32Cell.write (cell : UInt32Cell) (value : UInt32) : M Unit := do
  match cell with
  | .bytes p => store32 p value.toInt32
  | .gzHave p =>
    let s ← ldGzState p
    stGzState p { s with x := { s.x with «have» := value } }
  | .inflateHave p =>
    let s ← ldInflateState p
    stInflateState p { s with «have» := value }

/-- `*(uint64_t *)p` -/
def load64 (p : BPtr) : M UInt64 := do
  let mut v : UInt64 := 0
  for i in [0:8] do
    v := v ||| ((← index8 p i).toUInt64 <<< (8 * i).toUInt64)
  return v

/-- `*(uint64_t *)p = v` -/
def store64 (p : BPtr) (v : UInt64) : M Unit := do
  for i in [0:8] do
    store8 (← p.add i) (v >>> (8 * i).toUInt64).toUInt8

end C
