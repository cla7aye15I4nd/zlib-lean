import ZlibF.Runtime.Alloc

/-!
# Runtime: pure C ABI surface annotations

`@[reducible]` / `abbrev` type wrappers over `ZlibF.Runtime.Schema` types.
Every wrapper is definitionally equal to its underlying Lean type, so existing
safety proofs remain unchanged while `Lean2C` derives C signatures, pointer
qualifiers, linkage, globals, and stack storage purely from Lean types.
-/

namespace C

/-- Pointer qualifiers over `BPtr`, `WPtr`, `CodePtr`, and `UPtr`. -/
abbrev ConstBPtr := BPtr
abbrev CStr := BPtr
abbrev ConstCStr := BPtr
abbrev VoidPtr := BPtr
abbrev ConstVoidPtr := BPtr
abbrev ConstWPtr := WPtr
abbrev ConstCodePtr := CodePtr
abbrev ConstUPtr := UPtr

/-- Out/in-out pointer conventions. -/
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

/-- Field address helper: equal to `fallback` in Lean, lowered as `(unsigned char *)(&<base>.<field>)` in C. -/
abbrev stackAddr {α β : Type} (_base : α) (_field : String) (fallback : β) : β := fallback

/-- Function linkage and external C symbol annotations. -/
abbrev CExport (α : Type) := α
abbrev CExportAs (_cname : String) (α : Type) := α
abbrev CHidden (α : Type) := α
abbrev CStatic (α : Type) := α
abbrev CStaticInline (α : Type) := α
abbrev COrder (_order : Nat) (α : Type) := α

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
