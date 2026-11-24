import C99.AST

/-!
# Flat Byte-Block Memory Model (`C99.Mem`)

CompCert-style flat byte-block memory model for x86-64 LP64.
- Memory is a map from never-reused `BlockId`s to `Block`s (`blocks b = none` means unallocated or freed).
- Each byte is `undef`, a concrete `UInt8`, or a fragment of a block/function pointer,
  supporting `memcpy` over structs containing pointers as well as byte-level reinterpretation.
- Every block carries its size `< 2^63` (`PTRDIFF_MAX` bound), alignment, and aligned base address.
-/

namespace C99

abbrev BlockId := Nat
abbrev SymId := String

inductive AllocKind where
  | heap | stack | global
  deriving DecidableEq, Repr, Inhabited

inductive Perm where
  | ro | rw
  deriving DecidableEq, Repr, Inhabited

inductive MemByte where
  | undef
  | byte (b : UInt8)
  | ptrFrag (b : BlockId) (off : Int64) (idx : Fin 8)
  | fnFrag (sym : SymId) (idx : Fin 8)
  deriving DecidableEq, Repr, Inhabited

def ptrDiffLimit : Nat := 2 ^ 63

structure Block where
  size : Nat
  align : Nat
  perm : Perm
  kind : AllocKind
  baseAddr : UInt64
  bytes : Nat → MemByte
  sizeLt : size < ptrDiffLimit
  alignPos : 0 < align
  baseAligned : baseAddr.toNat % align = 0

structure Mem where
  blocks : BlockId → Option Block
  nextBlock : BlockId
  fresh : ∀ b, nextBlock ≤ b → blocks b = none

namespace Mem

def empty : Mem where
  blocks := fun _ => none
  nextBlock := 0
  fresh := fun _ _ => rfl

def alloc (m : Mem) (size align : Nat) (perm : Perm) (kind : AllocKind)
    (baseAddr : UInt64) (init : Nat → MemByte)
    (hsz : size < ptrDiffLimit) (hal : 0 < align)
    (hba : baseAddr.toNat % align = 0) : BlockId × Mem :=
  let blk : Block := { size, align, perm, kind, baseAddr, bytes := init, sizeLt := hsz, alignPos := hal, baseAligned := hba }
  let m' : Mem :=
    { blocks := fun b => if b == m.nextBlock then some blk else m.blocks b
      nextBlock := m.nextBlock + 1
      fresh := by
        intro b hb
        have hne : (b == m.nextBlock) = false := beq_false_of_ne (Nat.ne_of_gt hb)
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        exact m.fresh b (Nat.le_trans (Nat.le_succ _) hb) }
  (m.nextBlock, m')

def free (m : Mem) (bid : BlockId) : Option Mem :=
  match m.blocks bid with
  | some blk =>
    if blk.kind == .heap then
      some {
        blocks := fun b => if b == bid then none else m.blocks b
        nextBlock := m.nextBlock
        fresh := by
          intro b hb
          split
          · rfl
          · exact m.fresh b hb
      }
    else none
  | none => none

def freeStack (m : Mem) (bids : List BlockId) : Mem :=
  { blocks := fun b =>
      if bids.contains b then
        match m.blocks b with
        | some blk => if blk.kind == .stack then none else m.blocks b
        | none => none
      else m.blocks b
    nextBlock := m.nextBlock
    fresh := by
      intro b hb
      split
      · rw [m.fresh b hb]
      · exact m.fresh b hb }

/-- Invalidate a single block regardless of `AllocKind` (used only by OS runtime for `strerror`). -/
def dropBlock (m : Mem) (bid : BlockId) : Mem :=
  { blocks := fun b => if b == bid then none else m.blocks b
    nextBlock := m.nextBlock
    fresh := by
      intro b hb
      split
      · rfl
      · exact m.fresh b hb }

def inBounds (blk : Block) (off : Int64) (len : Nat) : Bool :=
  0 ≤ off.toInt && decide (off.toInt.toNat + len ≤ blk.size)

def isAligned (blk : Block) (off : Int64) (align : Nat) : Bool :=
  0 ≤ off.toInt && align > 0 && decide ((blk.baseAddr.toNat + off.toInt.toNat) % align == 0)

def addrOf (m : Mem) (b : BlockId) (off : Int64) : Option UInt64 :=
  match m.blocks b with
  | some blk =>
    if 0 ≤ off.toInt && off.toInt ≤ (blk.size : Int) then
      some (blk.baseAddr + UInt64.ofNat off.toInt.toNat)
    else none
  | none => none

def readBytes (m : Mem) (b : BlockId) (off : Int64) (len : Nat) : Option (List MemByte) := do
  let blk ← m.blocks b
  guard (inBounds blk off len)
  let base := off.toInt.toNat
  return (List.range len).map fun i => blk.bytes (base + i)

def writeBytes (m : Mem) (b : BlockId) (off : Int64) (bs : List MemByte) : Option Mem :=
  match hblk : m.blocks b with
  | none => none
  | some blk =>
    if blk.perm == .rw && inBounds blk off bs.length then
      let base := off.toInt.toNat
      let blk' : Block :=
        { blk with
          bytes := fun i =>
            if base ≤ i ∧ i < base + bs.length then bs[i - base]?.getD .undef
            else blk.bytes i }
      some {
        blocks := fun x => if x == b then some blk' else m.blocks x
        nextBlock := m.nextBlock
        fresh := by
          intro x hx
          have hne : (x == b) = false := beq_false_of_ne (by
            intro hxb
            subst hxb
            rw [m.fresh x hx] at hblk
            cases hblk)
          simp [hne, m.fresh x hx]
      }
    else none

/-- Check whether `b[off .. off + len)` is a NUL-terminated readable C string; returns `strlen`. -/
def strlenAt (m : Mem) (b : BlockId) (off : Int64) : Option Nat := do
  let blk ← m.blocks b
  guard (0 ≤ off.toInt && off.toInt.toNat ≤ blk.size)
  let start := off.toInt.toNat
  let rec go (i : Nat) : Option Nat :=
    if _ : i < blk.size then
      match blk.bytes i with
      | .byte 0 => some (i - start)
      | .byte _ => go (i + 1)
      | _ => none
    else none
  termination_by blk.size - i
  go start

/-! ## Scalar Byte Encoding / Decoding (Little-Endian LP64) -/

def encodeInt (k : IntKind) (v : BitVec k.bits) : List MemByte :=
  (List.range k.bytes).map fun i =>
    MemByte.byte (UInt8.ofNat ((v.toNat >>> (8 * i)) % 256))

def decodeInt (k : IntKind) (bs : List MemByte) : Option (BitVec k.bits) := do
  guard (bs.length == k.bytes)
  let rec go (acc : Nat) (shift : Nat) : List MemByte → Option Nat
    | [] => some acc
    | .byte b :: rest => go (acc ||| (b.toNat <<< shift)) (shift + 8) rest
    | _ => none
  let n ← go 0 0 bs
  return BitVec.ofNat k.bits n

def encodePtr (b : BlockId) (off : Int64) : List MemByte :=
  (List.range 8).map fun i =>
    if h : i < 8 then MemByte.ptrFrag b off ⟨i, h⟩ else MemByte.undef

def encodeFnPtr (sym : SymId) : List MemByte :=
  (List.range 8).map fun i =>
    if h : i < 8 then MemByte.fnFrag sym ⟨i, h⟩ else MemByte.undef

def encodeNull : List MemByte :=
  List.replicate 8 (MemByte.byte 0)

inductive DecodedPtr where
  | null
  | ptr (b : BlockId) (off : Int64)
  | fnPtr (sym : SymId)
  deriving DecidableEq, Repr, Inhabited

def decodePtr (bs : List MemByte) : Option DecodedPtr := do
  guard (bs.length == 8)
  if bs.all (· == MemByte.byte 0) then
    return .null
  match bs with
  | [.ptrFrag b o ⟨0, _⟩, .ptrFrag b1 o1 ⟨1, _⟩, .ptrFrag b2 o2 ⟨2, _⟩, .ptrFrag b3 o3 ⟨3, _⟩,
     .ptrFrag b4 o4 ⟨4, _⟩, .ptrFrag b5 o5 ⟨5, _⟩, .ptrFrag b6 o6 ⟨6, _⟩, .ptrFrag b7 o7 ⟨7, _⟩] =>
    guard (b == b1 && b == b2 && b == b3 && b == b4 && b == b5 && b == b6 && b == b7 &&
           o == o1 && o == o2 && o == o3 && o == o4 && o == o5 && o == o6 && o == o7)
    return .ptr b o
  | [.fnFrag s ⟨0, _⟩, .fnFrag s1 ⟨1, _⟩, .fnFrag s2 ⟨2, _⟩, .fnFrag s3 ⟨3, _⟩,
     .fnFrag s4 ⟨4, _⟩, .fnFrag s5 ⟨5, _⟩, .fnFrag s6 ⟨6, _⟩, .fnFrag s7 ⟨7, _⟩] =>
    guard (s == s1 && s == s2 && s == s3 && s == s4 && s == s5 && s == s6 && s == s7)
    return .fnPtr s
  | _ => none

end Mem
end C99
