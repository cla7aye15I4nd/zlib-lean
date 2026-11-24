import C99.Mem

/-!
# Minimal Safety-Only Libc and Abstract POSIX Model (`C99.Libc`)

Defines C runtime values (`Val`), minimal OS state (`OSState`), and relational
external call semantics (`ExtStep`) for memory libc and POSIX/stdio functions
used by C programs. No mock filesystem or functional output equations are included.
-/

namespace C99

/-- Runtime C values on LP64. -/
inductive Val where
  | undef
  | void
  | int (k : IntKind) (v : BitVec k.bits)
  | ptr (b : BlockId) (off : Int64)
  | null
  | fnPtr (sym : SymId)
  | vaList (valid : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Minimal external OS state: an addressable `int errno` block, the active
`strerror` buffer block (invalidated on next call), and an optional finite read budget. -/
structure OSState where
  errnoBlk : BlockId
  strerrorBlk : Option BlockId := none
  readBudget : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

inductive ExtOutcome where
  | ok (ret : Val) (m' : Mem) (os' : OSState)
  | ub

namespace Libc

def allConcreteBytes : List MemByte → Option (List UInt8)
  | [] => some []
  | .byte b :: rest => return b :: (← allConcreteBytes rest)
  | _ => none

def memcmpBytes : List UInt8 → List UInt8 → Int32
  | [], [] => 0
  | x :: xs, y :: ys =>
    if x == y then memcmpBytes xs ys
    else if x < y then -1 else 1
  | _, _ => 0

def memchrStep (m : Mem) (b : BlockId) (off : Int64) (target : UInt8) (n : Nat) : Option Val := do
  let blk ← m.blocks b
  guard (0 ≤ off.toInt && off.toInt.toNat + n ≤ blk.size)
  let start := off.toInt.toNat
  let rec go (i : Nat) : Option Val :=
    if _ : i < n then
      match blk.bytes (start + i) with
      | .byte byte =>
        if byte == target then some (.ptr b (Int64.ofInt (off.toInt + i)))
        else go (i + 1)
      | _ => none
    else some .null
  termination_by n - i
  go 0

def hasPctN : List UInt8 → Bool
  | 37 :: 110 :: _ => true  -- '%' 'n'
  | 37 :: 37 :: rest => hasPctN rest
  | _ :: rest => hasPctN rest
  | [] => false

def hasNul : List MemByte → Bool
  | [] => false
  | .byte 0 :: _ => true
  | _ :: rest => hasNul rest

def writeErrno (m : Mem) (os : OSState) (e : Int32) : Option Mem :=
  m.writeBytes os.errnoBlk 0 (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt))

def ptrDisjointOrEq (b1 : BlockId) (o1 : Int64) (b2 : BlockId) (o2 : Int64) (n : Nat) : Bool :=
  b1 != b2 || o1.toInt + n ≤ o2.toInt || o2.toInt + n ≤ o1.toInt

def validWritableRange (m : Mem) (b : BlockId) (off : Int64) (n : Nat) : Bool :=
  match m.blocks b with
  | some blk => blk.perm == .rw && Mem.inBounds blk off n
  | none => false

def validReadableRange (m : Mem) (b : BlockId) (off : Int64) (n : Nat) : Bool :=
  match m.blocks b with
  | some blk => Mem.inBounds blk off n
  | none => false

def printfFmtOk (m : Mem) (bf : BlockId) (of_ : Int64) : Prop :=
  ∃ flen rawFmt fmtBytes,
    m.strlenAt bf of_ = some flen ∧ m.readBytes bf of_ flen = some rawFmt ∧
    allConcreteBytes rawFmt = some fmtBytes ∧ hasPctN fmtBytes = false

/-- Relational safety-only valid transitions of external libc / POSIX calls. -/
inductive ExtOk : String → List Val → Mem → OSState → Val → Mem → OSState → Prop where
  | malloc_null (n : Nat) (m : Mem) (os : OSState) :
      ExtOk "malloc" [.int .u64 (BitVec.ofNat 64 n)] m os .null m os
  | malloc_ok (n : Nat) (hsz : n < ptrDiffLimit) (base : UInt64) (hba : base.toNat % 16 = 0)
      (m m' : Mem) (bid : BlockId) (os : OSState)
      (halloc : m.alloc n 16 .rw .heap base (fun _ => .undef) hsz (by decide) hba = (bid, m')) :
      ExtOk "malloc" [.int .u64 (BitVec.ofNat 64 n)] m os (.ptr bid 0) m' os
  | calloc_null (k n : Nat) (m : Mem) (os : OSState) :
      ExtOk "calloc" [.int .u64 (BitVec.ofNat 64 k), .int .u64 (BitVec.ofNat 64 n)] m os .null m os
  | calloc_ok (k n : Nat) (hsz : k * n < ptrDiffLimit) (base : UInt64) (hba : base.toNat % 16 = 0)
      (m m' : Mem) (bid : BlockId) (os : OSState)
      (halloc : m.alloc (k * n) 16 .rw .heap base (fun _ => .byte 0) hsz (by decide) hba = (bid, m')) :
      ExtOk "calloc" [.int .u64 (BitVec.ofNat 64 k), .int .u64 (BitVec.ofNat 64 n)] m os
        (.ptr bid 0) m' os
  | free_null (m : Mem) (os : OSState) :
      ExtOk "free" [.null] m os .void m os
  | free_ok (b : BlockId) (m m' : Mem) (os : OSState)
      (hfree : m.free b = some m') :
      ExtOk "free" [.ptr b 0] m os .void m' os
  | memcpy_ok (bd bs : BlockId) (od os_ : Int64) (n : Nat) (bytes : List MemByte)
      (m m' : Mem) (os : OSState)
      (hdis : ptrDisjointOrEq bd od bs os_ n = true)
      (hrd : m.readBytes bs os_ n = some bytes)
      (hwr : m.writeBytes bd od bytes = some m') :
      ExtOk "memcpy" [.ptr bd od, .ptr bs os_, .int .u64 (BitVec.ofNat 64 n)] m os
        (.ptr bd od) m' os
  | memmove_ok (bd bs : BlockId) (od os_ : Int64) (n : Nat) (bytes : List MemByte)
      (m m' : Mem) (os : OSState)
      (hrd : m.readBytes bs os_ n = some bytes)
      (hwr : m.writeBytes bd od bytes = some m') :
      ExtOk "memmove" [.ptr bd od, .ptr bs os_, .int .u64 (BitVec.ofNat 64 n)] m os
        (.ptr bd od) m' os
  | memset_ok (bd : BlockId) (od : Int64) (c : BitVec 32) (n : Nat)
      (m m' : Mem) (os : OSState)
      (hwr : m.writeBytes bd od (List.replicate n (.byte (UInt8.ofNat (c.toNat % 256)))) = some m') :
      ExtOk "memset" [.ptr bd od, .int .i32 c, .int .u64 (BitVec.ofNat 64 n)] m os
        (.ptr bd od) m' os
  | memcmp_ok (b1 b2 : BlockId) (o1 o2 : Int64) (n : Nat)
      (raw1 raw2 : List MemByte) (bs1 bs2 : List UInt8) (m : Mem) (os : OSState)
      (hr1 : m.readBytes b1 o1 n = some raw1) (hc1 : allConcreteBytes raw1 = some bs1)
      (hr2 : m.readBytes b2 o2 n = some raw2) (hc2 : allConcreteBytes raw2 = some bs2) :
      ExtOk "memcmp" [.ptr b1 o1, .ptr b2 o2, .int .u64 (BitVec.ofNat 64 n)] m os
        (.int .i32 (BitVec.ofInt 32 (memcmpBytes bs1 bs2).toInt)) m os
  | strlen_ok (b : BlockId) (off : Int64) (len : Nat) (m : Mem) (os : OSState)
      (hlen : m.strlenAt b off = some len) :
      ExtOk "strlen" [.ptr b off] m os (.int .u64 (BitVec.ofNat 64 len)) m os
  | memchr_ok (b : BlockId) (off : Int64) (c : BitVec 32) (n : Nat) (ret : Val)
      (m : Mem) (os : OSState)
      (hres : memchrStep m b off (UInt8.ofNat (c.toNat % 256)) n = some ret) :
      ExtOk "memchr" [.ptr b off, .int .i32 c, .int .u64 (BitVec.ofNat 64 n)] m os
        ret m os
  | open_ok (b : BlockId) (off : Int64) (plen : Nat) (flags : BitVec 32) (rest : List Val)
      (fd e : Int32) (m m' : Mem) (os : OSState)
      (hpath : m.strlenAt b off = some plen)
      (hfd : -1 ≤ fd.toInt)
      (herr : writeErrno m os e = some m') :
      ExtOk "open" (.ptr b off :: .int .i32 flags :: rest) m os
        (.int .i32 (BitVec.ofInt 32 fd.toInt)) m' os
  | close_ok (fd : BitVec 32) (ret e : Int32) (m m' : Mem) (os : OSState)
      (hret : ret = 0 ∨ ret = -1)
      (herr : writeErrno m os e = some m') :
      ExtOk "close" [.int .i32 fd] m os (.int .i32 (BitVec.ofInt 32 ret.toInt)) m' os
  | fcntl_ok (fd cmd : BitVec 32) (rest : List Val) (ret e : Int32) (m m' : Mem) (os : OSState)
      (herr : writeErrno m os e = some m') :
      ExtOk "fcntl" (.int .i32 fd :: .int .i32 cmd :: rest) m os
        (.int .i32 (BitVec.ofInt 32 ret.toInt)) m' os
  | lseek_ok (fn : String) (hfn : fn = "lseek" ∨ fn = "lseek64")
      (fd : BitVec 32) (off : BitVec 64) (whence : BitVec 32) (ret : Int64) (e : Int32)
      (m m' : Mem) (os : OSState)
      (herr : writeErrno m os e = some m') :
      ExtOk fn [.int .i32 fd, .int .i64 off, .int .i32 whence] m os
        (.int .i64 (BitVec.ofInt 64 ret.toInt)) m' os
  | read_fail (fd : BitVec 32) (b : BlockId) (off : Int64) (cnt : Nat) (e : Int32)
      (m m' : Mem) (os : OSState)
      (hbuf : validWritableRange m b off cnt = true)
      (herr : writeErrno m os e = some m') :
      ExtOk "read" [.int .i32 fd, .ptr b off, .int .u64 (BitVec.ofNat 64 cnt)] m os
        (.int .i64 (BitVec.ofInt 64 (-1))) m' os
  | read_ok (fd : BitVec 32) (b : BlockId) (off : Int64) (cnt k : Nat) (bs : List UInt8)
      (e : Int32) (m m1 m2 : Mem) (os : OSState)
      (hbuf : validWritableRange m b off cnt = true)
      (hk : k ≤ min cnt (2 ^ 63 - 1))
      (hlen : bs.length = k)
      (hbud : match os.readBudget with | some rem => k ≤ rem | none => true)
      (hwr : m.writeBytes b off (bs.map MemByte.byte) = some m1)
      (herr : writeErrno m1 os e = some m2) :
      ExtOk "read" [.int .i32 fd, .ptr b off, .int .u64 (BitVec.ofNat 64 cnt)] m os
        (.int .i64 (BitVec.ofNat 64 k)) m2 { os with readBudget := os.readBudget.map (· - k) }
  | write_fail (fd : BitVec 32) (b : BlockId) (off : Int64) (cnt : Nat) (e : Int32)
      (m m' : Mem) (os : OSState)
      (hbuf : validReadableRange m b off cnt = true)
      (herr : writeErrno m os e = some m') :
      ExtOk "write" [.int .i32 fd, .ptr b off, .int .u64 (BitVec.ofNat 64 cnt)] m os
        (.int .i64 (BitVec.ofInt 64 (-1))) m' os
  | write_ok (fd : BitVec 32) (b : BlockId) (off : Int64) (cnt k : Nat)
      (e : Int32) (m m' : Mem) (os : OSState)
      (hbuf : validReadableRange m b off cnt = true)
      (hk : (cnt = 0 → k = 0) ∧ (cnt > 0 → 1 ≤ k ∧ k ≤ min cnt (2 ^ 63 - 1)))
      (herr : writeErrno m os e = some m') :
      ExtOk "write" [.int .i32 fd, .ptr b off, .int .u64 (BitVec.ofNat 64 cnt)] m os
        (.int .i64 (BitVec.ofNat 64 k)) m' os
  | strerror_ok (ev : BitVec 32) (n : Nat) (bs : List UInt8) (base : UInt64)
      (hsz : n + 1 < ptrDiffLimit) (m m' : Mem) (bid : BlockId) (os : OSState)
      (hlen : bs.length = n) (hnonnul : (0 : UInt8) ∉ bs)
      (halloc : (match os.strerrorBlk with | some old => m.dropBlock old | none => m).alloc
        (n + 1) 1 .ro .global base (fun i => .byte (if i < n then bs[i]?.getD 0 else 0))
        hsz (by decide) (Nat.mod_one _) = (bid, m')) :
      ExtOk "strerror" [.int .i32 ev] m os (.ptr bid 0) m' { os with strerrorBlk := some bid }
  | printf_zero (fn : String) (hfn : fn = "snprintf" ∨ fn = "vsnprintf")
      (buf : Val) (bf : BlockId) (of_ : Int64) (rest : List Val) (ret e : Int32)
      (m m' : Mem) (os : OSState)
      (hva : fn = "vsnprintf" → ∃ rest', rest = .vaList true :: rest')
      (hfmt : printfFmtOk m bf of_)
      (herr : writeErrno m os e = some m') :
      ExtOk fn (buf :: .int .u64 0 :: .ptr bf of_ :: rest) m os
        (.int .i32 (BitVec.ofInt 32 ret.toInt)) m' os
  | printf_ok (fn : String) (hfn : fn = "snprintf" ∨ fn = "vsnprintf")
      (bb : BlockId) (ob : Int64) (sz : Nat) (bf : BlockId) (of_ : Int64) (rest : List Val)
      (outBytes : List MemByte) (ret e : Int32) (m m1 m2 : Mem) (os : OSState)
      (hva : fn = "vsnprintf" → ∃ rest', rest = .vaList true :: rest')
      (hsz : sz > 0)
      (hfmt : printfFmtOk m bf of_)
      (hbuf : validWritableRange m bb ob sz = true)
      (hlen : outBytes.length = sz)
      (hnul : hasNul outBytes = true)
      (hwr : m.writeBytes bb ob outBytes = some m1)
      (herr : writeErrno m1 os e = some m2) :
      ExtOk fn (.ptr bb ob :: .int .u64 (BitVec.ofNat 64 sz) :: .ptr bf of_ :: rest) m os
        (.int .i32 (BitVec.ofInt 32 ret.toInt)) m2 os

def ExtStep (fn : String) (args : List Val) (m : Mem) (os : OSState) : ExtOutcome → Prop
  | .ok ret m' os' => ExtOk fn args m os ret m' os'
  | .ub => ¬ ∃ ret m' os', ExtOk fn args m os ret m' os'

end Libc
end C99
