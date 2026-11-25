import C99

/-!
# Safety-Only Memory and Ownership Predicates (`Zlib.Spec.Memory`)

Lightweight separation, buffer-bounds, alignment, C-string, stream-lifecycle,
and heap-frame predicates over `C99.Mem` shared by all Verus-style `libz` contracts.
-/

namespace Zlib.Spec

open C99

/-- Abstract predicate classifying library-owned heap blocks. -/
abbrev BlockSet := BlockId → Prop

def DisjointSets (a b : BlockSet) : Prop := ∀ x, ¬ (a x ∧ b x)

def PtrBlock : Val → Option BlockId
  | .ptr b _ => some b
  | _ => none

def ZeroPtr (p : Val) : Prop :=
  ∃ b, p = .ptr b 0

def PtrDisjoint (p q : Val) : Prop :=
  ∀ b, PtrBlock p = some b → PtrBlock q ≠ some b

def DisjointFrom (p : Val) (owned : BlockSet) : Prop :=
  ∀ b, PtrBlock p = some b → ¬ owned b

def writes (ps : List Val) : BlockSet :=
  fun b => ∃ p ∈ ps, PtrBlock p = some b

/-- Readable byte slice `[p, p + len)` in `m` with initialized bytes. -/
def Readable (m : Mem) (p : Val) (len : Nat) : Prop :=
  ∃ b off blk, p = .ptr b off ∧ m.blocks b = some blk ∧ Mem.inBounds blk off len = true ∧
    ∀ i < len, ∃ byte, blk.bytes (off.toInt.toNat + i) = .byte byte

/-- Writable byte slice `[p, p + len)` in `m`. -/
def Writable (m : Mem) (p : Val) (len : Nat) : Prop :=
  ∃ b off blk, p = .ptr b off ∧ m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.inBounds blk off len = true

def OptReadable (m : Mem) (p : Val) (len : Nat) : Prop :=
  (p = .null ∧ len = 0) ∨ Readable m p len

def OptWritable (m : Mem) (p : Val) (len : Nat) : Prop :=
  (p = .null ∧ len = 0) ∨ Writable m p len

/-- Aligned, writable storage cell of C type `ty`. -/
def TypedCell (tags : TypeEnv) (m : Mem) (p : Val) (ty : CTy) : Prop :=
  ∃ b off blk, p = .ptr b off ∧ m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.inBounds blk off (sizeofTy tags ty) = true ∧
    Mem.isAligned blk off (alignofTy tags ty) = true

def OptTypedCell (tags : TypeEnv) (m : Mem) (p : Val) (ty : CTy) : Prop :=
  p = .null ∨ TypedCell tags m p ty

/-- NUL-terminated readable C string at `p`. -/
def CString (m : Mem) (p : Val) : Prop :=
  ∃ b off len, p = .ptr b off ∧ m.strlenAt b off = some len

def OptCString (m : Mem) (p : Val) : Prop :=
  p = .null ∨ CString m p

/-- Format string safe for `vsnprintf`/`snprintf` (NUL-terminated, no `%n`). -/
def SafeFmtString (m : Mem) (p : Val) : Prop :=
  ∃ b off, p = .ptr b off ∧ Libc.printfFmtOk m b off

/-- Pre-existing caller blocks outside `allowed` are preserved; new blocks outside `allowed` are RO string literals. -/
def FramePreserved (m m' : Mem) (allowed : BlockSet) : Prop :=
  (∀ b, (m.blocks b).isSome → ¬ allowed b → m'.blocks b = m.blocks b) ∧
  (∀ b blk, m.blocks b = none → m'.blocks b = some blk → ¬ allowed b →
    blk.kind = .global ∧ blk.perm = .ro)

/-- Every newly allocated heap block in `m'` is tracked in `owned'`. -/
def NoHeapLeak (m m' : Mem) (owned' : BlockSet) : Prop :=
  ∀ b blk, m'.blocks b = some blk → blk.kind = .heap → (m.blocks b).isSome ∨ owned' b

def readField? (tags : TypeEnv) (m : Mem) (p : Val) (structTag fld : String) : Option Val := do
  let .ptr b off := p | none
  let (foff, fty) ← fieldLayout? tags (.structTy structTag) fld
  Sem.readVal tags m b (Int64.ofInt (off.toInt + foff)) fty

def readNatField? (tags : TypeEnv) (m : Mem) (p : Val) (structTag fld : String) : Option Nat := do
  match ← readField? tags m p structTag fld with
  | .int k bv => if !k.signed then some bv.toNat else if 0 ≤ bv.toInt then some bv.toInt.toNat else none
  | _ => none

def readU64? (m : Mem) (p : Val) : Option Nat := do
  let .ptr b off := p | none
  match ← Sem.readVal [] m b off (.int .u64) with
  | .int .u64 bv => some bv.toNat
  | _ => none

/-- Live stateful zlib stream kinds tracked in `ClientView`. -/
inductive StreamKind where
  | deflate | inflate | inflateBack
  deriving DecidableEq, Repr

/-- Abstract caller-visible handles managed by `libz`. -/
structure ClientView where
  streams : List (BlockId × StreamKind) := []
  gzFiles : List BlockId := []
  deriving DecidableEq, Repr, Inhabited

namespace ClientView

def empty : ClientView := {}

def isEmpty (v : ClientView) : Prop :=
  v.streams = [] ∧ v.gzFiles = []

def hasStream (v : ClientView) (p : Val) (k : StreamKind) : Prop :=
  ∃ b, PtrBlock p = some b ∧ (b, k) ∈ v.streams

def hasGz (v : ClientView) (p : Val) : Prop :=
  ∃ b, PtrBlock p = some b ∧ b ∈ v.gzFiles

def addStream (v : ClientView) (p : Val) (k : StreamKind) : ClientView :=
  match PtrBlock p with
  | some b => { v with streams := (b, k) :: v.streams }
  | none => v

def removeStream (v : ClientView) (p : Val) : ClientView :=
  match PtrBlock p with
  | some b => { v with streams := v.streams.filter (·.1 != b) }
  | none => v

def addGz (v : ClientView) (p : Val) : ClientView :=
  match PtrBlock p with
  | some b => { v with gzFiles := b :: v.gzFiles }
  | none => v

def closeGz (v : ClientView) (p : Val) (m' : Mem) : ClientView :=
  match PtrBlock p with
  | some b => if (m'.blocks b).isNone then { v with gzFiles := v.gzFiles.filter (· != b) } else v
  | none => v

end ClientView

def InitStreamReady (tags : TypeEnv) (owned : BlockSet) (v : ClientView) (m : Mem) (strm : Val) : Prop :=
  strm = .null ∨
  (ZeroPtr strm ∧ TypedCell tags m strm (.structTy "z_stream_s") ∧ DisjointFrom strm owned ∧
    (∀ k, ¬ v.hasStream strm k) ∧
    readField? tags m strm "z_stream_s" "zalloc" = some .null ∧
    readField? tags m strm "z_stream_s" "zfree" = some .null)

def StreamAlive (tags : TypeEnv) (owned : BlockSet) (v : ClientView) (m : Mem)
    (strm : Val) (k : StreamKind) : Prop :=
  strm = .null ∨
  (ZeroPtr strm ∧ v.hasStream strm k ∧ TypedCell tags m strm (.structTy "z_stream_s") ∧ DisjointFrom strm owned)

def GzReady (v : ClientView) (file : Val) : Prop :=
  file = .null ∨ (ZeroPtr file ∧ v.hasGz file)

def StreamReady (tags : TypeEnv) (owned : BlockSet) (v : ClientView) (m : Mem)
    (strm : Val) (k : StreamKind) : Prop :=
  strm = .null ∨
  (ZeroPtr strm ∧ v.hasStream strm k ∧ TypedCell tags m strm (.structTy "z_stream_s") ∧ DisjointFrom strm owned ∧
    (∃ ti, readNatField? tags m strm "z_stream_s" "total_in" = some ti) ∧
    (∃ to_, readNatField? tags m strm "z_stream_s" "total_out" = some to_) ∧
    (∃ nIn avIn nOut avOut,
      readField? tags m strm "z_stream_s" "next_in" = some nIn ∧
      readNatField? tags m strm "z_stream_s" "avail_in" = some avIn ∧
      readField? tags m strm "z_stream_s" "next_out" = some nOut ∧
      readNatField? tags m strm "z_stream_s" "avail_out" = some avOut ∧
      (avIn = 0 ∨ (Readable m nIn avIn ∧ DisjointFrom nIn (fun b => owned b ∨ PtrBlock strm = some b))) ∧
      (avOut = 0 ∨ (Writable m nOut avOut ∧ DisjointFrom nOut (fun b => owned b ∨ PtrBlock strm = some b))) ∧
      (avIn = 0 ∨ avOut = 0 ∨ PtrBlock nIn ≠ PtrBlock nOut)))

/-- Caller blocks potentially mutated via `strm`, `strm->next_out`, `state->window`, or `state->head`. -/
def writesStream (tags : TypeEnv) (m : Mem) (strm : Val) : BlockSet :=
  let nextOut := (readField? tags m strm "z_stream_s" "next_out").getD .null
  let st := (readField? tags m strm "z_stream_s" "state").getD .null
  let win := (readField? tags m st "inflate_state" "window").getD .null
  let head := (readField? tags m st "inflate_state" "head").getD .null
  let extra := (readField? tags m head "gz_header_s" "extra").getD .null
  let name := (readField? tags m head "gz_header_s" "name").getD .null
  let comm := (readField? tags m head "gz_header_s" "comment").getD .null
  writes [strm, nextOut, win, head, extra, name, comm]

def DeflateHeaderReady (tags : TypeEnv) (owned : BlockSet) (m : Mem) (head : Val) : Prop :=
  head = .null ∨
  (TypedCell tags m head (.structTy "gz_header_s") ∧ DisjointFrom head owned ∧
    (∃ v, readField? tags m head "gz_header_s" "text" = some v) ∧
    (∃ v, readField? tags m head "gz_header_s" "time" = some v) ∧
    (∃ v, readField? tags m head "gz_header_s" "os" = some v) ∧
    (∃ v, readField? tags m head "gz_header_s" "hcrc" = some v) ∧
    (∃ ep elen, readField? tags m head "gz_header_s" "extra" = some ep ∧
      readNatField? tags m head "gz_header_s" "extra_len" = some elen ∧
      (ep = .null ∨ Readable m ep (elen % 65536))) ∧
    (∃ np, readField? tags m head "gz_header_s" "name" = some np ∧ OptCString m np) ∧
    (∃ cp, readField? tags m head "gz_header_s" "comment" = some cp ∧ OptCString m cp))

def HeaderDisjoint (tags : TypeEnv) (m : Mem) (head p : Val) : Prop :=
  PtrDisjoint head p ∧
  (∀ ep, readField? tags m head "gz_header_s" "extra" = some ep → PtrDisjoint ep p) ∧
  (∀ np, readField? tags m head "gz_header_s" "name" = some np → PtrDisjoint np p) ∧
  (∀ cp, readField? tags m head "gz_header_s" "comment" = some cp → PtrDisjoint cp p)

def InflateHeaderReady (tags : TypeEnv) (owned : BlockSet) (m : Mem) (head : Val) : Prop :=
  TypedCell tags m head (.structTy "gz_header_s") ∧ DisjointFrom head owned ∧
  (∃ elen, readNatField? tags m head "gz_header_s" "extra_len" = some elen) ∧
  (∃ ep emax np nmax cp cmax,
    readField? tags m head "gz_header_s" "extra" = some ep ∧
    readNatField? tags m head "gz_header_s" "extra_max" = some emax ∧
    readField? tags m head "gz_header_s" "name" = some np ∧
    readNatField? tags m head "gz_header_s" "name_max" = some nmax ∧
    readField? tags m head "gz_header_s" "comment" = some cp ∧
    readNatField? tags m head "gz_header_s" "comm_max" = some cmax ∧
    (ep = .null ∨ (Writable m ep emax ∧ DisjointFrom ep owned)) ∧
    (np = .null ∨ (Writable m np nmax ∧ DisjointFrom np owned)) ∧
    (cp = .null ∨ (Writable m cp cmax ∧ DisjointFrom cp owned)) ∧
    PtrDisjoint head ep ∧ PtrDisjoint head np ∧ PtrDisjoint head cp ∧
    PtrDisjoint ep np ∧ PtrDisjoint ep cp ∧ PtrDisjoint np cp)

def DictWritable (tags : TypeEnv) (owned : BlockSet) (m : Mem)
    (strm dict : Val) (isDeflate : Bool) : Prop :=
  dict = .null ∨
  (DisjointFrom dict owned ∧ PtrBlock dict ≠ PtrBlock strm ∧
    let st := (readField? tags m strm "z_stream_s" "state").getD .null
    let req := if isDeflate then (readNatField? tags m st "internal_state" "w_size").getD 32768
               else (readNatField? tags m st "inflate_state" "whave").getD 32768
    Writable m dict (min req 32768))

end Zlib.Spec
