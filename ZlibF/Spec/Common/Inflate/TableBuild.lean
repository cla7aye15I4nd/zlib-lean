import ZlibF.Zlib.«inftrees.c»
import ZlibF.Runtime.Schema
import ZlibF.Spec.Common.Inflate.TableCanon

/-!
# inftrees.c: the call of `inflate_table` and the table it builds

The code lengths sorted by length and their canonical codes (`Tc`, `Kc`, `lenAt`, `val`), the lengths the call
accepts (`Acc`), the call's premises (`CallPre`) and result (`Result`, `RetInfo`), and the entries and links that
the main loop writes (`Env`, `Written`, `Links`). The lemmas about them are in the proof modules
`ZlibF/Proof/inftrees.c.*.lean`.
-/

namespace Zlib.Inftrees.Proofs

/-- The `n` low bits of `v` in reverse order. -/
def rev : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => (v % 2) * 2 ^ n + rev n (v / 2)

section Model
variable (f : Nat → Nat) (n : Nat)

/-- The symbols below `k` of length `l`, in increasing order. -/
def fl (l k : Nat) : List Nat := (List.range k).filter (fun s => f s == l)

/-- `count[l]` after the counting loop has looked at the symbols below `n`. -/
def cnt (l : Nat) : Nat := (fl f l n).length

/-- `work[0 ..]` after the sort loop, for the lengths `1 .. l`: the symbols sorted by (length, symbol). -/
def wsAux : Nat → List Nat
  | 0 => []
  | l + 1 => wsAux l ++ fl f (l + 1) n

/-- The number of symbols of length at most `l` (and at least 1). -/
def Tc : Nat → Nat
  | 0 => 0
  | l + 1 => Tc l + cnt f n (l + 1)

/-- Kraft: `K l = sum_{j <= l} cnt j 2^(l - j)`; `2^l - K l` is the C variable `left` after step `l`. -/
def Kc : Nat → Nat
  | 0 => 0
  | l + 1 => 2 * Kc l + cnt f n (l + 1)

/-- `lens[work[i]]` once the sort loop is done. -/
def lenAt (i : Nat) : Nat := f ((wsAux f n 15).getD i 0)

/-- The canonical code of the `i`-th symbol in the sorted order (RFC 1951, 3.2.2): the `k`-th of length `l` is
`2 K(l-1) + k`. -/
def val (i : Nat) : Nat := 2 * Kc f n (lenAt f n i - 1) + (i - Tc f n (lenAt f n i - 1))

variable {f n}

/-- No code overflows its length (RFC 1951; `F-code-fits`). -/
def Fits (f : Nat → Nat) (n : Nat) : Prop := ∀ l, 1 ≤ l → l ≤ 15 → Kc f n l ≤ 2 ^ l

/-- The first `R` bits of the `j`-th code, when it is longer than `R` (the index of its root entry, before reversal). -/
def pre (f : Nat → Nat) (n R j : Nat) : Nat := val f n j / 2 ^ (lenAt f n j - R)

/-- `max`: the longest length. -/
def mxl (f : Nat → Nat) (n : Nat) : Nat := lenAt f n (Tc f n 15 - 1)

end Model

end Zlib.Inftrees.Proofs

namespace Zlib.Inftrees.Spec
open C

/-- The number of `code` entries the caller provides at `*table`: 128 for `CODES` (`1 << 7`), `ENOUGH_LENS` (1332) for
`LENS`, `ENOUGH_DISTS` (400) for `DISTS`. -/
def capOf (type : UInt32) : Nat := if type = CODES then 128 else if type = LENS then 1332 else 400

/-- The heap and the result after a call, safety part. The call changed only the `unsigned short` array `work` (inside
`[ow, ow + n)`) and the `code` array of the table (inside `[oc, oc + cap)`), through `wa'` and `ca'`; the arrays kept
their sizes. The result is `0` with the table pointer advanced by at most `cap` entries inside the same array, or `1`
(table too large) or `-1` (bad code lengths) with the table pointer and `*bits` as they were passed. -/
def Result (h : Heap) (rw : WRef) (rc : CodeRef) (ow oc cap n : Nat) (wa : Array UInt16) (ca : Array Code)
    (table : CodePtr) (bits : UInt32) (r : Int32 × CodePtr × UInt32) (h' : Heap) : Prop :=
  ∃ wa' ca', h' = Space.put (Space.put h rw wa') rc ca' ∧ wa'.size = wa.size ∧ ca'.size = ca.size ∧
    (∀ x, (x < ow ∨ ow + n ≤ x) → wa'[x]? = wa[x]?) ∧ (∀ x, (x < oc ∨ oc + cap ≤ x) → ca'[x]? = ca[x]?) ∧
    ((r.1 = 0 ∧ ∃ u, u ≤ cap ∧ r.2.1 = .ref rc (oc + u)) ∨ ((r.1 = 1 ∨ r.1 = -1) ∧ r.2.1 = table ∧ r.2.2 = bits))

end Zlib.Inftrees.Spec

namespace Zlib.Inftrees.Proofs

/-- The list of lengths that the call looks at. -/
def lensOf (f : Nat → Nat) (n : Nat) : List Nat := (List.range n).map f

/-- `inflate_table` accepts the lengths (the rule of `inftrees.c`, in the terms of the proofs). -/
def Acc (type : UInt32) (f : Nat → Nat) (n : Nat) : Prop :=
  Fits f n ∧ (Kc f n 15 = 2 ^ 15 ∨ Tc f n 15 = 0 ∨ (type ≠ C.CODES ∧ mxl f n = 1 ∧ Tc f n 15 = 1))

end Zlib.Inftrees.Proofs

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees

/-- Everything the main loop of `inflate_table` reads and never changes. `hb` is the heap before the loop (after the
sort); inside the loop the heap is `hb` with the table array replaced. -/
structure Env where
  c : Ctx
  f : Nat → Nat
  n : Nat
  R : Nat
  cap : Nat
  rc : CodeRef
  oc : Nat
  rw : WRef
  ow : Nat
  rl : WRef
  ol : Nat
  hb : Heap
  la : Array UInt16
  wa : Array UInt16
  h_table : c.table = .ref rc oc
  h_lens : c.lens = .ref rl ol
  h_work : c.work = .ref rw ow
  h_ro : Space.ro hb rc = false
  h_live : ∃ ca0, Space.get hb rc = some ca0
  h_get_la : Space.get hb rl = some la
  h_get_wa : Space.get hb rw = some wa
  h_f : ∀ k, f k = (la.getD (ol + k) 0).toNat
  h_la : ol + n ≤ la.size
  h_f15 : ∀ k, k < n → f k ≤ 15
  h_wa : ow + n ≤ wa.size
  h_wcont : ∀ i, i < Tc f n 15 → wa[ow + i]? = some (UInt16.ofNat ((wsAux f n 15).getD i 0))
  h_n : n ≤ 288
  h_root : c.root.toNat = R
  h_max : c.max.toNat = mxl f n
  h_R1 : 1 ≤ R
  h_Rmx : R ≤ mxl f n
  h_R0 : lenAt f n 0 ≤ R
  h_pos : 0 < Tc f n 15
  h_fits : Fits f n
  h_end : Kc f n 15 = 2 ^ 15 ∨ (mxl f n = 1 ∧ Tc f n 15 = 1 ∧ c.type ≠ CODES)
  h_type : c.type = CODES ∨ c.type = LENS ∨ c.type = DISTS
  h_cap : cap = (if c.type = CODES then 128 else if c.type = LENS then 1332 else 400)
  h_codes : c.type = CODES → mxl f n ≤ 7 ∧ R = mxl f n ∧ n ≤ 19 ∧ c.match_ = 20
  h_lens' : c.type = LENS → n ≤ 288 ∧ c.base = lbase ∧ c.extra = lext ∧ c.match_ = 257
  h_dists : c.type = DISTS → n ≤ 32 ∧ c.base = dbase ∧ c.extra = dext ∧ c.match_ = 0

namespace Env
def m (e : Env) : Nat := Tc e.f e.n 15

def l (e : Env) (i : Nat) : Nat := lenAt e.f e.n i

def v (e : Env) (i : Nat) : Nat := val e.f e.n i

def mx (e : Env) : Nat := mxl e.f e.n

end Env

/-- The entry that the C builds for the symbol `w` with `bits` table bits. -/
def hereC (c : Ctx) (w : UInt16) (bits : UInt8) : Code :=
  if w.toUInt32 + 1 < c.match_ then ⟨0, bits, w⟩
  else if w.toUInt32 ≥ c.match_ then
    ⟨(c.extra[(w.toUInt32 - c.match_).toNat]!).toUInt8, bits, c.base[(w.toUInt32 - c.match_).toNat]!⟩
  else ⟨96, bits, 0⟩

/-- The table cell of the `m`-th copy of the entry of the code with allocation index `i`. -/
def gAddr (ls : List Nat) (R mx i m : Nat) : Nat :=
  (Canon.desc ls R mx i).base + Canon.H ls i / 2 ^ (Canon.desc ls R mx i).drop +
    m * 2 ^ (Canon.L ls i - (Canon.desc ls R mx i).drop)

/-- The number of copies of that entry. -/
def gReps (ls : List Nat) (R mx i : Nat) : Nat :=
  2 ^ ((Canon.desc ls R mx i).curr - (Canon.L ls i - (Canon.desc ls R mx i).drop))

/-- The root cell of the link to the sub-table that starts at allocation index `a`. -/
def gSlot (ls : List Nat) (R a : Nat) : Nat := Canon.rev R (Canon.grp ls R a)

namespace Env
def ls (e : Env) : List Nat := lensOf e.f e.n

def D (e : Env) (i : Nat) : Canon.Desc := Canon.desc e.ls e.R e.mx i

def here (e : Env) (j : Nat) : Code :=
  hereC e.c (UInt16.ofNat ((wsAux e.f e.n 15).getD j 0)) (Canon.L e.ls j - (e.D j).drop).toUInt8

def link (e : Env) (a : Nat) : Code :=
  ⟨(Canon.width e.ls a e.R e.mx).toUInt8, e.R.toUInt8, (e.D a).base.toUInt16⟩

end Env

/-- The entries of the codes below `i` are in the table. -/
def Written (e : Env) (i : Nat) (ca : Array Code) : Prop :=
  ∀ j, j < i → ∀ m, m < gReps e.ls e.R e.mx j → ca[e.oc + gAddr e.ls e.R e.mx j m]? = some (e.here j)

/-- The links of the sub-tables that start at allocation index at most `i` are in the table. -/
def Links (e : Env) (i : Nat) (ca : Array Code) : Prop :=
  ∀ a, 1 ≤ a → a ≤ i → a < e.m → Canon.startsAt e.ls e.R (a - 1) → ca[e.oc + gSlot e.ls e.R a]? = some (e.link a)

end Zlib.Inftrees.Proofs

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec

/-- What the result code says about the lengths. -/
def RetInfo (type : UInt32) (f : Nat → Nat) (n : Nat) (r : Int32 × CodePtr × UInt32) : Prop :=
  (r.1 = 0 → Acc type f n) ∧ (r.1 = 1 → Acc type f n ∧ type ≠ CODES) ∧ (r.1 = -1 → ¬ Acc type f n)

/-- The inputs of the call that `zlib.h` and `inflate.c` allow (the part that lives in the heap). -/
structure CallPre (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32) (rc : CodeRef) (oc : Nat)
    (bits : UInt32) (rw : WRef) (ow : Nat) where
  la : Array UInt16
  wa : Array UInt16
  ca : Array Code
  hty : type = CODES ∨ type = LENS ∨ type = DISTS
  hgl : Space.get h rl = some la
  hgw : Space.get h rw = some wa
  hgc : Space.get h rc = some ca
  hro : Space.ro h rc = false
  hne : rw ≠ rl
  hla : ol + codes.toNat ≤ la.size
  hwa : ow + codes.toNat ≤ wa.size
  hca : oc + capOf type ≤ ca.size
  hf15 : ∀ k, k < codes.toNat → (la.getD (ol + k) 0).toNat ≤ 15
  hcodes : type = CODES → codes.toNat ≤ 19 ∧ (∀ k, k < codes.toNat → (la.getD (ol + k) 0).toNat ≤ 7) ∧ 7 ≤ bits.toNat
  hlens : type = LENS → codes.toNat ≤ 288
  hdists : type = DISTS → codes.toNat ≤ 32

def CallPre.f {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow) (k : Nat) : Nat :=
  (P.la.getD (ol + k) 0).toNat

end Zlib.Inftrees.Proofs
