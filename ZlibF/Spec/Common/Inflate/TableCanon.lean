/-!
# The canonical construction of the decoding tables in the list model

Pure mathematics about the code lengths `ls`: the allocation order, the Kraft sums `K`, the canonical code values
`cv`, `H` (the table index of the first entry of a code), the group widths of the sub-tables (`look`, `width`) and the
closed form `desc` of the table geometry. The lemmas about them are in `ZlibF/Proof/inftrees.c.canon.lean`.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Canon

/-- Reverse the low `k` bits of `x`. -/
def rev : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => rev k (x / 2) + (x % 2) * 2 ^ k

/-- Symbols of length `l`, increasing. -/
def symsOf (ls : List Nat) (l : Nat) : List Nat :=
  (List.range ls.length).filter fun s => ls.getD s 0 == l

/-- Number of symbols with nonzero length below `l` (`offs[l]` in the C). -/
def offL (ls : List Nat) (l : Nat) : Nat :=
  ((List.range l).map fun l' => if l' = 0 then 0 else ls.count l').sum

/-- Allocation order: lengths 1..15, increasing symbol within a length. -/
def ord (ls : List Nat) : List Nat :=
  (List.range 15).flatMap fun i => symsOf ls (i + 1)

/-- `j`-th symbol in allocation order. -/
def sy (ls : List Nat) (j : Nat) : Nat := (ord ls).getD j 0

/-- Length of the `j`-th symbol in allocation order. -/
def L (ls : List Nat) (j : Nat) : Nat := ls.getD (sy ls j) 0

def K (ls : List Nat) (j : Nat) : Nat := ((List.range j).map fun i => 2 ^ (15 - L ls i)).sum

def cv (ls : List Nat) (j : Nat) : Nat := K ls j / 2 ^ (15 - L ls j)

def H (ls : List Nat) (j : Nat) : Nat := rev (L ls j) (cv ls j)

/-- Remaining codes of length `l` at or after allocation index `a`. -/
def cntGE (ls : List Nat) (a l : Nat) : Nat := offL ls (l + 1) - max a (offL ls l)

def grp (ls : List Nat) (root j : Nat) : Nat := K ls j / 2 ^ (15 - root)

/-- The C lookahead
```c
while (curr + drop < max) { left -= count[curr + drop]; if (left <= 0) break;
                            curr++; left <<= 1; }
```
with `count[l] = cntGE a l` and a fuel bound. -/
def look (ls : List Nat) (a root mx : Nat) : Nat → Int → Nat → Nat
  | c, _, 0 => c
  | c, left, f + 1 =>
    if c + root < mx then
      if left - (cntGE ls a (c + root) : Int) ≤ 0 then c
      else look ls a root mx (c + 1) (2 * (left - (cntGE ls a (c + root) : Int))) f
    else c

/-- The sub-table width chosen for a group starting at allocation index `a`. -/
def width (ls : List Nat) (a root mx : Nat) : Nat :=
  look ls a root mx (L ls a - root) (2 ^ (L ls a - root) : Nat) 16

structure Desc where
  drop : Nat
  curr : Nat
  base : Nat
  used : Nat
  low : Nat
  deriving Repr

/-- A new sub-table starts at code `i+1`. -/
def startsAt (ls : List Nat) (root i : Nat) : Prop :=
  root < L ls (i + 1) ∧ (L ls i ≤ root ∨ grp ls root (i + 1) ≠ grp ls root i)

instance (ls : List Nat) (root i : Nat) : Decidable (startsAt ls root i) := by
  unfold startsAt; infer_instance

/-- Table descriptor in force while code `i` is written. -/
def desc (ls : List Nat) (root mx : Nat) : Nat → Desc
  | 0 => ⟨0, root, 0, 2 ^ root, 2 ^ 32 - 1⟩
  | i + 1 =>
    let d := desc ls root mx i
    if startsAt ls root i then
      ⟨root, width ls (i + 1) root mx, d.base + 2 ^ d.curr,
        d.used + 2 ^ width ls (i + 1) root mx, rev root (grp ls root (i + 1))⟩
    else d

end Zlib.Inftrees.Canon
