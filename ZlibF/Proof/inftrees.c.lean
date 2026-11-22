import ZlibF.Proof.«inftrees.c.main»

/-!
# inftrees.c: safety of `inflate_table`

The statement is `Zlib.Inftrees.Proofs.inflate_table_safe`. The proof is in the modules `inftrees.c.proofs.math`
(arithmetic of canonical codes), `.base` (the reasoning rules for the monad, the heap lemmas, the translation cut at
its join points), `.step` (one pass of the main loop) and `.main` (the other loops and the assembly).
-/

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec

/-- **inflate_table, safety.** Take the call `inflate_table(type, lens, codes, table, bits, work)` with `lens` the
array `la` from offset `ol`, `work` the array `wa` from offset `ow`, and `*table` the array `ca` from offset `oc`
(`code` entries), `*bits` the value `bits`, in any heap `h` in which

* `type` is `CODES`, `LENS` or `DISTS`;
* `lens` has at least `codes` entries, each at most 15 (`MAXBITS`; the C only assumes it), and `work` has at least
  `codes` entries; `lens` and `work` are different arrays;
* `ca` is writable and has at least `Spec.capOf type` entries from `oc` on: 128 for `CODES`, `ENOUGH_LENS` (1332) for
  `LENS`, `ENOUGH_DISTS` (400) for `DISTS`, which is what `inflate.c` provides;
* `codes` is at most 19 (`CODES`), 288 (`LENS`; `inflate.c` has at most 286) or 32 (`DISTS`; `inflate.c` has at most
  30), so that `work[sym] - match` stays inside the 31 or 32 entries of `lbase`, `lext`, `dbase`, `dext`;
* for `CODES` every length is at most 7 and `*bits` is at least 7 (the caller passes `7`): without them a `CODES`
  table could open sub-tables, which the C does not guard against with `ENOUGH`.

`*bits` is arbitrary for `LENS` and `DISTS`; incomplete and over-subscribed codes are allowed (they return `-1`).

Then the call ends without undefined behaviour (no fault, no write outside the table or `work`, no read outside
`lens`, `work` and the tables of base values), and `Spec.Result` holds: only `work` (inside `[ow, ow + codes)`) and
the table (inside `[oc, oc + cap)`) changed, the result is `0`, `1` or `-1`, and for `0` the table pointer moved
forward inside the space given. -/
theorem inflate_table_safe (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32) (rc : CodeRef)
    (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat) (la wa : Array UInt16) (ca : Array Code)
    (hty : type = CODES ∨ type = LENS ∨ type = DISTS)
    (hgl : Space.get h rl = some la) (hgw : Space.get h rw = some wa) (hgc : Space.get h rc = some ca)
    (hro : Space.ro h rc = false) (hne : rw ≠ rl)
    (hla : ol + codes.toNat ≤ la.size) (hwa : ow + codes.toNat ≤ wa.size) (hca : oc + capOf type ≤ ca.size)
    (hf15 : ∀ k, k < codes.toNat → (la.getD (ol + k) 0).toNat ≤ 15)
    (hcodes : type = CODES → codes.toNat ≤ 19 ∧ (∀ k, k < codes.toNat → (la.getD (ol + k) 0).toNat ≤ 7) ∧
      7 ≤ bits.toNat)
    (hlens : type = LENS → codes.toNat ≤ 288) (hdists : type = DISTS → codes.toNat ≤ 32) :
    ∃ r h', C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (r, h') ∧
      Result h rw rc ow oc (capOf type) codes.toNat wa ca (.ref rc oc) bits r h' := by
  let P : CallPre h type rl ol codes rc oc bits rw ow :=
    ⟨la, wa, ca, hty, hgl, hgw, hgc, hro, hne, hla, hwa, hca, hf15, hcodes, hlens, hdists⟩
  obtain ⟨r, h', hrun, hq, _⟩ := itTop_wp P
  exact ⟨r, h', by rw [C.run, inflate_table_eq]; exact hrun, hq⟩


/-- **inflate_table, return code.** Under the hypotheses of `inflate_table_safe`, the call returns `-1` exactly
when the lengths `lens[0 .. codes-1]` are not acceptable to `inflate_table` in the specification
(`ZlibF.Spec.Acceptable`: no length above 15, the Kraft inequality holds, and the code is complete, or has no
symbol, or (not for the code-length code) has one symbol, of length 1). It returns `0` or `1` only for acceptable
lengths, and `1` (table too large for `ENOUGH_LENS` / `ENOUGH_DISTS`) only for `LENS` or `DISTS`.

Callers covered. `inflate.c` (and `infback.c`) call `inflate_table(CODES, lens, 19, &next, &lenbits(=7), work)` on
3-bit lengths (so at most 7), `inflate_table(LENS, lens, nlen, ...)` with `nlen <= 286` and
`inflate_table(DISTS, lens + nlen, ndist, ...)` with `ndist <= 30`, with `next` inside `codes[1732]` such that at
least 1332 (`LENS`) or 400 (`DISTS`) entries remain, and `work[288]`. These satisfy the hypotheses: `CODES` needs
`codes <= 19`, every length `<= 7` and `bits >= 7` (they pass exactly 7); `LENS` needs `codes <= 288`; `DISTS` needs
`codes <= 32`. The theorem is wider than the callers in `codes` (288 and 32 instead of 286 and 30) and in `bits`
(arbitrary for `LENS` and `DISTS`). The fixed-code tables are not built by `inflate_table` in the default build. -/
theorem inflate_table_correct_ret (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32) (rc : CodeRef)
    (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat) (la wa : Array UInt16) (ca : Array Code)
    (hty : type = CODES ∨ type = LENS ∨ type = DISTS)
    (hgl : Space.get h rl = some la) (hgw : Space.get h rw = some wa) (hgc : Space.get h rc = some ca)
    (hro : Space.ro h rc = false) (hne : rw ≠ rl)
    (hla : ol + codes.toNat ≤ la.size) (hwa : ow + codes.toNat ≤ wa.size) (hca : oc + capOf type ≤ ca.size)
    (hf15 : ∀ k, k < codes.toNat → (la.getD (ol + k) 0).toNat ≤ 15)
    (hcodes : type = CODES → codes.toNat ≤ 19 ∧ (∀ k, k < codes.toNat → (la.getD (ol + k) 0).toNat ≤ 7) ∧
      7 ≤ bits.toNat)
    (hlens : type = LENS → codes.toNat ≤ 288) (hdists : type = DISTS → codes.toNat ≤ 32) :
    ∃ r h', C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (r, h') ∧
      (r.1 = -1 ↔ ¬ ZlibF.Spec.Acceptable (kindOf type) (lensList la ol codes.toNat)) ∧
      (r.1 = 0 → ZlibF.Spec.Acceptable (kindOf type) (lensList la ol codes.toNat)) ∧
      (r.1 = 1 → ZlibF.Spec.Acceptable (kindOf type) (lensList la ol codes.toNat) ∧ type ≠ CODES) := by
  let P : CallPre h type rl ol codes rc oc bits rw ow :=
    ⟨la, wa, ca, hty, hgl, hgw, hgc, hro, hne, hla, hwa, hca, hf15, hcodes, hlens, hdists⟩
  obtain ⟨r, h', hrun, hres, hr0, hr1, hrm⟩ := itTop_wp P
  have hacc := acc_iff type P.f codes.toNat hf15
  have e : lensOf P.f codes.toNat = lensList la ol codes.toNat := rfl
  rw [e] at hacc
  have hr3 : r.1 = 0 ∨ r.1 = 1 ∨ r.1 = -1 := by
    obtain ⟨_, _, _, _, _, _, _, hr⟩ := hres
    rcases hr with ⟨h0, _⟩ | ⟨h1 | h1, _⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  refine ⟨r, h', by rw [C.run, inflate_table_eq]; exact hrun, ⟨fun hm hA => hrm hm (hacc.mpr hA), fun hn => ?_⟩,
    fun h0 => hacc.mp (hr0 h0), fun h1 => ⟨hacc.mp (hr1 h1).1, (hr1 h1).2⟩⟩
  rcases hr3 with h0 | h1 | hm
  · exact absurd (hacc.mp (hr0 h0)) hn
  · exact absurd (hacc.mp (hr1 h1).1) hn
  · exact hm

/-! ### Non-vacuity

A heap made by the runtime: `allocInflateState` gives the inflate state, and the first three entries of its `lens`
array are set with `Ptr.store` to the lengths `1, 2, 2` (a complete code). -/

/-- The heap of the examples. -/
def witHeap : Heap :=
  match C.run (do
      let st ← allocInflateState
      Ptr.store (Ptr.ref (WRef.istate_lens 0) 0) (1 : UInt16)
      Ptr.store (Ptr.ref (WRef.istate_lens 0) 1) (2 : UInt16)
      Ptr.store (Ptr.ref (WRef.istate_lens 0) 2) (2 : UInt16)
      pure st) Heap.empty with
  | .ok (_, h) => h
  | .error _ => Heap.empty

/-! The kernel builds an `Array.ofFn` slowly: the 1732 entries of `codes` alone take gigabytes. `witHeap_eq` rewrites
`witHeap` to the same heap with its arrays written by `Array.replicate`, which the kernel builds directly. -/

/-- The inflate state of `witHeap`, its arrays written by `Array.replicate`. -/
def witStateR : InflateState :=
  { InflateState.garbage (fun _ => 0) with
    lens := (((Array.replicate 320 (Junk.of 0 : UInt16)).set! 0 1).set! 1 2).set! 2 2
    work := Array.replicate 288 (Junk.of 0 : UInt16)
    codes := Array.replicate 1732 (Code.garbage (fun _ => 0)) }

/-- `witHeap`, its arrays written by `Array.replicate`. -/
def witHeapR : Heap :=
  { Heap.empty with istates := upd Tbl.empty 0 (some witStateR), nextBlk := 1, nalloc := 1 }

theorem array_ofFn_const {α : Type} (n : Nat) (c : α) : Array.ofFn (fun _ : Fin n => c) = Array.replicate n c := by
  ext <;> simp

/-- The run of `allocInflateState` and the three stores, step by step. -/
theorem witHeap_eq : witHeap = witHeapR := by
  have key : ∀ (H : Heap) (s : InflateState) (i : Nat) (v : UInt16), H.istates 0 = some s → i < s.lens.size →
      Ptr.store (Ptr.ref (WRef.istate_lens 0) i) v H =
        .ok ((), { H with istates := upd H.istates 0 (some { s with lens := s.lens.set! i v }) }) :=
    fun H s i v e hi => by rw [Ptr.store_ok (WRef.get_istate_lens e) rfl hi, WRef.put_istate_lens e]
  let s0 := InflateState.garbage (Heap.empty.garbage Heap.empty.nalloc)
  have ha : allocInflateState Heap.empty = .ok (some (.tab 0),
      { Heap.empty with istates := upd Heap.empty.istates 0 (some s0), nextBlk := 1, nalloc := 1 }) :=
    allocInflateState_some rfl rfl
  have hsz : s0.lens.size = 320 := by simp [s0, InflateState.garbage]
  unfold witHeap
  simp only [C.run, bind_app, ha]
  rw [key _ s0 0 1 (upd_same _ _ _) (by omega)]
  dsimp only
  rw [key _ _ 1 2 (upd_same _ _ _) (by simp [hsz])]
  dsimp only
  rw [key _ _ 2 2 (upd_same _ _ _) (by simp [hsz])]
  dsimp only
  simp only [upd_upd]
  have hs : { s0 with lens := ((s0.lens.set! 0 1).set! 1 2).set! 2 2 } = witStateR := by
    simp [s0, witStateR, InflateState.garbage, array_ofFn_const, Heap.empty]
  rw [hs, pure_app]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `inflate_table_safe` hold on `witHeap`, for the call `inflate_table(DISTS, state->lens, 3,
&state->next, 5, state->work)`, and the conclusion is an actual run. -/
example : ∃ r h', C.run (inflate_table DISTS (.ref (WRef.istate_lens 0) 0) 3 (.ref (CodeRef.istate_codes 0) 0) 5
      (.ref (WRef.istate_work 0) 0)) witHeap = .ok (r, h') ∧
    Result witHeap (WRef.istate_work 0) (CodeRef.istate_codes 0) 0 0 (capOf DISTS) 3
      (witHeap.istates 0).get!.work (witHeap.istates 0).get!.codes (.ref (CodeRef.istate_codes 0) 0) 5 r h' :=
  inflate_table_safe witHeap DISTS (WRef.istate_lens 0) 0 3 (CodeRef.istate_codes 0) 0 5 (WRef.istate_work 0) 0
    (witHeap.istates 0).get!.lens (witHeap.istates 0).get!.work (witHeap.istates 0).get!.codes
    (Or.inr (Or.inr rfl)) rfl rfl rfl rfl (by decide) (by rw [witHeap_eq]; decide +kernel)
    (by rw [witHeap_eq]; decide +kernel) (by rw [witHeap_eq]; decide +kernel) (by rw [witHeap_eq]; decide +kernel)
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The run is a real one: the call returns `0`, the table pointer advances by 4 entries (the root has 2 bits, the longest
length) and `*bits` becomes 2. -/
example : ((C.run (inflate_table DISTS (.ref (WRef.istate_lens 0) 0) 3 (.ref (CodeRef.istate_codes 0) 0) 5
      (.ref (WRef.istate_work 0) 0)) witHeap).toOption.map (fun p => (p.1.1, p.1.2.1, p.1.2.2))) =
    some (0, .ref (CodeRef.istate_codes 0) 4, 2) := by
  rw [witHeap_eq]; decide +kernel

end Zlib.Inftrees.Proofs
