import ZlibF.Zlib.«deflate.c»
import ZlibF.Proof.«trees.c.monad»

/-! The original gzip extra-field loop represents its early return with a flag.
The generated loop uses an immediate break. A terminating flag-loop proof transfers
with its exact result and heap, including when a partial flush leaves pending bytes. -/

namespace Zlib.Deflate.Universal.Call
open C

/-- A successful flag-controlled loop has the same value and heap when its final
iteration exits immediately. This also covers a zero-iteration loop. -/
private theorem break_of_success {σ : Type} (flag : σ → Bool)
    (oldTest test : σ → M (Bool × σ)) (oldBody : σ → M σ)
    (body : σ → M (LoopStep σ Empty))
    (active : ∀ s h, flag s = false → test s h = oldTest s h)
    (enter : ∀ s h s' h', flag s = false → oldTest s h = .ok ((true,s'),h') → flag s' = false)
    (stopped : ∀ s h b s' h', flag s = true → oldTest s h = .ok ((b,s'),h') →
      b = false ∧ s' = s ∧ h' = h)
    (step : ∀ s h s' h', flag s = false → oldBody s h = .ok (s',h') →
      body s h = .ok (if flag s' then .brk s' else .next s', h'))
    {s r : σ} {h after : Heap} (initial : flag s = false)
    (run : cwhile oldTest oldBody s h = .ok (r,after)) :
    cwhileBrk test body s h = .ok (r,after) := by
  have atStop (n : Nat) {s r : σ} {h after : Heap} (yes : flag s = true)
      (result : cwhile.go oldTest oldBody n s h = .ok (r,after)) : (r,after) = (s,h) := by
    cases n with
    | zero => cases result
    | succ n =>
      simp only [cwhile.go, bind_app] at result
      cases a : oldTest s h with
      | error e => rw [a] at result; contradiction
      | ok tup =>
        obtain ⟨⟨b, s'⟩, h'⟩ := tup
        obtain ⟨rfl,rfl,rfl⟩ := stopped s h _ _ _ yes a
        simpa [a, pure_app] using result.symm
  have go (n : Nat) (s : σ) (h : Heap) (no : flag s = false) {r : σ} {after : Heap}
      (result : cwhile.go oldTest oldBody n s h = .ok (r,after)) :
      cwhileCtrl.go test body n s h = .ok (.ok r,after) := by
    induction n generalizing s h r after with
    | zero => cases result
    | succ n ih =>
      simp only [cwhile.go, bind_app] at result
      simp only [cwhileCtrl.go, bind_app, active s h no]
      cases a : oldTest s h with
      | error e => rw [a] at result; contradiction
      | ok tup =>
        obtain ⟨⟨b, middle⟩, hm⟩ := tup
        rw [a] at result
        cases b with
        | false => simpa [pure_app] using result
        | true =>
          simp only [ite_true, bind_app] at result ⊢
          cases work : oldBody middle hm with
          | error e => rw [work] at result; contradiction
          | ok pair =>
            obtain ⟨next, hn⟩ := pair
            rw [work] at result
            have middleActive := enter s h middle hm no a
            rw [step middle hm next hn middleActive work]
            cases nextFlag : flag next with
            | false => exact ih next hn nextFlag result
            | true =>
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (atStop n nextFlag result)
              rfl
  simp only [cwhileBrk, cwhileCtrl, bind_app, go fuel s h initial run, pure_app]
/-- The test of the extra-field copy loop. -/
def extraCond (s : DeflateStatePtr) (st : ExtraS) : M (Bool × ExtraS) := do
  let d ← ldDeflateState s
  pure (!st.ret && d.pending + st.left > d.pending_buf_size, st)

/-- One iteration of the extra-field copy loop: fill `pending_buf`, update the header CRC, flush. -/
def extraBody (strm : ZStreamPtr) (s : DeflateStatePtr) (st : ExtraS) : M ExtraS := do
  let d ← ldDeflateState s
  let gh ← ldGzHeader d.gzhead
  let copy := d.pending_buf_size - d.pending
  memcpyB (← padd d.pending_buf d.pending.toNat) (← padd gh.extra d.gzindex.toNat) copy.toNat
  wr s (fun d => { d with pending := d.pending_buf_size })
  HCRC_UPDATE strm s st.beg
  wr s (fun d => { d with gzindex := d.gzindex + copy })
  flush_pending strm
  if (← rd s (·.pending)) != 0 then
    wr s (fun d => { d with last_flush := -1 })
    return { st with ret := true }
  pure { st with beg := 0, left := st.left - copy }

/-- The test of the extra-field copy loop. -/
def extraSourceCond (s : DeflateStatePtr) (st : ExtraS) : M (Bool × ExtraS) := do
  let d ← ldDeflateState s
  pure (d.pending + st.left > d.pending_buf_size, st)

/-- One iteration of the extra-field copy loop: fill `pending_buf`, update the header CRC, flush. -/
def extraSourceBody (strm : ZStreamPtr) (s : DeflateStatePtr) (st : ExtraS) : M (LoopStep ExtraS Empty) := do
  let d ← ldDeflateState s
  let gh ← ldGzHeader d.gzhead
  let copy := d.pending_buf_size - d.pending
  memcpyB (← padd d.pending_buf d.pending.toNat) (← padd gh.extra d.gzindex.toNat) copy.toNat
  wr s (fun d => { d with pending := d.pending_buf_size })
  HCRC_UPDATE strm s st.beg
  wr s (fun d => { d with gzindex := d.gzindex + copy })
  flush_pending strm
  if (← rd s (·.pending)) != 0 then
    wr s (fun d => { d with last_flush := -1 })
    return .brk { st with ret := true }
  pure (.next { st with beg := 0, left := st.left - copy })


private theorem if_bind_extra {α β : Type} {p : Prop} [Decidable p] (t f : M α) (k : α → M β) :
    ((if p then t else f) >>= k) = (if p then t >>= k else f >>= k) := by
  by_cases h : p <;> simp only [h, ↓reduceIte]

theorem extraSourceBody_map (strm : ZStreamPtr) (s : DeflateStatePtr) (st : ExtraS)
    (active : st.ret = false) :
    extraSourceBody strm s st = (do
      let next ← extraBody strm s st
      pure (if next.ret then .brk next else .next next)) := by
  unfold extraSourceBody extraBody
  simp only [C.M_bind_assoc, if_bind_extra, C.M_pure_bind, active, Bool.false_eq_true, ↓reduceIte]

/-- Every successful run established by the previous loop invariant is a run of
the byte-matched source loop, with the same result and heap. -/
theorem extra_run_of_previous {strm : ZStreamPtr} {s : DeflateStatePtr} {st result : ExtraS} {h after : Heap}
    (active : st.ret = false) (run : cwhile (extraCond s) (extraBody strm s) st h = .ok (result,after)) :
    cwhileBrk (extraSourceCond s) (extraSourceBody strm s) st h = .ok (result,after) := by
  apply break_of_success ExtraS.ret _ _ _ _ _ _ _ _ active run
  · intro st h no
    simp [extraSourceCond, extraCond, no]
  · intro st h next after live read
    simp only [extraCond, bind_app] at read
    cases got : ldDeflateState s h with
    | error e => rw [got] at read; contradiction
    | ok pair =>
      obtain ⟨d,hm⟩ := pair
      rw [got] at read
      have same : st = next := congrArg Prod.snd (Prod.mk.inj (Except.ok.inj read)).1
      simpa only [← same] using live
  · intro st h b next after yes read
    simp only [extraCond, bind_app] at read
    cases got : ldDeflateState s h with
    | error e => rw [got] at read; contradiction
    | ok pair =>
      obtain ⟨d,hm⟩ := pair
      have unchanged : hm = h := by
        cases s with
        | none => cases got
        | some ptr => cases ptr with
          | tab i =>
            simp only [ldDeflateState, DeflateStateRef.get] at got
            split at got <;> cases got <;> rfl
      rw [got] at read
      simpa [yes, unchanged, pure_app, eq_comm, and_assoc] using read
  · intro st h next after no ran
    simp only [extraSourceBody_map strm s st no, bind_app, ran, pure_app]
end Zlib.Deflate.Universal.Call
