import ZlibF.Spec.Safety.StandaloneCAbi
import ZlibF.Proof.«public-stateless-safety»
import ZlibF.Proof.«inffast.c.abi»
import ZlibF.Proof.«inftrees.c.decoder-safe»
import ZlibF.Proof.«public-gz-call-safety»

/-!
# Standalone C-ABI companion equivalence and safety proofs

This module transfers the Adler, gzip open, gzip seek and fast decoder safety
goals to their C-shaped companions. The fast decoder simulation is imported
from `inffast.c.abi`; the table constructor has its own proof in `inftrees.c.abi`.
-/

namespace ZlibF.Proof.StandaloneCAbi
open C Zlib.GzFs Control

/-! ### Shared monad and state helpers -/

private theorem g_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1
      | .error e => .error e := by
  change (m fs >>= fun x => f x.1 x.2) h = _
  rw [m_bind_app]
  cases m fs h with
  | error e => rfl
  | ok p => rfl

private theorem g_pure_bind {α β : Type} (a : α) (f : α → G β) (fs : Fs) (h : Heap) :
    ((pure a : G α) >>= f) fs h = f a fs h := rfl

private theorem g_bind_assoc {α β γ : Type} (m : G α) (f : α → G β) (g : β → G γ)
    (fs : Fs) (h : Heap) :
    ((m >>= f) >>= g) fs h = (m >>= fun a => f a >>= g) fs h := by
  simp only [g_bind_app]
  cases m fs h <;> rfl

private theorem g_bind_congr {α β : Type} {m₁ m₂ : G α} {k₁ k₂ : α → G β} {fs : Fs} {h : Heap}
    (hm : m₁ fs h = m₂ fs h)
    (hk : ∀ a fs₁ h₁, m₂ fs h = .ok ((a, fs₁), h₁) → k₁ a fs₁ h₁ = k₂ a fs₁ h₁) :
    (m₁ >>= k₁) fs h = (m₂ >>= k₂) fs h := by
  rw [g_bind_app, g_bind_app, hm]
  cases h₂ : m₂ fs h with
  | error e => rfl
  | ok p => exact hk p.1.1 p.1.2 p.2 h₂

private theorem g_bind_ok {α₁ α₂ β : Type} {m₁ : G α₁} {m₂ : G α₂}
    {k₁ : α₁ → G β} {k₂ : α₂ → G β} {fs : Fs} {h : Heap} {res : (β × Fs) × Heap}
    (hok : (m₂ >>= k₂) fs h = .ok res)
    (hm : ∀ a₂ fs₁ h₁, m₂ fs h = .ok ((a₂, fs₁), h₁) →
      ∃ a₁, m₁ fs h = .ok ((a₁, fs₁), h₁) ∧ (k₂ a₂ fs₁ h₁ = .ok res → k₁ a₁ fs₁ h₁ = .ok res)) :
    (m₁ >>= k₁) fs h = .ok res := by
  rw [g_bind_app] at hok ⊢
  cases h₂ : m₂ fs h with
  | error e => simp [h₂] at hok
  | ok p =>
    simp only [h₂] at hok
    rcases hm p.1.1 p.1.2 p.2 h₂ with ⟨a₁, h₁, hk⟩
    rw [h₁]
    exact hk hok

private theorem g_bind_ok_same {α β : Type} {m₁ m₂ : G α}
    {k₁ k₂ : α → G β} {fs : Fs} {h : Heap} {res : (β × Fs) × Heap}
    (hm : m₁ fs h = m₂ fs h)
    (hok : (m₂ >>= k₂) fs h = .ok res)
    (hk : ∀ a fs₁ h₁, m₂ fs h = .ok ((a, fs₁), h₁) → k₂ a fs₁ h₁ = .ok res → k₁ a fs₁ h₁ = .ok res) :
    (m₁ >>= k₁) fs h = .ok res :=
  g_bind_ok hok fun a fs₁ h₁ h₂ => ⟨a, hm ▸ h₂, hk a fs₁ h₁ h₂⟩

private theorem liftM_m_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (liftM m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1)
      | .error e => .error e := by
  change (m >>= fun a => pure (a, fs)) h = _
  rw [m_bind_app]
  cases m h <;> rfl

private theorem updS_updS (state : GzStatePtr) (f g : GzState → GzState) :
    (do Zlib.Gzguts.updS state f; Zlib.Gzguts.updS state g) =
      Zlib.Gzguts.updS state (fun s => g (f s)) := by
  funext h
  cases state with
  | none => rfl
  | some r =>
    cases r with
    | tab i =>
      rw [m_bind_app, Zlib.Gzguts.updS, Zlib.Gzguts.updS, Zlib.Gzguts.updS]
      simp only [m_bind_app, ldGzState, stGzState, GzStateRef.get, GzStateRef.put]
      cases hg : h.gzstates.get i with
      | none => rfl
      | some v =>
        by_cases hro : (GzStateRef.tab i).isRo = true <;> simp [hro, hg, C.upd_upd]

private theorem updS_updS_bind {α : Type} (state : GzStatePtr) (f g : GzState → GzState)
    (k : Unit → M α) (h : Heap) :
    (Zlib.Gzguts.updS state f >>= fun _ => Zlib.Gzguts.updS state g >>= k) h =
      (Zlib.Gzguts.updS state (fun s => g (f s)) >>= k) h := by
  rw [← m_bind_assoc, updS_updS]

private theorem liftM_updS_updS_bind {α : Type} (state : GzStatePtr) (f g : GzState → GzState)
    (k : Unit → G α) (fs : Fs) (h : Heap) :
    ((liftM (Zlib.Gzguts.updS state f) : G Unit) >>= fun _ =>
        (liftM (Zlib.Gzguts.updS state g) : G Unit) >>= k) fs h =
      ((liftM (Zlib.Gzguts.updS state (fun s => g (f s))) : G Unit) >>= k) fs h := by
  rw [g_bind_app, liftM_m_app]
  have h0 := congrFun (updS_updS state f g) h
  rw [m_bind_app] at h0
  cases hu : Zlib.Gzguts.updS state f h with
  | error e =>
    simp only [hu] at h0
    rw [g_bind_app, liftM_m_app, ← h0]
  | ok p =>
    rcases p with ⟨⟨⟩, h1⟩
    simp only [hu] at h0
    simp only [g_bind_app, liftM_m_app, ← h0]

private theorem ldS_after_updS_field (state : GzStatePtr) (f : GzState → GzState)
    {fs fs₁ : Fs} {h h₁ : Heap}
    (hu : (liftM (Zlib.Gzguts.updS state f) : G Unit) fs h = .ok (((), fs₁), h₁)) :
    ∃ s₀, (liftM (Zlib.Gzguts.ldS state) : G GzState) fs₁ h₁ = .ok ((f s₀, fs₁), h₁) := by
  cases state with
  | none =>
    simp [liftM_m_app, Zlib.Gzguts.updS, ldGzState] at hu
  | some r =>
    cases r with
    | tab i =>
      simp only [liftM_m_app, Zlib.Gzguts.updS, Zlib.Gzguts.ldS, m_bind_app,
        ldGzState, stGzState, GzStateRef.get, GzStateRef.put] at hu ⊢
      cases hg : h.gzstates.get i with
      | none => simp [hg] at hu
      | some v =>
        by_cases hro : (GzStateRef.tab i).isRo = true
        · simp [hg, hro] at hu
        · simp only [hg, hro, Bool.false_eq_true, ↓reduceIte] at hu
          injection hu with hp
          injection hp with hp1 hh
          subst hh
          exact ⟨v, by simp⟩

private theorem i64sub_heap (x y : Int64) (h : Heap) (a : Int64) (h' : Heap)
    (hm : Zlib.Gzguts.i64sub x y h = .ok (a, h')) : h' = h := by
  unfold Zlib.Gzguts.i64sub Zlib.Gzguts.i64chk at hm
  split at hm
  · cases hm; rfl
  · cases hm

private theorem load8_freeGzState (state : GzStatePtr) {h h' : Heap}
    (hf : C.freeGzState state h = .ok ((), h')) (p : BPtr) :
    C.load8 p h' = match C.load8 p h with | .ok (b, _) => .ok (b, h') | .error e => .error e := by
  cases state with
  | none =>
    simp only [C.freeGzState, Except.ok.injEq, Prod.mk.injEq] at hf
    obtain ⟨_, rfl⟩ := hf
    cases p with
    | null => rfl
    | ref br o =>
      simp only [C.load8, C.Ptr.load]
      cases C.Space.get h br with
      | none => rfl
      | some a => by_cases hk : o < a.size <;> simp [hk]
  | some r =>
    cases r with
    | tab i =>
      simp only [C.freeGzState] at hf
      cases hg : h.gzstates i with
      | none => simp [hg] at hf
      | some _ =>
        simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hf
        obtain ⟨_, rfl⟩ := hf
        cases p with
        | null => rfl
        | ref br o =>
          simp only [C.load8, C.Ptr.load]
          have hsp : C.Space.get { h with gzstates := C.upd h.gzstates i none } br = C.Space.get h br := by
            cases br <;> rfl
          rw [hsp]
          cases hsp2 : C.Space.get h br with
          | none => rfl
          | some a => by_cases hk : o < a.size <;> simp [hk]

private theorem cwhile_sim {σ₁ σ₂ : Type} (proj : σ₁ → σ₂) (inv : σ₂ → σ₁)
    (_hinv : ∀ s, inv (proj s) = s) (hproj : ∀ s, proj (inv s) = s)
    (c₁ : σ₁ → M (Bool × σ₁)) (b₁ : σ₁ → M σ₁)
    (c₂ : σ₂ → M (Bool × σ₂)) (b₂ : σ₂ → M σ₂)
    (hc : ∀ s h, c₁ s h = (c₂ (proj s) >>= fun r => pure (r.1, inv r.2)) h)
    (hb : ∀ s h, b₁ s h = (b₂ (proj s) >>= fun s' => pure (inv s')) h)
    (s : σ₁) (h : Heap) :
    C.cwhile c₁ b₁ s h = (C.cwhile c₂ b₂ (proj s) >>= fun s' => pure (inv s')) h := by
  change C.cwhile.go c₁ b₁ C.fuel s h = (C.cwhile.go c₂ b₂ C.fuel (proj s) >>= fun s' => pure (inv s')) h
  suffices hgo : ∀ (n : Nat) (s : σ₁) (h : Heap),
      C.cwhile.go c₁ b₁ n s h = (C.cwhile.go c₂ b₂ n (proj s) >>= fun s' => pure (inv s')) h from
    hgo C.fuel s h
  intro n s h
  induction n generalizing s h with
  | zero => rw [C.cwhile.go, m_bind_app, C.cwhile.go]
  | succ n ih =>
    rw [cwhile_go_succ, m_bind_app, cwhile_go_succ]
    cases hc2 : c₂ (proj s) h with
    | error e =>
      have hc1 : c₁ s h = .error e := by simp [hc, hc2]
      simp [hc1]
    | ok p =>
      rcases p with ⟨⟨condB, s2⟩, h1⟩
      have hc1 : c₁ s h = .ok ((condB, inv s2), h1) := by simp [hc, hc2]
      cases condB
      · simp [hc1]
      · simp only [hc1]
        cases hb2 : b₂ s2 h1 with
        | error e =>
          have hb1 : b₁ (inv s2) h1 = .error e := by simp [hb, hproj, hb2]
          simp [hb1]
        | ok p2 =>
          rcases p2 with ⟨s3, h2'⟩
          have hb1 : b₁ (inv s2) h1 = .ok (inv s3, h2') := by simp [hb, hproj, hb2]
          simp only [hb1]
          have := ih (inv s3) h2'
          rw [hproj, m_bind_app] at this
          exact this

private theorem cwhile_sim_bind {σ₁ σ₂ β : Type} (proj : σ₁ → σ₂) (inv : σ₂ → σ₁)
    (hinv : ∀ s, inv (proj s) = s) (hproj : ∀ s, proj (inv s) = s)
    {c₁ : σ₁ → M (Bool × σ₁)} {b₁ : σ₁ → M σ₁}
    {c₂ : σ₂ → M (Bool × σ₂)} {b₂ : σ₂ → M σ₂}
    {k₁ : σ₁ → M β} {k₂ : σ₂ → M β}
    (hc : ∀ s h, c₁ s h = (c₂ (proj s) >>= fun r => pure (r.1, inv r.2)) h)
    (hb : ∀ s h, b₁ s h = (b₂ (proj s) >>= fun s' => pure (inv s')) h)
    (hk : ∀ s h, k₁ (inv s) h = k₂ s h)
    (s : σ₁) (h : Heap) :
    (C.cwhile c₁ b₁ s >>= k₁) h = (C.cwhile c₂ b₂ (proj s) >>= k₂) h := by
  rw [m_bind_app, cwhile_sim proj inv hinv hproj c₁ b₁ c₂ b₂ hc hb s h, m_bind_app, m_bind_app]
  cases C.cwhile c₂ b₂ (proj s) h with
  | error e => rfl
  | ok p => exact hk p.1 p.2

private theorem cdoWhile_sim {σ₁ σ₂ : Type} (proj : σ₁ → σ₂) (inv : σ₂ → σ₁)
    (_hinv : ∀ s, inv (proj s) = s) (hproj : ∀ s, proj (inv s) = s)
    (b₁ : σ₁ → M σ₁) (c₁ : σ₁ → M (Bool × σ₁))
    (b₂ : σ₂ → M σ₂) (c₂ : σ₂ → M (Bool × σ₂))
    (hb : ∀ s h, b₁ s h = (b₂ (proj s) >>= fun s' => pure (inv s')) h)
    (hc : ∀ s h, c₁ s h = (c₂ (proj s) >>= fun r => pure (r.1, inv r.2)) h)
    (s : σ₁) (h : Heap) :
    C.cdoWhile b₁ c₁ s h = (C.cdoWhile b₂ c₂ (proj s) >>= fun s' => pure (inv s')) h := by
  change C.cdoWhile.go b₁ c₁ C.fuel s h = (C.cdoWhile.go b₂ c₂ C.fuel (proj s) >>= fun s' => pure (inv s')) h
  suffices hgo : ∀ (n : Nat) (s : σ₁) (h : Heap),
      C.cdoWhile.go b₁ c₁ n s h = (C.cdoWhile.go b₂ c₂ n (proj s) >>= fun s' => pure (inv s')) h from
    hgo C.fuel s h
  intro n s h
  induction n generalizing s h with
  | zero => rw [C.cdoWhile.go, m_bind_app, C.cdoWhile.go]
  | succ n ih =>
    rw [cdoWhile_go_succ, m_bind_app, cdoWhile_go_succ]
    cases hb2 : b₂ (proj s) h with
    | error e =>
      have hb1 : b₁ s h = .error e := by simp [hb, hb2]
      simp [hb1]
    | ok p1 =>
      rcases p1 with ⟨s2, h1⟩
      have hb1 : b₁ s h = .ok (inv s2, h1) := by simp [hb, hb2]
      simp only [hb1]
      cases hc2 : c₂ s2 h1 with
      | error e =>
        have hc1 : c₁ (inv s2) h1 = .error e := by simp [hc, hproj, hc2]
        simp [hc1]
      | ok p2 =>
        rcases p2 with ⟨⟨condB, s3⟩, h2⟩
        have hc1 : c₁ (inv s2) h1 = .ok ((condB, inv s3), h2) := by simp [hc, hproj, hc2]
        cases condB
        · simp [hc1]
        · simp only [hc1]
          have := ih (inv s3) h2
          rw [hproj, m_bind_app] at this
          exact this

private theorem cdoWhile_sim_bind {σ₁ σ₂ β : Type} (proj : σ₁ → σ₂) (inv : σ₂ → σ₁)
    (hinv : ∀ s, inv (proj s) = s) (hproj : ∀ s, proj (inv s) = s)
    {b₁ : σ₁ → M σ₁} {c₁ : σ₁ → M (Bool × σ₁)}
    {b₂ : σ₂ → M σ₂} {c₂ : σ₂ → M (Bool × σ₂)}
    {k₁ : σ₁ → M β} {k₂ : σ₂ → M β}
    (hb : ∀ s h, b₁ s h = (b₂ (proj s) >>= fun s' => pure (inv s')) h)
    (hc : ∀ s h, c₁ s h = (c₂ (proj s) >>= fun r => pure (r.1, inv r.2)) h)
    (hk : ∀ s h, k₁ (inv s) h = k₂ s h)
    (s : σ₁) (h : Heap) :
    (C.cdoWhile b₁ c₁ s >>= k₁) h = (C.cdoWhile b₂ c₂ (proj s) >>= k₂) h := by
  rw [m_bind_app, cdoWhile_sim proj inv hinv hproj b₁ c₁ b₂ c₂ hb hc s h, m_bind_app, m_bind_app]
  cases C.cdoWhile b₂ c₂ (proj s) h with
  | error e => rfl
  | ok p => exact hk p.1 p.2

/-! ### Part 1: `adler32_z_c` equivalence and safety -/

section Adler32
open Zlib.Adler32

private def toLocals (s : LocalsC) : Locals := ⟨s.adler, s.sum2, s.buf, s.len, s.n⟩
private def ofLocals (s : Locals) : LocalsC := ⟨s.adler, s.sum2, s.buf, s.len, s.n⟩

private theorem ofLocals_toLocals (s : LocalsC) : ofLocals (toLocals s) = s := by
  cases s; rfl
private theorem toLocals_ofLocals (s : Locals) : toLocals (ofLocals s) = s := by
  cases s; rfl

private theorem do1C_eq (s : LocalsC) (i : Int) (h : Heap) :
    do1C s i h = (do1 (toLocals s) i >>= fun s' => pure (ofLocals s')) h := by
  simp only [do1C, do1, cinline, toLocals, ofLocals, m_bind_app]
  cases hidx : index8 s.buf i h <;> simp

private theorem do16C_eq (s : LocalsC) (h : Heap) :
    do16C s h = (do16 (toLocals s) >>= fun s' => pure (ofLocals s')) h := by
  have step (m₁ : M LocalsC) (m₂ : M Locals)
      (hm : ∀ hx, m₁ hx = (m₂ >>= fun r => pure (ofLocals r)) hx)
      (k₁ : LocalsC → M LocalsC) (k₂ : Locals → M Locals)
      (hk : ∀ y hy, k₁ y hy = (k₂ (toLocals y) >>= fun r => pure (ofLocals r)) hy)
      (hx : Heap) :
      (m₁ >>= k₁) hx = ((m₂ >>= k₂) >>= fun r => pure (ofLocals r)) hx := by
    rw [m_bind_app, hm hx, m_bind_app, m_bind_app]
    cases hm2 : m₂ hx with
    | error e => simp [hm2]
    | ok p => simp [hm2, hk, toLocals_ofLocals]; rfl
  simp only [do16C, do16]
  refine step _ _ (fun hx => do1C_eq s 0 hx) _ _ (fun y hy => ?_) h
  refine step _ _ (fun hx => do1C_eq y 1 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 2 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 3 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 4 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 5 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 6 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 7 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 8 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 9 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 10 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 11 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 12 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 13 hx) _ _ (fun y hy => ?_) hy
  refine step _ _ (fun hx => do1C_eq y 14 hx) _ _ (fun y hy => ?_) hy
  exact do1C_eq y 15 hy

private theorem stepByteC_eq (s : LocalsC) (h : Heap) :
    stepByteC s h = (stepByte (toLocals s) >>= fun s' => pure (ofLocals s')) h := by
  simp only [stepByteC, stepByte, cinline, toLocals, ofLocals, m_bind_app]
  cases load8 s.buf h with
  | error e => rfl
  | ok p =>
    rcases p with ⟨b, h1⟩
    simp only
    cases Ptr.add s.buf 1 h1 <;> rfl

theorem adler32_z_c_eq (adler : UInt64) (buf : ConstBPtr) (len : UInt64) :
    adler32_z_c adler buf len = adler32_z adler buf len := by
  funext h
  simp only [adler32_z_c, adler32_z, cdecl, cinline]
  have hdef : (default : UInt32) = 0 := rfl
  rw [hdef]
  simp only [m_pure_bind]
  by_cases h1 : (len == 1) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases hnull : (buf == .null) = true
    · simp [hnull]
    · simp only [hnull, Bool.false_eq_true, ↓reduceIte]
      by_cases hlt16 : len < 16
      · simp only [hlt16, ↓reduceIte]
        apply cwhile_sim_bind toLocals ofLocals ofLocals_toLocals toLocals_ofLocals
        · intro s _; rfl
        · exact stepByteC_eq
        · intro s _; rfl
      · simp only [hlt16, ↓reduceIte]
        apply cwhile_sim_bind toLocals ofLocals ofLocals_toLocals toLocals_ofLocals
        · intro s _; cases s; rfl
        · intro s hx
          rw [m_bind_assoc]
          apply cdoWhile_sim_bind toLocals ofLocals ofLocals_toLocals toLocals_ofLocals
          · intro u hu
            cases u
            rw [m_bind_app, do16C_eq, m_bind_app]
            dsimp only [toLocals]
            simp only [m_bind_app]
            rcases do16 _ hu with e | ⟨u', h1'⟩
            · rfl
            · simp only [ofLocals, pure_app]
              cases Ptr.add u'.buf 16 h1' <;> rfl
          · intro u _; cases u; rfl
          · intro u _; rfl
        · intro s0 h0
          dsimp only [ofLocals]
          by_cases hnz : (s0.len != 0) = true
          · simp only [hnz, ↓reduceIte]
            apply cwhile_sim_bind toLocals ofLocals ofLocals_toLocals toLocals_ofLocals
            · intro u _; cases u; rfl
            · intro u hu
              cases u
              rw [m_bind_app, do16C_eq, m_bind_app]
              dsimp only [toLocals]
              simp only [m_bind_app]
              rcases do16 _ hu with e | ⟨u', h1'⟩
              · rfl
              · simp only [ofLocals, pure_app]
                cases Ptr.add u'.buf 16 h1' <;> rfl
            · intro s1 h1'
              apply cwhile_sim_bind toLocals ofLocals ofLocals_toLocals toLocals_ofLocals
              · intro u _; rfl
              · exact stepByteC_eq
              · intro u _; rfl
          · simp [hnz]

theorem adler32_z_c_safety : ZlibF.Spec.Public.Goal.adler32_z_c_safety := by
  intro h seed ptr len bytes hpre
  rw [adler32_z_c_eq]
  exact ZlibF.Spec.Public.StatelessSafetyProof.adler32_z_safety h seed ptr len bytes hpre

end Adler32

open Zlib.Inflate in
/-- Materialize C's optional output store in the heap, after the dictionary copy.
    A refused call leaves the output alone, including when its address is invalid. -/
theorem inflateGetDictionary_c_eq (strm : ZStreamPtr) (dictionary length : BPtr) :
    inflateGetDictionary_c strm dictionary length = (do
      let (rc, result) ← inflateGetDictionary strm dictionary (some 0)
      if rc == Z_OK && length != .null then
        storeU32 length (result.getD 0)
      return rc) := by
  simp [inflateGetDictionary_c, inflateGetDictionary, getDictionaryWith, m_bind_assoc_eq, m_pure_bind_eq, ite_bind_eq, Z_OK, Z_STREAM_ERROR]


open Zlib.Inflate in
/-- The two ordered C field writes update the same stream as the combined model write. -/
theorem inflateValidate_c_eq (strm : ZStreamPtr) (check : Int32) :
    inflateValidate_c strm check = inflateValidate strm check := by
  funext h
  unfold inflateValidate_c inflateValidate
  refine m_bind_congr rfl fun code h1 _ => ?_
  split
  · rfl
  · refine m_bind_congr rfl fun z h2 _ => ?_
    refine m_bind_congr rfl fun st h3 _ => ?_
    cases st with
    | none => rfl
    | some ref =>
      obtain ⟨i⟩ := ref
      cases old : h3.istates i with
      | none => simp [ ldInflateState, InflateStateRef.get, old]
      | some s =>
        by_cases c : check = 0 <;> by_cases w : s.wrap = 0 <;>
          by_cases q : s.reqwrap = 0 <;>
          simp [ wrS, ldInflateState, stInflateState, InflateStateRef.get, InflateStateRef.isRo,
            InflateStateRef.put, old, c, w, q, upd_upd]

/-! ### Part 2: `gz_reset_c`, `gzseek64_c`, `gz_open_c`, `gzopen_c` equivalence and safety -/

section Gzlib
open Zlib.Gzlib Zlib.Gzguts

theorem gz_reset_c_eq (state : GzStatePtr) : gz_reset_c state = gz_reset state := by
  funext h
  simp only [gz_reset_c, gz_reset]
  refine m_bind_congr rfl fun _ h1 _ => ?_
  refine m_bind_congr rfl fun _ h2 _ => ?_
  refine m_bind_congr rfl fun s h3 _ => ?_
  by_cases hm : (s.mode == GZ_READ) = true
  · simp only [hm, ↓reduceIte, updS_updS_bind]
  · simp only [hm, Bool.false_eq_true, ↓reduceIte, updS_updS_bind]

private theorem gzseek64_read_tail_eq (state : GzStatePtr) (p1 : Int64)
    (restR : GzState → Int64 → G ZOff64T) (restW : Int64 → G ZOff64T) (fs : Fs) (h : Heap) :
    (do
      let s1 ← liftM (Zlib.Gzguts.ldS state)
      let off1 ← liftM (Zlib.Gzguts.i64sub p1 s1.x.pos)
      let s2 ← liftM (Zlib.Gzguts.ldS state)
      if s2.mode == GZ_READ then restR s2 off1 else restW off1) fs h =
    (do
      let s1 ← liftM (Zlib.Gzguts.ldS state)
      let off1 ← liftM (Zlib.Gzguts.i64sub p1 s1.x.pos)
      if s1.mode == GZ_READ then do
        let s2 ← liftM (Zlib.Gzguts.ldS state)
        restR s2 off1
      else restW off1) fs h := by
  simp only [g_bind_app, liftM_m_app, Zlib.Gzguts.ldS, ldGzState]
  cases state with
  | none => rfl
  | some r =>
    simp only
    cases hget : C.GzStateRef.get h r with
    | none => simp
    | some s1 =>
      simp only
      cases hsub : Zlib.Gzguts.i64sub p1 s1.x.pos h with
      | error e => simp
      | ok p =>
        rcases p with ⟨off1, h'⟩
        have hh := i64sub_heap p1 s1.x.pos h off1 h' hsub
        subst hh
        by_cases hm : (s1.mode == GZ_READ) = true
        · simp only [hm, ↓reduceIte, g_bind_app, liftM_m_app, ldGzState, hget]
        · simp only [hm, Bool.false_eq_true, ↓reduceIte, hget]

private theorem gzseek64_after_tail_leaf (state : GzStatePtr) (p1 : Int64)
    {fs : Fs} {h : Heap}
    (restRC : GzState → Int64 → G ZOff64T)
    (restRR : GzState → Int64 → G ZOff64T)
    (restW : Int64 → G ZOff64T)
    (hrest : ∀ s2 off1 fs1 h1, restRC s2 off1 fs1 h1 = restRR s2 off1 fs1 h1) :
    (do
      let s1 ← liftM (Zlib.Gzguts.ldS state)
      let off1 ← liftM (Zlib.Gzguts.i64sub p1 s1.x.pos)
      let s2 ← liftM (Zlib.Gzguts.ldS state)
      if s2.mode == GZ_READ then restRC s2 off1 else restW off1) fs h =
    (do
      let s1 ← liftM (Zlib.Gzguts.ldS state)
      let off1 ← liftM (Zlib.Gzguts.i64sub p1 s1.x.pos)
      if s1.mode == GZ_READ then do
        let s2 ← liftM (Zlib.Gzguts.ldS state)
        restRR s2 off1
      else restW off1) fs h := by
  rw [← gzseek64_read_tail_eq state p1 restRR restW fs h]
  refine g_bind_congr rfl fun s1 _ _ _ => ?_
  refine g_bind_congr rfl fun off1 _ _ _ => ?_
  refine g_bind_congr rfl fun s2 _ _ _ => ?_
  by_cases hr : (s2.mode == GZ_READ) = true
  · simp only [hr, ↓reduceIte]
    exact hrest s2 off1 _ _
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]

local macro "solve_gzseek_leaf" file:ident p1:ident : tactic =>
  `(tactic| (
    refine gzseek64_after_tail_leaf (castState $file) $p1 _ _ _ fun s2 off1 fs_c h_c => ?_
    rw [g_bind_assoc]
    refine g_bind_congr rfl fun gtoff _ _ _ => ?_
    by_cases hn0 : (gtoff || decide (u32ToI64 s2.x.«have» > off1)) = true <;>
      simp only [hn0, ↓reduceIte, Bool.false_eq_true, g_pure_bind]))

local macro "solve_gzseek_after_bound2" file:ident s:ident p1:ident : tactic =>
  `(tactic| (
    by_cases hcopy : (($s).mode == GZ_READ && ($s).how == GZ_COPY) = true
    · simp only [hcopy, ↓reduceIte, g_bind_assoc]
      refine g_bind_congr rfl fun d0 _ _ _ => ?_
      rw [g_bind_assoc]
      refine g_bind_congr rfl fun d _ _ _ => ?_
      refine g_bind_congr rfl fun r _ _ _ => ?_
      by_cases hr1 : (r == -1) = true
      · simp only [hr1, ↓reduceIte]
      · simp only [hr1, Bool.false_eq_true, ↓reduceIte]
        refine g_bind_congr rfl fun _ _ _ _ => ?_
        rw [liftM_updS_updS_bind, liftM_updS_updS_bind]
    · simp only [hcopy, Bool.false_eq_true, ↓reduceIte]
      refine g_bind_congr rfl fun sx _ _ _ => ?_
      by_cases hlt_pos : $p1 < sx.x.pos
      · simp only [hlt_pos, ↓reduceIte]
        by_cases hnr : (sx.mode != GZ_READ) = true
        · simp only [hnr, ↓reduceIte]
        · simp only [hnr, Bool.false_eq_true, ↓reduceIte]
          refine g_bind_congr rfl fun rw _ _ _ => ?_
          by_cases hrw : (rw == -1) = true
          · simp only [hrw, ↓reduceIte]
          · simp only [hrw, Bool.false_eq_true, ↓reduceIte]
            solve_gzseek_leaf $file $p1
      · simp only [hlt_pos, ↓reduceIte]
        solve_gzseek_leaf $file $p1))

local macro "solve_gzseek_after_p0" file:ident offset:ident s:ident p0:term : tactic =>
  `(tactic| (
    by_cases hp0 : $p0 > 0
    · simp only [hp0, ↓reduceIte]
      refine g_bind_congr rfl fun bound _ _ _ => ?_
      by_cases hgt : $offset > bound
      · simp only [hgt, ↓reduceIte]
      · simp only [hgt, ↓reduceIte, g_pure_bind]
        refine g_bind_congr rfl fun negPos _ _ _ => ?_
        by_cases hlt_neg : $offset < negPos
        · simp only [hlt_neg, ↓reduceIte]
        · simp only [hlt_neg, ↓reduceIte]
          refine g_bind_congr rfl fun p1 _ _ _ => ?_
          by_cases hxneg : ($s).x.pos < 0
          · simp only [hxneg, ↓reduceIte]
            refine g_bind_congr rfl fun bound2 _ _ _ => ?_
            by_cases hgt2 : p1 > bound2
            · simp only [hgt2, ↓reduceIte]
            · simp only [hgt2, ↓reduceIte]
              solve_gzseek_after_bound2 $file $s p1
          · simp only [hxneg, ↓reduceIte]
            solve_gzseek_after_bound2 $file $s p1
    · simp only [hp0, ↓reduceIte, g_pure_bind]
      refine g_bind_congr rfl fun negPos _ _ _ => ?_
      by_cases hlt_neg : $offset < negPos
      · simp only [hlt_neg, ↓reduceIte]
      · simp only [hlt_neg, ↓reduceIte]
        refine g_bind_congr rfl fun p1 _ _ _ => ?_
        by_cases hxneg : ($s).x.pos < 0
        · simp only [hxneg, ↓reduceIte]
          refine g_bind_congr rfl fun bound2 _ _ _ => ?_
          by_cases hgt2 : p1 > bound2
          · simp only [hgt2, ↓reduceIte]
          · simp only [hgt2, ↓reduceIte]
            solve_gzseek_after_bound2 $file $s p1
        · simp only [hxneg, ↓reduceIte]
          solve_gzseek_after_bound2 $file $s p1))

theorem gzseek64_c_eq (file : GzFilePtr) (offset : ZOff64T) (whence : Int32) :
    gzseek64_c file offset whence = gzseek64 file offset whence := by
  funext fs h
  simp only [gzseek64_c, gzseek64, gdecl, ginline, g_pure_bind]
  by_cases hnone : file.isNone = true
  · simp [hnone]
  · simp only [hnone, Bool.false_eq_true, ↓reduceIte]
    refine g_bind_congr rfl fun s fs1 h1 _ => ?_
    by_cases hm : (s.mode != GZ_READ && s.mode != GZ_WRITE) = true
    · simp [hm]
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]
      by_cases herr : (s.err != Z_OK && s.err != Z_BUF_ERROR) = true
      · simp [herr]
      · simp only [herr, Bool.false_eq_true, ↓reduceIte]
        by_cases hwh : (whence != SEEK_SET && whence != SEEK_CUR) = true
        · simp [hwh]
        · simp only [hwh, Bool.false_eq_true, ↓reduceIte]
          by_cases hset : (whence == SEEK_SET) = true
          · simp only [hset, ↓reduceIte, g_pure_bind]
            solve_gzseek_after_p0 file offset s (0 : Int64)
          · simp only [hset, Bool.false_eq_true, ↓reduceIte]
            refine g_bind_congr rfl fun p0 _ _ _ => ?_
            solve_gzseek_after_p0 file offset s p0

theorem gzseek64_c_safety : ZlibF.Spec.Public.Goal.gzseek64_c_safety := by
  have ⟨href, hcall⟩ := ZlibF.Spec.Public.GzCallSafetyProof.gzseek64_safety
  refine ⟨fun fs h offset whence => ?_, fun h fs i s offset whence hhist hget harg => ?_⟩
  · rw [gzseek64_c_eq]; exact href fs h offset whence
  · have hc := hcall h fs i s (.gzseek64 (some (.in_gzstate_x i)) offset whence) hhist hget trivial rfl harg
    dsimp only [ZlibF.Spec.Public.Call.execute, ZlibF.Spec.Public.Call.Result] at hc
    change _ ∧ _ ∧ ∀ (value : CExportAs "gzseek64" ZOff64T) (fs' : Fs) (after : Heap),
      gzseek64_c (some (.in_gzstate_x i)) offset whence fs h = .ok ((value, fs'), after) → _
    simpa only [gzseek64_c_eq] using hc

private theorem gwhile_go_succ {σ : Type} (cond : σ → G (Bool × σ)) (body : σ → G σ)
    (n : Nat) (s : σ) (fs : Fs) (h : Heap) :
    gwhile.go cond body (n + 1) s fs h =
      match cond s fs h with
      | .error e => .error e
      | .ok (((false, s1), fs1), h1) => .ok ((s1, fs1), h1)
      | .ok (((true, s1), fs1), h1) =>
        match body s1 fs1 h1 with
        | .error e => .error e
        | .ok ((s2, fs2), h2) => gwhile.go cond body n s2 fs2 h2 := by
  rw [gwhile.go]; simp only [g_bind_app]
  rcases h1 : cond s fs h with e | ⟨⟨⟨c, s1⟩, fs1⟩, h1'⟩
  · rfl
  · cases c
    · rfl
    · simp only [ite_true, g_bind_app]
      cases body s1 fs1 h1' <;> rfl

private theorem gwhileCtrl_go_succ {σ ρ : Type} (cond : σ → G (Bool × σ))
    (body : σ → G (LoopStep σ ρ)) (n : Nat) (s : σ) (fs : Fs) (h : Heap) :
    gwhileCtrl.go cond body (n + 1) s fs h =
      match cond s fs h with
      | .error e => .error e
      | .ok (((false, s1), fs1), h1) => .ok ((.ok s1, fs1), h1)
      | .ok (((true, s1), fs1), h1) =>
        match body s1 fs1 h1 with
        | .error e => .error e
        | .ok ((.next s2, fs2), h2) | .ok ((.cont s2, fs2), h2) => gwhileCtrl.go cond body n s2 fs2 h2
        | .ok ((.brk s2, fs2), h2) => .ok ((.ok s2, fs2), h2)
        | .ok ((.ret r, fs2), h2) => .ok ((.error r, fs2), h2) := by
  rw [gwhileCtrl.go]; simp only [g_bind_app]
  rcases h1 : cond s fs h with e | ⟨⟨⟨c, s1⟩, fs1⟩, h1'⟩
  · rfl
  · cases c
    · rfl
    · simp only [ite_true, g_bind_app]
      rcases body s1 fs1 h1' with e | ⟨⟨st, fs2⟩, h2⟩
      · rfl
      · cases st <;> rfl

private theorem gz_open_post_append_of_ok (state : GzStatePtr)
    (fs9 : Fs) (h9 : Heap) (res : (GzFilePtr × Fs) × Heap)
    (ht9 :
      (do
        let s ← liftM (ldS state)
        if s.mode == GZ_READ then
          let st ← fsLseek s.fd 0 SEEK_CUR
          liftM (updS state fun s => { s with start := st })
          if st == -1 then liftM (updS state fun s => { s with start := 0 })
        liftM (gz_reset state)
        pure (castFile state)) fs9 h9 = .ok res) :
    (do
      let s ← liftM (ldS state)
      if s.mode == GZ_READ then
        let st ← fsLseek s.fd 0 SEEK_CUR
        liftM (updS state fun s => { s with start := st })
        let s ← liftM (ldS state)
        if s.start == -1 then liftM (updS state fun s => { s with start := 0 })
      liftM (gz_reset state)
      pure (castFile state)) fs9 h9 = .ok res := by
  refine g_bind_ok_same rfl ht9 fun s fs10 h10 _ ht10 => ?_
  by_cases hmr : (s.mode == GZ_READ) = true
  · simp only [hmr, ↓reduceIte] at ht10 ⊢
    refine g_bind_ok_same rfl ht10 fun st fs11 h11 _ ht11 => ?_
    rw [g_bind_app] at ht11 ⊢
    cases hus : (liftM (updS state fun s => { s with start := st }) : G Unit) fs11 h11 with
    | error e => simp [hus] at ht11
    | ok q2 =>
      rcases q2 with ⟨⟨⟨⟩, fs12⟩, h12⟩
      simp only [hus] at ht11 ⊢
      obtain ⟨s₀', hlds'⟩ := ldS_after_updS_field state (fun s => { s with start := st }) hus
      rw [g_bind_app, hlds']
      dsimp only
      by_cases hst1 : (st == -1) = true
      · simpa only [hst1, ↓reduceIte] using ht11
      · simpa only [hst1, Bool.false_eq_true, ↓reduceIte] using ht11
  · simpa only [hmr, Bool.false_eq_true, ↓reduceIte] using ht10

private theorem gz_open_post_fd_of_ok (state : GzStatePtr)
    (fs7 : Fs) (h7 : Heap) (res : (GzFilePtr × Fs) × Heap)
    (ht7 :
      (do
        let s ← liftM (ldS state)
        if s.fd == -1 then
          liftM (freeB s.path)
          liftM (freeGzState state)
          pure none
        else do
          if s.mode == GZ_APPEND then
            let _ ← fsLseek s.fd 0 SEEK_END
            liftM (updS state fun s => { s with mode := GZ_WRITE })
          let s ← liftM (ldS state)
          if s.mode == GZ_READ then
            let st ← fsLseek s.fd 0 SEEK_CUR
            liftM (updS state fun s => { s with start := st })
            if st == -1 then liftM (updS state fun s => { s with start := 0 })
          liftM (gz_reset state)
          pure (castFile state)) fs7 h7 = .ok res) :
    (do
      let s ← liftM (ldS state)
      if s.fd == -1 then
        liftM (freeB s.path)
        liftM (freeGzState state)
        pure none
      else do
        if s.mode == GZ_APPEND then
          let _ ← fsLseek s.fd 0 SEEK_END
          liftM (updS state fun s => { s with mode := GZ_WRITE })
        let s ← liftM (ldS state)
        if s.mode == GZ_READ then
          let st ← fsLseek s.fd 0 SEEK_CUR
          liftM (updS state fun s => { s with start := st })
          let s ← liftM (ldS state)
          if s.start == -1 then liftM (updS state fun s => { s with start := 0 })
        liftM (gz_reset state)
        pure (castFile state)) fs7 h7 = .ok res := by
  refine g_bind_ok_same rfl ht7 fun s fs8 h8 _ ht8 => ?_
  by_cases hfd1 : (s.fd == -1) = true
  · simpa only [hfd1, ↓reduceIte] using ht8
  · simp only [hfd1, Bool.false_eq_true, ↓reduceIte] at ht8 ⊢
    by_cases hma : (s.mode == GZ_APPEND) = true
    · simp only [hma, ↓reduceIte] at ht8 ⊢
      refine g_bind_ok_same rfl ht8 fun _ fsa ha _ hta => ?_
      refine g_bind_ok_same rfl hta fun _ fs9 h9 _ ht9 => ?_
      exact gz_open_post_append_of_ok state fs9 h9 res ht9
    · simp only [hma, Bool.false_eq_true, ↓reduceIte] at ht8 ⊢
      exact gz_open_post_append_of_ok state fs8 h8 res ht8

private theorem gz_open_after_loop_of_ok (path : ConstVoidPtr) (fd : Int32) (state : GzStatePtr)
    (l : GzOpenLocals) (hlst : l.state = state)
    (fs : Fs) (h : Heap) (res : (GzFilePtr × Fs) × Heap)
    (hok :
      (do
        let oflag0 := l.oflag
        let exclusive := l.exclusive
        let s ← liftM (ldS state)
        if s.mode == GZ_NONE then
          liftM (freeGzState state)
          pure none
        else do
          if s.mode == GZ_READ then
            if s.direct == 1 then
              liftM (freeGzState state)
              pure none
            else do
              if s.direct == 0 then liftM (updS state fun s => { s with direct := 1 })
              let len ← liftM (strlenB path)
              let p ← liftM (allocB (len + 1).toNat)
              liftM (updS state fun s => { s with path := p })
              if p == (Ptr.null : BPtr) then
                liftM (freeGzState state)
                pure none
              else do
                let fmt ← liftM (strLit "%s")
                let _ ← liftM (snprintf p (len + 1) fmt [.str path])
                let s ← liftM (ldS state)
                let oflag : Int32 := oflag0 ||| (O_LARGEFILE |||
                  (if s.mode == GZ_READ then 0
                   else (O_WRONLY ||| O_CREAT ||| (if exclusive != 0 then O_EXCL else 0) |||
                         (if s.mode == GZ_WRITE then O_TRUNC else O_APPEND))))
                if fd == -1 then
                  let name ← liftM (cstring path)
                  let r ← fsOpen name oflag
                  liftM (updS state fun s => { s with fd := r })
                else do
                  if oflag &&& O_NONBLOCK != 0 then fsFcntl fd
                  if oflag &&& O_CLOEXEC != 0 then fsFcntl fd
                  liftM (updS state fun s => { s with fd := fd })
                let s ← liftM (ldS state)
                if s.fd == -1 then
                  liftM (freeB s.path)
                  liftM (freeGzState state)
                  pure none
                else do
                  if s.mode == GZ_APPEND then
                    let _ ← fsLseek s.fd 0 SEEK_END
                    liftM (updS state fun s => { s with mode := GZ_WRITE })
                  let s ← liftM (ldS state)
                  if s.mode == GZ_READ then
                    let st ← fsLseek s.fd 0 SEEK_CUR
                    liftM (updS state fun s => { s with start := st })
                    if st == -1 then liftM (updS state fun s => { s with start := 0 })
                  liftM (gz_reset state)
                  pure (castFile state)
          else if s.direct == -1 then
            liftM (freeGzState state)
            pure none
          else do
            let len ← liftM (strlenB path)
            let p ← liftM (allocB (len + 1).toNat)
            liftM (updS state fun s => { s with path := p })
            if p == (Ptr.null : BPtr) then
              liftM (freeGzState state)
              pure none
            else do
              let fmt ← liftM (strLit "%s")
              let _ ← liftM (snprintf p (len + 1) fmt [.str path])
              let s ← liftM (ldS state)
              let oflag : Int32 := oflag0 ||| (O_LARGEFILE |||
                (if s.mode == GZ_READ then 0
                 else (O_WRONLY ||| O_CREAT ||| (if exclusive != 0 then O_EXCL else 0) |||
                       (if s.mode == GZ_WRITE then O_TRUNC else O_APPEND))))
              if fd == -1 then
                let name ← liftM (cstring path)
                let r ← fsOpen name oflag
                liftM (updS state fun s => { s with fd := r })
              else do
                if oflag &&& O_NONBLOCK != 0 then fsFcntl fd
                if oflag &&& O_CLOEXEC != 0 then fsFcntl fd
                liftM (updS state fun s => { s with fd := fd })
              let s ← liftM (ldS state)
              if s.fd == -1 then
                liftM (freeB s.path)
                liftM (freeGzState state)
                pure none
              else do
                if s.mode == GZ_APPEND then
                  let _ ← fsLseek s.fd 0 SEEK_END
                  liftM (updS state fun s => { s with mode := GZ_WRITE })
                let s ← liftM (ldS state)
                if s.mode == GZ_READ then
                  let st ← fsLseek s.fd 0 SEEK_CUR
                  liftM (updS state fun s => { s with start := st })
                  if st == -1 then liftM (updS state fun s => { s with start := 0 })
                liftM (gz_reset state)
                pure (castFile state)) fs h = .ok res) :
    (do
      let s ← liftM (ldS l.state)
      if s.mode == GZ_NONE then
        liftM (freeGzState l.state)
        pure none
      else do
        if s.mode == GZ_READ then
          if s.direct == 1 then
            liftM (freeGzState l.state)
            pure none
          else do
            if s.direct == 0 then liftM (updS l.state fun s => { s with direct := 1 })
            let len_ ← ginline (liftM (strlenB path))
            let l := { l with len := len_ }
            let p ← ginline (liftM (allocB (l.len + 1).toNat))
            liftM (updS l.state fun s => { s with path := p })
            let s ← liftM (ldS l.state)
            if s.path == (Ptr.null : BPtr) then
              liftM (freeGzState l.state)
              pure none
            else do
              let fmt ← liftM (strLit "%s")
              let _ ← liftM (snprintf s.path (l.len + 1) fmt [.str path])
              let s ← liftM (ldS l.state)
              let l := { l with oflag := l.oflag ||| (O_LARGEFILE |||
                (if s.mode == GZ_READ then 0
                 else (O_WRONLY ||| O_CREAT ||| (if l.exclusive != 0 then O_EXCL else 0) |||
                       (if s.mode == GZ_WRITE then O_TRUNC else O_APPEND)))) }
              if fd == -1 then
                let r ← ginline (do let name ← liftM (cstring path); fsOpen name l.oflag)
                liftM (updS l.state fun s => { s with fd := r })
              else do
                if l.oflag &&& O_NONBLOCK != 0 then fsFcntl fd
                if l.oflag &&& O_CLOEXEC != 0 then fsFcntl fd
                liftM (updS l.state fun s => { s with fd := fd })
              let s ← liftM (ldS l.state)
              if s.fd == -1 then
                liftM (freeB s.path)
                liftM (freeGzState l.state)
                pure none
              else do
                if s.mode == GZ_APPEND then
                  let _ ← fsLseek s.fd 0 SEEK_END
                  liftM (updS l.state fun s => { s with mode := GZ_WRITE })
                let s ← liftM (ldS l.state)
                if s.mode == GZ_READ then
                  let st ← ginline (fsLseek s.fd 0 SEEK_CUR)
                  liftM (updS l.state fun s => { s with start := st })
                  let s ← liftM (ldS l.state)
                  if s.start == -1 then liftM (updS l.state fun s => { s with start := 0 })
                liftM (gz_reset l.state)
                pure (castFile l.state)
        else if s.direct == -1 then
          liftM (freeGzState l.state)
          pure none
        else do
          let len_ ← ginline (liftM (strlenB path))
          let l := { l with len := len_ }
          let p ← ginline (liftM (allocB (l.len + 1).toNat))
          liftM (updS l.state fun s => { s with path := p })
          let s ← liftM (ldS l.state)
          if s.path == (Ptr.null : BPtr) then
            liftM (freeGzState l.state)
            pure none
          else do
            let fmt ← liftM (strLit "%s")
            let _ ← liftM (snprintf s.path (l.len + 1) fmt [.str path])
            let s ← liftM (ldS l.state)
            let l := { l with oflag := l.oflag ||| (O_LARGEFILE |||
              (if s.mode == GZ_READ then 0
               else (O_WRONLY ||| O_CREAT ||| (if l.exclusive != 0 then O_EXCL else 0) |||
                     (if s.mode == GZ_WRITE then O_TRUNC else O_APPEND)))) }
            if fd == -1 then
              let r ← ginline (do let name ← liftM (cstring path); fsOpen name l.oflag)
              liftM (updS l.state fun s => { s with fd := r })
            else do
              if l.oflag &&& O_NONBLOCK != 0 then fsFcntl fd
              if l.oflag &&& O_CLOEXEC != 0 then fsFcntl fd
              liftM (updS l.state fun s => { s with fd := fd })
            let s ← liftM (ldS l.state)
            if s.fd == -1 then
              liftM (freeB s.path)
              liftM (freeGzState l.state)
              pure none
            else do
              if s.mode == GZ_APPEND then
                let _ ← fsLseek s.fd 0 SEEK_END
                liftM (updS l.state fun s => { s with mode := GZ_WRITE })
              let s ← liftM (ldS l.state)
              if s.mode == GZ_READ then
                let st ← ginline (fsLseek s.fd 0 SEEK_CUR)
                liftM (updS l.state fun s => { s with start := st })
                let s ← liftM (ldS l.state)
                if s.start == -1 then liftM (updS l.state fun s => { s with start := 0 })
              liftM (gz_reset l.state)
              pure (castFile l.state)) fs h = .ok res := by
  subst hlst
  simp only [ginline]
  have commonTail (fs0 : Fs) (h0 : Heap)
      (ht :
        (do
          let len ← liftM (strlenB path)
          let p ← liftM (allocB (len + 1).toNat)
          liftM (updS l.state fun s => { s with path := p })
          if p == (Ptr.null : BPtr) then
            liftM (freeGzState l.state)
            pure none
          else do
            let fmt ← liftM (strLit "%s")
            let _ ← liftM (snprintf p (len + 1) fmt [.str path])
            let s ← liftM (ldS l.state)
            let oflag : Int32 := l.oflag ||| (O_LARGEFILE |||
              (if s.mode == GZ_READ then 0
               else (O_WRONLY ||| O_CREAT ||| (if l.exclusive != 0 then O_EXCL else 0) |||
                     (if s.mode == GZ_WRITE then O_TRUNC else O_APPEND))))
            if fd == -1 then
              let name ← liftM (cstring path)
              let r ← fsOpen name oflag
              liftM (updS l.state fun s => { s with fd := r })
            else do
              if oflag &&& O_NONBLOCK != 0 then fsFcntl fd
              if oflag &&& O_CLOEXEC != 0 then fsFcntl fd
              liftM (updS l.state fun s => { s with fd := fd })
            let s ← liftM (ldS l.state)
            if s.fd == -1 then
              liftM (freeB s.path)
              liftM (freeGzState l.state)
              pure none
            else do
              if s.mode == GZ_APPEND then
                let _ ← fsLseek s.fd 0 SEEK_END
                liftM (updS l.state fun s => { s with mode := GZ_WRITE })
              let s ← liftM (ldS l.state)
              if s.mode == GZ_READ then
                let st ← fsLseek s.fd 0 SEEK_CUR
                liftM (updS l.state fun s => { s with start := st })
                if st == -1 then liftM (updS l.state fun s => { s with start := 0 })
              liftM (gz_reset l.state)
              pure (castFile l.state)) fs0 h0 = .ok res) :
      (do
        let len_ ← liftM (strlenB path)
        let l := { l with len := len_ }
        let p ← liftM (allocB (l.len + 1).toNat)
        liftM (updS l.state fun s => { s with path := p })
        let s ← liftM (ldS l.state)
        if s.path == (Ptr.null : BPtr) then
          liftM (freeGzState l.state)
          pure none
        else do
          let fmt ← liftM (strLit "%s")
          let _ ← liftM (snprintf s.path (l.len + 1) fmt [.str path])
          let s ← liftM (ldS l.state)
          let l := { l with oflag := l.oflag ||| (O_LARGEFILE |||
            (if s.mode == GZ_READ then 0
             else (O_WRONLY ||| O_CREAT ||| (if l.exclusive != 0 then O_EXCL else 0) |||
                   (if s.mode == GZ_WRITE then O_TRUNC else O_APPEND)))) }
          if fd == -1 then
            let r ← (do let name ← liftM (cstring path); fsOpen name l.oflag)
            liftM (updS l.state fun s => { s with fd := r })
          else do
            if l.oflag &&& O_NONBLOCK != 0 then fsFcntl fd
            if l.oflag &&& O_CLOEXEC != 0 then fsFcntl fd
            liftM (updS l.state fun s => { s with fd := fd })
          let s ← liftM (ldS l.state)
          if s.fd == -1 then
            liftM (freeB s.path)
            liftM (freeGzState l.state)
            pure none
          else do
            if s.mode == GZ_APPEND then
              let _ ← fsLseek s.fd 0 SEEK_END
              liftM (updS l.state fun s => { s with mode := GZ_WRITE })
            let s ← liftM (ldS l.state)
            if s.mode == GZ_READ then
              let st ← fsLseek s.fd 0 SEEK_CUR
              liftM (updS l.state fun s => { s with start := st })
              let s ← liftM (ldS l.state)
              if s.start == -1 then liftM (updS l.state fun s => { s with start := 0 })
            liftM (gz_reset l.state)
            pure (castFile l.state)) fs0 h0 = .ok res := by
    refine g_bind_ok_same rfl ht fun len fs1 h1 _ ht1 => ?_
    refine g_bind_ok_same rfl ht1 fun p fs2 h2 _ ht2 => ?_
    rw [g_bind_app] at ht2 ⊢
    cases hu : (liftM (updS l.state fun s => { s with path := p }) : G Unit) fs2 h2 with
    | error e => simp [hu] at ht2
    | ok q =>
      rcases q with ⟨⟨⟨⟩, fs3⟩, h3⟩
      simp only [hu] at ht2 ⊢
      obtain ⟨s₀, hlds⟩ := ldS_after_updS_field l.state (fun s => { s with path := p }) hu
      rw [g_bind_app, hlds]
      dsimp only
      by_cases hp : (p == .null) = true
      · simpa only [hp, ↓reduceIte] using ht2
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at ht2 ⊢
        refine g_bind_ok_same rfl ht2 fun fmt fs4 h4 _ ht4 => ?_
        refine g_bind_ok_same rfl ht4 fun _ fs5 h5 _ ht5 => ?_
        refine g_bind_ok_same rfl ht5 fun s fs6 h6 _ ht6 => ?_
        by_cases hfd : (fd == -1) = true
        · simp only [hfd, ↓reduceIte, g_bind_assoc] at ht6 ⊢
          refine g_bind_ok_same rfl ht6 fun _ fsa ha _ hta => ?_
          refine g_bind_ok_same rfl hta fun _ fsb hb _ htb => ?_
          refine g_bind_ok_same rfl htb fun _ fs7 h7 _ ht7 => ?_
          exact gz_open_post_fd_of_ok l.state fs7 h7 res ht7
        · simp only [hfd, Bool.false_eq_true, ↓reduceIte] at ht6 ⊢
          let oflagVal : Int32 := l.oflag |||
            (O_LARGEFILE |||
              (if s.mode == GZ_READ then 0
               else (O_WRONLY ||| O_CREAT ||| (if l.exclusive != 0 then O_EXCL else 0) |||
                     (if s.mode == GZ_WRITE then O_TRUNC else O_APPEND))))
          by_cases hnb : (oflagVal &&& O_NONBLOCK != 0) = true
          · simp only [oflagVal, hnb, ↓reduceIte] at ht6 ⊢
            refine g_bind_ok_same rfl ht6 fun _ fsa ha _ hta => ?_
            by_cases hclo : (oflagVal &&& O_CLOEXEC != 0) = true
            · simp only [oflagVal, hclo, ↓reduceIte] at hta ⊢
              refine g_bind_ok_same rfl hta fun _ fsb hb _ htb => ?_
              refine g_bind_ok_same rfl htb fun _ fs7 h7 _ ht7 => ?_
              exact gz_open_post_fd_of_ok l.state fs7 h7 res ht7
            · simp only [oflagVal, hclo, Bool.false_eq_true, ↓reduceIte] at hta ⊢
              refine g_bind_ok_same rfl hta fun _ fs7 h7 _ ht7 => ?_
              exact gz_open_post_fd_of_ok l.state fs7 h7 res ht7
          · simp only [oflagVal, hnb, Bool.false_eq_true, ↓reduceIte] at ht6 ⊢
            by_cases hclo : (oflagVal &&& O_CLOEXEC != 0) = true
            · simp only [oflagVal, hclo, ↓reduceIte] at ht6 ⊢
              refine g_bind_ok_same rfl ht6 fun _ fsb hb _ htb => ?_
              refine g_bind_ok_same rfl htb fun _ fs7 h7 _ ht7 => ?_
              exact gz_open_post_fd_of_ok l.state fs7 h7 res ht7
            · simp only [oflagVal, hclo, Bool.false_eq_true, ↓reduceIte] at ht6 ⊢
              refine g_bind_ok_same rfl ht6 fun _ fs7 h7 _ ht7 => ?_
              exact gz_open_post_fd_of_ok l.state fs7 h7 res ht7
  refine g_bind_ok_same rfl hok fun s fs1 h1 _ hok1 => ?_
  by_cases hnone : (s.mode == GZ_NONE) = true
  · simpa only [hnone, ↓reduceIte] using hok1
  · simp only [hnone, Bool.false_eq_true, ↓reduceIte] at hok1 ⊢
    by_cases hmr : (s.mode == GZ_READ) = true
    · simp only [hmr, ↓reduceIte] at hok1 ⊢
      by_cases hd1 : (s.direct == 1) = true
      · simpa only [hd1, ↓reduceIte] using hok1
      · simp only [hd1, Bool.false_eq_true, ↓reduceIte] at hok1 ⊢
        by_cases hd0 : (s.direct == 0) = true
        · simp only [hd0, ↓reduceIte] at hok1 ⊢
          refine g_bind_ok_same rfl hok1 fun _ fs2 h2 _ hok2 => ?_
          exact commonTail fs2 h2 hok2
        · simp only [hd0, Bool.false_eq_true, ↓reduceIte] at hok1 ⊢
          exact commonTail fs1 h1 hok1
    · simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hok1 ⊢
      by_cases hdm : (s.direct == -1) = true
      · simpa only [hdm, ↓reduceIte] using hok1
      · simp only [hdm, Bool.false_eq_true, ↓reduceIte] at hok1 ⊢
        exact commonTail fs1 h1 hok1

private theorem ptr_load_heap {R T : Type} [C.Space Heap R T] {p : C.Ptr R} {h : Heap}
    {v : T} {h' : Heap} (hok : C.Ptr.load p h = .ok (v, h')) : h' = h := by
  unfold C.Ptr.load at hok
  cases p with
  | null => simp at hok
  | ref r off =>
    cases hg : C.Space.get h r with
    | none => simp [hg] at hok
    | some a =>
      by_cases hk : off < a.size <;> simp [hg, hk] at hok
      exact hok.2.symm

private theorem gwhileRet_go_of_gwhile_ok {σ₁ σ₂ ρ : Type}
    (rel : σ₁ → σ₂ → Prop)
    (cond₁ : σ₂ → G (Bool × σ₂)) (body₁ : σ₂ → G σ₂) (after₁ : σ₂ → G ρ)
    (cond₂ : σ₁ → G (Bool × σ₁)) (body₂ : σ₁ → G (C.LoopStep σ₁ ρ)) (after₂ : σ₁ → G ρ)
    (hfalse : ∀ {s₁ s₂ s₂' fs h fs' h' res}, rel s₁ s₂ →
      cond₁ s₂ fs h = .ok (((false, s₂'), fs'), h') →
      after₁ s₂' fs' h' = .ok res →
      ∃ s₁', cond₂ s₁ fs h = .ok (((false, s₁'), fs'), h') ∧ after₂ s₁' fs' h' = .ok res)
    (hstep : ∀ {s₁ s₂ s₂' s₂'' fs h fs' h' fs'' h''}, rel s₁ s₂ →
      cond₁ s₂ fs h = .ok (((true, s₂'), fs'), h') →
      body₁ s₂' fs' h' = .ok ((s₂'', fs''), h'') →
      ∃ s₁', cond₂ s₁ fs h = .ok (((true, s₁'), fs'), h') ∧
        ((∃ s₁'', (body₂ s₁' fs' h' = .ok ((.next s₁'', fs''), h'') ∨
                   body₂ s₁' fs' h' = .ok ((.cont s₁'', fs''), h'')) ∧ rel s₁'' s₂'') ∨
         (∃ r, body₂ s₁' fs' h' = .ok ((.ret r, fs''), h'') ∧
            ∀ m res, (gwhile.go cond₁ body₁ m s₂'' >>= after₁) fs'' h'' = .ok res →
              res = ((r, fs''), h'')))) :
    ∀ n {s₁ s₂ fs h res}, rel s₁ s₂ →
      (gwhile.go cond₁ body₁ n s₂ >>= after₁) fs h = .ok res →
      (gwhileCtrl.go cond₂ body₂ n s₁ >>= fun | .error r => pure r | .ok s => after₂ s) fs h = .ok res := by
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ fs h res _ hok
    rw [g_bind_app, gwhile.go] at hok
    simp at hok
  | succ m ih =>
    intro s₁ s₂ fs h res hrel hok
    rw [g_bind_app, gwhile_go_succ] at hok
    rw [g_bind_app, gwhileCtrl_go_succ]
    rcases hc1 : cond₁ s₂ fs h with e | ⟨⟨⟨c, s₂'⟩, fs'⟩, h'⟩
    · simp [hc1] at hok
    · cases c
      · simp only [hc1] at hok
        obtain ⟨s₁', hc2, ha2⟩ := hfalse hrel hc1 hok
        simp only [hc2]
        exact ha2
      · simp only [hc1] at hok
        rcases hb1 : body₁ s₂' fs' h' with e | ⟨⟨s₂'', fs''⟩, h''⟩
        · simp [hb1] at hok
        · simp only [hb1] at hok
          obtain ⟨s₁', hc2, hbr⟩ := hstep hrel hc1 hb1
          simp only [hc2]
          rcases hbr with ⟨s₁'', hb2, hrel'⟩ | ⟨r, hb2, hret⟩
          · rw [← g_bind_app] at hok
            rcases hb2 with hb2 | hb2 <;> simp only [hb2] <;> rw [← g_bind_app] <;> exact ih hrel' hok
          · simp only [hb2]
            rw [← g_bind_app] at hok
            rw [hret m res hok]
            rfl

private theorem gz_mode_upd_step (state : GzStatePtr) (l : GzOpenLocals) (hlst : l.state = state)
    (f : GzState → GzState) (fsa fsc : Fs) (ha hc : Heap) (ml'' : ModeLoop)
    (hok : (do liftM (Zlib.Gzguts.updS state f)
               let m' ← liftM (Ptr.add l.mode 1)
               pure { mode := m', oflag := l.oflag, exclusive := l.exclusive, done := false } : G ModeLoop)
            fsa ha = .ok ((ml'', fsc), hc)) :
    ∃ s₁'',
      ((do liftM (Zlib.Gzguts.updS l.state f)
           let m' ← liftM (Ptr.add l.mode 1)
           pure (C.LoopStep.next { l with mode := m' }) : G (C.LoopStep GzOpenLocals GzFilePtr))
         fsa ha = .ok ((.next s₁'', fsc), hc)) ∧
      s₁''.state = state ∧ ml'' = { mode := s₁''.mode, oflag := s₁''.oflag, exclusive := s₁''.exclusive, done := false } := by
  subst hlst
  rw [g_bind_app, liftM_m_app] at hok ⊢
  cases hu : Zlib.Gzguts.updS l.state f ha with
  | error e => simp [hu] at hok
  | ok q =>
    rcases q with ⟨⟨⟩, ha1⟩
    simp only [hu, g_bind_app, liftM_m_app] at hok ⊢
    cases hadd : Ptr.add l.mode 1 ha1 with
    | error e => simp [hadd] at hok
    | ok p =>
      rcases p with ⟨m', ha2⟩
      simp only [hadd] at hok ⊢
      cases hok
      exact ⟨{ l with mode := m' }, rfl, rfl, rfl⟩

private theorem gz_mode_pure_step (state : GzStatePtr) (l : GzOpenLocals) (hlst : l.state = state)
    (oflag' exclusive' : Int32) (fsa fsc : Fs) (ha hc : Heap) (ml'' : ModeLoop)
    (hok : (do let m' ← liftM (Ptr.add l.mode 1)
               pure { mode := m', oflag := oflag', exclusive := exclusive', done := false } : G ModeLoop)
            fsa ha = .ok ((ml'', fsc), hc)) :
    ∃ s₁'',
      ((do let m' ← liftM (Ptr.add l.mode 1)
           pure (C.LoopStep.next { l with oflag := oflag', exclusive := exclusive', mode := m' }) :
             G (C.LoopStep GzOpenLocals GzFilePtr))
         fsa ha = .ok ((.next s₁'', fsc), hc)) ∧
      s₁''.state = state ∧ ml'' = { mode := s₁''.mode, oflag := s₁''.oflag, exclusive := s₁''.exclusive, done := false } := by
  rw [g_bind_app, liftM_m_app] at hok ⊢
  cases hadd : Ptr.add l.mode 1 ha with
  | error e => simp [hadd] at hok
  | ok p =>
    rcases p with ⟨m', ha1⟩
    simp only [hadd] at hok ⊢
    cases hok
    exact ⟨{ l with oflag := oflag', exclusive := exclusive', mode := m' }, rfl, hlst, rfl⟩

theorem gz_open_c_of_ok {path : ConstVoidPtr} {fd : Int32} {mode : ConstCStr}
    {fs : Fs} {h : Heap} {res : (GzFilePtr × Fs) × Heap}
    (hok : gz_open path fd mode fs h = .ok res) :
    gz_open_c path fd mode fs h = .ok res := by
  simp only [gz_open_c, gz_open, gdecl, ginline] at hok ⊢
  rw [g_pure_bind]
  by_cases hnull : (path == (Ptr.null : ConstVoidPtr) || mode == (Ptr.null : ConstCStr)) = true
  · simp [hnull] at hok ⊢; exact hok
  · simp only [hnull, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    refine g_bind_ok_same rfl hok fun state fs1 h1 _ hok1 => ?_
    by_cases hnone : state.isNone = true
    · simp [hnone] at hok1 ⊢; exact hok1
    · simp only [hnone, Bool.false_eq_true, ↓reduceIte] at hok1 ⊢
      rw [liftM_updS_updS_bind] at hok1
      rw [liftM_updS_updS_bind, liftM_updS_updS_bind, liftM_updS_updS_bind,
          liftM_updS_updS_bind, liftM_updS_updS_bind, liftM_updS_updS_bind,
          liftM_updS_updS_bind]
      refine g_bind_ok_same rfl hok1 fun _ fs3 h3 _ hok3 => ?_
      change (gwhileRet _ _ _ _) fs3 h3 = .ok res
      change ((gwhile.go _ _ C.fuel _) >>= _) fs3 h3 = .ok res at hok3
      rw [gwhileRet]
      let rel : GzOpenLocals → ModeLoop → Prop := fun l ml =>
        l.state = state ∧ ml = { mode := l.mode, oflag := l.oflag, exclusive := l.exclusive, done := false }
      refine gwhileRet_go_of_gwhile_ok rel _ _ _ _ _ _ ?_ ?_ C.fuel
          ⟨rfl, rfl⟩ hok3
      · intro l ml ml' fsa ha fsb hb res0 hrel hc1 ha1
        rcases hrel with ⟨hlst, rfl⟩
        rw [g_bind_app, liftM_m_app] at hc1
        cases hld : C.load8 l.mode ha with
        | error e => simp [hld] at hc1
        | ok p =>
          rcases p with ⟨b0, ha'⟩
          simp only [hld, Bool.not_false, Bool.and_true] at hc1
          have hb0 : (b0 != 0) = false := by
            by_cases ht : (b0 != 0) = true
            · simp [pure, StateT.pure, ht] at hc1
            · exact Bool.eq_false_iff.mpr ht
          simp only [hb0, pure, StateT.pure] at hc1
          cases hc1
          refine ⟨l, ?_, ?_⟩
          · rw [g_bind_app, liftM_m_app, hld]
            simp only [hb0]; rfl
          · simp only [Bool.false_eq_true, ↓reduceIte] at ha1
            exact gz_open_after_loop_of_ok path fd state l hlst fsa hb res0 ha1
      · intro l ml ml' ml'' fsa ha fsb hb fsc hc hrel hc1 hb1
        rcases hrel with ⟨hlst, rfl⟩
        rw [g_bind_app, liftM_m_app] at hc1
        cases hld : C.load8 l.mode ha with
        | error e => simp [hld] at hc1
        | ok p =>
          rcases p with ⟨b0, ha'⟩
          simp only [hld, Bool.not_false, Bool.and_true] at hc1
          have hb0 : (b0 != 0) = true := by
            by_cases ht : (b0 != 0) = true
            · exact ht
            · simp [pure, StateT.pure, ht] at hc1
          simp only [hb0, pure, StateT.pure] at hc1
          cases hc1
          refine ⟨l, ?_, ?_⟩
          · rw [g_bind_app, liftM_m_app, hld]
            simp only [hb0]; rfl
          · rw [g_bind_app, liftM_m_app] at hb1
            rw [g_bind_assoc, g_bind_app, liftM_m_app]
            cases hld2 : C.load8 l.mode hb with
            | error e => simp [hld2] at hb1
            | ok q =>
              rcases q with ⟨b1, ha''⟩
              have hhb : ha'' = hb := ptr_load_heap hld2
              subst ha''
              simp only [hld2, g_pure_bind] at hb1 ⊢
              generalize b1.toInt8.toInt32 = c32 at hb1 ⊢
              by_cases h0 : (c32 ≥ 48 && c32 ≤ 57) = true
              · simp only [h0, ↓reduceIte, Bool.not_false] at hb1 ⊢
                obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
              · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                by_cases h1 : (c32 == 114) = true
                · simp only [h1, ↓reduceIte, Bool.not_false] at hb1 ⊢
                  obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                  exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                  by_cases h2 : (c32 == 119) = true
                  · simp only [h2, ↓reduceIte, Bool.not_false] at hb1 ⊢
                    obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                    exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                  · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                    by_cases h3 : (c32 == 97) = true
                    · simp only [h3, ↓reduceIte, Bool.not_false] at hb1 ⊢
                      obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                      exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                    · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                      by_cases h4 : (c32 == 43) = true
                      · simp only [h4, ↓reduceIte, Bool.not_true] at hb1 ⊢
                        rw [g_bind_app, liftM_m_app] at hb1 ⊢
                        cases hfree : C.freeGzState state hb with
                        | error e => simp [hfree] at hb1
                        | ok pf =>
                          rcases pf with ⟨⟨⟩, ha3⟩
                          simp only [hlst, hfree] at hb1 ⊢
                          cases hb1
                          refine Or.inr ⟨none, rfl, ?_⟩
                          intro m0 res0 hm0
                          cases m0 with
                          | zero => rw [g_bind_app, gwhile.go] at hm0; simp at hm0
                          | succ k0 =>
                            rw [g_bind_app, gwhile_go_succ, g_bind_app, liftM_m_app] at hm0
                            rw [load8_freeGzState state hfree l.mode, hld2] at hm0
                            simp only [Bool.not_true, Bool.and_false] at hm0
                            exact Except.ok.inj hm0 |>.symm
                      · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                        by_cases h5 : (c32 == 98) = true
                        · simp only [h5, ↓reduceIte, Bool.not_false] at hb1 ⊢
                          obtain ⟨s₁'', hb2, hs⟩ := gz_mode_pure_step state l hlst l.oflag l.exclusive fsa fsc hb hc ml'' hb1
                          exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                        · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                          by_cases h6 : (c32 == 101) = true
                          · simp only [h6, ↓reduceIte, Bool.not_false] at hb1 ⊢
                            obtain ⟨s₁'', hb2, hs⟩ := gz_mode_pure_step state l hlst (l.oflag ||| O_CLOEXEC) l.exclusive fsa fsc hb hc ml'' hb1
                            exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                          · simp only [h6, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                            by_cases h7 : (c32 == 120) = true
                            · simp only [h7, ↓reduceIte, Bool.not_false] at hb1 ⊢
                              obtain ⟨s₁'', hb2, hs⟩ := gz_mode_pure_step state l hlst l.oflag 1 fsa fsc hb hc ml'' hb1
                              exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                            · simp only [h7, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                              by_cases h8 : (c32 == 102) = true
                              · simp only [h8, ↓reduceIte, Bool.not_false] at hb1 ⊢
                                obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                                exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                              · simp only [h8, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                                by_cases h9 : (c32 == 104) = true
                                · simp only [h9, ↓reduceIte, Bool.not_false] at hb1 ⊢
                                  obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                                  exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                                · simp only [h9, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                                  by_cases h10 : (c32 == 82) = true
                                  · simp only [h10, ↓reduceIte, Bool.not_false] at hb1 ⊢
                                    obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                                    exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                                  · simp only [h10, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                                    by_cases h11 : (c32 == 70) = true
                                    · simp only [h11, ↓reduceIte, Bool.not_false] at hb1 ⊢
                                      obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                                      exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                                    · simp only [h11, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                                      by_cases h12 : (c32 == 71) = true
                                      · simp only [h12, ↓reduceIte, Bool.not_false] at hb1 ⊢
                                        obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                                        exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                                      · simp only [h12, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                                        by_cases h13 : (c32 == 78) = true
                                        · simp only [h13, ↓reduceIte, Bool.not_false] at hb1 ⊢
                                          obtain ⟨s₁'', hb2, hs⟩ := gz_mode_pure_step state l hlst (l.oflag ||| O_NONBLOCK) l.exclusive fsa fsc hb hc ml'' hb1
                                          exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                                        · simp only [h13, Bool.false_eq_true, ↓reduceIte] at hb1 ⊢
                                          by_cases h14 : (c32 == 84) = true
                                          · simp only [h14, ↓reduceIte, Bool.not_false] at hb1 ⊢
                                            obtain ⟨s₁'', hb2, hs⟩ := gz_mode_upd_step state l hlst _ fsa fsc hb hc ml'' hb1
                                            exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩
                                          · simp only [h14, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hb1 ⊢
                                            obtain ⟨s₁'', hb2, hs⟩ := gz_mode_pure_step state l hlst l.oflag l.exclusive fsa fsc hb hc ml'' hb1
                                            exact Or.inl ⟨s₁'', Or.inl hb2, hs⟩

theorem gzopen_c_of_ok {path mode : ConstCStr} {fs : Fs} {h : Heap}
    {res : (GzFilePtr × Fs) × Heap}
    (hok : gzopen path mode fs h = .ok res) :
    gzopen_c path mode fs h = .ok res :=
  gz_open_c_of_ok hok

theorem gzopen_c_safety : ZlibF.Spec.Public.Goal.gzopen_c_safety := by
  intro h fs path mode name flags hfresh huniq hlib hfit hfs hp hm
  rcases ZlibF.Spec.Public.GzCallSafetyProof.gzopen_safety h fs path mode name flags
      hfresh huniq hlib hfit hfs hp hm with ⟨result, fs', after, hok, hpost⟩
  exact ⟨result, fs', after, gzopen_c_of_ok hok, hpost⟩

end Gzlib

section Inffast
open Zlib.Inffast

theorem fast_c_safe : Zlib.Inffast.Spec.Goal.fast_c_safe := by
  intro e
  rcases Zlib.Inffast.Proofs.inflate_fast_safe e with ⟨after, hok, hpost⟩
  exact ⟨after, inflate_fast_c_of_ok e.strm e.start hok, hpost⟩

end Inffast

end ZlibF.Proof.StandaloneCAbi
