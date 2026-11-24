import ZlibF.Proof.StandaloneCAbiControl
import ZlibF.Proof.«inffast.c.final»

/-! Agreement of the C-shaped fast decoder with the safety model on every returning execution. -/
namespace ZlibF.Proof.StandaloneCAbi
open C Control

private theorem ptr_add_heap {R T : Type} [C.Space Heap R T] {p : C.Ptr R} {k : Int}
    {h : Heap} {p' : C.Ptr R} {h' : Heap}
    (hok : C.Ptr.add p k h = .ok (p', h')) : h' = h := by
  unfold C.Ptr.add at hok
  by_cases hk : k = 0
  · subst hk; simp at hok; exact hok.2.symm
  · simp only [hk, ↓reduceIte] at hok
    cases p with
    | null => simp at hok
    | ref r off =>
      cases hg : C.Space.get h r with
      | none => simp [hg] at hok
      | some a =>
        by_cases hbd : 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int)
        · simp [hg, hbd] at hok; exact hok.2.symm
        · simp [hg, hbd] at hok

private theorem ptr_diff_heap {R T : Type} [DecidableEq R] [C.Space Heap R T] {p q : C.Ptr R}
    {h : Heap} {d : Int64} {h' : Heap}
    (hok : C.Ptr.diff p q h = .ok (d, h')) : h' = h := by
  unfold C.Ptr.diff at hok
  cases p with
  | null =>
    cases q with
    | null => simp at hok; exact hok.2.symm
    | ref _ _ => simp at hok
  | ref r1 o1 =>
    cases q with
    | null => simp at hok
    | ref r2 o2 =>
      by_cases hr : r1 = r2
      · subst hr
        cases hg : C.Space.get h r1 with
        | none => simp [hg] at hok
        | some a =>
          by_cases hb1 : o1 ≤ a.size ∧ o2 ≤ a.size
          · simp only [hg, hb1, ↓reduceIte] at hok
            by_cases hb2 : (-9223372036854775808 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 9223372036854775808
            · simp [hb2] at hok; exact hok.2.symm
            · simp [hb2] at hok
          · simp [hg, hb1] at hok
      · simp [hr] at hok

private theorem ptr_lt_heap {R T : Type} [DecidableEq R] [C.Space Heap R T] {p q : C.Ptr R}
    {h : Heap} {b : Bool} {h' : Heap}
    (hok : C.Ptr.lt p q h = .ok (b, h')) : h' = h := by
  unfold C.Ptr.lt at hok
  cases p with
  | null => cases q <;> simp at hok
  | ref r1 o1 =>
    cases q with
    | null => simp at hok
    | ref r2 o2 =>
      by_cases hr : r1 = r2
      · subst hr
        cases hg : C.Space.get h r1 with
        | none => simp [hg] at hok
        | some a =>
          by_cases hbd : o1 ≤ a.size ∧ o2 ≤ a.size
          · simp [hg, hbd] at hok; exact hok.2.symm
          · simp [hg, hbd] at hok
      · simp [hr] at hok

private theorem ptr_le_heap {R T : Type} [DecidableEq R] [C.Space Heap R T] {p q : C.Ptr R}
    {h : Heap} {b : Bool} {h' : Heap}
    (hok : C.Ptr.le p q h = .ok (b, h')) : h' = h := by
  unfold C.Ptr.le at hok
  rw [m_bind_app] at hok
  cases hlt : C.Ptr.lt q p h with
  | error e => simp [hlt] at hok
  | ok p1 =>
    rcases p1 with ⟨b1, h1⟩
    have hh1 := ptr_lt_heap hlt
    subst hh1
    simp [hlt] at hok
    exact hok.2.symm

private theorem zstream_put_spaceB (r : ZStreamRef) (h : Heap) (v : ZStream) (b : BRef) :
    (Space.get (ZStreamRef.put h r v) b : Option (Array UInt8)) = Space.get h b := by
  cases r with
  | tab i =>
    dsimp only [ZStreamRef.put]
    cases h.streams i <;> cases b <;> rfl
  | in_gzstate_strm i =>
    dsimp only [ZStreamRef.put]
    cases h.gzstates i <;> cases b <;> rfl

private theorem ptr_lt_zstream_put (r : ZStreamRef) (v : ZStream) (p q : BPtr) {h : Heap} {b : Bool}
    (hok : C.Ptr.lt p q h = .ok (b, h)) :
    C.Ptr.lt p q (ZStreamRef.put h r v) = .ok (b, ZStreamRef.put h r v) := by
  unfold C.Ptr.lt at hok ⊢
  cases p with
  | null => cases q <;> simp at hok
  | ref r1 o1 =>
    cases q with
    | null => simp at hok
    | ref r2 o2 =>
      by_cases hr : r1 = r2
      · subst hr
        have hsp := zstream_put_spaceB r h v r1
        dsimp only at hok ⊢
        simp only [↓reduceIte] at hok ⊢
        rw [hsp]
        cases hg : Space.get h r1 with
        | none => simp [hg] at hok
        | some a =>
          simp only [hg] at hok ⊢
          by_cases hbd : o1 ≤ a.size ∧ o2 ≤ a.size
          · simp only [hbd] at hok ⊢
            cases hok; rfl
          · simp [hbd] at hok
      · simp [hr] at hok

private theorem ptr_diff_zstream_put (r : ZStreamRef) (v : ZStream) (p q : BPtr) {h : Heap} {d : Int64}
    (hok : C.Ptr.diff p q h = .ok (d, h)) :
    C.Ptr.diff p q (ZStreamRef.put h r v) = .ok (d, ZStreamRef.put h r v) := by
  unfold C.Ptr.diff at hok ⊢
  cases p with
  | null =>
    cases q with
    | null => cases hok; rfl
    | ref _ _ => simp at hok
  | ref r1 o1 =>
    cases q with
    | null => simp at hok
    | ref r2 o2 =>
      by_cases hr : r1 = r2
      · subst hr
        have hsp := zstream_put_spaceB r h v r1
        dsimp only at hok ⊢
        simp only [↓reduceIte] at hok ⊢
        rw [hsp]
        cases hg : Space.get h r1 with
        | none => simp [hg] at hok
        | some a =>
          simp only [hg] at hok ⊢
          by_cases hb1 : o1 ≤ a.size ∧ o2 ≤ a.size
          · simp only [hb1] at hok ⊢
            by_cases hb2 : (-9223372036854775808 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 9223372036854775808
            · simp [hb2] at hok ⊢; exact hok
            · simp [hb2] at hok
          · simp [hb1] at hok
      · simp [hr] at hok

private theorem clabel_go_succ {σ α : Type} (body : σ → M (GotoStep σ α))
    (n : Nat) (s : σ) (h : Heap) :
    C.clabel.go body (n + 1) s h =
      match body s h with
      | .error e => .error e
      | .ok (.goto s', h') => C.clabel.go body n s' h'
      | .ok (.done a, h') => .ok (a, h') := by
  rw [C.clabel.go, bind_app]
  rcases body s h with e | ⟨st, h'⟩
  · rfl
  · cases st <;> rfl

private theorem cwhileCtrl_go_succ {σ ρ : Type} (cond : σ → M (Bool × σ))
    (body : σ → M (LoopStep σ ρ)) (n : Nat) (s : σ) (h : Heap) :
    C.cwhileCtrl.go cond body (n + 1) s h =
      match cond s h with
      | .error e => .error e
      | .ok ((false, s1), h1) => .ok (.ok s1, h1)
      | .ok ((true, s1), h1) =>
        match body s1 h1 with
        | .error e => .error e
        | .ok (.next s2, h2) | .ok (.cont s2, h2) => C.cwhileCtrl.go cond body n s2 h2
        | .ok (.brk s2, h2) => .ok (.ok s2, h2)
        | .ok (.ret r, h2) => .ok (.error r, h2) := by
  rw [C.cwhileCtrl.go, bind_app]
  rcases cond s h with e | ⟨⟨c, s1⟩, h1'⟩
  · rfl
  · cases c
    · rfl
    · simp only [ite_true, bind_app]
      rcases body s1 h1' with e | ⟨st, h2'⟩
      · rfl
      · cases st <;> rfl

private theorem cdoWhileCtrl_go_succ {σ ρ : Type} (body : σ → M (LoopStep σ ρ))
    (cond : σ → M (Bool × σ)) (n : Nat) (s : σ) (h : Heap) :
    C.cdoWhileCtrl.go body cond (n + 1) s h =
      match body s h with
      | .error e => .error e
      | .ok (.brk s', h') => .ok (.ok s', h')
      | .ok (.ret r, h') => .ok (.error r, h')
      | .ok (.next s', h') | .ok (.cont s', h') =>
        match cond s' h' with
        | .error e => .error e
        | .ok ((true, s''), h'') => C.cdoWhileCtrl.go body cond n s'' h''
        | .ok ((false, s''), h'') => .ok (.ok s'', h'') := by
  rw [C.cdoWhileCtrl.go, bind_app]
  rcases body s h with e | ⟨st, h'⟩
  · rfl
  · cases st with
    | brk => rfl
    | ret => rfl
    | next s' =>
      dsimp only; rw [bind_app]
      rcases cond s' h' with e | ⟨⟨c, s''⟩, h''⟩
      · rfl
      · cases c <;> rfl
    | cont s' =>
      dsimp only; rw [bind_app]
      rcases cond s' h' with e | ⟨⟨c, s''⟩, h''⟩
      · rfl
      · cases c <;> rfl

private theorem cforEver_go_succ {σ ρ : Type} (body : σ → M (LoopStep σ ρ))
    (n : Nat) (s : σ) (h : Heap) :
    C.cforEver.go body (n + 1) s h =
      match body s h with
      | .error e => .error e
      | .ok (.next s', h') | .ok (.cont s', h') => C.cforEver.go body n s' h'
      | .ok (.brk s', h') => .ok (.ok s', h')
      | .ok (.ret r, h') => .ok (.error r, h') := by
  rw [C.cforEver.go, bind_app]
  rcases body s h with e | ⟨st, h'⟩
  · rfl
  · cases st <;> rfl

private theorem cwhile_go_rel_ok {σ₁ σ₂ β : Type} (rel : σ₁ → σ₂ → Prop)
    (c₁ : σ₁ → M (Bool × σ₁)) (b₁ : σ₁ → M σ₁) (k₁ : σ₁ → M β)
    (c₂ : σ₂ → M (Bool × σ₂)) (b₂ : σ₂ → M σ₂) (k₂ : σ₂ → M β)
    (hstep : ∀ {s₁ s₂ b s₂' h h1}, rel s₁ s₂ → c₂ s₂ h = .ok ((b, s₂'), h1) →
      ∃ s₁', c₁ s₁ h = .ok ((b, s₁'), h1) ∧
        (b = false → ∀ res, k₂ s₂' h1 = .ok res → k₁ s₁' h1 = .ok res) ∧
        (b = true → ∀ s₂'' h2, b₂ s₂' h1 = .ok (s₂'', h2) →
          ∃ s₁'', b₁ s₁' h1 = .ok (s₁'', h2) ∧ rel s₁'' s₂'')) :
    ∀ n {s₁ s₂ h res}, rel s₁ s₂ →
      (C.cwhile.go c₂ b₂ n s₂ >>= k₂) h = .ok res →
      (C.cwhile.go c₁ b₁ n s₁ >>= k₁) h = .ok res := by
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ h res _ hok
    rw [m_bind_app, C.cwhile.go] at hok; simp at hok
  | succ m ih =>
    intro s₁ s₂ h res hrel hok
    rw [m_bind_app, cwhile_go_succ] at hok
    rw [m_bind_app, cwhile_go_succ]
    cases hc2 : c₂ s₂ h with
    | error e => simp [hc2] at hok
    | ok p1 =>
      rcases p1 with ⟨⟨b, s₂'⟩, h1⟩
      simp only [hc2] at hok
      obtain ⟨s₁', hc1, hfalse, htrue⟩ := hstep hrel hc2
      simp only [hc1]
      cases b
      · exact hfalse rfl res hok
      · cases hb2 : b₂ s₂' h1 with
        | error e => simp [hb2] at hok
        | ok p2 =>
          rcases p2 with ⟨s₂'', h2⟩
          simp only [hb2] at hok
          obtain ⟨s₁'', hb1, hrel'⟩ := htrue rfl s₂'' h2 hb2
          simp only [hb1]
          rw [← m_bind_app] at hok ⊢
          exact ih hrel' hok

private theorem cdoWhile_go_rel_eq {σ₁ σ₂ β : Type} (rel : σ₁ → σ₂ → Prop)
    (upd : σ₁ → σ₂ → σ₁)
    (b₁ : σ₁ → M σ₁) (c₁ : σ₁ → M (Bool × σ₁)) (k₁ : σ₁ → M β)
    (b₂ : σ₂ → M σ₂) (c₂ : σ₂ → M (Bool × σ₂)) (k₂ : σ₂ → M β)
    (hupd : ∀ s₁ s₂ s₂', rel s₁ s₂ → rel (upd s₁ s₂') s₂')
    (hb : ∀ s₁ s₂ h, rel s₁ s₂ → b₁ s₁ h = (b₂ s₂ >>= fun s' => pure (upd s₁ s')) h)
    (hc : ∀ s₁ s₂ sb₂ h, rel s₁ s₂ →
      c₁ (upd s₁ sb₂) h = (c₂ sb₂ >>= fun r => pure (r.1, upd s₁ r.2)) h)
    (hk : ∀ s₁ s₂ h, rel s₁ s₂ → k₁ s₁ h = k₂ s₂ h) :
    ∀ n s₁ s₂ h, rel s₁ s₂ →
      (C.cdoWhile.go b₁ c₁ n s₁ >>= k₁) h = (C.cdoWhile.go b₂ c₂ n s₂ >>= k₂) h := by
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ h _
    rw [m_bind_app, C.cdoWhile.go, m_bind_app, C.cdoWhile.go]
  | succ m ih =>
    intro s₁ s₂ h hrel
    rw [m_bind_app, cdoWhile_go_succ, m_bind_app, cdoWhile_go_succ]
    rw [hb s₁ s₂ h hrel, m_bind_app]
    cases hb2 : b₂ s₂ h with
    | error e => rfl
    | ok p1 =>
      rcases p1 with ⟨sb₂, h1⟩
      simp only [pure_app]
      rw [hc s₁ s₂ sb₂ h1 hrel, m_bind_app]
      cases hc2 : c₂ sb₂ h1 with
      | error e => rfl
      | ok p2 =>
        rcases p2 with ⟨⟨condB, s₂'⟩, h2⟩
        simp only [pure_app]
        cases condB
        · exact hk (upd s₁ s₂') s₂' h2 (hupd s₁ s₂ s₂' hrel)
        · exact ih (upd s₁ s₂') s₂' h2 (hupd s₁ s₂ s₂' hrel)

private theorem cdoWhile_go_rel_ok {σ₁ σ₂ β : Type} (rel : σ₁ → σ₂ → Prop)
    (b₁ : σ₁ → M σ₁) (c₁ : σ₁ → M (Bool × σ₁)) (k₁ : σ₁ → M β)
    (b₂ : σ₂ → M σ₂) (c₂ : σ₂ → M (Bool × σ₂)) (k₂ : σ₂ → M β)
    (hstep : ∀ {s₁ s₂ sb₂ h h1 condB s₂' h2}, rel s₁ s₂ →
      b₂ s₂ h = .ok (sb₂, h1) → c₂ sb₂ h1 = .ok ((condB, s₂'), h2) →
      ∃ sb₁ s₁', b₁ s₁ h = .ok (sb₁, h1) ∧ c₁ sb₁ h1 = .ok ((condB, s₁'), h2) ∧
        (condB = false → ∀ res, k₂ s₂' h2 = .ok res → k₁ s₁' h2 = .ok res) ∧
        (condB = true → rel s₁' s₂')) :
    ∀ n {s₁ s₂ h res}, rel s₁ s₂ →
      (C.cdoWhile.go b₂ c₂ n s₂ >>= k₂) h = .ok res →
      (C.cdoWhile.go b₁ c₁ n s₁ >>= k₁) h = .ok res := by
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ h res _ hok
    rw [m_bind_app, C.cdoWhile.go] at hok; simp at hok
  | succ m ih =>
    intro s₁ s₂ h res hrel hok
    rw [m_bind_app, cdoWhile_go_succ] at hok
    rw [m_bind_app, cdoWhile_go_succ]
    cases hb2 : b₂ s₂ h with
    | error e => simp [hb2] at hok
    | ok p1 =>
      rcases p1 with ⟨sb₂, h1⟩
      simp only [hb2] at hok
      cases hc2 : c₂ sb₂ h1 with
      | error e => simp [hc2] at hok
      | ok p2 =>
        rcases p2 with ⟨⟨condB, s₂'⟩, h2⟩
        simp only [hc2] at hok
        obtain ⟨sb₁, s₁', hb1, hc1, hfalse, htrue⟩ := hstep hrel hb2 hc2
        simp only [hb1, hc1]
        cases condB
        · exact hfalse rfl res hok
        · rw [← m_bind_app] at hok ⊢
          exact ih (htrue rfl) hok

private theorem m_bind_bind_ok_same {α β₁ β₂ γ : Type} {m₁ m₂ : M α}
    {f₁ : α → M β₁} {f₂ : α → M β₂} {k₁ : β₁ → M γ} {k₂ : β₂ → M γ}
    {h : Heap} {res : γ × Heap}
    (hm : m₁ h = m₂ h)
    (hok : ((m₂ >>= f₂) >>= k₂) h = .ok res)
    (hk : ∀ a h₁, m₂ h = .ok (a, h₁) → (f₂ a >>= k₂) h₁ = .ok res → (f₁ a >>= k₁) h₁ = .ok res) :
    ((m₁ >>= f₁) >>= k₁) h = .ok res := by
  rw [m_bind_assoc] at hok ⊢
  exact m_bind_ok_same hm hok hk

private theorem cwhile_go_cps_ok {σ₁ σ₂ β : Type} (rel : σ₁ → σ₂ → Prop)
    (c₁ : σ₁ → M (Bool × σ₁)) (b₁ : σ₁ → M σ₁) (k₁ : σ₁ → M β)
    (c₂ : σ₂ → M (Bool × σ₂)) (b₂ : σ₂ → M σ₂) (k₂ : σ₂ → M β)
    (res : β × Heap)
    (hstep : ∀ {s₁ s₂ h} {cont₁ : σ₁ → M β} {cont₂ : σ₂ → M β},
      rel s₁ s₂ →
      (∀ s₁' s₂' h', rel s₁' s₂' → cont₂ s₂' h' = .ok res → cont₁ s₁' h' = .ok res) →
      (c₂ s₂ >>= fun (b, s₂') => if b then (b₂ s₂' >>= cont₂) else k₂ s₂') h = .ok res →
      (c₁ s₁ >>= fun (b, s₁') => if b then (b₁ s₁' >>= cont₁) else k₁ s₁') h = .ok res) :
    ∀ n {s₁ s₂ h}, rel s₁ s₂ →
      (C.cwhile.go c₂ b₂ n s₂ >>= k₂) h = .ok res →
      (C.cwhile.go c₁ b₁ n s₁ >>= k₁) h = .ok res := by
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ h _ hok
    rw [m_bind_app, C.cwhile.go] at hok; simp at hok
  | succ m ih =>
    intro s₁ s₂ h hrel hok
    have hok' : (c₂ s₂ >>= fun (b, s₂') =>
        if b then (b₂ s₂' >>= fun s₂'' => C.cwhile.go c₂ b₂ m s₂'' >>= k₂) else k₂ s₂') h = .ok res := by
      rw [m_bind_app, cwhile_go_succ] at hok
      rw [m_bind_app]
      cases hc2 : c₂ s₂ h with
      | error e => simp [hc2] at hok
      | ok p1 =>
        rcases p1 with ⟨⟨cb, s2'⟩, h1⟩
        simp only [hc2] at hok ⊢
        cases cb
        · exact hok
        · simp only [↓reduceIte, m_bind_app]
          dsimp only at hok
          cases hb2 : b₂ s2' h1 with
          | error e => simp [hb2] at hok
          | ok p2 => simp [hb2] at hok ⊢; exact hok
    have hres := hstep (cont₁ := fun s₁' => C.cwhile.go c₁ b₁ m s₁' >>= k₁)
      (cont₂ := fun s₂' => C.cwhile.go c₂ b₂ m s₂' >>= k₂) hrel (fun s₁' s₂' h' hr' hk' => ih hr' hk') hok'
    rw [m_bind_app, cwhile_go_succ]
    rw [m_bind_app] at hres
    cases hc1 : c₁ s₁ h with
    | error e => simp [hc1] at hres
    | ok p1 =>
      rcases p1 with ⟨⟨cb, s1'⟩, h1⟩
      simp only [hc1] at hres ⊢
      cases cb
      · exact hres
      · simp only [ite_true, m_bind_app] at hres ⊢
        cases hb1 : b₁ s1' h1 with
        | error e => simp [hb1] at hres
        | ok p2 => simp only [hb1] at hres ⊢; exact hres

private theorem cdoWhile_go_cps_ok {σ₁ σ₂ β : Type} (rel : σ₁ → σ₂ → Prop)
    (b₁ : σ₁ → M σ₁) (c₁ : σ₁ → M (Bool × σ₁)) (k₁ : σ₁ → M β)
    (b₂ : σ₂ → M σ₂) (c₂ : σ₂ → M (Bool × σ₂)) (k₂ : σ₂ → M β)
    (res : β × Heap)
    (hstep : ∀ {s₁ s₂ h} {cont₁ : σ₁ → M β} {cont₂ : σ₂ → M β},
      rel s₁ s₂ →
      (∀ s₁' s₂' h', rel s₁' s₂' → cont₂ s₂' h' = .ok res → cont₁ s₁' h' = .ok res) →
      (b₂ s₂ >>= fun sb₂ => c₂ sb₂ >>= fun (b, s₂') =>
        if b then cont₂ s₂' else k₂ s₂') h = .ok res →
      (b₁ s₁ >>= fun sb₁ => c₁ sb₁ >>= fun (b, s₁') =>
        if b then cont₁ s₁' else k₁ s₁') h = .ok res) :
    ∀ n {s₁ s₂ h}, rel s₁ s₂ →
      (C.cdoWhile.go b₂ c₂ n s₂ >>= k₂) h = .ok res →
      (C.cdoWhile.go b₁ c₁ n s₁ >>= k₁) h = .ok res := by
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ h _ hok
    rw [m_bind_app, C.cdoWhile.go] at hok; simp at hok
  | succ m ih =>
    intro s₁ s₂ h hrel hok
    have hok' : (b₂ s₂ >>= fun sb₂ => c₂ sb₂ >>= fun (b, s₂') =>
        if b then (C.cdoWhile.go b₂ c₂ m s₂' >>= k₂) else k₂ s₂') h = .ok res := by
      rw [m_bind_app, cdoWhile_go_succ] at hok
      rw [m_bind_app]
      cases hb2 : b₂ s₂ h with
      | error e => simp [hb2] at hok
      | ok p1 =>
        rcases p1 with ⟨sb2, h1⟩
        simp only [hb2, m_bind_app] at hok ⊢
        cases hc2 : c₂ sb2 h1 with
        | error e => simp [hc2] at hok
        | ok p2 =>
          rcases p2 with ⟨⟨cb, s2'⟩, h2⟩
          simp only [hc2] at hok ⊢
          cases cb <;> exact hok
    have hres := hstep (cont₁ := fun s₁' => C.cdoWhile.go b₁ c₁ m s₁' >>= k₁)
      (cont₂ := fun s₂' => C.cdoWhile.go b₂ c₂ m s₂' >>= k₂) hrel (fun s₁' s₂' h' hr' hk' => ih hr' hk') hok'
    rw [m_bind_app, cdoWhile_go_succ]
    rw [m_bind_app] at hres
    cases hb1 : b₁ s₁ h with
    | error e => simp [hb1] at hres
    | ok p1 =>
      rcases p1 with ⟨sb1, h1⟩
      simp only [hb1, m_bind_app] at hres ⊢
      cases hc1 : c₁ sb1 h1 with
      | error e => simp [hc1] at hres
      | ok p2 =>
        rcases p2 with ⟨⟨cb, s1'⟩, h2⟩
        simp only [hc1] at hres ⊢
        cases cb <;> exact hres

private theorem clabel_of_cdoWhile_ok {σ₁ σ₂ α β : Type}
    (rel : σ₁ → σ₂ → Prop)
    (body₁ : σ₁ → M (GotoStep σ₁ α)) (k₁ : α → M β)
    (body₂ : σ₂ → M σ₂) (cond₂ : σ₂ → M (Bool × σ₂)) (k₂ : σ₂ → M β)
    (res : β × Heap)
    (hstep : ∀ {s₁ s₂ h} {cont₁ : σ₁ → M β} {cont₂ : σ₂ → M β},
      rel s₁ s₂ →
      (∀ s₁' s₂' h', rel s₁' s₂' → cont₂ s₂' h' = .ok res → cont₁ s₁' h' = .ok res) →
      (body₂ s₂ >>= fun sb₂ => cond₂ sb₂ >>= fun (b, s₂') =>
        if b then cont₂ s₂' else k₂ s₂') h = .ok res →
      (body₁ s₁ >>= fun | .goto s₁' => cont₁ s₁' | .done a => k₁ a) h = .ok res) :
    ∀ n {s₁ s₂ h}, rel s₁ s₂ →
      (C.cdoWhile.go body₂ cond₂ n s₂ >>= k₂) h = .ok res →
      (C.clabel.go body₁ n s₁ >>= k₁) h = .ok res := by
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ h _ hok
    rw [m_bind_app, C.cdoWhile.go] at hok; simp at hok
  | succ m ih =>
    intro s₁ s₂ h hrel hok
    have hok' : (body₂ s₂ >>= fun sb₂ => cond₂ sb₂ >>= fun (b, s₂') =>
        if b then (C.cdoWhile.go body₂ cond₂ m s₂' >>= k₂) else k₂ s₂') h = .ok res := by
      rw [m_bind_app, cdoWhile_go_succ] at hok
      rw [m_bind_app]
      cases hb2 : body₂ s₂ h with
      | error e => simp [hb2] at hok
      | ok p1 =>
        rcases p1 with ⟨sb2, h1⟩
        simp only [hb2, m_bind_app] at hok ⊢
        cases hc2 : cond₂ sb2 h1 with
        | error e => simp [hc2] at hok
        | ok p2 =>
          rcases p2 with ⟨⟨cb, s2'⟩, h2⟩
          simp only [hc2] at hok ⊢
          cases cb <;> exact hok
    have hres := hstep (cont₁ := fun s₁' => C.clabel.go body₁ m s₁' >>= k₁)
      (cont₂ := fun s₂' => C.cdoWhile.go body₂ cond₂ m s₂' >>= k₂) hrel (fun s₁' s₂' h' hr' hk' => ih hr' hk') hok'
    rw [m_bind_app, clabel_go_succ]
    rw [m_bind_app] at hres
    cases hb1 : body₁ s₁ h with
    | error e => simp [hb1] at hres
    | ok p1 =>
      rcases p1 with ⟨st, h1⟩
      simp only [hb1] at hres ⊢
      cases st <;> exact hres

private theorem cdoWhileBrk_of_cdoWhile_ok {σ₁ σ₂ β : Type}
    (rel : σ₁ → σ₂ → Prop)
    (body₁ : σ₁ → M (LoopStep σ₁ Empty)) (cond₁ : σ₁ → M (Bool × σ₁)) (k₁ : σ₁ → M β)
    (body₂ : σ₂ → M σ₂) (cond₂ : σ₂ → M (Bool × σ₂)) (k₂ : σ₂ → M β)
    (res : β × Heap)
    (hstep : ∀ {s₁ s₂ h} {cont₁ : σ₁ → M β} {cont₂ : σ₂ → M β},
      rel s₁ s₂ →
      (∀ s₁' s₂' h', rel s₁' s₂' → cont₂ s₂' h' = .ok res → cont₁ s₁' h' = .ok res) →
      (body₂ s₂ >>= fun sb₂ => cond₂ sb₂ >>= fun x =>
        if x.1 then cont₂ x.2 else k₂ x.2) h = .ok res →
      (body₁ s₁ >>= fun
        | .brk s₁' => k₁ s₁'
        | .ret e => nomatch e
        | .next s₁' | .cont s₁' => cond₁ s₁' >>= fun x =>
          if x.1 then cont₁ x.2 else k₁ x.2) h = .ok res) :
    ∀ n {s₁ s₂ h}, rel s₁ s₂ →
      (C.cdoWhile.go body₂ cond₂ n s₂ >>= k₂) h = .ok res →
      (C.cdoWhileCtrl.go body₁ cond₁ n s₁ >>= fun
        | .error e => nomatch e
        | .ok s => k₁ s) h = .ok res := by
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ h _ hok
    rw [m_bind_app, C.cdoWhile.go] at hok; simp at hok
  | succ m ih =>
    intro s₁ s₂ h hrel hok
    have hok' : (body₂ s₂ >>= fun sb₂ => cond₂ sb₂ >>= fun x =>
        if x.1 then (C.cdoWhile.go body₂ cond₂ m x.2 >>= k₂) else k₂ x.2) h = .ok res := by
      rw [m_bind_app, cdoWhile_go_succ] at hok
      rw [m_bind_app]
      cases hb2 : body₂ s₂ h with
      | error e => simp [hb2] at hok
      | ok p1 =>
        rcases p1 with ⟨sb2, h1⟩
        simp only [hb2, m_bind_app] at hok ⊢
        cases hc2 : cond₂ sb2 h1 with
        | error e => simp [hc2] at hok
        | ok p2 =>
          rcases p2 with ⟨⟨cb, s2'⟩, h2⟩
          simp only [hc2] at hok ⊢
          cases cb <;> exact hok
    have hres := hstep (cont₁ := fun s₁' => C.cdoWhileCtrl.go body₁ cond₁ m s₁' >>= fun | .error e => nomatch e | .ok s => k₁ s)
      (cont₂ := fun s₂' => C.cdoWhile.go body₂ cond₂ m s₂' >>= k₂) hrel (fun s₁' s₂' h' hr' hk' => ih hr' hk') hok'
    rw [m_bind_app, cdoWhileCtrl_go_succ]
    rw [m_bind_app] at hres
    cases hb1 : body₁ s₁ h with
    | error e => simp [hb1] at hres
    | ok p1 =>
      rcases p1 with ⟨st, h1⟩
      simp only [hb1] at hres ⊢
      cases st with
      | brk s₁' => exact hres
      | ret e => nomatch e
      | next s₁' =>
        dsimp only at hres ⊢
        rw [m_bind_app] at hres
        cases hc1 : cond₁ s₁' h1 with
        | error e => simp [hc1] at hres
        | ok p2 =>
          rcases p2 with ⟨⟨condB, s₁''⟩, h2⟩
          simp only [hc1] at hres ⊢
          cases condB <;> exact hres
      | cont s₁' =>
        dsimp only at hres ⊢
        rw [m_bind_app] at hres
        cases hc1 : cond₁ s₁' h1 with
        | error e => simp [hc1] at hres
        | ok p2 =>
          rcases p2 with ⟨⟨condB, s₁''⟩, h2⟩
          simp only [hc1] at hres ⊢
          cases condB <;> exact hres

section Inffast
open Zlib.Inffast

theorem load64_c_eq (p : BPtr) : load64_c p = Zlib.Inffast.load64 p := by
  funext h
  simp only [load64_c, memcpyLoad64, Zlib.Inffast.load64, m_bind_app]

private theorem memcpyLoad64_eq (p : BPtr) : memcpyLoad64 p = Zlib.Inffast.load64 p :=
  load64_c_eq p

private theorem memcpyStore64_eq (out : BPtr) (v : UInt64) :
    memcpyStore64 out v = Zlib.Inffast.store64 out v := rfl

private theorem shl32_heap (x n : UInt32) {h : Heap} {v : UInt32} {h' : Heap}
    (hok : shl32 x n h = .ok (v, h')) : h' = h := by
  unfold shl32 at hok
  by_cases hn : n < 32
  · simp [hn] at hok; exact hok.2.symm
  · simp [hn, ub] at hok

private theorem shl64_heap (x n : UInt64) {h : Heap} {v : UInt64} {h' : Heap}
    (hok : shl64 x n h = .ok (v, h')) : h' = h := by
  unfold shl64 at hok
  by_cases hn : n < 64
  · simp [hn] at hok; exact hok.2.symm
  · simp [hn, ub] at hok

private theorem shr64_heap (x n : UInt64) {h : Heap} {v : UInt64} {h' : Heap}
    (hok : shr64 x n h = .ok (v, h')) : h' = h := by
  unfold shr64 at hok
  by_cases hn : n < 64
  · simp [hn] at hok; exact hok.2.symm
  · simp [hn, ub] at hok

private theorem chk64_heap (v : Int) {h : Heap} {v' : Int64} {h' : Heap}
    (hok : chk64 v h = .ok (v', h')) : h' = h := by
  unfold chk64 at hok
  by_cases hb : -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807
  · simp [hb] at hok; exact hok.2.symm
  · simp [hb, ub] at hok

private theorem comm_add_shl32_ok {α : Type} (p : CodePtr) (off : Nat) (x n : UInt32)
    (h : Heap) (res : α × Heap) (k : CodePtr → UInt32 → M α)
    (hok : (do let a ← Ptr.add p off; let b ← shl32 x n; k a b) h = .ok res) :
    (do let b ← shl32 x n; let a ← Ptr.add p off; k a b) h = .ok res := by
  rw [m_bind_app] at hok ⊢
  cases ha : Ptr.add p off h with
  | error e => simp [ha] at hok
  | ok pa =>
    rcases pa with ⟨a, h1⟩
    have hh1 : h1 = h := ptr_add_heap ha
    subst h1
    simp only [ha, m_bind_app] at hok
    cases hb : shl32 x n h with
    | error e => simp [hb] at hok
    | ok pb =>
      rcases pb with ⟨b, h2⟩
      have hh2 : h2 = h := shl32_heap x n hb
      subst h2
      simp only [hb, m_bind_app, ha] at hok ⊢
      exact hok

theorem copy_back_c_eq (out : BPtr) (dist len : UInt32) :
    copy_back_c out dist len = copy_back out dist len := by
  funext h
  simp only [copy_back_c, copy_back, cdecl, cinline]
  refine m_bind_congr rfl fun from0 h1 _ => ?_
  refine m_bind_congr rfl fun stop0 h2 _ => ?_
  rw [m_pure_bind]
  by_cases h16 : dist ≥ 16
  · simp only [h16, ↓reduceIte]
    refine cdoWhile_go_rel_eq
      (fun (l : CopyBackLocals) (p : BPtr × BPtr) => l.out = p.1 ∧ l.from_ = p.2 ∧ l.stop = stop0)
      (fun l p => { l with out := p.1, from_ := p.2 })
      _ _ _ _ _ _ ?_ ?_ ?_ ?_ C.fuel { from_ := from0, stop := stop0, out } (out, from0) h2 ⟨rfl, rfl, rfl⟩
    · intro l p _ hp; exact ⟨rfl, rfl, hp.2.2⟩
    · intro l p hx hp
      rcases hp with ⟨ho, hf, _⟩; rw [ho, hf]
      simp only [m_bind_app]
      cases memcpyB p.1 p.2 16 hx with
      | error e => rfl
      | ok p1 =>
        dsimp only
        cases Ptr.add p.1 16 p1.2 with
        | error e => rfl
        | ok p2 =>
          dsimp only
          cases Ptr.add p.2 16 p2.2 <;> rfl
    · intro l p sb₂ hx hp
      dsimp only
      rw [hp.2.2]
      simp only [m_bind_app]
      cases Ptr.lt sb₂.1 stop0 hx <;> rfl
    · intro _ _ _ _; rfl
  · simp only [h16, ↓reduceIte]
    by_cases h8 : dist ≥ 8
    · simp only [h8, ↓reduceIte]
      refine cdoWhile_go_rel_eq
        (fun (l : CopyBackLocals) (p : BPtr × BPtr) => l.out = p.1 ∧ l.from_ = p.2 ∧ l.stop = stop0)
        (fun l p => { l with out := p.1, from_ := p.2 })
        _ _ _ _ _ _ ?_ ?_ ?_ ?_ C.fuel { from_ := from0, stop := stop0, out } (out, from0) h2 ⟨rfl, rfl, rfl⟩
      · intro l p _ hp; exact ⟨rfl, rfl, hp.2.2⟩
      · intro l p hx hp
        rcases hp with ⟨ho, hf, _⟩; rw [ho, hf]
        simp only [m_bind_app]
        cases memcpyB p.1 p.2 8 hx with
        | error e => rfl
        | ok p1 =>
          dsimp only
          cases Ptr.add p.1 8 p1.2 with
          | error e => rfl
          | ok p2 =>
            dsimp only
            cases Ptr.add p.2 8 p2.2 <;> rfl
      · intro l p sb₂ hx hp
        dsimp only
        rw [hp.2.2]
        simp only [m_bind_app]
        cases Ptr.lt sb₂.1 stop0 hx <;> rfl
      · intro _ _ _ _; rfl
    · simp only [h8, ↓reduceIte]
      by_cases h1d : (dist == 1) = true
      · simp only [h1d, ↓reduceIte]
        refine m_bind_congr rfl fun b h3 _ => ?_
        refine cdoWhile_go_rel_eq
          (fun (l : CopyBackLocals) (o : BPtr) => l.out = o ∧ l.stop = stop0)
          (fun l o => { l with out := o })
          _ _ _ _ _ _ ?_ ?_ ?_ ?_ C.fuel { from_ := from0, stop := stop0, out } out h3 ⟨rfl, rfl⟩
        · intro l o _ ho; exact ⟨rfl, ho.2⟩
        · intro l o hx ho
          rw [ho.1, memcpyStore64_eq]
          simp only [m_bind_app]
          cases Zlib.Inffast.store64 o _ hx <;> rfl
        · intro l o sb hx ho
          dsimp only
          rw [ho.2]
          simp only [m_bind_app]
          cases Ptr.lt sb stop0 hx <;> rfl
        · intro _ _ _ _; rfl
      · simp only [h1d, Bool.false_eq_true, ↓reduceIte]
        refine cdoWhile_go_rel_eq
          (fun (l : CopyBackLocals) (p : BPtr × BPtr) => l.out = p.1 ∧ l.from_ = p.2 ∧ l.stop = stop0)
          (fun l p => { l with out := p.1, from_ := p.2 })
          _ _ _ _ _ _ ?_ ?_ ?_ ?_ C.fuel { from_ := from0, stop := stop0, out } (out, from0) h2 ⟨rfl, rfl, rfl⟩
        · intro l p _ hp; exact ⟨rfl, rfl, hp.2.2⟩
        · intro l p hx hp
          rcases hp with ⟨ho, hf, _⟩; rw [ho, hf]
          simp only [m_bind_app, memcpyLoad64_eq, memcpyStore64_eq]
          cases Zlib.Inffast.load64 p.2 hx with
          | error e => rfl
          | ok pv =>
            dsimp only
            cases Zlib.Inffast.store64 p.1 pv.1 pv.2 with
            | error e => rfl
            | ok ps =>
              dsimp only
              cases Ptr.add p.1 (dist.toNat : Int) ps.2 with
              | error e => rfl
              | ok po =>
                dsimp only
                cases Ptr.add p.2 (dist.toNat : Int) po.2 <;> rfl
        · intro l p sb₂ hx hp
          dsimp only
          rw [hp.2.2]
          simp only [m_bind_app]
          cases Ptr.lt sb₂.1 stop0 hx <;> rfl
        · intro _ _ _ _; rfl

private theorem badDataC_eq (c : Ctx) (msg : String) :
    badDataC c.strm c.state msg = badData c msg := rfl

private theorem copyBytePostInc_bind_eq {β : Type} (l : L) (k : BPtr × BPtr → M β) (h : Heap) :
    (copyBytePostInc l.out l.from_ >>= k) h =
    (copy1 l >>= fun l' => k (l'.out, l'.from_)) h := by
  simp only [copyBytePostInc, copy1, m_bind_app]
  cases hld : load8 l.from_ h with
  | error e => simp only
  | ok p1 =>
    rcases p1 with ⟨b, h1⟩
    simp only
    cases hadd : Ptr.add l.from_ 1 h1 with
    | error e => simp only
    | ok p2 =>
      rcases p2 with ⟨f', h2⟩
      simp only
      cases hst : store8 l.out b h2 with
      | error e => simp only
      | ok p3 =>
        rcases p3 with ⟨_, h3⟩
        simp only
        cases hadd2 : Ptr.add l.out 1 h3 <;> simp

private theorem copy1_fields {l l' : L} {h h' : Heap} (hok : copy1 l h = .ok (l', h')) :
    l'.in_ = l.in_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧ l'.here = l.here ∧
    l'.op = l.op ∧ l'.len = l.len ∧ l'.dist = l.dist ∧ l'.broke = l.broke ∧
    l'.againL = l.againL ∧ l'.againD = l.againD := by
  simp only [copy1, m_bind_app] at hok
  cases hld : load8 l.from_ h with
  | error e => simp [hld] at hok
  | ok p1 =>
    rcases p1 with ⟨b, h1⟩
    simp only [hld] at hok
    cases hadd : Ptr.add l.from_ 1 h1 with
    | error e => simp [hadd] at hok
    | ok p2 =>
      rcases p2 with ⟨f', h2⟩
      simp only [hadd] at hok
      cases hst : store8 l.out b h2 with
      | error e => simp [hst] at hok
      | ok p3 =>
        rcases p3 with ⟨_, h3⟩
        simp only [hst] at hok
        cases hadd2 : Ptr.add l.out 1 h3 with
        | error e => simp [hadd2] at hok
        | ok p4 =>
          rcases p4 with ⟨o', h4⟩
          simp only [hadd2, pure] at hok
          cases Except.ok.inj hok
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def RelCtx (c : Ctx) (fl : InflateFastLocals) : Prop :=
  fl.state = c.state ∧ fl.last = c.last ∧ fl.beg = c.beg ∧ fl.end_ = c.end_ ∧
  fl.wsize = c.wsize ∧ fl.whave = c.whave ∧ fl.wnext = c.wnext ∧ fl.window = c.window ∧
  fl.lcode = c.lcode ∧ fl.dcode = c.dcode ∧ fl.lmask = c.lmask ∧ fl.dmask = c.dmask

private theorem RelCtx.state {c fl} (h : RelCtx c fl) : fl.state = c.state := h.1
private theorem RelCtx.last {c fl} (h : RelCtx c fl) : fl.last = c.last := h.2.1
private theorem RelCtx.beg {c fl} (h : RelCtx c fl) : fl.beg = c.beg := h.2.2.1
private theorem RelCtx.end_ {c fl} (h : RelCtx c fl) : fl.end_ = c.end_ := h.2.2.2.1
private theorem RelCtx.wsize {c fl} (h : RelCtx c fl) : fl.wsize = c.wsize := h.2.2.2.2.1
private theorem RelCtx.whave {c fl} (h : RelCtx c fl) : fl.whave = c.whave := h.2.2.2.2.2.1
private theorem RelCtx.wnext {c fl} (h : RelCtx c fl) : fl.wnext = c.wnext := h.2.2.2.2.2.2.1
private theorem RelCtx.window {c fl} (h : RelCtx c fl) : fl.window = c.window := h.2.2.2.2.2.2.2.1
private theorem RelCtx.lcode {c fl} (h : RelCtx c fl) : fl.lcode = c.lcode := h.2.2.2.2.2.2.2.2.1
private theorem RelCtx.dcode {c fl} (h : RelCtx c fl) : fl.dcode = c.dcode := h.2.2.2.2.2.2.2.2.2.1
private theorem RelCtx.lmask {c fl} (h : RelCtx c fl) : fl.lmask = c.lmask := h.2.2.2.2.2.2.2.2.2.2.1
private theorem RelCtx.dmask {c fl} (h : RelCtx c fl) : fl.dmask = c.dmask := h.2.2.2.2.2.2.2.2.2.2.2

private def Rel8Core (c : Ctx) (fl : InflateFastLocals) (l : L) : Prop :=
  RelCtx c fl ∧ fl.in_ = l.in_ ∧ fl.out = l.out ∧ fl.hold8 = l.hold ∧ fl.bits = l.bits

private def RelCore (c : Ctx) (fl : InflateFastLocals) (l : L) : Prop :=
  RelCtx c fl ∧ fl.in_ = l.in_ ∧ fl.out = l.out ∧ fl.hold = l.hold ∧ fl.bits = l.bits

private theorem copyMatch8C_tail_of_ok {β : Type} (c : Ctx)
    (fl : InflateFastLocals) (l : L) (h : Heap) (res : β × Heap)
    (hctx : Rel8Core c fl l) (hop : fl.op = l.op) (hlen : fl.len = l.len)
    (hdist : fl.dist = l.dist) (hfrom : fl.from_ = l.from_) (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok :
      (if l.op > l.len then
        (do
          memcpyB l.out l.from_ l.len.toNat
          let o1 ← l.out.add l.len.toNat
          if (l.len - l.len != 0) = true then
            let o2 ← copy_back o1 l.dist (l.len - l.len)
            k₂ { l with op := l.len, out := o2, len := l.len - l.len }
          else k₂ { l with op := l.len, out := o1, len := l.len - l.len })
       else
        (do
          memcpyB l.out l.from_ l.op.toNat
          let o1 ← l.out.add l.op.toNat
          if (l.len - l.op != 0) = true then
            let o2 ← copy_back o1 l.dist (l.len - l.op)
            k₂ { l with out := o2, len := l.len - l.op }
          else k₂ { l with out := o1, len := l.len - l.op })) h = .ok res)
    (hk_next : ∀ fl' l' h', Rel8Core c fl' l' → fl'.last8 = fl.last8 → fl'.end8 = fl.end8 →
      l'.againL = l.againL → l'.againD = l.againD →
      l'.broke = false → k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (if fl.op > fl.len then
      (do
        memcpyB fl.out fl.from_ fl.len.toNat
        let o1 ← fl.out.add fl.len.toNat
        if (fl.len - fl.len != 0) = true then
          let o2 ← copy_back o1 fl.dist (fl.len - fl.len)
          k₁ (.next { fl with op := fl.len, out := o2, len := fl.len - fl.len })
        else k₁ (.next { fl with op := fl.len, out := o1, len := fl.len - fl.len }))
     else
      (do
        memcpyB fl.out fl.from_ fl.op.toNat
        let o1 ← fl.out.add fl.op.toNat
        if (fl.len - fl.op != 0) = true then
          let o2 ← copy_back o1 fl.dist (fl.len - fl.op)
          k₁ (.next { fl with out := o2, len := fl.len - fl.op })
        else k₁ (.next { fl with out := o1, len := fl.len - fl.op }))) h = .ok res := by
  rcases hctx with ⟨hrc, hin, hou, hho, hbi⟩
  rw [hop, hlen, hdist, hfrom, hou]
  by_cases hopl : l.op > l.len
  · simp only [hopl, ↓reduceIte] at hok ⊢
    refine m_bind_ok_same rfl hok fun _ h1 _ hok1 => ?_
    refine m_bind_ok_same rfl hok1 fun o1 h2 _ hok2 => ?_
    by_cases hlz : (l.len - l.len != 0) = true
    · simp only [hlz, ↓reduceIte] at hok2 ⊢
      refine m_bind_ok_same rfl hok2 fun o2 h3 _ hok3 => ?_
      refine hk_next _ { l with op := l.len, out := o2, len := l.len - l.len } h3 ?_ rfl rfl rfl rfl hbrk0 hok3
      exact ⟨hrc, hin, rfl, hho, hbi⟩
    · simp only [hlz, Bool.false_eq_true, ↓reduceIte] at hok2 ⊢
      refine hk_next _ { l with op := l.len, out := o1, len := l.len - l.len } h2 ?_ rfl rfl rfl rfl hbrk0 hok2
      exact ⟨hrc, hin, rfl, hho, hbi⟩
  · simp only [hopl, ↓reduceIte] at hok ⊢
    refine m_bind_ok_same rfl hok fun _ h1 _ hok1 => ?_
    refine m_bind_ok_same rfl hok1 fun o1 h2 _ hok2 => ?_
    by_cases hlz : (l.len - l.op != 0) = true
    · simp only [hlz, ↓reduceIte] at hok2 ⊢
      refine m_bind_ok_same rfl hok2 fun o2 h3 _ hok3 => ?_
      refine hk_next _ { l with out := o2, len := l.len - l.op } h3 ?_ rfl rfl rfl rfl hbrk0 hok3
      exact ⟨hrc, hin, rfl, hho, hbi⟩
    · simp only [hlz, Bool.false_eq_true, ↓reduceIte] at hok2 ⊢
      refine hk_next _ { l with out := o1, len := l.len - l.op } h2 ?_ rfl rfl rfl rfl hbrk0 hok2
      exact ⟨hrc, hin, rfl, hho, hbi⟩

private def NotModeLen (state : InflateStatePtr) (h : Heap) : Prop :=
  ∀ s h', ldInflateState state h = .ok (s, h') → s.mode ≠ LEN

private theorem notModeLen_of_st {state : InflateStatePtr} {s : InflateState} {h h' : Heap}
    (hst : stInflateState state s h = .ok ((), h')) (hm : s.mode ≠ LEN) :
    NotModeLen state h' := by
  intro s' h'' hld
  cases state with
  | none => simp [stInflateState] at hst
  | some r =>
    cases r with
    | tab i =>
      simp only [stInflateState, InflateStateRef.get, InflateStateRef.put, InflateStateRef.isRo] at hst
      cases hg : h.istates i with
      | none => simp [hg] at hst
      | some _ =>
        simp only [hg, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hst
        rcases hst with ⟨_, rfl⟩
        simp only [ldInflateState, InflateStateRef.get] at hld
        rw [show (upd h.istates i (some s)).get i = some s from C.upd_same h.istates i (some s)] at hld
        injection hld with hp
        injection hp with hs _
        rw [← hs]
        exact hm

private theorem notModeLen_badData {c : Ctx} {msg : String} {h h' : Heap}
    (hb : badData c msg h = .ok ((), h')) : NotModeLen c.state h' := by
  simp only [badData, m_bind_app] at hb
  cases h0 : Zlib.Zutil.strLit msg h with
  | error e => simp [h0] at hb
  | ok p0 =>
    simp only [h0] at hb
    cases h1 : ldZStream c.strm p0.2 with
    | error e => simp [h1] at hb
    | ok p1 =>
      simp only [h1] at hb
      cases h2 : stZStream c.strm { p1.1 with msg := p0.1 } p1.2 with
      | error e => simp [h2] at hb
      | ok p2 =>
        simp only [h2] at hb
        cases h3 : ldInflateState c.state p2.2 with
        | error e => simp [h3] at hb
        | ok p3 =>
          rcases p3 with ⟨s3, hs3⟩
          simp only [h3] at hb
          exact notModeLen_of_st hb (show BAD ≠ LEN by decide)

private theorem ldInflateState_heap {p : InflateStatePtr} {h h' : Heap} {s : InflateState}
    (hok : ldInflateState p h = .ok (s, h')) : h' = h := by
  cases p with
  | none => simp [ldInflateState] at hok
  | some r =>
    cases r with
    | tab i =>
      simp only [ldInflateState, InflateStateRef.get] at hok
      cases hg : h.istates i with
      | none => simp [hg] at hok
      | some _ => simp [hg] at hok; exact hok.2.symm

private theorem whave_guard_bind_of_ok {α β γ : Type} (c : Ctx)
    (state1 : InflateStatePtr) (op0 whave1 : UInt32) (h : Heap) (res : γ × Heap)
    (hstate : state1 = c.state) (hwhave : whave1 = c.whave)
    (brk2 fall2 : M α) (k₂ : α → M γ)
    (brk1 fall1 : M β) (k₁ : β → M γ)
    (hok :
      ((if op0 > c.whave then do
          let s ← ldInflateState c.state
          if (s.sane != 0) = true then
            let _ ← badData c "invalid distance too far back"
            brk2
          else fall2
        else fall2) >>= k₂) h = .ok res)
    (hbrk : ∀ h', badData c "invalid distance too far back" h = .ok ((), h') →
      (brk2 >>= k₂) h' = .ok res → (brk1 >>= k₁) h' = .ok res)
    (hfall : (fall2 >>= k₂) h = .ok res → (fall1 >>= k₁) h = .ok res) :
    ((if op0 > whave1 then do
        let s ← ldInflateState state1
        if (s.sane != 0) = true then
          let _ ← badDataC c.strm state1 "invalid distance too far back"
          brk1
        else fall1
      else fall1) >>= k₁) h = .ok res := by
  by_cases hwhv : op0 > c.whave
  · have hwhv1 : op0 > whave1 := by rw [hwhave]; exact hwhv
    simp only [hwhv, hwhv1, ↓reduceIte] at hok ⊢
    repeat rw [m_bind_assoc] at hok
    repeat rw [m_bind_assoc]
    refine m_bind_ok_same (by rw [hstate]) hok fun s h1 hld hok1 => ?_
    have hh1 := ldInflateState_heap hld; subst hh1
    by_cases hs : (s.sane != 0) = true
    · simp only [hs, ↓reduceIte] at hok1 ⊢
      repeat rw [m_bind_assoc] at hok1
      repeat rw [m_bind_assoc]
      refine m_bind_ok_same (by rw [hstate, ← badDataC_eq]) hok1 fun _ h2 hb2 hok2 => ?_
      exact hbrk h2 hb2 hok2
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hok1 ⊢
      exact hfall hok1
  · have hwhv1 : ¬(op0 > whave1) := by rw [hwhave]; exact hwhv
    simp only [hwhv, hwhv1, ↓reduceIte] at hok ⊢
    exact hfall hok

private theorem copyMatch8C_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : Rel8Core c fl l) (hdist : fl.dist = l.dist) (hlen : fl.len = l.len)
    (hop : fl.op = l.op) (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok : (copyMatch8 c l >>= k₂) h = .ok res)
    (hk_brk : ∀ fl' l' h', Rel8Core c fl' l' → l'.againL = l.againL → l'.againD = l.againD →
      l'.broke = true → NotModeLen c.state h' → k₂ l' h' = .ok res → k₁ (.brk fl') h' = .ok res)
    (hk_next : ∀ fl' l' h', Rel8Core c fl' l' → fl'.last8 = fl.last8 → fl'.end8 = fl.end8 →
      l'.againL = l.againL → l'.againD = l.againD →
      l'.broke = false → k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (copyMatch8C c.strm fl >>= k₁) h = .ok res := by
  rcases hctx with ⟨hc0, hin, hou, hho, hbi⟩
  simp only [copyMatch8C, copyMatch8, cinline, copy_back_c_eq] at hok ⊢
  have runAfterFrom (fl' : InflateFastLocals) (l' : L) (hx : Heap)
      (hrel' : Rel8Core c fl' l') (hla8' : fl'.last8 = fl.last8) (hen8' : fl'.end8 = fl.end8)
      (hd' : fl'.dist = l'.dist) (hle' : fl'.len = l'.len)
      (hop' : fl'.op = l'.op) (hfr' : fl'.from_ = l'.from_)
      (hag' : l'.againL = l.againL) (had' : l'.againD = l.againD) (hbr' : l'.broke = false)
      (hwok :
        (if l'.op > l'.len then
          (do
            memcpyB l'.out l'.from_ l'.len.toNat
            let o1 ← l'.out.add l'.len.toNat
            if (l'.len - l'.len != 0) = true then
              let o2 ← copy_back o1 l'.dist (l'.len - l'.len)
              k₂ { l' with op := l'.len, out := o2, len := l'.len - l'.len }
            else k₂ { l' with op := l'.len, out := o1, len := l'.len - l'.len })
         else
          (do
            memcpyB l'.out l'.from_ l'.op.toNat
            let o1 ← l'.out.add l'.op.toNat
            if (l'.len - l'.op != 0) = true then
              let o2 ← copy_back o1 l'.dist (l'.len - l'.op)
              k₂ { l' with out := o2, len := l'.len - l'.op }
            else k₂ { l' with out := o1, len := l'.len - l'.op })) hx = .ok res) :
      (if fl'.op > fl'.len then
        (do
          memcpyB fl'.out fl'.from_ fl'.len.toNat
          let o1 ← fl'.out.add fl'.len.toNat
          if (fl'.len - fl'.len != 0) = true then
            let o2 ← copy_back o1 fl'.dist (fl'.len - fl'.len)
            k₁ (.next { fl' with op := fl'.len, out := o2, len := fl'.len - fl'.len })
          else k₁ (.next { fl' with op := fl'.len, out := o1, len := fl'.len - fl'.len }))
       else
        (do
          memcpyB fl'.out fl'.from_ fl'.op.toNat
          let o1 ← fl'.out.add fl'.op.toNat
          if (fl'.len - fl'.op != 0) = true then
            let o2 ← copy_back o1 fl'.dist (fl'.len - fl'.op)
            k₁ (.next { fl' with out := o2, len := fl'.len - fl'.op })
          else k₁ (.next { fl' with out := o1, len := fl'.len - fl'.op }))) hx = .ok res := by
    exact copyMatch8C_tail_of_ok c fl' l' hx res hrel' hop' hle' hd' hfr' hbr' k₁ k₂ hwok
      fun fl'' l'' h'' hr'' hla8'' hen8'' hag'' had'' hbr'' hok'' =>
        hk_next fl'' l'' h'' hr'' (hla8''.trans hla8') (hen8''.trans hen8')
          (hag''.trans hag') (had''.trans had') hbr'' hok''
  rw [hdist, hop]
  by_cases hd : l.dist > l.op
  · simp only [hd, ↓reduceIte] at hok ⊢
    refine whave_guard_bind_of_ok c fl.state (l.dist - l.op) fl.whave h res hc0.state hc0.whave
      _ _ k₂ _ _ k₁ hok ?_ ?_
    · intro h2 hbad hok2
      repeat rw [m_pure_bind] at hok2
      repeat rw [m_pure_bind]
      exact hk_brk { fl with op := l.dist - l.op, dist := l.dist } { l with op := l.dist - l.op, broke := true } h2
        ⟨hc0, hin, hou, hho, hbi⟩
        rfl rfl rfl (notModeLen_badData hbad) hok2
    · intro hokW
      simp only [ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at hokW ⊢
      by_cases hwn0 : (c.wnext == 0) = true
      · have hwn0_fl : (fl.wnext == 0) = true := by rw [hc0.wnext]; exact hwn0
        simp only [hwn0, hwn0_fl, ↓reduceIte] at hokW ⊢
        refine m_bind_ok_same (by rw [hc0.window, hc0.wsize]) hokW fun f1 h2 _ hok2 => ?_
        exact runAfterFrom { fl with dist := l.dist, op := l.dist - l.op, from_ := f1 }
          { l with op := l.dist - l.op, from_ := f1 } h2
          ⟨hc0, hin, hou, hho, hbi⟩ rfl rfl rfl hlen rfl rfl rfl rfl hbrk0 hok2
      · have hwn0_fl : ¬((fl.wnext == 0) = true) := by rw [hc0.wnext]; exact hwn0
        simp only [hwn0, hwn0_fl] at hokW ⊢
        by_cases hwnl : c.wnext < l.dist - l.op
        · have hwnl_fl : fl.wnext < l.dist - l.op := by rw [hc0.wnext]; exact hwnl
          simp only [hwnl, hwnl_fl, ↓reduceIte] at hokW ⊢
          refine m_bind_ok_same (by rw [hc0.window, hc0.wsize, hc0.wnext]) hokW fun f1 h2 _ hok2 => ?_
          by_cases hopl : l.dist - l.op - c.wnext < l.len
          · have hopl_fl : l.dist - l.op - fl.wnext < fl.len := by rw [hc0.wnext, hlen]; exact hopl
            simp only [hopl, hopl_fl, ↓reduceIte] at hok2 ⊢
            refine m_bind_ok_same (by rw [hou, hc0.wnext]) hok2 fun _ h3 _ hok3 => ?_
            refine m_bind_ok_same (by rw [hou, hc0.wnext]) hok3 fun o1 h4 _ hok4 => ?_
            exact runAfterFrom
              { fl with dist := l.dist, out := o1, op := fl.wnext, len := fl.len - (l.dist - l.op - fl.wnext), from_ := fl.window }
              { l with out := o1, op := c.wnext, len := l.len - (l.dist - l.op - c.wnext), from_ := c.window }
              h4 ⟨hc0, hin, rfl, hho, hbi⟩ rfl rfl rfl
              (by rw [hlen, hc0.wnext]) hc0.wnext hc0.window rfl rfl hbrk0 hok4
          · have hopl_fl : ¬(l.dist - l.op - fl.wnext < fl.len) := by rw [hc0.wnext, hlen]; exact hopl
            simp only [hopl, hopl_fl, ↓reduceIte] at hok2 ⊢
            exact runAfterFrom { fl with dist := l.dist, op := l.dist - l.op - fl.wnext, from_ := f1 }
              { l with op := l.dist - l.op - c.wnext, from_ := f1 }
              h2 ⟨hc0, hin, hou, hho, hbi⟩ rfl rfl rfl hlen (by rw [hc0.wnext]) rfl rfl rfl hbrk0 hok2
        · have hwnl_fl : ¬(fl.wnext < l.dist - l.op) := by rw [hc0.wnext]; exact hwnl
          simp only [hwnl, hwnl_fl, ↓reduceIte] at hokW ⊢
          refine m_bind_ok_same (by rw [hc0.window, hc0.wnext]) hokW fun f1 h2 _ hok2 => ?_
          exact runAfterFrom { fl with dist := l.dist, op := l.dist - l.op, from_ := f1 }
            { l with op := l.dist - l.op, from_ := f1 }
            h2 ⟨hc0, hin, hou, hho, hbi⟩ rfl rfl rfl hlen rfl rfl rfl rfl hbrk0 hok2
  · simp only [hd, ↓reduceIte] at hok ⊢
    repeat rw [m_bind_assoc] at hok
    repeat rw [m_bind_assoc]
    refine m_bind_ok_same (by rw [hou, hlen]) hok fun o2 h2 _ hok2 => ?_
    repeat rw [m_pure_bind] at hok2
    repeat rw [m_pure_bind]
    refine hk_next _ { l with out := o2 } h2 ?_ rfl rfl rfl rfl hbrk0 hok2
    exact ⟨hc0, hin, rfl, hho, hbi⟩


private theorem dodist8_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : Rel8Core c fl l) (hhere : fl.here = l.here) (hlen : fl.len = l.len)
    (hagl : l.againL = false) (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok : (C.cdoWhile (dodist8 c) (fun l => pure (l.againD, l)) l >>= k₂) h = .ok res)
    (hk_brk : ∀ fl' l' h', Rel8Core c fl' l' → l'.againL = false → l'.broke = true →
      NotModeLen c.state h' → k₂ l' h' = .ok res → k₁ (.brk fl') h' = .ok res)
    (hk_next : ∀ fl' l' h', Rel8Core c fl' l' → fl'.last8 = fl.last8 → fl'.end8 = fl.end8 →
      l'.againL = false → l'.broke = false →
      k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (clabel "dodist8" (dodist8BodyC c.strm) fl >>= k₁) h = .ok res := by
  let rel : InflateFastLocals → L → Prop := fun fl' l' =>
    Rel8Core c fl' l' ∧ fl'.last8 = fl.last8 ∧ fl'.end8 = fl.end8 ∧
    fl'.here = l'.here ∧ fl'.len = l'.len ∧ l'.againL = false ∧ l'.broke = false
  refine clabel_of_cdoWhile_ok rel (dodist8BodyC c.strm) k₁ (dodist8 c)
    (fun l => pure (l.againD, l)) k₂ res ?_ C.fuel ⟨hctx, rfl, rfl, hhere, hlen, hagl, hbrk0⟩ hok
  intro fl1 l1 hx cont₁ cont₂ ⟨hrc, hla8, hen8, hhe, hle, hal, hbr⟩ hih hokS
  rcases hrc with ⟨hc0, hin, hou, hho, hbi⟩
  simp only [dodist8BodyC, dodist8, cinline, ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at hokS ⊢
  refine m_bind_ok_same (by rw [hhe]) hokS fun e0 h_e0 _ hok1 => ?_
  refine m_bind_ok_same (by rw [hho]) hok1 fun sh0 h_sh0 _ hok2 => ?_
  refine m_bind_ok_same (by rw [hhe]) hok2 fun e1 h_e1 _ hok3 => ?_
  by_cases hop16 : (e1.op.toUInt32 &&& 16 != 0) = true
  · simp only [hop16, ↓reduceIte] at hok3 ⊢
    refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
    refine m_bind_ok_same rfl hok4 fun mVal h_m _ hok5 => ?_
    refine m_bind_ok_same rfl hok5 fun sh1 h_sh1 _ hok6 => ?_
    refine m_bind_ok_same (by rw [hou, hc0.beg]) hok6 fun dVal h_df _ hok7 => ?_
    refine @copyMatch8C_of_ok β c
      { fl1 with hold8 := sh1, bits := fl1.bits - e0.bits.toUInt32 - (e1.op.toUInt32 &&& 15),
                 dist := e2.val.toUInt32 + (sh0.toUInt32 &&& (mVal - 1)), op := dVal.toUInt64.toUInt32 }
      { l1 with hold := sh1, bits := l1.bits - e0.bits.toUInt32 - (e1.op.toUInt32 &&& 15),
                dist := e2.val.toUInt32 + (sh0.toUInt32 &&& (mVal - 1)), op := dVal.toUInt64.toUInt32, againD := false }
      h_df res ⟨hc0, hin, hou, rfl, by rw [hbi]⟩ rfl hle rfl hbr k₁ (fun l => if l.againD then cont₂ l else k₂ l) hok7
      (fun fl' l' h' hr' hag' had' hbr' hnml hok8 => by
        change l'.againD = false at had'
        simp only [had', Bool.false_eq_true, ↓reduceIte] at hok8
        exact hk_brk fl' l' h' hr' (hag'.trans hal) hbr' hnml hok8)
      (fun fl' l' h' hr' hla8' hen8' hag' had' hbr' hok8 => by
        change l'.againD = false at had'
        simp only [had', Bool.false_eq_true, ↓reduceIte] at hok8
        exact hk_next fl' l' h' hr' (hla8'.trans hla8) (hen8'.trans hen8) (hag'.trans hal) hbr' hok8)
  · simp only [hop16, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
    by_cases hop64 : (e1.op.toUInt32 &&& 64 == 0) = true
    · simp only [hop64, ↓reduceIte] at hok3 ⊢
      refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
      have hcomm := comm_add_shl32_ok c.dcode e2.val.toNat 1 e1.op.toUInt32 h_e2 res _
        hok4
      refine m_bind_ok_same rfl hcomm fun mVal h_m _ hok5 => ?_
      repeat rw [m_bind_assoc]
      refine m_bind_ok_same (by rw [hc0.dcode]) hok5 fun h1 h_1 _ hok6 => ?_
      refine m_bind_ok_same rfl hok6 fun here1 h_hr _ hok7 => ?_
      refine hih _ _ h_hr ?_ hok7
      exact ⟨⟨hc0, hin, hou, rfl, by dsimp; rw [hbi]⟩, hla8, hen8, rfl, hle, hal, hbr⟩
    · simp only [hop64, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
      repeat rw [m_bind_assoc] at hok3
      repeat rw [m_bind_assoc]
      refine m_bind_ok_same (by rw [hc0.state, ← badDataC_eq]) hok3 fun _ h_bd hbd hok4 => ?_
      refine hk_brk _ _ h_bd ?_ ?_ ?_ (notModeLen_badData hbd) hok4
      · exact ⟨hc0, hin, hou, rfl, by dsimp; rw [hbi]⟩
      · exact hal
      · rfl

private theorem dolen8_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : Rel8Core c fl l) (hhere : fl.here = l.here) (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok : (C.cdoWhile (dolen8 c) (fun l => pure (l.againL, l)) l >>= k₂) h = .ok res)
    (hk_brk : ∀ fl' l' h', Rel8Core c fl' l' → l'.broke = true →
      NotModeLen c.state h' → k₂ l' h' = .ok res → k₁ (.brk fl') h' = .ok res)
    (hk_next : ∀ fl' l' h', Rel8Core c fl' l' → fl'.last8 = fl.last8 → fl'.end8 = fl.end8 →
      l'.broke = false → k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (clabel "dolen8" (dolen8BodyC c.strm) fl >>= k₁) h = .ok res := by
  let rel : InflateFastLocals → L → Prop := fun fl' l' =>
    Rel8Core c fl' l' ∧ fl'.last8 = fl.last8 ∧ fl'.end8 = fl.end8 ∧ fl'.here = l'.here ∧ l'.broke = false
  refine clabel_of_cdoWhile_ok rel (dolen8BodyC c.strm) k₁ (dolen8 c)
    (fun l => pure (l.againL, l)) k₂ res ?_ C.fuel ⟨hctx, rfl, rfl, hhere, hbrk0⟩ hok
  intro fl1 l1 hx cont₁ cont₂ ⟨hrc, hla8, hen8, hhe, hbr⟩ hih hokS
  rcases hrc with ⟨hc0, hin, hou, hho, hbi⟩
  simp only [dolen8BodyC, dolen8, cinline, ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at hokS ⊢
  refine m_bind_ok_same (by rw [hhe]) hokS fun e0 h_e0 _ hok1 => ?_
  refine m_bind_ok_same (by rw [hho]) hok1 fun sh0 h_sh0 _ hok2 => ?_
  refine m_bind_ok_same (by rw [hhe]) hok2 fun e1 h_e1 _ hok3 => ?_
  by_cases hop0 : (e1.op.toUInt32 == 0) = true
  · simp only [hop0, ↓reduceIte] at hok3 ⊢
    refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
    refine m_bind_ok_same (by rw [hou]) hok4 fun _ h_st _ hok5 => ?_
    refine m_bind_ok_same (by rw [hou]) hok5 fun out1 h_out _ hok6 => ?_
    refine hk_next _ _ h_out ?_ hla8 hen8 ?_ hok6
    · exact ⟨hc0, hin, rfl, rfl, by dsimp; rw [hbi]⟩
    · exact hbr
  · simp only [hop0, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
    by_cases hop16 : (e1.op.toUInt32 &&& 16 != 0) = true
    · simp only [hop16, ↓reduceIte] at hok3 ⊢
      refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
      refine m_bind_ok_same rfl hok4 fun mVal h_m _ hok5 => ?_
      refine m_bind_ok_same rfl hok5 fun sh1 h_sh1 _ hok6 => ?_
      refine m_bind_ok_same (by rw [hc0.dcode, hc0.dmask]) hok6 fun here1 h_hr _ hok7 => ?_
      refine @dodist8_of_ok β c
        { fl1 with hold8 := sh1, bits := fl1.bits - e0.bits.toUInt32 - (e1.op.toUInt32 &&& 15),
                   here := here1, op := e1.op.toUInt32 &&& 15, len := e2.val.toUInt32 + (sh0.toUInt32 &&& (mVal - 1)) }
        { l1 with hold := sh1, bits := l1.bits - e0.bits.toUInt32 - (e1.op.toUInt32 &&& 15),
                  here := here1, op := e1.op.toUInt32 &&& 15, len := e2.val.toUInt32 + (sh0.toUInt32 &&& (mVal - 1)),
                  againL := false }
        h_hr res ⟨hc0, hin, hou, rfl, by rw [hbi]⟩ rfl rfl rfl hbr k₁ (fun l => if l.againL then cont₂ l else k₂ l) hok7
        (fun fl' l' h' hr' hal' hbr' hnml hok8 => by
          simp only [hal', Bool.false_eq_true, ↓reduceIte] at hok8
          exact hk_brk fl' l' h' hr' hbr' hnml hok8)
        (fun fl' l' h' hr' hla8' hen8' hal' hbr' hok8 => by
          simp only [hal', Bool.false_eq_true, ↓reduceIte] at hok8
          exact hk_next fl' l' h' hr' (hla8'.trans hla8) (hen8'.trans hen8) hbr' hok8)
    · simp only [hop16, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
      by_cases hop64 : (e1.op.toUInt32 &&& 64 == 0) = true
      · simp only [hop64, ↓reduceIte] at hok3 ⊢
        refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
        have hcomm := comm_add_shl32_ok c.lcode e2.val.toNat 1 e1.op.toUInt32 h_e2 res _
          hok4
        refine m_bind_ok_same rfl hcomm fun mVal h_m _ hok5 => ?_
        refine m_bind_ok_same (by rw [hc0.lcode]) hok5 fun h1 h_1 _ hok6 => ?_
        refine m_bind_ok_same rfl hok6 fun here1 h_hr _ hok7 => ?_
        refine hih _ _ h_hr ?_ hok7
        exact ⟨⟨hc0, hin, hou, rfl, by dsimp; rw [hbi]⟩, hla8, hen8, rfl, hbr⟩
      · simp only [hop64, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
        by_cases hop32 : (e1.op.toUInt32 &&& 32 != 0) = true
        · simp only [hop32, ↓reduceIte] at hok3 ⊢
          refine m_bind_ok_same (by rw [hc0.state]) hok3 fun s h_s _ hok4 => ?_
          refine m_bind_ok_same (by rw [hc0.state]) hok4 fun _ h_st hst_ok hok5 => ?_
          refine hk_brk _ _ h_st ?_ ?_
            (notModeLen_of_st hst_ok (show TYPE ≠ LEN by decide)) hok5
          · exact ⟨hc0, hin, hou, rfl, by dsimp; rw [hbi]⟩
          · rfl
        · simp only [hop32, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
          refine m_bind_ok_same (by rw [hc0.state, ← badDataC_eq]) hok3 fun _ h_bd hbd hok4 => ?_
          refine hk_brk _ _ h_bd ?_ ?_ (notModeLen_badData hbd) hok4
          · exact ⟨hc0, hin, hou, rfl, by dsimp; rw [hbi]⟩
          · rfl

private theorem cdoWhileBrk_bind_eq {σ β : Type} (body : σ → M (LoopStep σ Empty))
    (cond : σ → M (Bool × σ)) (s : σ) (k : σ → M β) (h : Heap) :
    (C.cdoWhileBrk body cond s >>= k) h =
    (C.cdoWhileCtrl.go body cond C.fuel s >>= fun
      | .error e => nomatch e
      | .ok s' => k s') h := by
  unfold C.cdoWhileBrk C.cdoWhileCtrl
  rw [m_bind_assoc]
  refine m_bind_congr rfl fun r _ _ => ?_
  cases r with
  | error e => nomatch e
  | ok s' => rfl

private theorem body8_of_ok {β : Type} (c : Ctx) (last8 : ConstBPtr) (end8 : BPtr)
    {fl : InflateFastLocals} {l : L} {h : Heap} {res : β × Heap}
    (hctx : Rel8Core c fl l) (hlast8 : fl.last8 = last8) (hend8 : fl.end8 = end8)
    (hbrk0 : l.broke = false)
    (k₁ : InflateFastLocals → M β) (k₂ : L → M β)
    (hok :
      (C.cdoWhile (inflate_fast_body8 c)
        (fun l => do
          if l.broke then pure (false, l)
          else if ← Ptr.le l.in_ last8 then pure (← Ptr.le l.out end8, l)
          else pure (false, l)) l >>= k₂) h = .ok res)
    (hk : ∀ fl' l' h', Rel8Core c fl' l' → (l'.broke = true → NotModeLen c.state h') →
      k₂ l' h' = .ok res → k₁ fl' h' = .ok res) :
    (C.cdoWhileBrk
      (fun (l : InflateFastLocals) => do
        let mut l := l
        let w0 ← cinline (load64_c l.in_)
        let sh0 ← cinline (shl64 w0 l.bits.toUInt64)
        let in0 ← cinline (l.in_.add (((63 - l.bits) >>> 3).toNat : Int))
        l := { l with hold8 := l.hold8 ||| sh0 }
        l := { l with in_ := in0, bits := l.bits ||| 56 }
        let h0 ← cinline (l.lcode.add (l.hold8 &&& l.lmask.toUInt64).toNat)
        l := { l with here := h0 }
        let e0 ← cinline l.here.load
        if e0.op == 0 then
          let sh1 ← cinline (shr64 l.hold8 e0.bits.toUInt64)
          l := { l with hold8 := sh1 }
          l := { l with bits := l.bits - e0.bits.toUInt32 }
          store8 l.out e0.val.toUInt8
          let out1 ← cinline (l.out.add 1)
          l := { l with out := out1 }
          let h1 ← cinline (l.lcode.add (l.hold8 &&& l.lmask.toUInt64).toNat)
          l := { l with here := h1 }
          let e1 ← cinline l.here.load
          if e1.op == 0 then
            let sh2 ← cinline (shr64 l.hold8 e1.bits.toUInt64)
            l := { l with hold8 := sh2 }
            l := { l with bits := l.bits - e1.bits.toUInt32 }
            store8 l.out e1.val.toUInt8
            let out2 ← cinline (l.out.add 1)
            l := { l with out := out2 }
            let h2 ← cinline (l.lcode.add (l.hold8 &&& l.lmask.toUInt64).toNat)
            l := { l with here := h2 }
            let e2 ← cinline l.here.load
            if e2.op == 0 then
              let sh3 ← cinline (shr64 l.hold8 e2.bits.toUInt64)
              l := { l with hold8 := sh3 }
              l := { l with bits := l.bits - e2.bits.toUInt32 }
              store8 l.out e2.val.toUInt8
              let out3 ← cinline (l.out.add 1)
              return .cont { l with out := out3 }
          let w1 ← cinline (load64_c l.in_)
          let sh4 ← cinline (shl64 w1 l.bits.toUInt64)
          let in1 ← cinline (l.in_.add (((63 - l.bits) >>> 3).toNat : Int))
          l := { l with hold8 := l.hold8 ||| sh4 }
          l := { l with in_ := in1, bits := l.bits ||| 56 }
        clabel "dolen8" (dolen8BodyC c.strm) l)
      (fun (l : InflateFastLocals) => do
        if ← Ptr.le l.in_ l.last8 then pure (← Ptr.le l.out l.end8, l)
        else pure (false, l)) fl >>= k₁) h = .ok res := by
  rw [cdoWhileBrk_bind_eq]
  let rel : InflateFastLocals → L → Prop := fun fl l =>
    Rel8Core c fl l ∧ fl.last8 = last8 ∧ fl.end8 = end8 ∧ l.broke = false
  refine cdoWhileBrk_of_cdoWhile_ok rel _ _ k₁ _ _ k₂ res ?_ C.fuel
    ⟨hctx, hlast8, hend8, hbrk0⟩ hok
  intro fl1 l1 hx cont₁ cont₂ ⟨hrc, hla8, hen8, hbr⟩ hih hokS
  rcases hrc with ⟨hc0, hin, hou, hho, hbi⟩
  have evalCond (fl' : InflateFastLocals) (l' : L) (hx' : Heap)
      (hr' : Rel8Core c fl' l') (hla8' : fl'.last8 = last8) (hen8' : fl'.end8 = end8)
      (hbr' : l'.broke = false)
      (hokC : ((do
        if l'.broke then pure (false, l')
        else if ← Ptr.le l'.in_ last8 then pure (← Ptr.le l'.out end8, l')
        else pure (false, l')) >>= fun x => if x.1 then cont₂ x.2 else k₂ x.2) hx' = .ok res) :
      ((do
        if ← Ptr.le fl'.in_ fl'.last8 then pure (← Ptr.le fl'.out fl'.end8, fl')
        else pure (false, fl')) >>= fun x => if x.1 then cont₁ x.2 else k₁ x.2) hx' = .ok res := by
    simp only [hbr', Bool.false_eq_true, ↓reduceIte] at hokC ⊢
    repeat rw [m_bind_assoc] at hokC
    repeat rw [m_bind_assoc]
    rcases hr' with ⟨hc0', hin', hou', hho', hbi'⟩
    refine m_bind_ok_same (by rw [hin', hla8']) hokC fun le1 h1 _ hok1 => ?_
    by_cases hle1 : le1 = true
    · subst hle1; simp only [↓reduceIte] at hok1 ⊢
      repeat rw [m_bind_assoc] at hok1
      repeat rw [m_bind_assoc]
      refine m_bind_ok_same (by rw [hou', hen8']) hok1 fun le2 h2 _ hok2 => ?_
      rw [m_pure_bind] at hok2 ⊢
      by_cases hle2 : le2 = true
      · subst hle2; simp only [↓reduceIte] at hok2 ⊢
        exact hih fl' l' h2 ⟨⟨hc0', hin', hou', hho', hbi'⟩, hla8', hen8', hbr'⟩ hok2
      · simp only [hle2, Bool.false_eq_true, ↓reduceIte] at hok2 ⊢
        exact hk fl' l' h2 ⟨hc0', hin', hou', hho', hbi'⟩ (fun hf => by simp [hbr'] at hf) hok2
    · simp only [hle1, Bool.false_eq_true, ↓reduceIte, m_pure_bind] at hok1 ⊢
      exact hk fl' l' h1 ⟨hc0', hin', hou', hho', hbi'⟩ (fun hf => by simp [hbr'] at hf) hok1
  have finishDolen (fl' : InflateFastLocals) (l' : L) (hx' : Heap)
      (hr' : Rel8Core c fl' l') (hhe' : fl'.here = l'.here)
      (hla8' : fl'.last8 = last8) (hen8' : fl'.end8 = end8) (hbr' : l'.broke = false)
      (k_step : LoopStep InflateFastLocals Empty → M β)
      (hk_brk_step : ∀ s₁', k_step (.brk s₁') = k₁ s₁')
      (hk_next_step : ∀ s₁', k_step (.next s₁') =
        ((do if ← Ptr.le s₁'.in_ s₁'.last8 then pure (← Ptr.le s₁'.out s₁'.end8, s₁') else pure (false, s₁')) >>=
          fun x => if x.1 then cont₁ x.2 else k₁ x.2))
      (hokD : (C.cdoWhile (dolen8 c) (fun l => pure (l.againL, l)) l' >>= fun sb₂ =>
        (do if sb₂.broke then pure (false, sb₂)
            else if ← Ptr.le sb₂.in_ last8 then pure (← Ptr.le sb₂.out end8, sb₂)
            else pure (false, sb₂)) >>= fun x => if x.1 then cont₂ x.2 else k₂ x.2) hx' = .ok res) :
      (clabel "dolen8" (dolen8BodyC c.strm) fl' >>= k_step) hx' = .ok res := by
    refine dolen8_of_ok c hr' hhe' hbr' k_step _ hokD
      (fun fl'' l'' h'' hr'' hbr'' hnml hok1 => by
        rw [hk_brk_step]
        simp only [hbr'', ↓reduceIte, m_pure_bind] at hok1
        exact hk fl'' l'' h'' hr'' (fun _ => hnml) hok1)
      (fun fl'' l'' h'' hr'' hla8'' hen8'' hbr'' hok1 => by
        rw [hk_next_step]
        exact evalCond fl'' l'' h'' hr'' (hla8''.trans hla8') (hen8''.trans hen8') hbr'' hok1)
  simp only [m_bind_pure_eq, m_bind_assoc_eq] at finishDolen evalCond
  simp only [inflate_fast_body8, refill64, load64_c_eq, cinline, m_bind_assoc_eq, m_pure_bind_eq] at hokS ⊢
  refine m_bind_ok_same (by rw [hin]) hokS fun word hWord _ wordRun => ?_
  refine m_bind_ok_same (by rw [hbi]) wordRun fun sh0 hShift _ shiftRun => ?_
  refine m_bind_ok_same (by rw [hin, hbi]) shiftRun fun in0 h_in0 _ hok1 => ?_
  let fl_in0 := { fl1 with hold8 := fl1.hold8 ||| sh0, in_ := in0, bits := fl1.bits ||| 56 }
  let l_in0 := { l1 with in_ := in0, hold := l1.hold ||| sh0, bits := l1.bits ||| 56 }
  have hr_in0 : Rel8Core c fl_in0 l_in0 := ⟨hc0, rfl, hou, by simp only [fl_in0, l_in0, hho], by simp only [fl_in0, l_in0, hbi]⟩
  refine m_bind_ok_same (by rw [hc0.lcode, hho, hc0.lmask]) hok1 fun hr0 h_hr0 _ hok4 => ?_
  refine m_bind_ok_same rfl hok4 fun e0 h_e0 _ hok5 => ?_
  by_cases he0 : (e0.op == 0) = true
  · simp only [he0, ↓reduceIte, m_bind_assoc_eq] at hok5 ⊢
    refine m_bind_ok_same (by rw [hho]) hok5 fun sh1 hShift _ shiftRun => ?_
    refine m_bind_ok_same (by rw [hou]) shiftRun fun _ hStore _ storeRun => ?_
    refine m_bind_ok_same (by rw [hou]) storeRun fun out1 h_out1 _ hok8 => ?_
    let fl_l1 := { fl_in0 with hold8 := sh1, bits := fl_in0.bits - e0.bits.toUInt32, out := out1 }
    let l_l1 := { l_in0 with hold := sh1, bits := l_in0.bits - e0.bits.toUInt32, out := out1 }
    refine m_bind_ok_same (by rw [hc0.lcode, hc0.lmask]) hok8 fun hr1 h_hr1 _ hok9 => ?_
    refine m_bind_ok_same rfl hok9 fun e1 h_e1 _ hok10 => ?_
    by_cases he1 : (e1.op == 0) = true
    · simp only [he1, ↓reduceIte, m_bind_assoc_eq] at hok10 ⊢
      refine m_bind_ok_same rfl hok10 fun sh2 hShift _ shiftRun => ?_
      refine m_bind_ok_same rfl shiftRun fun _ hStore _ storeRun => ?_
      refine m_bind_ok_same rfl storeRun fun out2 h_out2 _ hok13 => ?_
      let fl_l2 := { fl_l1 with hold8 := sh2, bits := fl_l1.bits - e1.bits.toUInt32, out := out2 }
      let l_l2 := { l_l1 with hold := sh2, bits := l_l1.bits - e1.bits.toUInt32, out := out2 }
      refine m_bind_ok_same (by rw [hc0.lcode, hc0.lmask]) hok13 fun hr2 h_hr2 _ hok14 => ?_
      refine m_bind_ok_same rfl hok14 fun e2 h_e2 _ hok15 => ?_
      by_cases he2 : (e2.op == 0) = true
      · simp only [he2, ↓reduceIte, m_bind_assoc_eq, m_pure_bind_eq] at hok15 ⊢
        refine m_bind_ok_same rfl hok15 fun sh3 hShift _ shiftRun => ?_
        refine m_bind_ok_same rfl shiftRun fun _ hStore _ storeRun => ?_
        refine m_bind_ok_same rfl storeRun fun out3 h_out3 _ hok18 => ?_
        exact evalCond { fl_l2 with here := hr2, hold8 := sh3, bits := fl_l2.bits - e2.bits.toUInt32, out := out3 }
          { l_l2 with here := hr2, hold := sh3, bits := l_l2.bits - e2.bits.toUInt32, out := out3 }
          h_out3 ⟨hc0, rfl, rfl, rfl, by simp only [fl_l2, l_l2, fl_l1, l_l1, fl_in0, l_in0, hbi]⟩ hla8 hen8 hbr hok18
      · simp only [he2, Bool.false_eq_true, ↓reduceIte, m_bind_assoc_eq] at hok15 ⊢
        refine m_bind_ok_same rfl hok15 fun word hWord _ wordRun => ?_
        refine m_bind_ok_same (by rw [hbi]) wordRun fun sh4 hShift _ shiftRun => ?_
        refine m_bind_ok_same (by rw [hbi]) shiftRun fun in1 h_in1 _ hok18 => ?_
        let ff := {fl_l2 with here := hr2, in_ := in1, hold8 := sh2 ||| sh4, bits := fl_l2.bits ||| 56}
        let ll := {l_l2 with here := hr2, in_ := in1, hold := sh2 ||| sh4, bits := l_l2.bits ||| 56}
        refine finishDolen ff ll h_in1
          ⟨hc0, rfl, rfl, rfl, by simp only [ff, ll, fl_l2, l_l2, fl_l1, l_l1, fl_in0, l_in0, hbi]⟩
          rfl hla8 hen8 hbr _ (fun _ => rfl) (fun _ => rfl) hok18
    · simp only [he1, Bool.false_eq_true, ↓reduceIte, m_bind_assoc_eq] at hok10 ⊢
      refine m_bind_ok_same rfl hok10 fun word hWord _ wordRun => ?_
      refine m_bind_ok_same (by rw [hbi]) wordRun fun sh4 hShift _ shiftRun => ?_
      refine m_bind_ok_same (by rw [hbi]) shiftRun fun in1 h_in1 _ hok13 => ?_
      let ff := {fl_l1 with here := hr1, in_ := in1, hold8 := sh1 ||| sh4, bits := fl_l1.bits ||| 56}
      let ll := {l_l1 with here := hr1, in_ := in1, hold := sh1 ||| sh4, bits := l_l1.bits ||| 56}
      refine finishDolen ff ll h_in1
        ⟨hc0, rfl, rfl, rfl, by simp only [ff, ll, fl_l1, l_l1, fl_in0, l_in0, hbi]⟩
        rfl hla8 hen8 hbr _ (fun _ => rfl) (fun _ => rfl) hok13
  · simp only [he0, Bool.false_eq_true, ↓reduceIte] at hok5 ⊢
    refine finishDolen { fl_in0 with here := hr0 } { l_in0 with here := hr0 } h_e0 hr_in0 rfl hla8 hen8 hbr
      _ (fun _ => rfl) (fun _ => rfl) hok5

private theorem copyOpC_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : RelCore c fl l) (hop : fl.op = l.op) (hfrom : fl.from_ = l.from_)
    (hlen : fl.len = l.len) (hdist : fl.dist = l.dist)
    (k₁ : InflateFastLocals → M β) (k₂ : L → M β)
    (hok : (copyOp l >>= k₂) h = .ok res)
    (hk : ∀ fl' l' h', RelCore c fl' l' → fl'.len = l'.len → fl'.dist = l'.dist →
      fl'.from_ = l'.from_ → l'.againL = l.againL → l'.againD = l.againD →
      l'.broke = l.broke → k₂ l' h' = .ok res → k₁ fl' h' = .ok res) :
    (copyOpC fl >>= k₁) h = .ok res := by
  let rel : InflateFastLocals → L → Prop := fun fl' l' =>
    RelCore c fl' l' ∧ fl'.op = l'.op ∧ fl'.from_ = l'.from_ ∧ fl'.len = l'.len ∧
    fl'.dist = l'.dist ∧ l'.againL = l.againL ∧ l'.againD = l.againD ∧ l'.broke = l.broke
  unfold copyOp at hok
  unfold copyOpC
  refine cdoWhile_go_cps_ok rel _ _ k₁ _ _ k₂ res ?_ C.fuel
    ⟨hctx, hop, hfrom, hlen, hdist, rfl, rfl, rfl⟩ hok
  intro fl1 l1 hx cont₁ cont₂ ⟨hrc, hop1, hfr1, hle1, hdi1, hal1, had1, hbr1⟩ hih hokS
  rcases hrc with ⟨hc0, hin, hou, hho, hbi⟩
  dsimp only at hokS ⊢
  rw [m_bind_assoc, hou, hfr1, copyBytePostInc_bind_eq]
  refine m_bind_ok_same rfl hokS fun l1a h1 hp1 hok1 => ?_
  rcases copy1_fields hp1 with ⟨hina, hhoa, hbia, _, hopa, hlena, hdista, hbrka, hagla, hagda⟩
  dsimp only at hok1 ⊢
  rw [m_pure_bind] at hok1 ⊢; dsimp only at hok1 ⊢
  rw [hopa] at hok1
  by_cases hopz : (l1.op - 1 != 0) = true
  · have hopz_fl : (fl1.op - 1 != 0) = true := by rw [hop1]; exact hopz
    simp only [hopz, hopz_fl, ↓reduceIte] at hok1 ⊢
    refine hih _ _ h1 ?_ hok1
    exact ⟨⟨hc0, hin.trans hina.symm, rfl, hho.trans hhoa.symm, hbi.trans hbia.symm⟩,
      congrArg (· - 1) hop1, rfl, hle1.trans hlena.symm, hdi1.trans hdista.symm,
      hagla.trans hal1, hagda.trans had1, hbrka.trans hbr1⟩
  · have hopz_fl : ¬((fl1.op - 1 != 0) = true) := by rw [hop1]; exact hopz
    simp only [hopz, hopz_fl, Bool.false_eq_true, ↓reduceIte] at hok1 ⊢
    refine hk _ {l1a with op := l1.op - 1} h1 ?_ ?_ ?_ rfl ?_ ?_ ?_ hok1
    · exact ⟨hc0, hin.trans hina.symm, rfl, hho.trans hhoa.symm, hbi.trans hbia.symm⟩
    · exact hle1.trans hlena.symm
    · exact hdi1.trans hdista.symm
    · exact hagla.trans hal1
    · exact hagda.trans had1
    · exact hbrka.trans hbr1

private theorem copyMatchC_len_end_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : RelCore c fl l) (hlen : fl.len = l.len) (hfrom : fl.from_ = l.from_)
    (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok :
      ((if (l.len != 0) = true then
          (do
            let l ← copy1 l
            if l.len > 1 then copy1 l else pure l)
        else pure l) >>= k₂) h = .ok res)
    (hk_next : ∀ fl' l' h', RelCore c fl' l' → l'.againL = l.againL → l'.againD = l.againD →
      l'.broke = false → k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (do
      let mut l := fl
      if l.len != 0 then
        let (out1, from1) ← copyBytePostInc l.out l.from_
        l := { l with out := out1, from_ := from1 }
        if l.len > 1 then
          let (out2, from2) ← copyBytePostInc l.out l.from_
          l := { l with out := out2, from_ := from2 }
      k₁ (.next l)) h = .ok res := by
  rcases hctx with ⟨hc0, hin, hou, hho, hbi⟩
  dsimp only at hok ⊢
  rw [hlen, hou, hfrom]
  by_cases hlz : (l.len != 0) = true
  · simp only [hlz, ↓reduceIte] at hok ⊢
    repeat rw [m_bind_assoc] at hok
    rw [copyBytePostInc_bind_eq]
    refine m_bind_ok_same rfl hok fun l1a h1 hp1 hok1 => ?_
    rcases copy1_fields hp1 with ⟨hina, hhoa, hbia, _, _, hlena, _, hbrka, hagla, hagda⟩
    dsimp only at hok1 ⊢
    rw [hlena] at hok1
    by_cases hl1 : l.len > 1
    · simp only [hl1, ↓reduceIte] at hok1 ⊢
      rw [copyBytePostInc_bind_eq]
      refine m_bind_ok_same rfl hok1 fun l1b h2 hp2 hok2 => ?_
      rcases copy1_fields hp2 with ⟨hinb, hhob, hbib, _, _, _, _, hbrkb, haglb, hagdb⟩
      dsimp only at hok2 ⊢
      refine hk_next _ _ h2 ?_ (haglb.trans hagla) (hagdb.trans hagda) (hbrkb.trans (hbrka.trans hbrk0)) hok2
      exact ⟨hc0, by rw [hin, hinb, hina], rfl, by rw [hho, hhob, hhoa], by rw [hbi, hbib, hbia]⟩
    · simp only [hl1, ↓reduceIte] at hok1 ⊢
      repeat rw [m_pure_bind] at hok1
      refine hk_next _ _ h1 ?_ hagla hagda (hbrka.trans hbrk0) hok1
      exact ⟨hc0, by rw [hin, hina], rfl, by rw [hho, hhoa], by rw [hbi, hbia]⟩
  · simp only [hlz] at hok ⊢
    repeat rw [m_pure_bind] at hok
    refine hk_next _ _ h ?_ rfl rfl hbrk0 hok
    exact ⟨hc0, hin, hou, hho, hbi⟩

private theorem copyMatchC_while_tail_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : RelCore c fl l) (hlen : fl.len = l.len) (hfrom : fl.from_ = l.from_)
    (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok :
      ((do
        let l ← C.cwhile (fun (l : L) => pure (l.len > 2, l))
          (fun (l : L) => do let l ← copy1 l; let l ← copy1 l; let l ← copy1 l; pure { l with len := l.len - 3 }) l
        if l.len != 0 then
          let l ← copy1 l
          if l.len > 1 then copy1 l else pure l
        else pure l) >>= k₂) h = .ok res)
    (hk_next : ∀ fl' l' h', RelCore c fl' l' → l'.againL = l.againL → l'.againD = l.againD →
      l'.broke = false → k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (do
      let l ← C.cwhile (fun (l : InflateFastLocals) => pure (l.len > 2, l))
        (fun (l : InflateFastLocals) => do
          let (out1, from1) ← copyBytePostInc l.out l.from_
          let (out2, from2) ← copyBytePostInc out1 from1
          let (out3, from3) ← copyBytePostInc out2 from2
          let l := { l with out := out3, from_ := from3 }
          pure { l with len := l.len - 3 }) fl
      if l.len != 0 then
        let (out1, from1) ← copyBytePostInc l.out l.from_
        let l := { l with out := out1, from_ := from1 }
        if l.len > 1 then
          let (out2, from2) ← copyBytePostInc l.out l.from_
          k₁ (.next { l with out := out2, from_ := from2 })
        else k₁ (.next l)
      else k₁ (.next l)) h = .ok res := by
  let rel : InflateFastLocals → L → Prop := fun fl' l' =>
    RelCore c fl' l' ∧ fl'.len = l'.len ∧ fl'.from_ = l'.from_ ∧
    l'.againL = l.againL ∧ l'.againD = l.againD ∧ l'.broke = false
  rw [m_bind_assoc] at hok
  change (C.cwhile.go _ _ C.fuel fl >>= _) h = .ok res
  change (C.cwhile.go _ _ C.fuel l >>= _) h = .ok res at hok
  refine cwhile_go_cps_ok rel _ _ _ _ _ _ res ?_ C.fuel ⟨hctx, hlen, hfrom, rfl, rfl, hbrk0⟩ hok
  intro fl1 l1 hx cont₁ cont₂ ⟨hrc, hle1, hfr1, hal1, had1, hbr1⟩ hih hokS
  rcases hrc with ⟨hc0, hin, hou, hho, hbi⟩
  dsimp only at hokS ⊢
  rw [m_pure_bind] at hokS; rw [m_pure_bind]; dsimp only at hokS ⊢
  by_cases hl2 : l1.len > 2
  · simp only [hl2, show fl1.len > 2 by rwa [hle1], decide_true, ↓reduceIte] at hokS ⊢
    rw [m_bind_assoc, hou, hfr1, copyBytePostInc_bind_eq]
    rw [m_bind_assoc] at hokS
    refine m_bind_ok_same rfl hokS fun l1a h1 hp1 hok1 => ?_
    rcases copy1_fields hp1 with ⟨hina, hhoa, hbia, _, _, hlena, _, hbrka, hagla, hagda⟩
    dsimp only at hok1 ⊢
    rw [m_bind_assoc, copyBytePostInc_bind_eq]; rw [m_bind_assoc] at hok1
    refine m_bind_ok_same rfl hok1 fun l1b h2 hp2 hok2 => ?_
    rcases copy1_fields hp2 with ⟨hinb, hhob, hbib, _, _, hlenb, _, hbrkb, haglb, hagdb⟩
    dsimp only at hok2 ⊢
    rw [m_bind_assoc, copyBytePostInc_bind_eq]; rw [m_bind_assoc] at hok2
    refine m_bind_ok_same rfl hok2 fun l1c h3 hp3 hok3 => ?_
    rcases copy1_fields hp3 with ⟨hinc, hhoc, hbic, _, _, hlenc, _, hbrkc, haglc, hagdc⟩
    dsimp only at hok3 ⊢
    simp only [m_pure_bind] at hok3 ⊢
    refine hih _ _ h3 ?_ hok3
    exact ⟨⟨hc0, by rw [hin, hinc, hinb, hina], rfl,
      by rw [hho, hhoc, hhob, hhoa], by rw [hbi, hbic, hbib, hbia]⟩,
      by rw [hle1, hlenc, hlenb, hlena], rfl,
      haglc.trans (haglb.trans (hagla.trans hal1)),
      hagdc.trans (hagdb.trans (hagda.trans had1)),
      hbrkc.trans (hbrkb.trans (hbrka.trans hbr1))⟩
  · simp only [hl2, show ¬fl1.len > 2 by rwa [hle1], decide_false, Bool.false_eq_true, ↓reduceIte] at hokS ⊢
    exact copyMatchC_len_end_of_ok c ⟨hc0, hin, hou, hho, hbi⟩ hle1 hfr1 hbr1 k₁ k₂ hokS
      (fun fl' l' h' hr' hag' had' hbr' hok' =>
        hk_next fl' l' h' hr' (hag'.trans hal1) (had'.trans had1) hbr' hok')

private theorem copyMatchC_doWhile_tail_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : RelCore c fl l) (hlen : fl.len = l.len) (hfrom : fl.from_ = l.from_)
    (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok :
      ((do
        let l ← C.cdoWhile
          (fun (l : L) => do let l ← copy1 l; let l ← copy1 l; let l ← copy1 l; pure { l with len := l.len - 3 })
          (fun (l : L) => pure (l.len > 2, l)) l
        if l.len != 0 then
          let l ← copy1 l
          if l.len > 1 then copy1 l else pure l
        else pure l) >>= k₂) h = .ok res)
    (hk_next : ∀ fl' l' h', RelCore c fl' l' → l'.againL = l.againL → l'.againD = l.againD →
      l'.broke = false → k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (do
      let l ← C.cdoWhile
        (fun (l : InflateFastLocals) => do
          let (out1, from1) ← copyBytePostInc l.out l.from_
          let (out2, from2) ← copyBytePostInc out1 from1
          let (out3, from3) ← copyBytePostInc out2 from2
          let l := { l with out := out3, from_ := from3 }
          pure { l with len := l.len - 3 })
        (fun (l : InflateFastLocals) => pure (l.len > 2, l)) fl
      if l.len != 0 then
        let (out1, from1) ← copyBytePostInc l.out l.from_
        let l := { l with out := out1, from_ := from1 }
        if l.len > 1 then
          let (out2, from2) ← copyBytePostInc l.out l.from_
          k₁ (.next { l with out := out2, from_ := from2 })
        else k₁ (.next l)
      else k₁ (.next l)) h = .ok res := by
  let rel : InflateFastLocals → L → Prop := fun fl' l' =>
    RelCore c fl' l' ∧ fl'.len = l'.len ∧ fl'.from_ = l'.from_ ∧
    l'.againL = l.againL ∧ l'.againD = l.againD ∧ l'.broke = false
  rw [m_bind_assoc] at hok
  change (C.cdoWhile.go _ _ C.fuel fl >>= _) h = .ok res
  change (C.cdoWhile.go _ _ C.fuel l >>= _) h = .ok res at hok
  refine cdoWhile_go_cps_ok rel _ _ _ _ _ _ res ?_ C.fuel ⟨hctx, hlen, hfrom, rfl, rfl, hbrk0⟩ hok
  intro fl1 l1 hx cont₁ cont₂ ⟨hrc, hle1, hfr1, hal1, had1, hbr1⟩ hih hokS
  rcases hrc with ⟨hc0, hin, hou, hho, hbi⟩
  dsimp only at hokS ⊢
  rw [m_bind_assoc, hou, hfr1, copyBytePostInc_bind_eq]
  rw [m_bind_assoc] at hokS
  refine m_bind_ok_same rfl hokS fun l1a h1 hp1 hok1 => ?_
  rcases copy1_fields hp1 with ⟨hina, hhoa, hbia, _, _, hlena, _, hbrka, hagla, hagda⟩
  dsimp only at hok1 ⊢
  rw [m_bind_assoc, copyBytePostInc_bind_eq]; rw [m_bind_assoc] at hok1
  refine m_bind_ok_same rfl hok1 fun l1b h2 hp2 hok2 => ?_
  rcases copy1_fields hp2 with ⟨hinb, hhob, hbib, _, _, hlenb, _, hbrkb, haglb, hagdb⟩
  dsimp only at hok2 ⊢
  rw [m_bind_assoc, copyBytePostInc_bind_eq]; rw [m_bind_assoc] at hok2
  refine m_bind_ok_same rfl hok2 fun l1c h3 hp3 hok3 => ?_
  rcases copy1_fields hp3 with ⟨hinc, hhoc, hbic, _, _, hlenc, _, hbrkc, haglc, hagdc⟩
  simp only [m_pure_bind] at hok3 ⊢
  rw [hlenc, hlenb, hlena] at hok3
  rw [hle1]
  let fc := {fl1 with out := l1c.out, from_ := l1c.from_, len := l1.len - 3}
  let lc := {l1c with len := l1.len - 3}
  have related : RelCore c fc lc := ⟨hc0, hin.trans (hinc.trans (hinb.trans hina)).symm, rfl,
    hho.trans (hhoc.trans (hhob.trans hhoa)).symm, hbi.trans (hbic.trans (hbib.trans hbia)).symm⟩
  by_cases hl2 : l1.len - 3 > 2
  · simp only [hl2, decide_true, ↓reduceIte] at hok3 ⊢
    exact hih fc lc h3 ⟨related, rfl, rfl, haglc.trans (haglb.trans (hagla.trans hal1)),
      hagdc.trans (hagdb.trans (hagda.trans had1)), hbrkc.trans (hbrkb.trans (hbrka.trans hbr1))⟩ hok3
  · simp only [hl2, decide_false, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
    exact copyMatchC_len_end_of_ok c related rfl rfl
      (hbrkc.trans (hbrkb.trans (hbrka.trans hbr1))) k₁ k₂ hok3
      (fun fl' l' h' hr' hag' had' hbr' hok' =>
        hk_next fl' l' h' hr' (hag'.trans (haglc.trans (haglb.trans (hagla.trans hal1))))
          (had'.trans (hagdc.trans (hagdb.trans (hagda.trans had1)))) hbr' hok')

private theorem copyMatchC_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : RelCore c fl l) (hdist : fl.dist = l.dist) (hlen : fl.len = l.len)
    (hop : fl.op = l.op) (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok : (copyMatch c l >>= k₂) h = .ok res)
    (hk_brk : ∀ fl' l' h', RelCore c fl' l' → l'.againL = l.againL → l'.againD = l.againD →
      l'.broke = true → k₂ l' h' = .ok res → k₁ (.brk fl') h' = .ok res)
    (hk_next : ∀ fl' l' h', RelCore c fl' l' → l'.againL = l.againL → l'.againD = l.againD →
      l'.broke = false → k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (copyMatchC c.strm fl >>= k₁) h = .ok res := by
  rcases hctx with ⟨hc0, hin, hou, hho, hbi⟩
  simp only [copyMatchC, copyMatch, cinline] at hok ⊢
  have afterWin (fl' : InflateFastLocals) (l' : L) (hx : Heap)
      (hr' : RelCore c fl' l') (hle' : fl'.len = l'.len) (hfr' : fl'.from_ = l'.from_)
      (hal' : l'.againL = l.againL) (had' : l'.againD = l.againD) (hbr' : l'.broke = false)
      (hwok :
        ((do
          let l ← C.cwhile (fun (l : L) => pure (l.len > 2, l))
            (fun (l : L) => do let l ← copy1 l; let l ← copy1 l; let l ← copy1 l; pure { l with len := l.len - 3 }) l'
          if l.len != 0 then
            let l ← copy1 l
            if l.len > 1 then copy1 l else pure l
          else pure l) >>= k₂) hx = .ok res) :
      (do
        let l ← C.cwhile (fun (l : InflateFastLocals) => pure (l.len > 2, l))
          (fun (l : InflateFastLocals) => do
            let (out1, from1) ← copyBytePostInc l.out l.from_
            let (out2, from2) ← copyBytePostInc out1 from1
            let (out3, from3) ← copyBytePostInc out2 from2
            let l := { l with out := out3, from_ := from3 }
            pure { l with len := l.len - 3 }) fl'
        if l.len != 0 then
          let (out1, from1) ← copyBytePostInc l.out l.from_
          let l := { l with out := out1, from_ := from1 }
          if l.len > 1 then
            let (out2, from2) ← copyBytePostInc l.out l.from_
            k₁ (.next { l with out := out2, from_ := from2 })
          else k₁ (.next l)
        else k₁ (.next l)) hx = .ok res :=
    copyMatchC_while_tail_of_ok c hr' hle' hfr' hbr' k₁ k₂ hwok
      (fun fl'' l'' h'' hr'' hag'' had'' hbr'' hok'' =>
        hk_next fl'' l'' h'' hr'' (hag''.trans hal') (had''.trans had') hbr'' hok'')
  simp only [ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at afterWin
  rw [hdist, hop]
  by_cases hd : l.dist > l.op
  · simp only [hd, ↓reduceIte] at hok ⊢
    refine whave_guard_bind_of_ok c fl.state (l.dist - l.op) fl.whave h res hc0.state hc0.whave
      _ _ k₂ _ _ k₁ hok ?_ ?_
    · intro h2 _ hok2
      repeat rw [m_pure_bind] at hok2
      repeat rw [m_pure_bind]
      exact hk_brk { fl with dist := l.dist, op := l.dist - l.op } { l with op := l.dist - l.op, broke := true } h2
        ⟨hc0, hin, hou, hho, hbi⟩ rfl rfl rfl hok2
    · intro hokW
      simp only [ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at hokW ⊢
      by_cases hwn0 : (c.wnext == 0) = true
      · have hwn0_fl : (fl.wnext == 0) = true := by rw [hc0.wnext]; exact hwn0
        simp only [hwn0, hwn0_fl, ↓reduceIte] at hokW ⊢
        repeat rw [m_bind_assoc] at hokW
        repeat rw [m_bind_assoc]
        refine m_bind_ok_same (by rw [hc0.window, hc0.wsize]) hokW fun f1 h1 _ hok1 => ?_
        by_cases hopl : l.dist - l.op < l.len
        · have hopl_fl : l.dist - l.op < fl.len := by rw [hlen]; exact hopl
          simp only [hopl, hopl_fl, ↓reduceIte] at hok1 ⊢
          repeat rw [m_bind_assoc] at hok1
          repeat rw [m_bind_assoc]
          refine @copyOpC_of_ok β c
            { fl with dist := l.dist, op := l.dist - l.op, from_ := f1, len := fl.len - (l.dist - l.op) }
            { l with op := l.dist - l.op, from_ := f1, len := l.len - (l.dist - l.op) }
            h1 res ⟨hc0, hin, hou, hho, hbi⟩ rfl rfl (by rw [hlen]) rfl _ _ hok1
            fun fl' l' h2 hr' hle' hdi' hfr' hal' had' hbr' hok2 => ?_
          repeat rw [m_bind_assoc] at hok2
          repeat rw [m_bind_assoc]
          refine m_bind_ok_same (by rw [hr'.2.2.1, hdi']) hok2 fun f2 h3 _ hok3 => ?_
          exact afterWin { fl' with from_ := f2 } { l' with from_ := f2 } h3 hr' hle' rfl hal' had' (hbr'.trans hbrk0) hok3
        · have hopl_fl : ¬(l.dist - l.op < fl.len) := by rw [hlen]; exact hopl
          simp only [hopl, hopl_fl, ↓reduceIte] at hok1 ⊢
          repeat rw [m_pure_bind] at hok1
          repeat rw [m_bind_assoc] at hok1
          repeat rw [m_pure_bind]
          repeat rw [m_bind_assoc]
          exact afterWin { fl with dist := l.dist, op := l.dist - l.op, from_ := f1 }
            { l with op := l.dist - l.op, from_ := f1 } h1 ⟨hc0, hin, hou, hho, hbi⟩ hlen rfl rfl rfl hbrk0 hok1
      · have hwn0_fl : ¬((fl.wnext == 0) = true) := by rw [hc0.wnext]; exact hwn0
        simp only [hwn0, hwn0_fl] at hokW ⊢
        by_cases hwnl : c.wnext < l.dist - l.op
        · have hwnl_fl : fl.wnext < l.dist - l.op := by rw [hc0.wnext]; exact hwnl
          simp only [hwnl, hwnl_fl, ↓reduceIte] at hokW ⊢
          repeat rw [m_bind_assoc] at hokW
          repeat rw [m_bind_assoc]
          refine m_bind_ok_same (by rw [hc0.window, hc0.wsize, hc0.wnext]) hokW fun f1 h1 _ hok1 => ?_
          by_cases hopl : l.dist - l.op - c.wnext < l.len
          · have hopl_fl : l.dist - l.op - fl.wnext < fl.len := by rw [hc0.wnext, hlen]; exact hopl
            simp only [hopl, hopl_fl, ↓reduceIte] at hok1 ⊢
            repeat rw [m_bind_assoc] at hok1
            repeat rw [m_bind_assoc]
            refine @copyOpC_of_ok β c
              { fl with dist := l.dist, op := l.dist - l.op - fl.wnext, from_ := f1, len := fl.len - (l.dist - l.op - fl.wnext) }
              { l with op := l.dist - l.op - c.wnext, from_ := f1, len := l.len - (l.dist - l.op - c.wnext) }
              h1 res ⟨hc0, hin, hou, hho, hbi⟩ (by rw [hc0.wnext]) rfl (by rw [hlen, hc0.wnext]) rfl _ _ hok1
              fun fl' l' h2 hr' hle' hdi' hfr' hal' had' hbr' hok2 => ?_
            by_cases hwnle : c.wnext < l'.len
            · have hwnle_fl : fl'.wnext < fl'.len := by rw [hr'.1.wnext, hle']; exact hwnle
              simp only [hwnle, hwnle_fl, ↓reduceIte] at hok2 ⊢
              repeat rw [m_bind_assoc] at hok2
              repeat rw [m_bind_assoc]
              refine @copyOpC_of_ok β c
                { fl' with from_ := fl'.window, op := fl'.wnext, len := fl'.len - fl'.wnext }
                { l' with from_ := c.window, op := c.wnext, len := l'.len - c.wnext }
                h2 res hr' hr'.1.wnext hr'.1.window (by rw [hle', hr'.1.wnext]) hdi' _ _ hok2
                fun fl'' l'' h3 hr'' hle'' hdi'' hfr'' hal'' had'' hbr'' hok3 => ?_
              repeat rw [m_bind_assoc] at hok3
              repeat rw [m_bind_assoc]
              refine m_bind_ok_same (by rw [hr''.2.2.1, hdi'']) hok3 fun f2 h4 _ hok4 => ?_
              exact afterWin { fl'' with from_ := f2 } { l'' with from_ := f2 } h4
                hr'' hle'' rfl (hal''.trans hal') (had''.trans had') (hbr''.trans (hbr'.trans hbrk0)) hok4
            · have hwnle_fl : ¬(fl'.wnext < fl'.len) := by rw [hr'.1.wnext, hle']; exact hwnle
              simp only [hwnle, hwnle_fl, ↓reduceIte] at hok2 ⊢
              repeat rw [m_pure_bind] at hok2
              repeat rw [m_bind_assoc] at hok2
              repeat rw [m_pure_bind]
              repeat rw [m_bind_assoc]
              exact afterWin { fl' with from_ := fl'.window } { l' with from_ := c.window } h2
                hr' hle' hr'.1.window hal' had' (hbr'.trans hbrk0) hok2
          · have hopl_fl : ¬(l.dist - l.op - fl.wnext < fl.len) := by rw [hc0.wnext, hlen]; exact hopl
            simp only [hopl, hopl_fl, ↓reduceIte] at hok1 ⊢
            repeat rw [m_pure_bind] at hok1
            repeat rw [m_bind_assoc] at hok1
            repeat rw [m_pure_bind]
            repeat rw [m_bind_assoc]
            exact afterWin { fl with dist := l.dist, op := l.dist - l.op - fl.wnext, from_ := f1 }
              { l with op := l.dist - l.op - c.wnext, from_ := f1 }
              h1 ⟨hc0, hin, hou, hho, hbi⟩ hlen rfl rfl rfl hbrk0 hok1
        · have hwnl_fl : ¬(fl.wnext < l.dist - l.op) := by rw [hc0.wnext]; exact hwnl
          simp only [hwnl, hwnl_fl, ↓reduceIte] at hokW ⊢
          repeat rw [m_bind_assoc] at hokW
          repeat rw [m_bind_assoc]
          refine m_bind_ok_same (by rw [hc0.window, hc0.wnext]) hokW fun f1 h1 _ hok1 => ?_
          by_cases hopl : l.dist - l.op < l.len
          · have hopl_fl : l.dist - l.op < fl.len := by rw [hlen]; exact hopl
            simp only [hopl, hopl_fl, ↓reduceIte] at hok1 ⊢
            repeat rw [m_bind_assoc] at hok1
            repeat rw [m_bind_assoc]
            refine @copyOpC_of_ok β c
              { fl with dist := l.dist, op := l.dist - l.op, from_ := f1, len := fl.len - (l.dist - l.op) }
              { l with op := l.dist - l.op, from_ := f1, len := l.len - (l.dist - l.op) }
              h1 res ⟨hc0, hin, hou, hho, hbi⟩ rfl rfl (by rw [hlen]) rfl _ _ hok1
              fun fl' l' h2 hr' hle' hdi' hfr' hal' had' hbr' hok2 => ?_
            repeat rw [m_bind_assoc] at hok2
            repeat rw [m_bind_assoc]
            refine m_bind_ok_same (by rw [hr'.2.2.1, hdi']) hok2 fun f2 h3 _ hok3 => ?_
            exact afterWin { fl' with from_ := f2 } { l' with from_ := f2 } h3 hr' hle' rfl hal' had' (hbr'.trans hbrk0) hok3
          · have hopl_fl : ¬(l.dist - l.op < fl.len) := by rw [hlen]; exact hopl
            simp only [hopl, hopl_fl, ↓reduceIte] at hok1 ⊢
            repeat rw [m_pure_bind] at hok1
            repeat rw [m_bind_assoc] at hok1
            repeat rw [m_pure_bind]
            repeat rw [m_bind_assoc]
            exact afterWin { fl with dist := l.dist, op := l.dist - l.op, from_ := f1 }
              { l with op := l.dist - l.op, from_ := f1 } h1 ⟨hc0, hin, hou, hho, hbi⟩ hlen rfl rfl rfl hbrk0 hok1
  · simp only [hd, ↓reduceIte] at hok ⊢
    repeat rw [m_bind_assoc] at hok
    repeat rw [m_bind_assoc]
    refine m_bind_ok_same (by rw [hou]) hok fun f1 h1 _ hok1 => ?_
    simp only [m_bind_pure_eq] at hok1
    simpa only [ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] using @copyMatchC_doWhile_tail_of_ok β c { fl with dist := l.dist, op := l.op, from_ := f1 } { l with from_ := f1 } h1 res
      ⟨hc0, hin, hou, hho, hbi⟩ hlen rfl hbrk0 k₁ k₂ hok1 hk_next

private theorem pull_via_bytes (l : L) :
    pull l = (do
      let p ← pullByte64 l.in_ l.hold l.bits
      pure {l with in_ := p.1, hold := p.2.1, bits := p.2.2}) := by
  funext h
  simp only [pull, pullByte64, shl64, m_bind_app]
  cases load8 l.in_ h with
  | error => rfl
  | ok p =>
    rcases p with ⟨byte, h₁⟩
    dsimp only
    cases Ptr.add l.in_ 1 h₁ with
    | error => rfl
    | ok q =>
      rcases q with ⟨ptr, h₂⟩
      dsimp only
      by_cases small : l.bits.toUInt64 < 64 <;> simp [small, ub]

private theorem dodist_copyMatch_step {β : Type} (c : Ctx)
    (fl' : InflateFastLocals) (l' : L) (hp : Heap) (res : β × Heap)
    (out1 beg1 lout1 : BPtr) (eop1 : UInt8) (eval2 : UInt16)
    (hctx : RelCore c fl' l') (hle' : fl'.len = l'.len)
    (hou1 : out1 = lout1) (hbeg1 : beg1 = c.beg)
    (hal0 : l'.againL = false) (hbr0 : l'.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok :
      ((do
        let m ← shl32 1 (eop1.toUInt32 &&& 15)
        let h2 ← shr64 l'.hold (eop1.toUInt32 &&& 15).toUInt64
        let d ← lout1.diff c.beg
        copyMatch c { l' with hold := h2, bits := l'.bits - (eop1.toUInt32 &&& 15),
                              op := d.toUInt64.toUInt32, dist := eval2.toUInt32 + (l'.hold.toUInt32 &&& (m - 1)),
                              againD := false }) >>= k₂) hp = .ok res)
    (hk_brk : ∀ fl'' l'' h'', RelCore c fl'' l'' → l''.againL = false → l''.againD = false → l''.broke = true →
      k₂ l'' h'' = .ok res → k₁ (.brk fl'') h'' = .ok res)
    (hk_next : ∀ fl'' l'' h'', RelCore c fl'' l'' → l''.againL = false → l''.againD = false → l''.broke = false →
      k₂ l'' h'' = .ok res → k₁ (.next fl'') h'' = .ok res) :
    ((do
      let m ← shl32 1 (eop1.toUInt32 &&& 15)
      let h2 ← shr64 fl'.hold (eop1.toUInt32 &&& 15).toUInt64
      let d ← out1.diff beg1
      copyMatchC c.strm { fl' with op := d.toUInt64.toUInt32, hold := h2,
                                   bits := fl'.bits - (eop1.toUInt32 &&& 15),
                                   dist := eval2.toUInt32 + (fl'.hold.toUInt32 &&& (m - 1)) }) >>= k₁) hp = .ok res := by
  rcases hctx with ⟨hc0, hin', hou', hho', hbi'⟩
  simp only [m_bind_assoc_eq] at hok ⊢
  refine m_bind_ok_same rfl hok fun mVal h_m _ hok5 => ?_
  refine m_bind_ok_same (by rw [hho']) hok5 fun sh1 h_sh1 _ hok6 => ?_
  refine m_bind_ok_same (by rw [hou1, hbeg1]) hok6 fun dVal h_df _ hok7 => ?_
  exact @copyMatchC_of_ok β c
    { fl' with op := dVal.toUInt64.toUInt32, hold := sh1,
               bits := fl'.bits - (eop1.toUInt32 &&& 15),
               dist := eval2.toUInt32 + (fl'.hold.toUInt32 &&& (mVal - 1)) }
    { l' with hold := sh1, bits := l'.bits - (eop1.toUInt32 &&& 15),
              op := dVal.toUInt64.toUInt32, dist := eval2.toUInt32 + (l'.hold.toUInt32 &&& (mVal - 1)),
              againD := false }
    h_df res ⟨hc0, hin', hou', rfl, by rw [hbi']⟩ (by rw [hho']) hle' rfl hbr0 k₁ k₂ hok7
    (fun fl'' l'' h'' hr'' hag'' had'' hbr'' hok8 =>
      hk_brk fl'' l'' h'' hr'' (hag''.trans hal0) had'' hbr'' hok8)
    (fun fl'' l'' h'' hr'' hag'' had'' hbr'' hok8 =>
      hk_next fl'' l'' h'' hr'' (hag''.trans hal0) had'' hbr'' hok8)

private theorem dodist_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : RelCore c fl l) (hhere : fl.here = l.here) (hlen : fl.len = l.len)
    (hagl : l.againL = false) (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok : (C.cdoWhile (dodist c) (fun l => pure (l.againD, l)) l >>= k₂) h = .ok res)
    (hk_brk : ∀ fl' l' h', RelCore c fl' l' → l'.againL = false → l'.broke = true →
      k₂ l' h' = .ok res → k₁ (.brk fl') h' = .ok res)
    (hk_next : ∀ fl' l' h', RelCore c fl' l' → l'.againL = false → l'.broke = false →
      k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (clabel "dodist" (dodistBodyC c.strm) fl >>= k₁) h = .ok res := by
  let rel : InflateFastLocals → L → Prop := fun fl l =>
    RelCore c fl l ∧ fl.here = l.here ∧ fl.len = l.len ∧ l.againL = false ∧ l.broke = false
  refine clabel_of_cdoWhile_ok rel (dodistBodyC c.strm) k₁ (dodist c)
    (fun l => pure (l.againD, l)) k₂ res ?_ C.fuel ⟨hctx, hhere, hlen, hagl, hbrk0⟩ hok
  intro fl1 l1 hx cont₁ cont₂ ⟨hrc, hhe, hle, hal, hbr⟩ hih hokS
  rcases hrc with ⟨hc0, hin, hou, hho, hbi⟩
  simp only [dodistBodyC, dodist, cinline, pull_via_bytes, ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at hokS ⊢
  refine m_bind_ok_same (by rw [hhe]) hokS fun e0 h_e0 _ hok1 => ?_
  refine m_bind_ok_same (by rw [hho]) hok1 fun sh0 h_sh0 _ hok2 => ?_
  refine m_bind_ok_same (by rw [hhe]) hok2 fun e1 h_e1 _ hok3 => ?_
  by_cases hop16 : (e1.op.toUInt32 &&& 16 != 0) = true
  · simp only [hop16, ↓reduceIte] at hok3 ⊢
    refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
    let resume := fun (v : L) => if v.againD then cont₂ v else k₂ v
    have brk (fl' : InflateFastLocals) (l' : L) (h' : Heap) (hr : RelCore c fl' l')
        (al : l'.againL = false) (ad : l'.againD = false) (br : l'.broke = true)
        (run : resume l' h' = .ok res) := hk_brk fl' l' h' hr al br (by simpa [resume, ad] using run)
    have next (fl' : InflateFastLocals) (l' : L) (h' : Heap) (hr : RelCore c fl' l')
        (al : l'.againL = false) (ad : l'.againD = false) (br : l'.broke = false)
        (run : resume l' h' = .ok res) := hk_next fl' l' h' hr al br (by simpa [resume, ad] using run)
    have finish (p : BPtr) (hold : UInt64) (bits : UInt32) (hp : Heap) :=
      dodist_copyMatch_step c {fl1 with in_ := p, hold, bits} {l1 with in_ := p, hold, bits}
        hp res fl1.out fl1.beg l1.out e1.op e2.val ⟨hc0, rfl, hou, rfl, rfl⟩ hle
        hou hc0.beg hal hbr k₁ resume
    simp only [m_bind_assoc_eq, resume] at finish
    rw [hbi, hin]
    by_cases one : l1.bits - e0.bits.toUInt32 < e1.op.toUInt32 &&& 15
    · simp only [one, ↓reduceIte] at hok4 ⊢
      refine m_bind_ok_same rfl hok4 fun a ha _ runA => ?_
      rcases a with ⟨p, v, n⟩
      dsimp only at runA ⊢
      by_cases two : n < e1.op.toUInt32 &&& 15
      · simp only [two, ↓reduceIte] at runA ⊢
        refine m_bind_ok_same rfl runA fun q hb _ runB => ?_
        rcases q with ⟨p', v', n'⟩
        exact finish p' v' n' hb runB brk next
      · simp only [two, ↓reduceIte] at runA ⊢
        exact finish p v n ha runA brk next
    · simp only [one, ↓reduceIte] at hok4 ⊢
      exact finish l1.in_ sh0 (l1.bits - e0.bits.toUInt32) h_e2 hok4 brk next
  · simp only [hop16, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
    by_cases hop64 : (e1.op.toUInt32 &&& 64 == 0) = true
    · simp only [hop64, ↓reduceIte] at hok3 ⊢
      refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
      have hcomm := comm_add_shl32_ok c.dcode e2.val.toNat 1 e1.op.toUInt32 h_e2 res _ hok4
      refine m_bind_ok_same rfl hcomm fun mVal h_m _ hok5 => ?_
      refine m_bind_ok_same (by rw [hc0.dcode]) hok5 fun h1 h_1 _ hok6 => ?_
      refine m_bind_ok_same rfl hok6 fun here1 h_hr _ hok7 => ?_
      refine hih _ _ h_hr ?_ hok7
      exact ⟨⟨hc0, hin, hou, rfl, by simp only [hbi]⟩, rfl, hle, hal, hbr⟩
    · simp only [hop64, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
      refine m_bind_ok_same (by rw [hc0.state, badDataC_eq]) hok3 fun _ h_bd _ hok4 => ?_
      refine hk_brk _ _ h_bd ?_ ?_ ?_ hok4
      · exact ⟨hc0, hin, hou, rfl, by simp only [hbi]⟩
      · exact hal
      · rfl

private theorem dolen_finishDist_step {β : Type} (c : Ctx)
    (fl'' : InflateFastLocals) (l'' : L) (hp' : Heap) (res : β × Heap)
    (hctx : RelCore c fl'' l'') (hle'' : fl''.len = l''.len)
    (hal'' : l''.againL = false) (hbr'' : l''.broke = false)
    (k₁ : GotoStep InflateFastLocals (LoopStep InflateFastLocals Empty) → M β) (k₂ : L → M β)
    (hdo' :
      ((do
        let h1 ← c.dcode.add (l''.hold &&& c.dmask.toUInt64).toNat
        C.cdoWhile (dodist c) (fun l => pure (l.againD, l)) { l'' with here := h1 }) >>= k₂) hp' = .ok res)
    (hk_brk : ∀ fl3 l3 h3, RelCore c fl3 l3 → l3.againL = false → l3.broke = true →
      k₂ l3 h3 = .ok res → k₁ (.done (.brk fl3)) h3 = .ok res)
    (hk_next : ∀ fl3 l3 h3, RelCore c fl3 l3 → l3.againL = false → l3.broke = false →
      k₂ l3 h3 = .ok res → k₁ (.done (.next fl3)) h3 = .ok res) :
    ((do
      let here1 ← fl''.dcode.add (fl''.hold &&& fl''.dmask.toUInt64).toNat
      let step ← clabel "dodist" (dodistBodyC c.strm) { fl'' with here := here1 }
      pure (GotoStep.done step)) >>= k₁) hp' = .ok res := by
  rcases hctx with ⟨hc0, hin'', hou'', hho'', hbi''⟩
  repeat rw [m_bind_assoc] at hdo'
  repeat rw [m_bind_assoc]
  refine m_bind_ok_same (by rw [hc0.dcode, hho'', hc0.dmask]) hdo' fun here1 h_hr _ hokD => ?_
  rw [m_bind_assoc]
  exact @dodist_of_ok β c { fl'' with here := here1 } { l'' with here := here1 } h_hr res
    ⟨hc0, hin'', hou'', hho'', hbi''⟩ rfl hle'' hal'' hbr'' _ k₂ hokD
    (fun fl3 l3 h3 hr3 hal3 hbr3 hok8 => by
      rw [m_pure_bind]
      exact hk_brk fl3 l3 h3 hr3 hal3 hbr3 hok8)
    (fun fl3 l3 h3 hr3 hal3 hbr3 hok8 => by
      rw [m_pure_bind]
      exact hk_next fl3 l3 h3 hr3 hal3 hbr3 hok8)

private theorem dolen_dist_chain {β : Type} (c : Ctx)
    (fl' : InflateFastLocals) (l' : L) (hp : Heap) (res : β × Heap)
    (hrc' : RelCore c fl' l') (hle' : fl'.len = l'.len) (hal' : l'.againL = false) (hbr' : l'.broke = false)
    (k₁ : GotoStep InflateFastLocals (LoopStep InflateFastLocals Empty) → M β) (k₂ : L → M β)
    (hdo :
      ((do
        let mut l : L := l'
        if l.bits < (15 : UInt32) then
          let l1 ← pull l
          l ← pull l1
        let h1 ← c.dcode.add (l.hold &&& c.dmask.toUInt64).toNat
        C.cdoWhile (dodist c) (fun l => pure (l.againD, l)) { l with here := h1 }) >>= k₂) hp = .ok res)
    (hk_brk : ∀ fl3 l3 h3, RelCore c fl3 l3 → l3.againL = false → l3.broke = true →
      k₂ l3 h3 = .ok res → k₁ (.done (.brk fl3)) h3 = .ok res)
    (hk_next : ∀ fl3 l3 h3, RelCore c fl3 l3 → l3.againL = false → l3.broke = false →
      k₂ l3 h3 = .ok res → k₁ (.done (.next fl3)) h3 = .ok res) :
    ((do
      let mut l : InflateFastLocals := fl'
      if l.bits < (15 : UInt32) then
        let (in1, hold1, bits1) ← pullByte64 l.in_ l.hold l.bits
        let (in2, hold2, bits2) ← pullByte64 in1 hold1 bits1
        l := { l with in_ := in2, hold := hold2, bits := bits2 }
      let here1 ← l.dcode.add (l.hold &&& l.dmask.toUInt64).toNat
      let step ← clabel "dodist" (dodistBodyC c.strm) { l with here := here1 }
      pure (GotoStep.done step)) >>= k₁) hp = .ok res := by
  have finish := @dolen_finishDist_step β c
  simp only [m_bind_assoc_eq, m_pure_bind_eq] at finish
  simp only [pull_via_bytes, ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at hdo ⊢
  rcases hrc' with ⟨hc, hin, hout, hhold, hbits⟩
  rw [hbits]
  by_cases refill : l'.bits < 15
  · simp only [refill, ↓reduceIte] at hdo ⊢
    refine m_bind_ok_same (by rw [hin, hhold]) hdo fun a ha _ runA => ?_
    rcases a with ⟨p, v, n⟩
    refine m_bind_ok_same rfl runA fun b hb _ runB => ?_
    rcases b with ⟨p', v', n'⟩
    exact finish {fl' with in_ := p', hold := v', bits := n'} {l' with in_ := p', hold := v', bits := n'}
      hb res ⟨hc, rfl, hout, rfl, rfl⟩ hle' hal' hbr' k₁ k₂ runB hk_brk hk_next
  · simp only [refill, ↓reduceIte] at hdo ⊢
    simpa only [hbits] using finish fl' l' hp res ⟨hc, hin, hout, hhold, hbits⟩ hle' hal' hbr' k₁ k₂ hdo hk_brk hk_next

private theorem dolen_shl_shr_chain {β : Type} (c : Ctx)
    (fl' : InflateFastLocals) (l' : L) (op0 : UInt32) (hp : Heap) (res : β × Heap)
    (hrc' : RelCore c fl' l') (hle' : fl'.len = l'.len) (hal' : l'.againL = false) (hbr' : l'.broke = false)
    (k₁ : GotoStep InflateFastLocals (LoopStep InflateFastLocals Empty) → M β) (k₂ : L → M β)
    (hlp :
      ((do
        let m ← shl32 1 op0
        let len' := l'.len + (l'.hold.toUInt32 &&& (m - 1))
        let hold' ← shr64 l'.hold op0.toUInt64
        let bits' := l'.bits - op0
        let mut l : L := { l' with len := len', hold := hold', bits := bits' }
        if l.bits < (15 : UInt32) then
          let l1 ← pull l
          l ← pull l1
        let h1 ← c.dcode.add (l.hold &&& c.dmask.toUInt64).toNat
        C.cdoWhile (dodist c) (fun l => pure (l.againD, l)) { l with here := h1 }) >>= k₂) hp = .ok res)
    (hk_brk : ∀ fl3 l3 h3, RelCore c fl3 l3 → l3.againL = false → l3.broke = true →
      k₂ l3 h3 = .ok res → k₁ (.done (.brk fl3)) h3 = .ok res)
    (hk_next : ∀ fl3 l3 h3, RelCore c fl3 l3 → l3.againL = false → l3.broke = false →
      k₂ l3 h3 = .ok res → k₁ (.done (.next fl3)) h3 = .ok res) :
    ((do
      let m ← shl32 1 op0
      let len' := fl'.len + (fl'.hold.toUInt32 &&& (m - 1))
      let h2 ← shr64 fl'.hold op0.toUInt64
      let bits' := fl'.bits - op0
      let mut l : InflateFastLocals := { fl' with len := len', hold := h2, bits := bits' }
      if l.bits < (15 : UInt32) then
        let (in1, hold1, bits1) ← pullByte64 l.in_ l.hold l.bits
        let (in2, hold2, bits2) ← pullByte64 in1 hold1 bits1
        l := { l with in_ := in2, hold := hold2, bits := bits2 }
      let here1 ← l.dcode.add (l.hold &&& l.dmask.toUInt64).toNat
      let step ← clabel "dodist" (dodistBodyC c.strm) { l with here := here1 }
      pure (GotoStep.done step)) >>= k₁) hp = .ok res := by
  rcases hrc' with ⟨hc0', hin', hou', hho', hbi'⟩
  simp only [m_bind_assoc_eq] at hlp ⊢
  refine m_bind_ok_same rfl hlp fun mVal h_m _ hok5 => ?_
  refine m_bind_ok_same (by rw [hho']) hok5 fun sh1 h_sh1 _ hok6 => ?_
  exact dolen_dist_chain c
    { fl' with len := fl'.len + (fl'.hold.toUInt32 &&& (mVal - 1)), hold := sh1, bits := fl'.bits - op0 }
    { l' with len := l'.len + (l'.hold.toUInt32 &&& (mVal - 1)), hold := sh1, bits := l'.bits - op0 }
    h_sh1 res ⟨hc0', hin', hou', rfl, by rw [hbi']⟩ (by rw [hle', hho']) hal' hbr' k₁ k₂ hok6 hk_brk hk_next

private theorem dolen_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : RelCore c fl l) (hhere : fl.here = l.here) (hbrk0 : l.broke = false)
    (k₁ : LoopStep InflateFastLocals Empty → M β) (k₂ : L → M β)
    (hok : (C.cdoWhile (dolen c) (fun l => pure (l.againL, l)) l >>= k₂) h = .ok res)
    (hk_brk : ∀ fl' l' h', RelCore c fl' l' → l'.broke = true →
      k₂ l' h' = .ok res → k₁ (.brk fl') h' = .ok res)
    (hk_next : ∀ fl' l' h', RelCore c fl' l' → l'.broke = false →
      k₂ l' h' = .ok res → k₁ (.next fl') h' = .ok res) :
    (clabel "dolen" (dolenBodyC c.strm) fl >>= k₁) h = .ok res := by
  let rel : InflateFastLocals → L → Prop := fun fl l =>
    RelCore c fl l ∧ fl.here = l.here ∧ l.broke = false
  refine clabel_of_cdoWhile_ok rel (dolenBodyC c.strm) k₁ (dolen c)
    (fun l => pure (l.againL, l)) k₂ res ?_ C.fuel ⟨hctx, hhere, hbrk0⟩ hok
  intro fl1 l1 hx cont₁ cont₂ ⟨hrc, hhe, hbr⟩ hih hokS
  rcases hrc with ⟨hc0, hin, hou, hho, hbi⟩
  let resume := fun (v : L) => if v.againL then cont₂ v else k₂ v
  let jump : GotoStep InflateFastLocals (LoopStep InflateFastLocals Empty) → M β
    | .goto v => cont₁ v
    | .done step => k₁ step
  have brk (f : InflateFastLocals) (v : L) (H : Heap) (rel : RelCore c f v)
      (al : v.againL = false) (br : v.broke = true) (run : resume v H = .ok res) :
      jump (.done (.brk f)) H = .ok res := hk_brk f v H rel br (by simpa [resume, al] using run)
  have next (f : InflateFastLocals) (v : L) (H : Heap) (rel : RelCore c f v)
      (al : v.againL = false) (br : v.broke = false) (run : resume v H = .ok res) :
      jump (.done (.next f)) H = .ok res := hk_next f v H rel br (by simpa [resume, al] using run)
  have extra := @dolen_shl_shr_chain β c
  have distance := @dolen_dist_chain β c
  simp only [pull_via_bytes, ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at extra distance
  simp only [dolenBodyC, dolen, cinline, pull_via_bytes, ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at hokS ⊢
  refine m_bind_ok_same (by rw [hhe]) hokS fun e0 h_e0 _ hok1 => ?_
  refine m_bind_ok_same (by rw [hho]) hok1 fun sh0 h_sh0 _ hok2 => ?_
  refine m_bind_ok_same (by rw [hhe]) hok2 fun e1 h_e1 _ hok3 => ?_
  by_cases lit : (e1.op.toUInt32 == 0) = true
  · simp only [lit, ↓reduceIte] at hok3 ⊢
    refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
    refine m_bind_ok_same (by rw [hou]) hok4 fun _ h_st _ hok5 => ?_
    refine m_bind_ok_same (by rw [hou]) hok5 fun out1 h_out _ hok6 => ?_
    refine hk_next _ _ h_out ?_ ?_ hok6
    · exact ⟨hc0, hin, rfl, rfl, by simp only [hbi]⟩
    · exact hbr
  · simp only [lit, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
    by_cases base : (e1.op.toUInt32 &&& 16 != 0) = true
    · simp only [base, ↓reduceIte] at hok3 ⊢
      refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
      let op := e1.op.toUInt32 &&& 15
      let f := fun (p : BPtr) (v : UInt64) (n : UInt32) => {fl1 with in_ := p, hold := v, bits := n, len := e2.val.toUInt32, op}
      let d := fun (p : BPtr) (v : UInt64) (n : UInt32) => {l1 with in_ := p, hold := v, bits := n, len := e2.val.toUInt32, op, againL := false}
      have step (p : BPtr) (v : UInt64) (n : UInt32) (H : Heap) :=
        extra (f p v n) (d p v n) op H res ⟨hc0, rfl, hou, rfl, rfl⟩ rfl rfl hbr jump resume
      rw [hbi, hin]
      by_cases more : (op != 0) = true
      · simp only [← show op = e1.op.toUInt32 &&& 15 from rfl, more, ↓reduceIte] at hok4 ⊢
        by_cases refill : l1.bits - e0.bits.toUInt32 < op
        · simp only [refill, ↓reduceIte] at hok4 ⊢
          refine m_bind_ok_same rfl hok4 fun q hp _ run => ?_
          rcases q with ⟨p, v, n⟩
          exact step p v n hp run brk next
        · simp only [refill, ↓reduceIte] at hok4 ⊢
          exact step l1.in_ sh0 (l1.bits - e0.bits.toUInt32) h_e2 hok4 brk next
      · simp only [← show op = e1.op.toUInt32 &&& 15 from rfl, more, Bool.false_eq_true, ↓reduceIte] at hok4 ⊢
        exact distance (f l1.in_ sh0 (l1.bits - e0.bits.toUInt32)) (d l1.in_ sh0 (l1.bits - e0.bits.toUInt32))
          h_e2 res ⟨hc0, rfl, hou, rfl, rfl⟩ rfl rfl hbr jump resume hok4 brk next
    · simp only [base, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
      by_cases link : (e1.op.toUInt32 &&& 64 == 0) = true
      · simp only [link, ↓reduceIte] at hok3 ⊢
        refine m_bind_ok_same (by rw [hhe]) hok3 fun e2 h_e2 _ hok4 => ?_
        have hcomm := comm_add_shl32_ok c.lcode e2.val.toNat 1 e1.op.toUInt32 h_e2 res _ hok4
        refine m_bind_ok_same rfl hcomm fun mVal h_m _ hok5 => ?_
        refine m_bind_ok_same (by rw [hc0.lcode]) hok5 fun h1 h_1 _ hok6 => ?_
        refine m_bind_ok_same rfl hok6 fun here1 h_hr _ hok7 => ?_
        refine hih _ _ h_hr ?_ hok7
        exact ⟨⟨hc0, hin, hou, rfl, by simp only [hbi]⟩, rfl, hbr⟩
      · simp only [link, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
        by_cases endBlock : (e1.op.toUInt32 &&& 32 != 0) = true
        · simp only [endBlock, ↓reduceIte] at hok3 ⊢
          refine m_bind_ok_same (by rw [hc0.state]) hok3 fun s h_s _ hok4 => ?_
          refine m_bind_ok_same (by rw [hc0.state]) hok4 fun _ h_st _ hok5 => ?_
          refine hk_brk _ _ h_st ?_ ?_ hok5
          · exact ⟨hc0, hin, hou, rfl, by simp only [hbi]⟩
          · rfl
        · simp only [endBlock, Bool.false_eq_true, ↓reduceIte] at hok3 ⊢
          refine m_bind_ok_same (by rw [hc0.state, badDataC_eq]) hok3 fun _ h_bd _ hok4 => ?_
          refine hk_brk _ _ h_bd ?_ ?_ hok4
          · exact ⟨hc0, hin, hou, rfl, by simp only [hbi]⟩
          · rfl

private theorem body_of_ok {β : Type} (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : β × Heap}
    (hctx : RelCore c fl l) (hbrk0 : l.broke = false)
    (k₁ : InflateFastLocals → M β) (k₂ : L → M β)
    (hok :
      (C.cdoWhile (inflate_fast_body c)
        (fun l => do
          if l.broke then pure (false, l)
          else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
          else pure (false, l)) l >>= k₂) h = .ok res)
    (hk : ∀ fl' l' h', RelCore c fl' l' → k₂ l' h' = .ok res → k₁ fl' h' = .ok res) :
    (C.cdoWhileBrk
      (fun (l : InflateFastLocals) => do
        let mut l := l
        if l.bits < 15 then
          let (in1, hold1, bits1) ← pullByte64 l.in_ l.hold l.bits
          let (in2, hold2, bits2) ← pullByte64 in1 hold1 bits1
          l := { l with in_ := in2, hold := hold2, bits := bits2 }
        let h0 ← cinline (l.lcode.add (l.hold &&& l.lmask.toUInt64).toNat)
        l := { l with here := h0 }
        clabel "dolen" (dolenBodyC c.strm) l)
      (fun (l : InflateFastLocals) => do
        if ← Ptr.lt l.in_ l.last then pure (← Ptr.lt l.out l.end_, l)
        else pure (false, l)) fl >>= k₁) h = .ok res := by
  rw [cdoWhileBrk_bind_eq]
  let rel : InflateFastLocals → L → Prop := fun fl l => RelCore c fl l ∧ l.broke = false
  refine cdoWhileBrk_of_cdoWhile_ok rel _ _ k₁ _ _ k₂ res ?_ C.fuel ⟨hctx, hbrk0⟩ hok
  intro fl1 l1 hx cont₁ cont₂ ⟨hrc, hbr⟩ hih hokS
  rcases hrc with ⟨hc0, hin, hou, hho, hbi⟩
  have afterBits (fl' : InflateFastLocals) (l' : L) (hp : Heap)
      (hr' : RelCore c fl' l') (hbr' : l'.broke = false)
      (k_step : LoopStep InflateFastLocals Empty → M β)
      (hk_brk_step : ∀ s₁', k_step (.brk s₁') = k₁ s₁')
      (hk_next_step : ∀ s₁', k_step (.next s₁') =
        ((do if ← Ptr.lt s₁'.in_ s₁'.last then pure (← Ptr.lt s₁'.out s₁'.end_, s₁') else pure (false, s₁')) >>=
          fun x => if x.1 then cont₁ x.2 else k₁ x.2))
      (hokB :
        ((do
          let here1 ← c.lcode.add (l'.hold &&& c.lmask.toUInt64).toNat
          C.cdoWhile (dolen c) (fun l => pure (l.againL, l)) { l' with here := here1 }) >>=
            fun sb2 => (do
              if sb2.broke then pure (false, sb2)
              else if ← Ptr.lt sb2.in_ c.last then pure (← Ptr.lt sb2.out c.end_, sb2)
              else pure (false, sb2)) >>= fun x => if x.1 then cont₂ x.2 else k₂ x.2) hp = .ok res) :
      ((do
        let h0 ← fl'.lcode.add (fl'.hold &&& fl'.lmask.toUInt64).toNat
        clabel "dolen" (dolenBodyC c.strm) { fl' with here := h0 }) >>= k_step) hp = .ok res := by
    rcases hr' with ⟨hc0', hin', hou', hho', hbi'⟩
    repeat rw [m_bind_assoc] at hokB
    repeat rw [m_bind_assoc]
    refine m_bind_ok_same (by rw [hc0'.lcode, hho', hc0'.lmask]) hokB fun here1 h_hr _ hok1 => ?_
    refine @dolen_of_ok β c { fl' with here := here1 } { l' with here := here1 } h_hr res
      ⟨hc0', hin', hou', hho', hbi'⟩ rfl hbr' k_step
      (fun sb2 => (do
        if sb2.broke then pure (false, sb2)
        else if ← Ptr.lt sb2.in_ c.last then pure (← Ptr.lt sb2.out c.end_, sb2)
        else pure (false, sb2)) >>= fun x => if x.1 then cont₂ x.2 else k₂ x.2) hok1
      (fun fl'' l'' h'' hr'' hbr'' hok2 => by
        rw [hk_brk_step]
        simp only [hbr'', ↓reduceIte, m_pure_bind] at hok2
        exact hk fl'' l'' h'' hr'' hok2)
      (fun fl'' l'' h'' hr'' hbr'' hok2 => by
        rw [hk_next_step]
        simp only [hbr'', Bool.false_eq_true, ↓reduceIte] at hok2
        repeat rw [m_bind_assoc] at hok2
        repeat rw [m_bind_assoc]
        rcases hr'' with ⟨hc0'', hin'', hou'', hho'', hbi''⟩
        refine m_bind_ok_same (by rw [hin'', hc0''.last]) hok2 fun lt1 h1 _ hok3 => ?_
        by_cases hlt1 : lt1 = true
        · subst hlt1; simp only [↓reduceIte] at hok3 ⊢
          repeat rw [m_bind_assoc] at hok3
          repeat rw [m_bind_assoc]
          refine m_bind_ok_same (by rw [hou'', hc0''.end_]) hok3 fun lt2 h2 _ hok4 => ?_
          rw [m_pure_bind] at hok4 ⊢
          by_cases hlt2 : lt2 = true
          · subst hlt2; simp only [↓reduceIte] at hok4 ⊢
            exact hih _ _ h2 ⟨⟨hc0'', hin'', hou'', hho'', hbi''⟩, hbr''⟩ hok4
          · simp only [hlt2, Bool.false_eq_true, ↓reduceIte] at hok4 ⊢
            exact hk fl'' l'' h2 ⟨hc0'', hin'', hou'', hho'', hbi''⟩ hok4
        · simp only [hlt1, Bool.false_eq_true, ↓reduceIte, m_pure_bind] at hok3 ⊢
          exact hk fl'' l'' h1 ⟨hc0'', hin'', hou'', hho'', hbi''⟩ hok3)
  simp only [ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at afterBits
  simp only [inflate_fast_body, cinline, pull_via_bytes, ite_bind_eq, m_bind_assoc_eq, m_pure_bind_eq] at hokS ⊢
  by_cases refill : l1.bits < 15
  · have refill' : fl1.bits < 15 := hbi ▸ refill
    simp only [refill, refill', ↓reduceIte] at hokS ⊢
    refine m_bind_ok_same (by rw [hin, hho, hbi]) hokS fun q hq _ got => ?_
    rcases q with ⟨p, v, n⟩
    refine m_bind_ok_same rfl got fun q' hq' _ got' => ?_
    rcases q' with ⟨p', v', n'⟩
    exact afterBits {fl1 with in_ := p', hold := v', bits := n'} {l1 with in_ := p', hold := v', bits := n'}
      hq' ⟨hc0, rfl, hou, rfl, rfl⟩ hbr _ (fun _ => rfl) (fun _ => rfl) got'
  · have refill' : ¬fl1.bits < 15 := hbi ▸ refill
    simp only [refill, refill', ↓reduceIte] at hokS ⊢
    exact afterBits fl1 l1 hx ⟨hc0, hin, hou, hho, hbi⟩ hbr _ (fun _ => rfl) (fun _ => rfl) hokS

private theorem zstream_get_put_same (r : ZStreamRef) (h : Heap) (v₀ v₁ : ZStream)
    (hg : r.get h = some v₀) :
    r.get (r.put h v₁) = some v₁ := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.get, ZStreamRef.put] at hg ⊢
    cases hs : h.streams.get i with
    | none => simp [hs] at hg
    | some _ => exact C.upd_same h.streams i (some v₁)
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get, ZStreamRef.put] at hg ⊢
    cases hgz : h.gzstates.get i with
    | none => simp [hgz] at hg
    | some gz => rw [C.upd_same]; rfl

private theorem zstream_put_put (r : ZStreamRef) (h : Heap) (v₁ v₂ : ZStream) :
    r.put (r.put h v₁) v₂ = r.put h v₂ := by
  cases r with
  | tab i =>
    dsimp only [ZStreamRef.put]
    cases hs : h.streams i with
    | none => simp [hs]
    | some _ => simp [upd_upd]
  | in_gzstate_strm i =>
    dsimp only [ZStreamRef.put]
    cases hgz : h.gzstates i with
    | none => simp [hgz]
    | some gz => simp [upd_upd]

private theorem avail_calc_heap (p q : BPtr) (bias : Int) {h : Heap} {v : Int64} {h' : Heap}
    (hok : (do
      if ← Ptr.lt p q then do let d ← q.diff p; chk64 (bias + d.toInt)
      else do let d ← p.diff q; chk64 (bias - d.toInt)) h = .ok (v, h')) : h' = h := by
  rw [m_bind_app] at hok
  cases hlt : Ptr.lt p q h with
  | error e => simp [hlt] at hok
  | ok p1 =>
    rcases p1 with ⟨b, h1⟩
    have hh1 := ptr_lt_heap hlt; subst h1
    simp only [hlt] at hok
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, m_bind_app] at hok
      cases hdf : p.diff q h with
      | error e => simp [hdf] at hok
      | ok p2 =>
        rcases p2 with ⟨d, h2⟩
        have hh2 := ptr_diff_heap hdf; subst h2
        simp only [hdf] at hok
        exact chk64_heap _ hok
    · simp only [↓reduceIte, m_bind_app] at hok
      cases hdf : q.diff p h with
      | error e => simp [hdf] at hok
      | ok p2 =>
        rcases p2 with ⟨d, h2⟩
        have hh2 := ptr_diff_heap hdf; subst h2
        simp only [hdf] at hok
        exact chk64_heap _ hok

private theorem avail_calc_zstream_put (r : ZStreamRef) (z : ZStream) (p q : BPtr) (bias : Int)
    {h : Heap} {v : Int64}
    (hok : (do
      if ← Ptr.lt p q then do let d ← q.diff p; chk64 (bias + d.toInt)
      else do let d ← p.diff q; chk64 (bias - d.toInt)) h = .ok (v, h)) :
    (do
      if ← Ptr.lt p q then do let d ← q.diff p; chk64 (bias + d.toInt)
      else do let d ← p.diff q; chk64 (bias - d.toInt)) (r.put h z) = .ok (v, r.put h z) := by
  rw [m_bind_app] at hok ⊢
  cases hlt : Ptr.lt p q h with
  | error e => simp [hlt] at hok
  | ok p1 =>
    rcases p1 with ⟨b, h1⟩
    have hh1 := ptr_lt_heap hlt; subst h1
    rw [ptr_lt_zstream_put r z p q hlt]
    simp only [hlt] at hok ⊢
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, m_bind_app] at hok ⊢
      cases hdf : p.diff q h with
      | error e => simp [hdf] at hok
      | ok p2 =>
        rcases p2 with ⟨d, h2⟩
        have hh2 := ptr_diff_heap hdf; subst h2
        rw [ptr_diff_zstream_put r z p q hdf]
        simp only [hdf] at hok ⊢
        have hc := chk64_heap _ hok
        unfold chk64 at hok ⊢
        by_cases hbd : -9223372036854775808 ≤ bias - d.toInt ∧ bias - d.toInt ≤ 9223372036854775807
        · simp [hbd, pure] at hok ⊢; exact hok
        · simp [hbd, ub] at hok
    · simp only [↓reduceIte, m_bind_app] at hok ⊢
      cases hdf : q.diff p h with
      | error e => simp [hdf] at hok
      | ok p2 =>
        rcases p2 with ⟨d, h2⟩
        have hh2 := ptr_diff_heap hdf; subst h2
        rw [ptr_diff_zstream_put r z q p hdf]
        simp only [hdf] at hok ⊢
        have hc := chk64_heap _ hok
        unfold chk64 at hok ⊢
        by_cases hbd : -9223372036854775808 ≤ bias + d.toInt ∧ bias + d.toInt ≤ 9223372036854775807
        · simp [hbd, pure] at hok ⊢; exact hok
        · simp [hbd, ub] at hok

private theorem inflate_fast_leave_of_ok (c : Ctx) {fl : InflateFastLocals} {l : L}
    {h : Heap} {res : Unit × Heap}
    (hctx : RelCore c fl l)
    (hok :
      (do
        let len := l.bits >>> 3
        let in_ ← subn l.in_ len
        let bits := l.bits - (len <<< 3)
        let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
        let ai : Int64 ←
          if ← Ptr.lt in_ c.last then do let d ← c.last.diff in_; chk64 (5 + d.toInt)
          else do let d ← in_.diff c.last; chk64 (5 - d.toInt)
        let ao : Int64 ←
          if ← Ptr.lt l.out c.end_ then do let d ← c.end_.diff l.out; chk64 (257 + d.toInt)
          else do let d ← l.out.diff c.end_; chk64 (257 - d.toInt)
        let sm ← ldZStream c.strm
        stZStream c.strm { sm with next_in := in_, next_out := l.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32 }
        let s ← ldInflateState c.state
        stInflateState c.state { s with hold, bits }) h = .ok res) :
    (do
      let mut l := fl
      l := { l with len := l.bits >>> 3 }
      let in1 ← cinline (subn l.in_ l.len)
      l := { l with in_ := in1, bits := l.bits - (l.len <<< 3) }
      let msk ← cinline (shl32 1 l.bits)
      l := { l with hold := l.hold &&& (msk - 1).toUInt64 }
      let sm2 ← ldZStream c.strm
      stZStream c.strm { sm2 with next_in := l.in_, next_out := l.out }
      let ai ← cinline (do
        if ← Ptr.lt l.in_ l.last then do let d ← l.last.diff l.in_; chk64 (5 + d.toInt)
        else do let d ← l.in_.diff l.last; chk64 (5 - d.toInt))
      let sm3 ← ldZStream c.strm
      stZStream c.strm { sm3 with avail_in := ai.toUInt64.toUInt32 }
      let ao ← cinline (do
        if ← Ptr.lt l.out l.end_ then do let d ← l.end_.diff l.out; chk64 (257 + d.toInt)
        else do let d ← l.out.diff l.end_; chk64 (257 - d.toInt))
      let sm4 ← ldZStream c.strm
      stZStream c.strm { sm4 with avail_out := ao.toUInt64.toUInt32 }
      let s2 ← ldInflateState l.state
      stInflateState l.state { s2 with hold := l.hold, bits := l.bits }) h = .ok res := by
  rcases hctx with ⟨hc0, hin, hou, hho, hbi⟩
  dsimp only [cinline] at hok ⊢
  rw [hbi, hin, hou, hho, hc0.last, hc0.end_, hc0.state]
  refine m_bind_ok_same rfl hok fun in1 h₁ _ run₁ => ?_
  refine m_bind_ok_same rfl run₁ fun mask h₂ _ run₂ => ?_
  let avail (p q : BPtr) (bias : Int) : M Int64 := do
    if ← Ptr.lt p q then do let d ← q.diff p; chk64 (bias + d.toInt)
    else do let d ← p.diff q; chk64 (bias - d.toInt)
  let bits := l.bits - ((l.bits >>> 3) <<< 3)
  let hold := l.hold &&& (mask - 1).toUInt64
  let publish (ai ao : Int64) : M Unit := do
    let z ← ldZStream c.strm
    stZStream c.strm {z with next_in := in1, next_out := l.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32}
    let s ← ldInflateState c.state
    stInflateState c.state {s with hold, bits}
  have seq : (do
        let ai ← avail in1 c.last 5
        let ao ← avail l.out c.end_ 257
        publish ai ao) h₂ = .ok res := by
    simpa only [avail, publish, bits, hold, ite_bind_eq, m_bind_assoc_eq] using run₂
  rw [m_bind_app] at seq
  cases hai : avail in1 c.last 5 h₂ with
  | error => simp [hai] at seq
  | ok p =>
    rcases p with ⟨ai, H⟩
    have eq := avail_calc_heap _ _ 5 hai
    subst H
    simp only [hai] at seq
    rw [m_bind_app] at seq
    cases hao : avail l.out c.end_ 257 h₂ with
    | error => simp [hao] at seq
    | ok q =>
      rcases q with ⟨ao, H⟩
      have eq := avail_calc_heap _ _ 257 hao
      subst H
      simp only [hao] at seq
      unfold publish at seq
      cases ref : c.strm with
      | none => simp [ref, ldZStream] at seq
      | some r =>
        rw [ref] at seq
        rw [m_bind_app] at seq ⊢
        cases live : r.get h₂ with
        | none => simp [ldZStream, live] at seq
        | some z =>
          have writable : r.isRo = false := by cases r <;> rfl
          let mid := {z with next_in := in1, next_out := l.out}
          rw [ldZStream_ok live] at seq ⊢
          dsimp only at seq ⊢
          rw [m_bind_app, stZStream_ok live writable] at seq ⊢
          dsimp only at seq ⊢
          rw [m_bind_app, avail_calc_zstream_put r mid in1 c.last 5 hai]
          dsimp only
          have get := zstream_get_put_same r h₂ z mid live
          rw [m_bind_app, ldZStream_ok get]
          dsimp only
          rw [m_bind_app, stZStream_ok get writable]
          dsimp only
          let counted := {mid with avail_in := ai.toUInt64.toUInt32}
          rw [zstream_put_put r h₂ mid]
          rw [m_bind_app, avail_calc_zstream_put r counted l.out c.end_ 257 hao]
          dsimp only
          have get' := zstream_get_put_same r h₂ z counted live
          rw [m_bind_app, ldZStream_ok get']
          dsimp only
          rw [m_bind_app, stZStream_ok get' writable]
          dsimp only
          rw [zstream_put_put r h₂ counted]
          exact seq

private theorem forward_then_leave {σ α : Type} (name : String) (before : M (FwdStep σ))
    (skipped : σ → M σ) (leave : σ → M α) : cforwardLabel name before skipped leave = (do
      let step ← before
      let v ← match step with | .goto x => pure x | .fall x => skipped x
      leave v) := by
  funext h
  unfold cforwardLabel
  refine m_bind_congr rfl fun step H _ => ?_
  cases step <;> rfl

theorem inflate_fast_c_of_ok (strm : ZStreamPtr) (start : UInt32) {h : Heap} {after : Heap}
    (hok : C.run (inflate_fast strm start) h = .ok ((), after)) :
    C.run (inflate_fast_c strm start) h = .ok ((), after) := by
  change C.run (inflate_fast strm start) h = .ok ((), after) at hok
  dsimp only [C.run] at hok ⊢
  simp only [inflate_fast_c, inflate_fast, cinline, forward_then_leave, cdecl_eq, m_pure_bind_eq, m_bind_assoc_eq] at hok ⊢
  refine m_bind_ok_same rfl hok fun sm h1 _ hok1 => ?_
  refine m_bind_ok_same rfl hok1 fun state h2 _ hok2 => ?_
  refine m_bind_ok_same rfl hok2 fun last0 h3 _ hok3 => ?_
  refine m_bind_ok_same rfl hok3 fun beg0 h4 _ hok4 => ?_
  refine m_bind_ok_same rfl hok4 fun end0 h5 _ hok5 => ?_
  refine m_bind_ok_same rfl hok5 fun s h6 _ hok6 => ?_
  have afterBack (back0 : Bool) (hx0 : Heap)
      (hokB :
        (do
          let lmask := (← shl32 1 s.lenbits) - 1
          let dmask := (← shl32 1 s.distbits) - 1
          let c : Ctx := { strm, state, last := last0, beg := beg0, end_ := end0, wsize := s.wsize,
                           whave := s.whave, wnext := s.wnext, window := s.window, lcode := s.lencode,
                           dcode := s.distcode, lmask, dmask }
          let l : L := { in_ := sm.next_in, out := sm.next_out, hold := s.hold, bits := s.bits, here := default,
                         op := 0, len := 0, dist := 0, from_ := default, broke := false, againL := false, againD := false }
          let (l, skip8) ←
            if !back0 && sm.avail_in >= 16 && sm.avail_out >= 2 + 258 + 15 then
              let last8 ← sm.next_in.add (sm.avail_in - 16).toNat
              let end8 ← sm.next_out.add (sm.avail_out - (2 + 258 + 15)).toNat
              let l ← cdoWhile (inflate_fast_body8 c)
                (fun l => do
                  if l.broke then pure (false, l)
                  else if ← Ptr.le l.in_ last8 then pure (← Ptr.le l.out end8, l)
                  else pure (false, l)) l
              let len := l.bits >>> 3
              let in_ ← subn l.in_ len
              let bits := l.bits - (len <<< 3)
              let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
              let l := { l with in_, bits, hold, len }
              let st ← ldInflateState state
              let skip8 ←
                if st.mode != LEN then pure true
                else pure !(← Ptr.lt l.out end0)
              pure (l, skip8)
            else
              pure (l, false)
          let l ←
            if skip8 then pure l
            else
              cdoWhile (inflate_fast_body c)
                (fun l => do
                  if l.broke then pure (false, l)
                  else if ← Ptr.lt l.in_ last0 then pure (← Ptr.lt l.out end0, l)
                  else pure (false, l)) l
          let len := l.bits >>> 3
          let in_ ← subn l.in_ len
          let bits := l.bits - (len <<< 3)
          let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
          let ai : Int64 ←
            if ← Ptr.lt in_ last0 then do let d ← last0.diff in_; chk64 (5 + d.toInt)
            else do let d ← in_.diff last0; chk64 (5 - d.toInt)
          let ao : Int64 ←
            if ← Ptr.lt l.out end0 then do let d ← end0.diff l.out; chk64 (257 + d.toInt)
            else do let d ← l.out.diff end0; chk64 (257 - d.toInt)
          let sm ← ldZStream strm
          stZStream strm { sm with next_in := in_, next_out := l.out, avail_in := ai.toUInt64.toUInt32,
                                   avail_out := ao.toUInt64.toUInt32 }
          let s ← ldInflateState state
          stInflateState state { s with hold, bits }) hx0 = .ok ((), after)) :
      (do
        let lmask0 ← pure ((← shl32 1 s.lenbits) - 1)
        let dmask0 ← pure ((← shl32 1 s.distbits) - 1)
        let l : InflateFastLocals := {
          state := state, in_ := sm.next_in, last := last0, out := sm.next_out, beg := beg0, end_ := end0,
          wsize := s.wsize, whave := s.whave, wnext := s.wnext, window := s.window, back := back0,
          hold := s.hold, bits := s.bits, lcode := s.lencode, dcode := s.distcode, lmask := lmask0,
          dmask := dmask0, here := default, op := default, len := default, dist := default,
          from_ := default, hold8 := default, last8 := default, end8 := default }
        cforwardLabel "leave"
          (do
            let mut l := l
            if !l.back && sm.avail_in >= 16 && sm.avail_out >= 2 + 258 + 15 then
              let last80 ← cinline (l.in_.add (sm.avail_in - 16).toNat)
              l := { l with last8 := last80 }
              let end80 ← cinline (l.out.add (sm.avail_out - (2 + 258 + 15)).toNat)
              l := { l with end8 := end80 }
              l := { l with hold8 := l.hold }
              l ← cdoWhileBrk
                (fun (l : InflateFastLocals) => do
                  let mut l := l
                  let w0 ← cinline (load64_c l.in_)
                  let sh0 ← cinline (shl64 w0 l.bits.toUInt64)
                  let in0 ← cinline (l.in_.add (((63 - l.bits) >>> 3).toNat : Int))
                  l := { l with hold8 := l.hold8 ||| sh0 }
                  l := { l with in_ := in0, bits := l.bits ||| 56 }
                  let h0 ← cinline (l.lcode.add (l.hold8 &&& l.lmask.toUInt64).toNat)
                  l := { l with here := h0 }
                  let e0 ← cinline l.here.load
                  if e0.op == 0 then
                    let sh1 ← cinline (shr64 l.hold8 e0.bits.toUInt64)
                    l := { l with hold8 := sh1 }
                    l := { l with bits := l.bits - e0.bits.toUInt32 }
                    store8 l.out e0.val.toUInt8
                    let out1 ← cinline (l.out.add 1)
                    l := { l with out := out1 }
                    let h1 ← cinline (l.lcode.add (l.hold8 &&& l.lmask.toUInt64).toNat)
                    l := { l with here := h1 }
                    let e1 ← cinline l.here.load
                    if e1.op == 0 then
                      let sh2 ← cinline (shr64 l.hold8 e1.bits.toUInt64)
                      l := { l with hold8 := sh2 }
                      l := { l with bits := l.bits - e1.bits.toUInt32 }
                      store8 l.out e1.val.toUInt8
                      let out2 ← cinline (l.out.add 1)
                      l := { l with out := out2 }
                      let h2 ← cinline (l.lcode.add (l.hold8 &&& l.lmask.toUInt64).toNat)
                      l := { l with here := h2 }
                      let e2 ← cinline l.here.load
                      if e2.op == 0 then
                        let sh3 ← cinline (shr64 l.hold8 e2.bits.toUInt64)
                        l := { l with hold8 := sh3 }
                        l := { l with bits := l.bits - e2.bits.toUInt32 }
                        store8 l.out e2.val.toUInt8
                        let out3 ← cinline (l.out.add 1)
                        return .cont { l with out := out3 }
                    let w1 ← cinline (load64_c l.in_)
                    let sh4 ← cinline (shl64 w1 l.bits.toUInt64)
                    let in1 ← cinline (l.in_.add (((63 - l.bits) >>> 3).toNat : Int))
                    l := { l with hold8 := l.hold8 ||| sh4 }
                    l := { l with in_ := in1, bits := l.bits ||| 56 }
                  clabel "dolen8" (dolen8BodyC strm) l)
                (fun (l : InflateFastLocals) => do
                  if ← Ptr.le l.in_ l.last8 then pure (← Ptr.le l.out l.end8, l)
                  else pure (false, l))
                l
              l := { l with len := l.bits >>> 3 }
              let in2 ← cinline (subn l.in_ l.len)
              l := { l with in_ := in2, bits := l.bits - (l.len <<< 3) }
              let msk ← cinline (shl32 1 l.bits)
              l := { l with hold := l.hold8 &&& (msk - 1).toUInt64 }
              let st1 ← ldInflateState l.state
              if st1.mode != LEN then return .goto l
              if !(← cinline (Ptr.lt l.out l.end_)) then return .goto l
              return .fall l
            else
              return .fall l)
          (fun (l : InflateFastLocals) => do
            cdoWhileBrk
              (fun (l : InflateFastLocals) => do
                let mut l := l
                if l.bits < 15 then
                  let (in1, hold1, bits1) ← pullByte64 l.in_ l.hold l.bits
                  let (in2, hold2, bits2) ← pullByte64 in1 hold1 bits1
                  l := { l with in_ := in2, hold := hold2, bits := bits2 }
                let h0 ← cinline (l.lcode.add (l.hold &&& l.lmask.toUInt64).toNat)
                l := { l with here := h0 }
                clabel "dolen" (dolenBodyC strm) l)
              (fun (l : InflateFastLocals) => do
                if ← Ptr.lt l.in_ l.last then pure (← Ptr.lt l.out l.end_, l)
                else pure (false, l))
              l)
          (fun (l : InflateFastLocals) => do
            let mut l := l
            l := { l with len := l.bits >>> 3 }
            let in1 ← cinline (subn l.in_ l.len)
            l := { l with in_ := in1, bits := l.bits - (l.len <<< 3) }
            let msk ← cinline (shl32 1 l.bits)
            l := { l with hold := l.hold &&& (msk - 1).toUInt64 }
            let sm2 ← ldZStream strm
            stZStream strm { sm2 with next_in := l.in_, next_out := l.out }
            let ai ← cinline (do
              if ← Ptr.lt l.in_ l.last then do let d ← l.last.diff l.in_; chk64 (5 + d.toInt)
              else do let d ← l.in_.diff l.last; chk64 (5 - d.toInt))
            let sm3 ← ldZStream strm
            stZStream strm { sm3 with avail_in := ai.toUInt64.toUInt32 }
            let ao ← cinline (do
              if ← Ptr.lt l.out l.end_ then do let d ← l.end_.diff l.out; chk64 (257 + d.toInt)
              else do let d ← l.out.diff l.end_; chk64 (257 - d.toInt))
            let sm4 ← ldZStream strm
            stZStream strm { sm4 with avail_out := ao.toUInt64.toUInt32 }
            let s2 ← ldInflateState l.state
            stInflateState l.state { s2 with hold := l.hold, bits := l.bits })) hx0 = .ok ((), after) := by
    simp only [cinline, forward_then_leave, m_bind_assoc_eq, m_pure_bind_eq] at hokB ⊢
    refine m_bind_ok_same rfl hokB fun mskL h8 _ hok8 => ?_
    refine m_bind_ok_same rfl hok8 fun mskD h9 _ hok9 => ?_
    let c : Ctx := { strm, state, last := last0, beg := beg0, end_ := end0, wsize := s.wsize,
                     whave := s.whave, wnext := s.wnext, window := s.window, lcode := s.lencode,
                     dcode := s.distcode, lmask := mskL - 1, dmask := mskD - 1 }
    have afterLeave (fl' : InflateFastLocals) (l' : L) (hx : Heap)
        (hrc : RelCore c fl' l')
        (hokL :
          (do
            let len := l'.bits >>> 3
            let in_ ← subn l'.in_ len
            let bits := l'.bits - (len <<< 3)
            let hold := l'.hold &&& ((← shl32 1 bits) - 1).toUInt64
            let ai : Int64 ←
              if ← Ptr.lt in_ last0 then do let d ← last0.diff in_; chk64 (5 + d.toInt)
              else do let d ← in_.diff last0; chk64 (5 - d.toInt)
            let ao : Int64 ←
              if ← Ptr.lt l'.out end0 then do let d ← end0.diff l'.out; chk64 (257 + d.toInt)
              else do let d ← l'.out.diff end0; chk64 (257 - d.toInt)
            let sm ← ldZStream strm
            stZStream strm { sm with next_in := in_, next_out := l'.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32 }
            let s ← ldInflateState state
            stInflateState state { s with hold, bits }) hx = .ok ((), after)) :
        (do
          let mut l := fl'
          l := { l with len := l.bits >>> 3 }
          let in1 ← subn l.in_ l.len
          l := { l with in_ := in1, bits := l.bits - (l.len <<< 3) }
          let msk ← shl32 1 l.bits
          l := { l with hold := l.hold &&& (msk - 1).toUInt64 }
          let sm2 ← ldZStream strm
          stZStream strm { sm2 with next_in := l.in_, next_out := l.out }
          let ai ← (do
            if ← Ptr.lt l.in_ l.last then do let d ← l.last.diff l.in_; chk64 (5 + d.toInt)
            else do let d ← l.in_.diff l.last; chk64 (5 - d.toInt))
          let sm3 ← ldZStream strm
          stZStream strm { sm3 with avail_in := ai.toUInt64.toUInt32 }
          let ao ← (do
            if ← Ptr.lt l.out l.end_ then do let d ← l.end_.diff l.out; chk64 (257 + d.toInt)
            else do let d ← l.out.diff l.end_; chk64 (257 - d.toInt))
          let sm4 ← ldZStream strm
          stZStream strm { sm4 with avail_out := ao.toUInt64.toUInt32 }
          let s2 ← ldInflateState l.state
          stInflateState l.state { s2 with hold := l.hold, bits := l.bits }) hx = .ok ((), after) :=
      inflate_fast_leave_of_ok c hrc hokL
    have runFall (fl' : InflateFastLocals) (l' : L) (hx : Heap)
        (hrc : RelCore c fl' l') (hbrk' : l'.broke = false)
        (hokF :
          (C.cdoWhile (inflate_fast_body c)
            (fun l => do
              if l.broke then pure (false, l)
              else if ← Ptr.lt l.in_ last0 then pure (← Ptr.lt l.out end0, l)
              else pure (false, l)) l' >>= fun l'' => do
            let len := l''.bits >>> 3
            let in_ ← subn l''.in_ len
            let bits := l''.bits - (len <<< 3)
            let hold := l''.hold &&& ((← shl32 1 bits) - 1).toUInt64
            let ai : Int64 ←
              if ← Ptr.lt in_ last0 then do let d ← last0.diff in_; chk64 (5 + d.toInt)
              else do let d ← in_.diff last0; chk64 (5 - d.toInt)
            let ao : Int64 ←
              if ← Ptr.lt l''.out end0 then do let d ← end0.diff l''.out; chk64 (257 + d.toInt)
              else do let d ← l''.out.diff end0; chk64 (257 - d.toInt)
            let sm ← ldZStream strm
            stZStream strm { sm with next_in := in_, next_out := l''.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32 }
            let s ← ldInflateState state
            stInflateState state { s with hold, bits }) hx = .ok ((), after)) :
        ((C.cdoWhileBrk
          (fun (l : InflateFastLocals) => do
            let mut l := l
            if l.bits < 15 then
              let (in1, hold1, bits1) ← pullByte64 l.in_ l.hold l.bits
              let (in2, hold2, bits2) ← pullByte64 in1 hold1 bits1
              l := { l with in_ := in2, hold := hold2, bits := bits2 }
            let h0 ← l.lcode.add (l.hold &&& l.lmask.toUInt64).toNat
            l := { l with here := h0 }
            clabel "dolen" (dolenBodyC strm) l)
          (fun (l : InflateFastLocals) => do
            if ← Ptr.lt l.in_ l.last then pure (← Ptr.lt l.out l.end_, l)
            else pure (false, l)) fl') >>= fun fl'' => do
          let mut l := fl''
          l := { l with len := l.bits >>> 3 }
          let in1 ← subn l.in_ l.len
          l := { l with in_ := in1, bits := l.bits - (l.len <<< 3) }
          let msk ← shl32 1 l.bits
          l := { l with hold := l.hold &&& (msk - 1).toUInt64 }
          let sm2 ← ldZStream strm
          stZStream strm { sm2 with next_in := l.in_, next_out := l.out }
          let ai ← (do
            if ← Ptr.lt l.in_ l.last then do let d ← l.last.diff l.in_; chk64 (5 + d.toInt)
            else do let d ← l.in_.diff l.last; chk64 (5 - d.toInt))
          let sm3 ← ldZStream strm
          stZStream strm { sm3 with avail_in := ai.toUInt64.toUInt32 }
          let ao ← (do
            if ← Ptr.lt l.out l.end_ then do let d ← l.end_.diff l.out; chk64 (257 + d.toInt)
            else do let d ← l.out.diff l.end_; chk64 (257 - d.toInt))
          let sm4 ← ldZStream strm
          stZStream strm { sm4 with avail_out := ao.toUInt64.toUInt32 }
          let s2 ← ldInflateState l.state
          stInflateState l.state { s2 with hold := l.hold, bits := l.bits }) hx = .ok ((), after) :=
      body_of_ok c hrc hbrk' _ _ hokF fun fl'' l'' h'' hr'' hok'' =>
        inflate_fast_leave_of_ok c hr'' hok''
    simp only [m_bind_assoc_eq] at afterLeave runFall
    by_cases hfast : (!back0 && sm.avail_in >= 16 && sm.avail_out >= 2 + 258 + 15) = true
    · simp only [hfast, ↓reduceIte, m_bind_assoc_eq] at hok9 ⊢
      refine m_bind_ok_same rfl hok9 fun last80 h10 _ hok10 => ?_
      refine m_bind_ok_same rfl hok10 fun end80 h11 _ hok11 => ?_
      refine body8_of_ok c last80 end80 ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        rfl, rfl, rfl, rfl⟩ rfl rfl rfl _ _ hok11 fun fl' l' h12 hr' hnml hok12 => ?_
      refine m_bind_ok_same (by rw [hr'.2.1, hr'.2.2.2.2]) hok12 fun in2 h13 hin2 hok13 => ?_
      have hh13 := ptr_add_heap hin2; subst hh13
      refine m_bind_ok_same (by rw [hr'.2.2.2.2]) hok13 fun msk2 h14 hshl hok14 => ?_
      have hh14 := shl32_heap _ _ hshl; subst hh14
      refine m_bind_ok_same (by rw [hr'.1.state]) hok14 fun st1 h15 hld hok15 => ?_
      let f := {fl' with in_ := in2, len := fl'.bits >>> 3, bits := fl'.bits - ((fl'.bits >>> 3) <<< 3), hold := fl'.hold8 &&& (msk2 - 1).toUInt64}
      let v := {l' with in_ := in2, len := l'.bits >>> 3, bits := l'.bits - ((l'.bits >>> 3) <<< 3), hold := l'.hold &&& (msk2 - 1).toUInt64}
      have rel : RelCore c f v := ⟨hr'.1, rfl, hr'.2.2.1, by simp only [f, v, hr'.2.2.2.1], by simp only [f, v, hr'.2.2.2.2]⟩
      by_cases hml : (st1.mode != LEN) = true
      · simp only [hml, ↓reduceIte, m_pure_bind_eq] at hok15 ⊢
        exact afterLeave f v h15 rel hok15
      · simp only [hml, Bool.false_eq_true, ↓reduceIte, m_bind_assoc_eq] at hok15 ⊢
        have hnl : st1.mode = LEN := by
          simpa [bne] using hml
        have hbr_false : l'.broke = false := by
          cases hb : l'.broke
          · rfl
          · exfalso; exact hnml hb st1 h15 hld hnl
        refine m_bind_ok_same (by rw [hr'.2.2.1, hr'.1.end_]) hok15 fun ltOut h16 _ hok16 => ?_
        cases ltOut with
        | false =>
          simp only [Bool.not_false, ↓reduceIte, m_pure_bind_eq] at hok16 ⊢
          exact afterLeave f v h16 rel hok16
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, m_pure_bind_eq] at hok16 ⊢
          exact runFall f v h16 rel hbr_false hok16
    · simp only [hfast, Bool.false_eq_true, ↓reduceIte, m_pure_bind_eq] at hok9 ⊢
      refine runFall _ _ h9 ?_ ?_ hok9
      · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
      · rfl
  simp only [cinline, forward_then_leave, m_bind_assoc_eq, m_pure_bind_eq] at afterBack
  rw [ite_bind_eq]
  by_cases hwin : (s.window != Ptr.null) = true
  · simp only [hwin, ↓reduceIte, m_bind_assoc_eq, m_pure_bind_eq] at hok6 ⊢
    refine m_bind_ok_same rfl hok6 fun outEnd h7 _ hok7 => ?_
    refine m_bind_ok_same rfl hok7 fun winEnd h8 _ hok8 => ?_
    exact afterBack (outEnd == winEnd) h8 hok8
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte, m_pure_bind_eq] at hok6 ⊢
    exact afterBack false h6 hok6

end Inffast

#print axioms inflate_fast_c_of_ok
end ZlibF.Proof.StandaloneCAbi
