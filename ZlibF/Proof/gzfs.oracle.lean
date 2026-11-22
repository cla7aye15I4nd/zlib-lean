import ZlibF.Proof.«gzlib.c.base»

/-!
# gzfs: the OS-call oracle never touches the heap, and its regular instance

Each of `fsRead`, `fsWrite`, `fsLseek`, `fsClose`, `fsOpen` is `pure` of a result that depends on the world only,
for every oracle value: it never faults and never changes the heap. When the oracle entry of the call is
`regular` (and, for `close`/`open`, no failure or move is chosen, and no errno is chosen after success), the call
is its regular-file version on the world with the counter advanced.
-/

namespace Zlib.GzFs.Proofs
open C Zlib.GzFs

/-! ## The regular-file versions are pure -/

theorem fsWriteReg_pure (fd : Int32) (bs : Array UInt8) (w : Fs) :
    ∃ x, fsWriteReg fd bs w = (pure x : M (Int64 × Fs)) := by
  unfold fsWriteReg
  repeat' first
    | exact ⟨_, rfl⟩
    | split
    | dsimp only

theorem fsLseekReg_pure (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) :
    ∃ x, fsLseekReg fd off wh w = (pure x : M (Int64 × Fs)) ∧ (x.1 = -1 ∨ 0 ≤ x.1.toInt) := by
  unfold fsLseekReg
  repeat' first
    | exact ⟨_, rfl, Or.inl rfl⟩
    | (refine ⟨_, rfl, Or.inr ?_⟩
       simp only []
       rw [Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)]
       omega)
    | split
    | dsimp only

theorem fsCloseReg_pure (fd : Int32) (w : Fs) :
    ∃ x, fsCloseReg fd w = (pure x : M (Int32 × Fs)) := by
  unfold fsCloseReg
  repeat' first
    | exact ⟨_, rfl⟩
    | split
    | dsimp only

theorem fsOpenReg_pure (path : Array UInt8) (flags : Int32) (w : Fs) :
    ∃ x, fsOpenReg path flags w = (pure x : M (Int32 × Fs)) := by
  unfold fsOpenReg
  repeat' first
    | exact ⟨_, rfl⟩
    | split
    | dsimp only

/-! ## The oracle versions are pure, for every oracle value -/

theorem fsWrite_pure (fd : Int32) (bs : Array UInt8) (w : Fs) :
    ∃ x, fsWrite fd bs w = (pure x : M (Int64 × Fs)) := by
  unfold fsWrite
  dsimp only
  split
  · obtain ⟨⟨r, w'⟩, hy⟩ := fsWriteReg_pure fd bs (tickW w)
    rw [hy]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem fsLseek_pure (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) :
    ∃ x, fsLseek fd off wh w = (pure x : M (Int64 × Fs)) := by
  unfold fsLseek
  dsimp only
  split
  · obtain ⟨⟨r, w'⟩, hy, -⟩ := fsLseekReg_pure fd off wh (tickW w)
    rw [hy]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem fsClose_pure (fd : Int32) (w : Fs) :
    ∃ x, fsClose fd w = (pure x : M (Int32 × Fs)) := by
  unfold fsClose
  dsimp only
  obtain ⟨⟨r, w'⟩, hy⟩ := fsCloseReg_pure fd (tickW w)
  rw [hy]
  exact ⟨_, rfl⟩

theorem fsOpen_pure (path : Array UInt8) (flags : Int32) (w : Fs) :
    ∃ x, fsOpen path flags w = (pure x : M (Int32 × Fs)) := by
  unfold fsOpen
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · obtain ⟨⟨r, w'⟩, hy⟩ := fsOpenReg_pure path flags (tickW w)
    rw [hy]
    exact ⟨_, rfl⟩

/-! ## The regular instance -/

/-- With a regular oracle entry, `lseek` is the regular-file `lseek` on the advanced world. -/
theorem fsLseek_regular (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) (hc : w.lseekChoice w.nos = .regular) :
    fsLseek fd off wh w = (do
      let (r, w') ← fsLseekReg fd off wh (tickW w)
      pure (r, if r = -1 then w' else okErrW (w.okErrno w.nos) w')) := by
  unfold fsLseek
  dsimp only
  rw [hc]

/-- With no oracle failure, `close` is the regular-file `close` on the advanced world. -/
theorem fsClose_regular (fd : Int32) (w : Fs) (hc : w.closeFail w.nos = none) :
    fsClose fd w = (do
      let (r, w') ← fsCloseReg fd (tickW w)
      pure (r, if r = -1 then w' else okErrW (w.okErrno w.nos) w')) := by
  unfold fsClose
  dsimp only
  rw [hc]

/-- With no oracle failure and no move, `open` is the regular-file `open` on the advanced world. -/
theorem fsOpen_regular (path : Array UInt8) (flags : Int32) (w : Fs) (hc : w.openFail w.nos = none)
    (hm : w.openFd w.nos = none) :
    fsOpen path flags w = (do
      let (r, w') ← fsOpenReg path flags (tickW w)
      pure (if r = -1 then (r, w') else (r, okErrW (w.okErrno w.nos) w'))) := by
  unfold fsOpen
  dsimp only
  rw [hc, hm]

end Zlib.GzFs.Proofs
