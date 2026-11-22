import ZlibF.Proof.«deflate.c.engine.strategy-size»
import ZlibF.Proof.«deflate.c.engine.encoded-state»

/-! # The size ledger at a call boundary

Beside `DefaultEncodingState`, a default stream between calls keeps a bound on what it has
delivered and holds, by status:

* `INIT_STATE`: nothing delivered or held, and the companion of the empty block;
* `BUSY_STATE`: delivered plus held bytes at most `base + 2 + 5 * (base / 16383)`, where `base` is
  the input covered by emitted blocks (2 is the zlib header), with the companion of the open block;
* `FINISH_STATE`: delivered plus held bytes, plus 4 while the trailer is not written, at most
  `n + 11 + 5 * (n / 16383)` for the `n` accepted bytes.

The boundary data of a state (`origin`, `base`, the open block's symbols) is determined by the
state and the accepted length, so the `BUSY_STATE` clause is stated for every such data.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The trailer bytes still owed: 4 until the zlib trailer is written. -/
def owedTrailer (d : DeflateState) : Nat := if d.wrap = 1 then 4 else 0

/-- **The size ledger** of a default stream at a call boundary. -/
structure SizeLedger (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (config : EngineConfig) (accepted observed : List UInt8) : Prop where
  init : d.status = INIT_STATE → observed = [] ∧ heldBytes d = 0 ∧ SizeCompanion d []
  busy : ∀ input origin base xs, BufferedBoundary h r ds z d input origin base xs config →
    d.status = BUSY_STATE → inputPrefix input (origin + fillEnd d) = accepted →
    SizeCompanion d xs ∧ observed.length + heldBytes d ≤ base + 2 + 5 * (base / 16383)
  finishing : d.status = FINISH_STATE →
    observed.length + heldBytes d + owedTrailer d ≤
      accepted.length + 11 + 5 * (accepted.length / 16383)
  window : config.windowBits = 15

/-- **The boundary data of a state is unique** given its origin: the covered base and the open
block's symbols. -/
theorem content_data_unique {h : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d : DeflateState}
    {input input' : Nat → UInt8} {origin base base' : Nat} {xs xs' : List Symbol}
    (one : ContentBoundary h r ds z d input origin base xs)
    (two : ContentBoundary h r ds z' d input' origin base' xs') :
    base = base' ∧ xs = xs' := by
  have b1 := content_base_eq one
  have b2 := content_base_eq two
  exact ⟨by omega, symbol_boundary_unique one.symbols two.symbols⟩

/-- **Setting the `BUSY_STATE` clause from one known boundary.** -/
theorem busy_clause_of_data {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {accepted observed : List UInt8}
    {input0 : Nat → UInt8} {origin0 base0 : Nat} {xs0 : List Symbol}
    (known : ContentBoundary h r ds z d input0 origin0 base0 xs0)
    (length : origin0 + fillEnd d = accepted.length)
    (companion : SizeCompanion d xs0)
    (size : observed.length + heldBytes d ≤ base0 + 2 + 5 * (base0 / 16383)) :
    ∀ input origin base xs, BufferedBoundary h r ds z d input origin base xs config →
      d.status = BUSY_STATE → inputPrefix input (origin + fillEnd d) = accepted →
      SizeCompanion d xs ∧ observed.length + heldBytes d ≤ base + 2 + 5 * (base / 16383) := by
  intro input origin base xs boundary _status prefixEq
  have l := congrArg List.length prefixEq
  rw [input_prefix_length] at l
  have origins : origin = origin0 := by omega
  subst origins
  obtain ⟨bases, lists⟩ := content_data_unique boundary.toContentBoundary known
  subst bases lists
  exact ⟨companion, size⟩

/-- The covered input of a content boundary is at most what the window holds. -/
theorem content_base_le {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {input : Nat → UInt8} {origin base : Nat} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs) : base ≤ origin + fillEnd d := by
  have accounted := boundary.accounted
  have fill : d.strstart.toNat ≤ fillEnd d := by unfold fillEnd; omega
  omega

/-- **The ledger bounds the delivered output** by `n + 11 + 5 * (n / 16383)`. -/
theorem SizeLedger.output_le {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed)
    (ledger : SizeLedger h r ds z d config accepted observed) :
    observed.length ≤ accepted.length + 11 + 5 * (accepted.length / 16383) := by
  rcases state.phase with ⟨_, empty, _⟩ | ⟨_, header, _⟩ |
      ⟨input, origin, base, xs, published, _outputEq, boundary, status, _encoding, inputEq⟩ |
      ⟨published, _outputEq, phase, _encoding⟩
  · rw [empty]; simp only [List.length_nil]; omega
  · rw [header]; simp only [List.length_cons, List.length_nil]; omega
  · obtain ⟨_, size⟩ := ledger.busy input origin base xs boundary status inputEq
    have covered := content_base_le boundary.toContentBoundary
    have l := congrArg List.length inputEq
    rw [input_prefix_length] at l
    have grow : base / 16383 ≤ accepted.length / 16383 := Nat.div_le_div_right (by omega)
    omega
  · have size := ledger.finishing phase.status
    omega

/-- A `BUSY_STATE` encoding state has boundary data for its accepted input. -/
theorem DefaultEncodingState.busy_data {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (status : d.status = BUSY_STATE) :
    ∃ input origin base xs, BufferedBoundary h r ds z d input origin base xs config ∧
      inputPrefix input (origin + fillEnd d) = accepted := by
  rcases state.phase with ⟨_, _, _, start, _⟩ | ⟨emptyInput, _, input, boundary, _, encoding⟩ |
      ⟨input, origin, base, xs, _published, _outputEq, boundary, _, _encoding, inputEq⟩ |
      ⟨_published, _outputEq, phase, _encoding⟩
  · exact absurd (start.status.symm.trans status) (by decide)
  · obtain ⟨_remaining, _pending, _wire, _bits, start, look⟩ := encoding
    refine ⟨input, 0, 0, [], boundary, ?_⟩
    rw [emptyInput]
    simp only [fillEnd, start, look, UInt32.toNat_zero, Nat.add_zero, inputPrefix, List.range_zero,
      List.map_nil]
  · exact ⟨input, origin, base, xs, boundary, inputEq⟩
  · exact absurd (phase.status.symm.trans status) (by decide)

/-- **The ledger after initialization.** -/
theorem DefaultEncodingState.size_ledger_init {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} {config : EngineConfig}
    (state : DefaultEncodingState h r ds z d config [] []) :
    SizeLedger h r ds z d config [] [] := by
  rcases state.phase with ⟨_, _, _, start, boundary⟩ | ⟨_, header, _⟩ |
      ⟨_, _, _, _, published, outputEq, _⟩ | ⟨published, outputEq, _⟩
  · have status := start.status
    refine ⟨fun _ => ⟨rfl, ?_, ?_⟩, fun _ _ _ _ _ busy => ?_, fun finish => ?_, ?_⟩
    · unfold heldBytes
      rw [start.pending, start.bits]
      rfl
    · unfold SizeCompanion
      refine ⟨fun s member => by simp at member, fun three => ?_, fun negative => ?_⟩
      · rw [start.matchLength] at three; cases three
      · rw [start.blockStart] at negative; cases negative
    · exact absurd (status.symm.trans busy) (by decide)
    · exact absurd (status.symm.trans finish) (by decide)
    · exact (congrArg EngineConfig.windowBits boundary.configuration).symm.trans start.windowBits
  · cases header
  · simp at outputEq
  · simp at outputEq

/-- **The ledger under caller edits.** -/
theorem SizeLedger.rebuffer {h g : Heap} {r : ZStreamRef} {ds : Nat} {z zg : ZStream}
    {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed)
    (ledger : SizeLedger h r ds z d config accepted observed) (edit : Rebuffer h g r)
    (getG : r.get g = some zg) :
    SizeLedger g r ds zg d config accepted observed := by
  refine ⟨ledger.init, ?_, ledger.finishing, ledger.window⟩
  intro input origin base xs boundary status prefixEq
  obtain ⟨input0, origin0, base0, xs0, boundary0, prefix0⟩ := state.busy_data status
  obtain ⟨companion, size⟩ := ledger.busy input0 origin0 base0 xs0 boundary0 status prefix0
  obtain ⟨zb, getB, boundaryG⟩ := rebuffer_buffered_boundary boundary0 edit state.protocol.no_header
  have same : zb = zg := Option.some.inj (getB.symm.trans getG)
  subst same
  have length := congrArg List.length prefix0
  rw [input_prefix_length] at length
  exact busy_clause_of_data (config := config) boundaryG.toContentBoundary length companion size
    input origin base xs boundary status prefixEq

end Zlib.Deflate.Engine.Proofs
