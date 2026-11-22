import ZlibF.Proof.«deflate.c.engine.flush-default»
import ZlibF.Proof.«deflate.c.engine.overlay-costs»
import ZlibF.Proof.«deflate.c.engine.dynamic-budget»

/-! # The bits of a default block, against the costs of its choice

`_tr_flush_block` writes the block tag (3 bits), a body and, for a final block, the alignment
padding. The body is what the selected branch writes: for a stored block its padding, `LEN`,
`NLEN` and the bytes; for a fixed block the fixed codes of the symbols and the end-of-block code
(`static_len` bits); for a dynamic block the dynamic header, codes and end-of-block code
(`opt_len` bits). The selection of `_tr_flush_block` then bounds the tag and body:

* when the stored fallback exists, in bytes: the bytes written so far, rounded up, grow by at
  most the represented bytes plus 5;
* when it does not (a block whose start slid out of the window), by the fixed cost of the
  symbols plus 3 bits, rounded up to bytes.

These are the per-block facts of the size ledger (`unfinished_output_lt`).
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt natBits)
open Zlib.Trees.Proofs (dynamicHeaderBits sourceWords curL)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateSelection (byteCost selectedCost)
set_option autoImplicit false

/-- The fixed cost of a symbol list, end-of-block code included, in bits. -/
def fixedCost (xs : List Symbol) : Nat :=
  7 + (xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum +
    (xs.map staticDistanceSymbolCost).sum

/-- `byteCost` of a small value, in natural numbers. -/
theorem byteCost_toNat {x : UInt64} (small : x.toNat < 2 ^ 60) :
    (byteCost x).toNat = (x.toNat + 10) / 8 := by
  unfold byteCost
  rw [UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp [Nat.shiftRight_eq_div_pow]

/-- The fixed payload of `fixed_block_ready_frame` has the fixed cost of its symbols. -/
theorem fixed_payload_cost (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) :
    (xs.map (fun s => (Zlib.Trees.Proofs.Out.payloadSymBits
      Zlib.Trees.Proofs.fixedLiteralWords Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)).length)).sum + 7 =
      fixedCost xs := by
  unfold fixedCost
  induction xs with
  | nil => simp
  | cons s rest ih =>
    have head := static_symbol_cost s (valid s (by simp))
    have tail := ih (fun t member => valid t (by simp [member]))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- **The cost of a default block.** Under the hypotheses of `flush_default_ready`, the actual
flush writes `tag ++ body ++ padding` after the `bi_valid` bits held so far. When the stored
fallback exists, the held bits, tag and body round up to at most the held bits' bytes plus the
represented bytes plus 5. When it does not, the tag and body take at most the fixed cost of the
symbols plus 3 bits, rounded up to bytes. -/
theorem flush_default_cost {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (z' : ZStream) (after : Heap) (result : DeflateState) (next : Array UInt8)
      (kind : Nat) (body padding : List Bool),
      Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧
      kind < 3 ∧ padding.length < 8 ∧ (last = false → padding = []) ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (natBits (if last then 1 else 0) 1 ++ natBits kind 2 ++ body ++ padding) ∧
      (defaultStoredSource d w = .null → 3 + body.length ≤ 8 * ((fixedCost xs + 10) / 8)) ∧
      (defaultStoredSource d w ≠ .null →
        (d.bi_valid.toInt.toNat + 3 + body.length + 7) / 8 ≤
          (d.bi_valid.toInt.toNat + 7) / 8 + represented xs + 5) := by
  obtain ⟨z', hint, goodZ, treesZ, buffersZ, _account, _sizesZ, _storageZ, _fieldsZ, _unknown, _known⟩ :=
    block_data_type_engine (ob := ob) good trees buffers
  obtain ⟨mb, prepared, allRun, goodP, treesP, buffersP, _sizesP, _storageP, fields, _cost, budget⟩ :=
    all_trees_static_budget_engine (ob := ob) goodZ treesZ buffersZ ledger clear
  have prepare : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) := by
    unfold blockPrepare
    rw [bind_app, hint]
    exact allRun
  have record := fields
  unfold TreePreparationFrame at record
  have cursorP : prepared.pending_out = prepared.pending_buf := by rw [record]; exact cursor
  have memoryP : prepared.lit_bufsize.toNat = 16384 := by rw [record]; exact memory
  have pendingP : prepared.pending = 0 := by rw [record]; exact pending
  have bitsP : prepared.bi_valid.toInt ≤ 7 := by rw [record]; exact bits
  have countP : prepared.sym_next.toNat = 3 * xs.length := by rw [record]; exact ledger.count
  have packedP : PackedSymbols buf prepared.lit_bufsize.toNat xs := by rw [record]; exact ledger.packed
  have outputP : Zlib.Trees.Proofs.Out.outBits buf prepared = Zlib.Trees.Proofs.Out.outBits buf d := by
    rw [record]; rfl
  -- the fixed cost, as `static_len`
  have staticEq := dynamic_static_len treesZ ledger clear allRun
  have countBound : xs.length ≤ 16383 := by
    have := trees.run.sym_next_le
    have := trees.base.sym_end
    have := ledger.count
    omega
  have staticSmall : fixedCost xs ≤ 31 * xs.length + 7 := by
    rw [← fixed_payload_cost xs ledger.valid]
    have each : ∀ ys : List Symbol, (∀ s ∈ ys, s.Valid) →
        (ys.map (fun s => (Zlib.Trees.Proofs.Out.payloadSymBits Zlib.Trees.Proofs.fixedLiteralWords
          Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)).length)).sum ≤ 31 * ys.length := by
      intro ys valid
      induction ys with
      | nil => simp
      | cons t rest ih =>
        have v := valid t (by simp)
        have one := Zlib.Trees.Proofs.fixed_payload_symbol_length t.distance t.value v.1 v.2
        have tail := ih (fun u member => valid u (by simp [member]))
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
    have := each xs ledger.valid
    omega
  have staticNat : prepared.static_len.toNat = fixedCost xs := by
    rw [staticEq, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by unfold fixedCost at staticSmall; omega)
  have staticBytes : (byteCost prepared.static_len).toNat = (fixedCost xs + 10) / 8 := by
    rw [byteCost_toNat (by rw [staticNat]; omega), staticNat]
  have byteBound := represented_le ledger.valid
  have natural : (UInt64.ofNat (represented xs)).toNat = represented xs := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have held : d.bi_valid.toInt.toNat ≤ 7 := by omega
  by_cases chooseStored : (UInt64.ofNat (represented xs)) + (4 : UInt64) ≤
      selectedCost (byteCost prepared.opt_len) (byteCost prepared.static_len) (prepared.strategy == Z_FIXED) ∧
      defaultStoredSource d w != .null
  · have nonnegative : 0 ≤ d.block_start.toInt := by
      by_cases yes : 0 ≤ d.block_start.toInt
      · exact yes
      · have impossible := chooseStored.2
        simp only [defaultStoredSource, yes, ite_false, bne_self_eq_false, Bool.false_eq_true] at impossible
    have source : defaultStoredSource d w = .ref (.blk w) d.block_start.toInt.toNat := ite_eq_left nonnegative
    have room := ZlibF.Math.DeflateSelection.stored_default_room countBound budget
      (stored := UInt64.ofNat (represented xs)) (by rw [natural]; omega) chooseStored.1
    rw [natural] at room
    obtain ⟨after, result, next, body, run, goodA, treesA, _buffersA, _sizesA, _storageA,
      _ledgerA, _clearA, _size, _bound, _cursorA, _aligned, bodyLength, output, _grammar⟩ :=
      stored_block_ready (ob := ob) goodP treesP buffersP cursorP memoryP pendingP bitsP
        (by rw [record]; exact win) (by simpa only [setD_bytes, ZStreamRef.put_bytes] using get)
        (by rw [record]; exact range) (by rw [record]; exact nonnegative)
        (by rw [record]; exact balance) (by rw [record]; exact accounted)
        (by rw [record]; exact view) room last
    have blockPosition : prepared.block_start = d.block_start := by rw [record]
    rw [blockPosition] at run
    have dispatch := flush_stored_dispatch good positive prepare goodP
      (.ref (.blk w) d.block_start.toInt.toNat) (by intro no; cases no)
      (UInt64.ofNat (represented xs)) (if last then 1 else 0) chooseStored.1
    rw [outputP] at output
    -- the stored choice is cheaper than the fixed one
    have selected := ZlibF.Math.DeflateSelection.selected_le_fixed (byteCost prepared.opt_len)
      (byteCost prepared.static_len) (prepared.strategy == Z_FIXED)
    have chosen := chooseStored.1
    have stored4 : (UInt64.ofNat (represented xs) + 4).toNat = represented xs + 4 := by
      rw [UInt64.toNat_add, natural]
      simp only [UInt64.reduceToNat]
      exact Nat.mod_eq_of_lt (by omega)
    have le := UInt64.le_iff_toNat_le.mp chosen
    rw [stored4] at le
    refine ⟨z', after, result, next, 0, body, [], ?_, goodA, treesA, by decide, by simp, by simp, ?_, ?_, ?_⟩
    · rw [source]
      exact dispatch.trans run
    · simpa only [Zlib.Trees.Proofs.Out.storedTag_wire, List.append_nil, List.append_assoc] using output
    · intro absent
      have present := chooseStored.2
      rw [absent] at present
      exact absurd present (by decide)
    · intro _
      have sameBits : prepared.bi_valid = d.bi_valid := by rw [record]
      rw [bodyLength, sameBits]
      omega
  · by_cases chooseFixed : byteCost prepared.static_len ≤ byteCost prepared.opt_len ∨
        (prepared.strategy == Z_FIXED) = true
    · have avoid : ¬ ((UInt64.ofNat (represented xs)) + (4 : UInt64) ≤ byteCost prepared.static_len ∧
          defaultStoredSource d w != .null) := by
        simpa only [selectedCost, chooseFixed, ite_true] using chooseStored
      obtain ⟨after, result, next, body, padding, run, goodA, treesA, _buffersA, _sizesA, _storageA,
        _ledgerA, _frame, _size, _bound, _nonfinal, _cursorA, _room, _final, padBound, padNone,
        payloadLength, output, _grammar⟩ :=
        fixed_block_ready_frame (ob := ob) goodP treesP buffersP cursorP memoryP pendingP bitsP
          countP packedP ledger.valid trace last
      have dispatch := flush_fixed_selected_dispatch good positive prepare goodP (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) chooseFixed avoid
      rw [outputP] at output
      have bodyCost : body.length = fixedCost xs := by
        rw [payloadLength]
        exact fixed_payload_cost xs ledger.valid
      refine ⟨z', after, result, next, 1, body, padding, dispatch.trans run, goodA, treesA,
        by decide, padBound, padNone, ?_, ?_, ?_⟩
      · simpa only [Zlib.Trees.Proofs.Out.fixedTag_wire, List.append_assoc] using output
      · intro _
        rw [bodyCost]
        omega
      · intro present
        have notCheap : ¬ (UInt64.ofNat (represented xs) + 4 ≤ byteCost prepared.static_len) := by
          intro cheap
          apply avoid
          refine ⟨cheap, ?_⟩
          simpa only [bne_iff_ne, ne_eq] using present
        have stored4 : (UInt64.ofNat (represented xs) + 4).toNat = represented xs + 4 := by
          rw [UInt64.toNat_add, natural]
          simp only [UInt64.reduceToNat]
          exact Nat.mod_eq_of_lt (by omega)
        have lt : (byteCost prepared.static_len).toNat < represented xs + 4 := by
          rw [← stored4]
          exact UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp notCheap)
        rw [staticBytes] at lt
        rw [bodyCost]
        omega
    · have avoid : ¬ ((UInt64.ofNat (represented xs)) + (4 : UInt64) ≤ byteCost prepared.opt_len ∧
          defaultStoredSource d w != .null) := by
        simpa only [selectedCost, chooseFixed, ite_false] using chooseStored
      have different : byteCost prepared.static_len ≠ byteCost prepared.opt_len := by
        intro equal
        apply chooseFixed
        left
        rw [equal]
        exact Nat.le_refl _
      obtain ⟨after, result, next, body, padding, emitRun, goodA, treesA, _buffersA, _sizesA, _storageA,
        _ledgerA, _clearA, _size, _bound, _cursorA, _room, _final, padBound, padNone, shape, output, _grammar⟩ :=
        dynamic_prepared_block_ready (ob := ob) goodZ treesZ buffersZ cursor memory pending bits ledger clear trace last
      obtain ⟨mb', ready, readyRun, bodyEq⟩ := shape
      have sameReady : ready = prepared := Zlib.Trees.Proofs.same_record_of_runs readyRun allRun
      subst sameReady
      have sameMb : mb' = mb := (Prod.mk.inj (Except.ok.inj (readyRun.symm.trans allRun))).1
      subst sameMb
      unfold dynamicPreparedPayload at emitRun
      have joined : ((do
          Zlib.Trees.Proofs.blPrepare (some (.tab ds))
          Zlib.Trees.build_bl_tree (some (.tab ds))) >>= fun idx => do
            Zlib.Trees.Proofs.dynamicBlockHeader (some (.tab ds)) (if last then 1 else 0) idx
            Zlib.Trees.compress_block (some (.tab ds)) (← Zlib.Trees.pLtree (some (.tab ds)))
              (← Zlib.Trees.pDtree (some (.tab ds)))
            Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0))
          (r.put h z') = .ok ((), after) := by
        simpa only [M_bind_assoc] using emitRun
      rw [bind_app, allRun] at joined
      have dispatch := flush_dynamic_dispatch good positive prepare goodP (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) chooseFixed avoid different
      -- the body is `opt_len` bits
      have optEq := dynamic_opt_len treesZ ledger clear allRun
      obtain ⟨mbB, resultB, budgetRun, _gB, _tB, _bB, _sB, _oB, _lowB, _upB, _guardsB, _frameB, _outB,
        _headerB, _prefixB, whole⟩ :=
        all_trees_dynamic_budget_engine (ob := ob) goodZ treesZ buffersZ ledger trees.run.sym_next_le memory pending bits
      have sameB : resultB = ready := Zlib.Trees.Proofs.same_record_of_runs budgetRun allRun
      subst sameB
      have sameMbB : mbB = mb' := (Prod.mk.inj (Except.ok.inj (budgetRun.symm.trans allRun))).1
      subst sameMbB
      have eobSmall : curL resultB.dyn_ltree 256 < 65536 := by
        unfold curL
        exact UInt16.toNat_lt _
      have bodyLen : body.length = (dynamicHeaderBits resultB mbB).length +
          (dynamicSymbolCosts resultB xs).sum + curL resultB.dyn_ltree 256 := by
        rw [bodyEq, List.length_append, payload_length]
        omega
      have optNat : resultB.opt_len.toNat = body.length := by
        rw [optEq, UInt64.toNat_ofNat', bodyLen]
        exact Nat.mod_eq_of_lt (by omega)
      have optBytes : (byteCost resultB.opt_len).toNat = (body.length + 10) / 8 := by
        rw [byteCost_toNat (by rw [optNat, bodyLen]; omega), optNat]
      have fixedNo : ¬ (byteCost resultB.static_len ≤ byteCost resultB.opt_len) := by
        intro yes
        exact chooseFixed (Or.inl yes)
      have optLess : (byteCost resultB.opt_len).toNat < (byteCost resultB.static_len).toNat :=
        UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp fixedNo)
      rw [optBytes, staticBytes] at optLess
      refine ⟨z', after, result, next, 2, body, padding, dispatch.trans joined, goodA, treesA,
        by decide, padBound, padNone, ?_, ?_, ?_⟩
      · simpa only [Zlib.Trees.Proofs.dynamicTag_wire, List.append_assoc] using output
      · intro _
        omega
      · intro present
        have notCheap : ¬ (UInt64.ofNat (represented xs) + 4 ≤ byteCost resultB.opt_len) := by
          intro cheap
          apply avoid
          refine ⟨cheap, ?_⟩
          simpa only [bne_iff_ne, ne_eq] using present
        have stored4 : (UInt64.ofNat (represented xs) + 4).toNat = represented xs + 4 := by
          rw [UInt64.toNat_add, natural]
          simp only [UInt64.reduceToNat]
          exact Nat.mod_eq_of_lt (by omega)
        have lt : (byteCost resultB.opt_len).toNat < represented xs + 4 := by
          rw [← stored4]
          exact UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp notCheap)
        rw [optBytes] at lt
        omega

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Engine.Proofs
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **A slid block costs less than its bytes.** Under the level-6 match quality (a 3-byte match is
within 4096), a block of at most 16383 symbols that represents at least 32506 bytes has a fixed
cost, rounded up to bytes after the tag, below its represented bytes. -/
theorem slid_fixed_cost {xs : List Symbol} (valid : ∀ s ∈ xs, s.Valid)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (symbols : xs.length ≤ 16383) (large : 32506 ≤ represented xs) :
    (fixedCost xs + 10) / 8 ≤ represented xs := by
  have sum := filtered_static_cost_sum xs valid quality
  unfold fixedCost
  omega

end Zlib.Deflate.Engine.Proofs
