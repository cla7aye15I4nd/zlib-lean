import ZlibF.Spec.Functional.GzTrace
import ZlibF.Spec.Common.Sequences

/-!
# gz file interface: the functional open and lifecycle goals

`gzWitnessHeap`, `gzWitnessFs`, `Goal.gz_initialisation_domain` and `Goal.gz_sequence`
(`docs/en/design/safety-functional-split.md`). The namespace is `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs ZlibF.Spec

def gzWitnessHeap (mode : List UInt8) : Heap :=
  { witnessHeap with
    bytes := upd (upd witnessHeap.bytes 3 (some #[120, 0])) 4 (some (mode ++ [0]).toArray)
    nextBlk := 5 }

def gzWitnessFs (mode : Api.GzMode) : Fs :=
  if mode = .read then Fs.put default #[120] #[] else default

/-- External open success is specified by the fixed file-system semantics. No gz contract
is an assumption. Every accepted mode has a successful concrete open witness.
The LP64 platform scope bounds each byte object below `2^63` bytes, including the caller's path
(`docs/en/deviations.md`). -/
def Goal.gz_initialisation_domain : Prop :=
  (∀ h fs path mode name flags kind level strategy direct fd world start,
    Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → FileSystem fs →
    NoAllocationFailure h → ZlibF.PlatformMemory.ByteObjectsFit h →
    CString h path name → CString h mode flags →
    parsedMode flags = some (kind, level, strategy, direct) →
    OpenWorld h fs world name flags kind none fd start → fd ≠ -1 →
    ∃ after fs' i s, Zlib.Gzlib.gzopen path mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) ∧
      OpenState after i s kind level strategy direct fd name ∧ GzReachable after fs' i ∧
      Frame h after (fun _ => False) ∧ LiveChange h after (GzOwned after i s) (fun _ => False)) ∧
  (∀ flags kind level strategy direct, 0 ∉ flags →
    parsedMode flags = some (kind, level, strategy, direct) →
    ∃ after fs' i s,
      Zlib.Gzlib.gzopen (.ref (.blk 3) 0) (.ref (.blk 4) 0) (gzWitnessFs kind) (gzWitnessHeap flags) =
        .ok ((some (.in_gzstate_x i), fs'), after) ∧
      OpenState after i s kind level strategy direct s.fd [120] ∧ GzReachable after fs' i)

/-- The gz lifecycle includes every admitted operation, external file growth and final close.
The per-entry read contracts express transparent/concatenated-member decoding and the
per-entry write contracts account for accepted bytes and seek zeros. -/
def Goal.gz_sequence : Prop :=
  (∀ h fs i, GzReachable h fs i → FileSystem fs ∧ ∃ s, GzValid h i s) ∧
  (∀ h fs i s call, GzReachable h fs i → h.gzstates i = some s →
    GzOperation i call → GzArguments h i s call → RegularOs fs →
    ∃ value fs' after s', call.execute fs h = .ok ((value, fs'), after) ∧
      GzValid after i s' ∧ FileSystem fs' ∧
      LiveChange h after
        (fun b => GzOwned after i s' b ∧ ¬ h.live b)
        (fun b => GzOwned h i s b ∧ ¬ GzOwned after i s' b)) ∧
  (∀ h fs i s, GzReachable h fs i → h.gzstates i = some s →
    ∃ rc fs' after, Zlib.Gzclose.gzclose (some (.in_gzstate_x i)) fs h = .ok ((rc, fs'), after) ∧
      CloseEffects h after fs fs' i s) ∧
  Goal.gzread ∧ Goal.gzfread ∧ Goal.gzgetc ∧ Goal.gzgets ∧
  Goal.gzwrite ∧ Goal.gzfwrite ∧ Goal.gzflush ∧ Goal.gzclose ∧ GzWriterFormat

end ZlibF.Spec.Public
