import ZlibF.Spec.Common.Inflate.InflateFastPlatform
import ZlibF.Proof.PlatformMemory
import ZlibF.Proof.«inffast.c.final»

/-!
# inffast.c: discharge size premises from the platform scope

The actual fast call keeps its existing safety and accounting conclusion.
Its returned heap also satisfies the explicit platform size condition.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.PlatformMemory
set_option autoImplicit false

/-- The existing exact fast-call frame establishes preservation of the
platform scope; a post-state size premise is not assumed. -/
theorem PlatformEntry.fit_after (entry : PlatformEntry) {after : Heap}
    (post : FastPost entry.toEnv after) : ByteObjectsFit after := by
  obtain ⟨used, produced, buffered, bytes, msg, mode, bits, hold,
    _, _, _, size, _, _, heap, _⟩ := post
  rw [heap]
  apply ByteObjectsFit.put_stream
  have bound : bytes.size < byteObjectLimit := by
    change bytes.size < 2 ^ 63
    rw [size]
    exact entry.toEnv.hAbig
  exact (entry.platform.with_bytes (block := entry.ob) bound).with_istates _

end Zlib.Inffast.Proofs
