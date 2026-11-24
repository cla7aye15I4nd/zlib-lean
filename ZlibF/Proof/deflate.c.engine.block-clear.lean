import ZlibF.Runtime.Schema

namespace Zlib.Deflate.Engine.Proofs.BlockInit
open C

/-- Reset data needed when constructing the next dynamic header. It is
established by actual init/reset and retained through non-flushing frames. -/
structure BlockClear (d : DeflateState) : Prop where
  bl : ∀ k, k < 19 → d.bl_tree[k]!.fc = 0
  opt : d.opt_len = 0
  fixed : d.static_len = 0


end Zlib.Deflate.Engine.Proofs.BlockInit
