import ZlibF.Proof.«deflate.c.universal-params-deflate»

/-!
# deflate.c: the phases of one `deflate` call

The phase functions below are the source of
`deflate` cut in source order, without any change; each phase takes the rest of the call as a
continuation, so that `deflate_phases` holds by unfolding.

1. `entryPhase`: the refusals, `last_flush`, the flush of pending output on entry with its early
   return, the `Z_BUF_ERROR` no-progress refusal and the `FINISH_STATE` refusal.
2. `headerPhase`: the zlib and gzip header states up to the flush on entering `BUSY_STATE`, with
   their early returns.
3. `strategyPhase`: the dispatch to the strategies and the flush
   markers after it (`_tr_align`, the empty stored block, `CLEAR_HASH`, `flush_pending`).
4. `trailerPhase`: the zlib or gzip trailer and the final `wrap` negation.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate
open Zlib.Trees («_tr_init» «_tr_flush_bits» «_tr_flush_block» «_tr_stored_block» «_tr_align»)
open Zlib.Crc32 (crc32 crc32_z)
set_option autoImplicit false

export Zlib.Deflate.Phases (entryPhase headerPhase strategyPhase trailerPhase)

/-- The four phases are the source used by the exported definition. -/
theorem deflate_phases (strm : ZStreamPtr) (flush : Int32) :
    deflate strm flush = entryPhase strm flush (fun s =>
      headerPhase strm s flush (strategyPhase strm s flush (trailerPhase strm s flush))) := rfl

end Zlib.Deflate.Universal.Call
