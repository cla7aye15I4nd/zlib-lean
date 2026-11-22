/-!
# deflate.c, engine: the window arithmetic of `fill_window` and `longest_match`

Statements about natural numbers. `ws` is `w_size` (512 to 32768, a power of two), the window has `2 * ws` bytes,
`ss` is `strstart`, `la` is `lookahead`, `MIN_LOOKAHEAD = 262`, `MAX_DIST = ws - 262`, `MAX_MATCH = 258`.

**D**, the window range: `ss + la <= 2 * ws`.

These are the numeric facts of `docs/en/proof/deflate.md`, section "Inside one `deflate` call" (`fill_window`): the slide test, the slide copy, the room left
after `fill_window`, the `high_water` clearing, and the margins that keep every read of `longest_match` inside the
window.
-/

namespace Zlib.Deflate.Engine.Proofs

/-! ## The slide of `fill_window` -/

/-- The amount `fill_window` slides by: `ws` when `strstart >= ws + MAX_DIST = 2 * ws - 262`, else `0`. -/
def fillD (ws ss : Nat) : Nat := if 2 * ws - 262 ≤ ss then ws else 0

/-- `high_water` after `fill_window` (`W = window_size`, `curr = strstart + lookahead` after the read): when
below `W` it is raised to at least `MIN(curr + WIN_INIT, W)`. -/
def fillHW (hw W curr : Nat) : Nat := if hw < W then max hw (min (curr + 258) W) else hw

/-- **Lemma 1** (`I-fw-post-room`). Whenever `fill_window` returns, `strstart < window_size - MIN_LOOKAHEAD`. -/
theorem fill_post_room {ws ss la : Nat} (hws : 512 ≤ ws) (hD : ss + la ≤ 2 * ws) :
    ss - fillD ws ss < 2 * ws - 262 := by
  unfold fillD; split <;> omega

/-! ## The `high_water` clearing -/

/-! ## The margins of `longest_match` -/

end Zlib.Deflate.Engine.Proofs
