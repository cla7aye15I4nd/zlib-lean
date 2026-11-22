import ZlibF.Proof.«inflate.c.meaning-dynamic-step-table»
import ZlibF.Proof.«inflate.c.meaning-dynamic-step-lenlens»
import ZlibF.Proof.«inflate.c.meaning-dynamic-step-codelens»

/-!
# inflate.c: `TABLE`, `LENLENS` and `CODELENS` keep the format meaning

The three modes of a dynamic block header. Each step starts from
`LoopMatches` at a `.dynamicHeader` position and ends in one of four ways:
it leaves the call with the meaning kept (for want of input: short of the
field it waits for, `LeaveShort`), it goes to `BAD` and no valid stream is
comparable with the input read so far (`LoopRefuted`), it reaches a
new position, or it falls through to the next mode with `LoopMatches` at
that mode.

* `case TABLE` waits for 14 bits and reads `HLIT`, `HDIST`, `HCLEN`
  (`DeflateParsed.dynamicBits`). Counts beyond 286 or 30 go to `BAD`: no
  `Body.dynamic` has them (`DynamicCountsOK`). Otherwise it falls through to
  `LENLENS` with no code-length code length read.
* `case LENLENS` reads the code-length code lengths three bits at a time
  across calls. With all of them it builds the code-length table: an
  unacceptable code goes to `BAD` (`Body.dynamic` needs
  `Acceptable .codeLength`), otherwise it falls through to `CODELENS` with
  `CodeLengthMeaning` of the table and no length read.
-/

/-! The three steps are proved in separate modules, which do not import each other, so that they
build in parallel. -/
