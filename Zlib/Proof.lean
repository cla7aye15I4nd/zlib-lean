import Zlib.Proof.ProgLookup
import Zlib.Proof.ProgLookupAll
import Zlib.Proof.ProgSpec
import Zlib.Proof.Zutil
import Zlib.Proof.ZutilAlloc
import Zlib.Proof.CompressBound
import Zlib.Proof.Adler32
import Zlib.Proof.Crc32Base
import Zlib.Proof.Crc32Combine
import Zlib.Proof.Crc32
import Zlib.Proof.Math.Inftrees
import Zlib.Proof.Math.Trees
import Zlib.Proof.Math.Gz
import Zlib.Proof.Invariant
import Zlib.Proof.VCGenBridge

/-!
# Top-Level Safety Proof Entrypoint for `zlib-lean` (`Zlib.Proof`)

Aggregates the Wave 1 safety proofs (`Zutil`, `CompressBound`, `Adler32`,
`Crc32Combine`, `Crc32`), Phase 0 allocator/lookup infrastructure (`ProgLookupAll`,
`ZutilAlloc`), pure mathematical foundations (`Math.Inftrees`, `Math.Trees`,
`Math.Gz`), unified invariants (`Invariant`), and VCGen bridge (`VCGenBridge`)
for Waves 2–4.
-/
