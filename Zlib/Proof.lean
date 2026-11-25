import Zlib.Proof.ProgLookup
import Zlib.Proof.ProgSpec
import Zlib.Proof.Zutil
import Zlib.Proof.CompressBound
import Zlib.Proof.Adler32
import Zlib.Proof.Crc32Base
import Zlib.Proof.Crc32Combine
import Zlib.Proof.Crc32
import Zlib.Proof.Math.Inftrees
import Zlib.Proof.Math.Trees

/-!
# Top-Level Safety Proof Entrypoint for `zlib-lean` (`Zlib.Proof`)

Aggregates the Wave 1 safety proofs (`Zutil`, `CompressBound`, `Adler32`,
`Crc32Combine`, `Crc32`) and pure mathematical foundations (`Math.Inftrees`,
`Math.Trees`) for Wave 2+.
-/
