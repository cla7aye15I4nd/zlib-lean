import C99
import Zlib.Headers.Common
import Zlib.Gzclose
import Zlib.Zutil
import Zlib.Adler32
import Zlib.Compress
import Zlib.Uncompr
import Zlib.Inftrees
import Zlib.Inffast
import Zlib.Crc32
import Zlib.Trees
import Zlib.Infback
import Zlib.Inflate
import Zlib.Deflate
import Zlib.Gzlib
import Zlib.Gzread
import Zlib.Gzwrite

namespace Zlib

/-- Header files emitted verbatim into the standalone C output directory. -/
def allHeaders : List C99.TU := Zlib.Headers.allABIHeaders

/-- All 15 C translation units of patched zlib 1.4.0.1-motley. -/
def allTUs : List C99.TU := [
  Zlib.Gzclose.gzcloseTU,
  Zlib.Zutil.zutilTU,
  Zlib.Adler32.adler32TU,
  Zlib.Compress.compressTU,
  Zlib.Uncompr.uncomprTU,
  Zlib.Inftrees.inftreesTU,
  Zlib.Inffast.inffastTU,
  Zlib.Crc32.crc32TU,
  Zlib.Trees.treesTU,
  Zlib.Infback.infbackTU,
  Zlib.Inflate.inflateTU,
  Zlib.Deflate.deflateTU,
  Zlib.Gzlib.gzlibTU,
  Zlib.Gzread.gzreadTU,
  Zlib.Gzwrite.gzwriteTU
]

/-- Combined list of emitted headers and translation units. -/
def allFiles : List C99.TU := allHeaders ++ allTUs

/-- All 86 Verus-style public API contracts embedded across the translation units. -/
def allContracts : List (C99.FnContract Zlib.Spec.ClientView) :=
  Zlib.Gzclose.gzcloseTUContracts ++
  Zlib.Zutil.zutilTUContracts ++
  Zlib.Adler32.adler32TUContracts ++
  Zlib.Compress.compressTUContracts ++
  Zlib.Uncompr.uncomprTUContracts ++
  Zlib.Inftrees.inftreesTUContracts ++
  Zlib.Inffast.inffastTUContracts ++
  Zlib.Crc32.crc32TUContracts ++
  Zlib.Trees.treesTUContracts ++
  Zlib.Infback.infbackTUContracts ++
  Zlib.Inflate.inflateTUContracts ++
  Zlib.Deflate.deflateTUContracts ++
  Zlib.Gzlib.gzlibTUContracts ++
  Zlib.Gzread.gzreadTUContracts ++
  Zlib.Gzwrite.gzwriteTUContracts

/-- Linked C99 program built from all translation units and shared tag declarations. -/
def prog : C99.Prog :=
  let p := C99.Sem.progOfTUs allFiles
  { p with fnProtos := fun sym =>
      if sym == "LSEEK" then p.fnProtos "lseek64" else p.fnProtos sym }

end Zlib
