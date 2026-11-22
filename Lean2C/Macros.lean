import ZlibF.Zlib.«adler32.c»
import ZlibF.Zlib.«crc32.c»
import ZlibF.Zlib.«deflate_base.c»
import ZlibF.Zlib.«inftrees.c»
import ZlibF.Zlib.«trees.c»

namespace Lean2C

/-- Numeric macro settings with named counterparts in the executable model. -/
def macros : List (String × List (String × String)) := [
  ("adler32.c", [("BASE", toString Zlib.Adler32.BASE), ("NMAX", toString Zlib.Adler32.NMAX)]),
  ("crc32.c", [("W", toString Zlib.Crc32.W), ("N", toString Zlib.Crc32.N),
    ("NLOW", toString Zlib.Crc32.NLOW), ("NMIN", toString Zlib.Crc32.NMIN),
    ("BRAID_CUT", toString Zlib.Crc32.BRAID_CUT)]),
  ("deflate.c", [("MAX_STORED", toString Zlib.Deflate.MAX_STORED), ("TOO_FAR", toString Zlib.Deflate.TOO_FAR)]),
  ("inftrees.c", [("MAXBITS", toString Zlib.Inftrees.MAXBITS)]),
  ("trees.c", [("MAX_BL_BITS", toString Zlib.Trees.MAX_BL_BITS), ("END_BLOCK", toString Zlib.Trees.END_BLOCK),
    ("REP_3_6", toString Zlib.Trees.REP_3_6), ("REPZ_3_10", toString Zlib.Trees.REPZ_3_10),
    ("REPZ_11_138", toString Zlib.Trees.REPZ_11_138)])]

end Lean2C
