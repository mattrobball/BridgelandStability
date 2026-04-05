import BridgelandStability
import Informal

#extract_decls BridgelandStability "extracted.json"

def main : IO UInt32 := do
  IO.eprintln "extracted.json was written at build time by #extract_decls"
  return 0
