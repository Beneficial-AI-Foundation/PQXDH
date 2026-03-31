import VersoManual
import PQXDHDocs.Contents

open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  manualMain (%doc PQXDHDocs.Contents) (options := args)
