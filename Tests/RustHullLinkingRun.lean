import Solcore.Test.RustHullCodeImage
import Solcore.Test.RustHullObjectLinking

def main : IO Unit := do
  Tests.RustHullCodeImage.run
  Tests.RustHullObjectLinking.run
