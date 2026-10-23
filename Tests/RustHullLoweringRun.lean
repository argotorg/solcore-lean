import Solcore.Test.RustHullLowering
import Solcore.Test.RustHullYul

def main : IO Unit := do
  Tests.RustHullYul.run
  Tests.RustHullLowering.run
