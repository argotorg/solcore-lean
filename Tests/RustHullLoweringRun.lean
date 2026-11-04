import Solcore.Test.Frontend.RustHull.Correspondence

def main : IO Unit := do
  Tests.RustHullYul.run
  Tests.RustHullLowering.run
