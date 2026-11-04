import Solcore.Test.Frontend.RustHull.Creation

def main : IO Unit := do
  Tests.RustHullCodeImage.run
  Tests.RustHullObjectLinking.run
