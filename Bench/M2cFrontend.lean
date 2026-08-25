import Solcore.Surface.Multi.Properties

set_option autoImplicit false

open Solcore.Workspace
open Solcore.Surface.Multi

namespace Bench.M2cFrontend

private def makeFile (content : String) : Option WorkspaceFile :=
  (CanonicalSourcePath.parse "Bench.solc").map fun path => {
    id := { library := .main, path }
    content
  }

private def observeResult
    (result : Except SurfaceDiagnostic ParsedModuleV1) :
    IO (Except String Nat) :=
  match result with
  | .ok parsed => pure (.ok parsed.payload.items.length)
  | .error diagnostic => pure (.error (diagnosticCode diagnostic))

private def runCase
    (name content : String) (expectedItems : Nat) : IO UInt32 := do
  let some file := makeFile content
    | IO.println s!"case={name} outcome=harness-error reason=invalid-path status=fail"
      return 2
  let started ← IO.monoNanosNow
  let observed ← observeResult (executeObservedContextualFrontend file)
  let finished ← IO.monoNanosNow
  let elapsed := finished - started
  match observed with
  | .ok actualItems =>
      if actualItems == expectedItems then
        IO.println
          s!"case={name} elapsed_ns={elapsed} outcome=ok items={actualItems} expected_items={expectedItems} status=pass"
        return 0
      else
        IO.println
          s!"case={name} elapsed_ns={elapsed} outcome=ok items={actualItems} expected_items={expectedItems} status=fail"
        return 1
  | .error code =>
      IO.println
        s!"case={name} elapsed_ns={elapsed} outcome=error code={code} expected_items={expectedItems} status=fail"
      return 1

end Bench.M2cFrontend

def main (args : List String) : IO UInt32 :=
  match args with
  | ["empty"] => Bench.M2cFrontend.runCase "empty" "" 0
  | ["tiny"] => Bench.M2cFrontend.runCase "tiny" "data A;" 1
  | ["import-path"] =>
      Bench.M2cFrontend.runCase "import-path" "import lib.core;" 1
  | ["return-literal"] =>
      Bench.M2cFrontend.runCase
        "return-literal" "function f() { return 0; }" 1
  | ["data-constructors"] =>
      Bench.M2cFrontend.runCase
        "data-constructors" "data Bool = False | True;" 1
  | ["contract-field"] =>
      Bench.M2cFrontend.runCase
        "contract-field" "contract C { value: word; }" 1
  | _ => do
      IO.println
        "usage: m2c-frontend-bench (empty|tiny|import-path|return-literal|data-constructors|contract-field)"
      return 2
