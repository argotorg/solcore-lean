import Solcore.Frontend.SourceCoreRootDiscovery

#check_failure Solcore.Frontend.SourceCoreRootDiscovery.CheckedEntry.mk

/-! Conventional main and exported ABI roots retain exact names and canonical
module identities without a runtime backend selection. Conflict diagnostics
are the existing Static Word profile's deterministic diagnostics. -/
set_option autoImplicit false
namespace Tests.SourceCoreRootDiscovery
open Solcore Solcore.Frontend SourceCoreRootDiscovery
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def single (content : String) : Workspace.RawWorkspace := {
  entry := "api.solc", externalLibraries := [], mainSources := [{path := "api.solc", content}] }
private def workspace : Workspace.RawWorkspace := {
  entry := "api.solc", externalLibraries := [], mainSources := [
    {path := "api.solc", content := String.intercalate "\n" [
      "import {twice as doubled, recursive} from provider;",
      "function main() returns (Word) { return 17; }",
      "function local(value: Word) returns (Word) { return value + 1; }",
      "function hidden(value: Word) returns (Word) { return value; }",
      "export {doubled, local, recursive};"]},
    {path := "provider.solc", content := String.intercalate "\n" [
      "function twice(value: Word) returns (Word) { return value * 2; }",
      "function recursive(value: Word) returns (Word) { return value == 0 ? 31 : recursive(value - 1); }",
      "function providerOnly(value: Word) returns (Word) { return value; }",
      "export {twice, recursive, providerOnly};"]}] }

example {raw : Workspace.RawWorkspace} {fuel : Nat} (entry : CheckedEntry raw fuel) :
    checkProgram raw fuel = .ok entry.program := entry.source_checked

def run : IO Unit := do
  let checked ← get "entry discovery" (checkEntry workspace)
  let request ← get "conventional main resolution" (SourceProgramExecution.resolveSeed checked.program checked.seed)
  require (request.declaration.moduleId == checked.moduleId) "main resolution changed the entry module"
  let roots ← get "ABI discovery" (discoverStaticWordRoots checked.program checked.moduleId)
  require (roots.map (·.metadata.name.text) == ["local", "doubled", "recursive"])
    s!"ABI alias/order/visibility changed: {reprStr (roots.map (·.metadata.name.text))}"
  let compiled ← get "one ABI Core compilation"
    (SourceCoreCompiler.compileChecked checked.program (roots.map (·.seed)) {specializationBudget := 128, compilationFuel := 1000})
  require (compiled.rootCount == 3 && compiled.roots.map (·.inputTypes) == [[.word], [.word], [.word]]) "ABI roots lost source metadata"
  let missing ← get "missing main check" (checkEntry (single "function helper() returns (Word) { return 0; }"))
  match SourceProgramExecution.resolveSeed missing.program missing.seed with
  | .error (.unknownName moduleId "main") => require (moduleId == missing.moduleId) "missing main lost canonical module"
  | _ => throw (IO.userError "missing main was accepted")
  let invalid ← get "invalid ABI check" (checkEntry (single "function bad(value: Bool) returns (Word) { return value ? 1 : 0; } export {bad};"))
  match discoverStaticWordRoots invalid.program invalid.moduleId with
  | .error (.unsupportedParameters _ "bad" [.bool] [false]) => pure ()
  | _ => throw (IO.userError "unsupported ABI parameter was skipped")
  let duplicate ← get "duplicate ABI check" (checkEntry (single "function same(value: Word) returns (Word) { return value; } function same(value: Word) returns (Word) { return value + 1; } export {same};"))
  match discoverStaticWordRoots duplicate.program duplicate.moduleId with
  | .error (.duplicateSignature "same" "same" "same(uint256)") => pure ()
  | _ => throw (IO.userError "duplicate ABI signature diagnostic changed")
  let collision ← get "selector collision check" (checkEntry (single "function f116643(value: Word) returns (Word) { return value; } function f38491(value: Word) returns (Word) { return value; } export {f38491, f116643};"))
  match discoverStaticWordRoots collision.program collision.moduleId with
  | .error (.selectorCollision "f116643" "f38491" "f116643(uint256)" "f38491(uint256)" selector) =>
      require (selector.toUInt32.toNat == 0x77dbd42e) "selector conflict lost its canonical selector"
  | _ => throw (IO.userError "selector collision diagnostic changed")
  match checkEntry (single "function bad() returns (Word) { return absent; }") with
  | .error _ => pure () | .ok _ => throw (IO.userError "root discovery bypassed source checking")

end Tests.SourceCoreRootDiscovery
