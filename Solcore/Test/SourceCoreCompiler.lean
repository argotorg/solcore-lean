import Solcore.Frontend.SourceCoreCompiler

#check_failure Solcore.Frontend.SourceCoreCompiler.Options.backendPreference
#check_failure Solcore.Frontend.SourceCoreCompiler.Compiled.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! One cached compiler artifact serves ordered and duplicate roots. Source
metadata comes from canonical specialization; raw mapping carriers remain a
compatibility observation used only to exercise the cached code here. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompiler
open Solcore Solcore.Frontend SourceCoreCompiler

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function identity<T>(value: T) returns (T) { return value; }",
    "function mappingEcho(value: mapping(Word => Word)) returns (mapping(Word => Word)) { return value; }",
    "function capture(seed: Word) returns (function(Word) returns (Word)) { let current = seed; return lam(step: Word) { current += step; return current; }; }"
  ]}] }
private def options : Options := { specializationBudget := 256, compilationFuel := 1000 }
private def declaration (program : CheckedProgram) (name : String) : IO Resolved.DeclarationId :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure signature.id
  | _ => throw (IO.userError s!"compiler fixture missing {name}")

example (compiled : Compiled) {cached : Cached} (selected : compiled.artifact? = some cached) :
    cached.sourceProgram = compiled.program ∧ cached.validationPlan = compiled.plan ∧ compiled.keys = cached.keys :=
  compiled.artifact_fields selected
example (compiled : Compiled) :
    SourceCompilationPlan.validateExecutablePlanEvidence compiled.program compiled.plan = .ok () := compiled.plan_validated
example {plan : Plan} (root : Root plan) :
    ∃ specialized,
      SourceCompilationPlan.exactSpecialization plan root.key = .ok specialized ∧
      root.inputTypes = specialized.function.typedBody.inputs.map (·.scheme.body) ∧
      root.resultType = specialized.function.inferredBodyType := root.source_metadata
example {raw : Workspace.RawWorkspace} {seeds : List Seed} {options : Options} {compiled : Compiled}
    (accepted : compile raw seeds options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.program := compile_checked_source accepted
example (compiled : Compiled) (empty : compiled.artifact? = none) :
    compiled.roots = [] ∧ compiled.plan.seedKeys = [] := compiled.no_artifact_empty empty

def run : IO Unit := do
  let program ← get "single Core checking" (checkProgram workspace)
  let identity ← declaration program "identity"
  let mapping ← declaration program "mappingEcho"
  let capture ← declaration program "capture"
  let seeds := [Seed.declaration mapping, Seed.declaration identity [.word],
    Seed.declaration capture, Seed.declaration identity [.word]]
  let compiled ← get "single Core compilation" (compileChecked program seeds options)
  let cached ← match compiled.artifact? with
    | some cached => pure cached | none => throw (IO.userError "nonempty roots have no cached code")
  require (compiled.rootCount == 4) "ordered roots were deduplicated"
  require (compiled.roots.map (·.seed) == seeds) "source root order changed"
  require (compiled.keys[1]? == compiled.keys[3]?) "duplicate root changed canonical specialization"
  let roots := compiled.roots
  require (roots.map (·.inputTypes) == [[.mapping .word .word], [.word], [.word], [.word]]) "public input metadata changed"
  require (roots.map (·.resultType) == [.mapping .word .word, .word, .function .word .word, .word]) "public result metadata changed"
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  let mappingKey ← match compiled.keys[0]? with
    | some key => pure key | none => throw (IO.userError "mapping root missing")
  let mapped ← get "cached raw mapping" (cached.run mappingKey [raw] 500 300000)
  match mapped.observation with
  | .done value _ => require (reprStr value == reprStr raw) "one compiler lost raw mapping metadata or duplicates"
  | other => throw (IO.userError s!"cached mapping failed: {reprStr other}")
  let identityKey ← match compiled.keys[1]? with
    | some key => pure key | none => throw (IO.userError "identity root missing")
  for value in [w 3, w 11] do
    let result ← get "reused cached identity" (cached.run identityKey [.word value] 500 300000)
    match result.observation with
    | .done (.word actual) _ => require (actual == value) "cached root reuse changed value"
    | other => throw (IO.userError s!"cached identity failed: {reprStr other}")
  let rawCompiled ← get "raw single Core compiler" (compile workspace seeds options)
  require (rawCompiled.keys == compiled.keys) "raw and checked compiler changed root identities"
  match compileChecked program [Seed.declaration mapping, Seed.declaration identity] options with
  | .error (.seed 1 _ (.typeArgumentArityMismatch owner 1 0)) => require (owner == identity) "wrong rejected seed"
  | other => throw (IO.userError s!"single Core compiler lost exact seed rejection: {other.toOption.isSome}")
  match compileChecked program [Seed.declaration mapping] {options with specializationBudget := 0} with
  | .error (.specializationBudgetExhausted _ _) => pure ()
  | _ => throw (IO.userError "single Core compiler lost discovery budget rejection")
  let empty ← get "empty ordered roots" (compileChecked program [] options)
  require (empty.rootCount == 0 && empty.keys.isEmpty) "empty compilation invented a root"
  require empty.artifact?.isNone "empty compilation invented callable code"

end Tests.SourceCoreCompiler
