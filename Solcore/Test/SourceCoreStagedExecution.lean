import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.SourceCoreSession

/-! Actual compiled callable contracts preserve the source invocation observations.
The public session, internal source observation adapter and ordinary prepared
body all execute Core. Owned handles retain the actual native descriptor. -/

set_option autoImplicit false
namespace Tests.SourceCoreStagedExecution
open Solcore Solcore.Frontend
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function markedEffects(comptime seed: Word) returns (comptime<Word>) { let total: Word = seed; let table: mapping(Word => Word); let bump = lam(comptime delta: Word) -> Word { total += delta; table[0] = total; return table[0]; }; return bump(3); }",
    "function markedEffectsEntry() returns (Word) { return markedEffects(9); }",
    "function markedClosureClosed() returns (Word) { let f = lam(comptime value: Word) -> Word { return value; }; return f(21); }",
    "function markedClosureRuntime(value: Word) returns (Word) { let f = lam(comptime item: Word) -> Word { return item; }; return f(value); }",
    "function markedGlobal(comptime value: Word) returns (Word) { return value; }",
    "function markedGlobalClosed() returns (Word) { let f = markedGlobal; return f(22); }",
    "function markedGlobalRuntime(value: Word) returns (Word) { let f = markedGlobal; return f(value); }",
    "function markedResult(comptime value: Word) returns (comptime<Word>) { return value; }",
    "function markedResultIndirectBlocked() returns (Word) { let f = markedResult; return f(23); }",
    "function markedResultIndirectStaged() returns (comptime<Word>) { let f = markedResult; return f(24); }",
    "function tupleBefore() returns (Word) { let trace: Word = 0; let f = lam(value: (Word, Word)) -> Word { return 7; }; let bump = lam() -> Word { trace += 1; return trace; }; return f(bump(), bump()); }",
    "function tupleAfter() returns (comptime<Word>) { let trace: Word = 0; let f = lam(value: (Word, Word)) -> Word { return 7; }; let bump = lam() -> Word { trace += 1; return trace; }; return f(bump(), bump()); }",
    "function tupleAccepted() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f((1, 2)); }",
    "function polymorphic(flag: Bool) returns (Word, Bool) { let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }",
    "function nested(flag: Bool) returns (Word, Word) { let outer = lam(item) { keep(item); let inner = lam(value) { return keep(value); }; return inner(1); }; return (outer(13), outer(flag)); }",
    "type F = function(Word) returns (Word);",
    "function maker(seed: Word) returns (F) { let total: Word = seed; let f = lam(item) { keep(item); total += 1; return total; }; return f; }",
    "function use(f: F, item: Word) returns (Word) { return f(item); }",
    "function identities() returns (Word, Word) { let table: mapping(F => Word); table[markedGlobal] = 7; table[markedGlobal] = 9; let f = lam(item: Word) -> Word { return item; }; table[f] = 11; table[f] = 13; return (table[markedGlobal], table[f]); }",
    "function builtinCall(value: integer) returns (Word) { let f = wordFromInteger; return f(value); }"
  ]}]
}

private def key (program : CheckedProgram) (name : String) : IO SourceCoreGeneralFunctions.Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"staged execution function missing: {name}")

private def plan (program : CheckedProgram) (keys : List SourceCoreGeneralFunctions.Key) : IO SourceCoreGeneralFunctions.Plan :=
  match SourceSpecializationWorklist.run program (keys.map fun key => ⟨key.declaration, []⟩) 128 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"staged execution worklist failed: {reprStr result}")

private def prepare (program : CheckedProgram) (keys : List SourceCoreGeneralFunctions.Key) : IO SourceCoreSession.Recipe := do
  let plan ← plan program keys
  match SourceCoreSession.Recipe.prepareAutomatic program plan 256 true with
  | .ok recipe => pure recipe
  | .error error => throw (IO.userError s!"staged execution compile failed: {reprStr error}")

private def publicArgument : Core.Value → Option SourceCoreExecution.Value
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | _ => none

private def legacyNative : SourceTypedRuntime.Value → Option Core.Value
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .product left right => do pure (.pair (← legacyNative left) (← legacyNative right))
  | _ => none


private def check (program : CheckedProgram) (name : String) (arguments : List Core.Value)
    (expected : Option Core.Value) (trace : Option Core.Word := none) : IO Unit := do
  let key ← key program name
  let recipe ← prepare program [key]
  let entry ← match recipe.program.findEntry? key with
    | some entry => pure entry
    | none => throw (IO.userError "staged cached entry missing")
  let compiled ← SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 128, compilationFuel := 1000}
  let publicInputs ← match arguments.mapM publicArgument with
    | some values => pure values
    | none => throw (IO.userError "staged fixture has unsupported public input")
  let old := (← compiled.audit publicInputs).observation
  let verify := fun observation diagnosticAt => do
    match observation, old, expected with
    | .succeeded value _, .done oldValue _, some expected =>
        unless value == expected && legacyNative oldValue == some expected do
          throw (IO.userError s!"{name} staged result changed: {reprStr value}")
    | .failed reason store, .fault oldError _, none =>
        let diagnostic ← match diagnosticAt reason with
          | some diagnostic => pure diagnostic
          | none => throw (IO.userError s!"{name} lost staged diagnostic")
        unless diagnostic.error == oldError do
          throw (IO.userError s!"{name} staged diagnostic differs: {reprStr diagnostic.error}; old: {reprStr oldError}")
        if let some trace := trace then
          let scalars := store.filterMap fun | .inRight .unit (.word value) => some value | _ => none
          unless scalars == [trace] do throw (IO.userError s!"{name} changed argument/parameter effects: {reprStr scalars}")
    | observation, _, _ => throw (IO.userError s!"{name} staged outcome changed: {reprStr observation}")
  for _ in [0, 1] do
    match entry.run arguments 65536 with
    | .ok result => verify result.observation entry.faultSites.diagnostic?
    | .error error => throw (IO.userError s!"{name} staged input rejected: {reprStr error}")
  match entry.run arguments 0 with
  | .ok {observation := .outOfFuel state, ..} => verify (Core.LanguageResult.observeResult (Core.runStateful 65536 state)) entry.faultSites.diagnostic?
  | _ => throw (IO.userError s!"{name} staged entry did not suspend")
  for _ in [0, 1] do
    let invoked ← compiled.invoke publicInputs
    match invoked.outcome, old with
    | .succeeded completion, .done value _ =>
        let observed ← SourceCompilerFeatureSupport.get "public staged value"
          (SourceCompilerFeatureSupport.rawData 128 completion.value)
        unless reprStr observed == reprStr value do
          throw (IO.userError s!"{name} public staged value changed")
    | .failed reason _, .fault error _ =>
        match ← invoked.diagnostic reason with
        | some diagnostic => unless diagnostic.error == error do
            throw (IO.userError s!"{name} public staged diagnostic changed")
        | none => throw (IO.userError s!"{name} public staged diagnostic missing")
    | _, _ => throw (IO.userError s!"{name} public staged classification changed")
  let artifact ← compiled.execution.open
  let session ← SourceCompilerFeatureSupport.boot artifact
  let checkpoint ← SourceCompilerFeatureSupport.get "public staged checkpoint" (session.start compiled.key publicInputs)
  let pending ← match ← checkpoint.resume 0 with
    | .outOfFuel pending => pure pending
    | _ => throw (IO.userError "public staged zero fuel did not suspend")
  match ← pending.resume 300000 with
  | .succeeded completion =>
      match old with
      | .done value _ =>
          let observed ← SourceCompilerFeatureSupport.get "public staged resumed value"
            (SourceCompilerFeatureSupport.rawData 128 completion.value)
          unless reprStr observed == reprStr value do throw (IO.userError "public staged resume changed result")
      | _ => throw (IO.userError "public staged resume changed fault into success")
  | .failed reason session =>
      match old, ← SourceCompilerFeatureSupport.get "public resumed diagnostic" (session.diagnostic compiled.key reason) with
      | .fault error _, some diagnostic =>
          unless diagnostic.error == error do throw (IO.userError "public staged resume changed diagnosis")
      | _, _ => throw (IO.userError "public staged resume changed fault")
  | _ => throw (IO.userError "public staged resume did not complete")

def run : IO Unit := do
  let program ← match checkProgram workspace 4096 with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"staged source rejected: {reprStr error}")
  check program "markedEffects" [.word (w 9)] (some (.word (w 12)))
  check program "markedEffectsEntry" [] (some (.word (w 12)))
  check program "markedClosureClosed" [] (some (.word (w 21)))
  check program "markedClosureRuntime" [.word (w 25)] none
  check program "markedGlobalClosed" [] (some (.word (w 22)))
  check program "markedGlobalRuntime" [.word (w 25)] none
  check program "markedResultIndirectBlocked" [] none
  check program "markedResultIndirectStaged" [] (some (.word (w 24)))
  check program "tupleBefore" [] none (some (w 0))
  check program "tupleAfter" [] none (some (w 2))
  check program "tupleAccepted" [] (some (.word (w 7)))
  check program "identities" [] (some (.pair (.word (w 9)) (.word (w 0))))
  check program "builtinCall" [.integer 42] (some (.word (w 42)))
  for flag in [true, false] do
    check program "polymorphic" [.bool flag] (some (.pair (.word (w 1)) (.bool flag)))
    check program "nested" [.bool flag] (some (.pair (.word (w 1)) (.word (w 1))))
  let producer ← key program "maker"
  let consumer ← key program "use"
  let recipe ← prepare program [producer, consumer]
  let artifact ← recipe.open
  let session ← artifact.newSession
  match ← session.run producer [.word (w 10)] 65536 256 with
  | .ok (.succeeded made) =>
      let handle ← match made.value with
        | .function handle => pure handle
        | _ => throw (IO.userError "staged closure was not exported as owned handle")
      unless made.session.functionIdentity? handle == some .anonymous do
        throw (IO.userError "wrapper lost anonymous owned identity")
      match ← made.session.run consumer [made.value, .word (w 1)] 65536 256 with
      | .ok (.succeeded first) =>
          unless first.value == .word (w 11) do throw (IO.userError "staged handle lost its capture")
          match ← first.session.run consumer [made.value, .word (w 2)] 65536 256 with
          | .ok (.succeeded second) =>
              unless second.value == .word (w 12) do throw (IO.userError "staged handle lost capture mutation")
          | _ => throw (IO.userError "staged handle second invocation failed")
      | _ => throw (IO.userError "staged handle invocation failed")
  | _ => throw (IO.userError "staged handle export failed")
  IO.println "actual staged Core compilation, guards, effects and owned captures GREEN"

end Tests.SourceCoreStagedExecution
