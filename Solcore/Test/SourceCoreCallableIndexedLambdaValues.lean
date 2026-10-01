import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityMeaning
import Solcore.Frontend.SourceCoreCallableIndexedRestoration
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaValues
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedLambdaValues GeneralHeap CompatiblePayload

theorem anonymous_comparison {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) (comparator : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {mapping : LocationMap}
    {sourceType : TypeSystem.Ty} {function : Dynamic.Closure} {native : Core.Value}
    (related : (model prepared profile).Represents registry mapping world sourceType (.closure function) native comparator.type)
    (store : Store) :
    Evaluates [native, native] store (CompatibleEquality.comparison comparator (.var 0) (.var 1)) (.bool false)
      (CompatibleEquality.preparedStore comparator [native, native] store) := by
  obtain ⟨result, equivalent, evaluated⟩ := CompatibleEquality.prepared_compare_preserves comparator
    (identity_faithful prepared) (observations prepared profile related) (observations prepared profile related)
    [native, native] store (.var 0) (.var 1) (.var rfl) (.var rfl)
  cases result with
  | false => exact evaluated
  | true => have impossible := (equivalent.mp rfl).2; cases impossible

/-- The completion is consumed after the actual renamed formation code, with
source captures and both full worlds retained. No body execution is supplied. -/
theorem completed_source {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap}
    {world : StoreTyping} {actual : Core.Environment}
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (program : SourceSemantics.Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = [])
    {before after : Store} {location : Location} {result : Core.Value}
    (stored : RuntimeStoreHasTypes world before prepared.layouts.definitions)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native))
    (completed : Evaluates actual before (code.lowered.expression.rename captured.embedding) result after) :
    after = before ∧ Dynamic.ExpressionEvaluates program function.context function.evidence function.source
      function.captured heap code.id (.closure function) heap := by
  have reflected := reflects captured code history program heap ordinary coercions stored reference read completed
  exact ⟨reflected.2.1, reflected.2.2.1⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function pair(seed: Word) returns (F, F) { let unused: Word = 9; let f: F = lam(item: Word) -> Word { seed += item; return seed; }; return (f, f); }",
    "function qualified<T>(seed: T) returns (function(T) returns (T)) where T: Mark { return lam(item: T) -> T { return keep(item); }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) (arguments : List TypeSystem.Ty) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, arguments⟩
  | none => throw (IO.userError s!"missing lambda fixture {name}")

private def capture {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    (templates : SourceCoreCallableIndexedTemplates.Cache prepared)
    (headers : SourceCoreCallablePairedHeaders.Prepared prepared.ancestry.graph)
    {world : StoreTyping} {store : Store} {native : Core.Value}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (typed : RuntimeValueHasType world native (CallableContract.functionType .word .word) prepared.layouts.definitions)
    (expectedEvidence : Nat) : IO SourceTypedRuntime.Environment := do
  let authenticated ← SourceCompilerFeatureSupport.get "owned indexed lambda"
    (SourceCoreCallableIndexedTemplates.authenticate templates stored native .word .word typed)
  let initial : List SourceTypedRuntime.Cell := [⟨.word, none⟩, ⟨.bool, none⟩]
  let ledger ← SourceCompilerFeatureSupport.get "lambda capture ledger"
    (SourceCoreAllocationLedger.scanTyped prepared.layouts initial world store stored)
  let restored ← SourceCompilerFeatureSupport.get "lambda raw header"
    (SourceCoreCallableIndexedRestoration.restoreOrdinary headers authenticated ledger)
  SourceCompilerFeatureSupport.require (restored.header.context.context.evidence.length == expectedEvidence)
    "lambda lexical dictionary was changed or inferred from its type"
  SourceCompilerFeatureSupport.require (authenticated.current.frame == .empty) "lambda formation failed to restore the caller frame"
  SourceCompilerFeatureSupport.require (restored.captures.environment.all (fun item => item.2.index ≥ initial.length))
    "lambda capture lost the opaque source prefix"
  SourceCompilerFeatureSupport.require (decide (restored.captures.environment.map Prod.fst = authenticated.template.source.scope.map Prod.fst))
    "lambda lexical capture order changed"
  pure restored.captures.environment

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "lambda value checker" (checkProgram workspace)
  let pairKey ← key program "pair" []
  let qualifiedKey ← key program "qualified" [.word]
  let qualifiedParameters ← match program.signatures.functions.find? (·.name == "qualified") with
    | some signature => pure signature.scheme.parameters
    | none => throw (IO.userError "missing qualified signature")
  let plan ← match SourceSpecializationWorklist.run program
      [⟨pairKey.declaration, []⟩, ⟨qualifiedKey.declaration, qualifiedParameters.zip [.word]⟩] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"lambda value worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "lambda base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "lambda indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let templates ← SourceCompilerFeatureSupport.get "lambda templates" (SourceCoreCallableIndexedTemplates.prepare prepared)
  let headers ← SourceCompilerFeatureSupport.get "lambda headers" (SourceCoreCallablePairedHeaders.prepare prepared.ancestry.graph)
  let word := Word.ofNatModulo
  for spent in [0, 21, 300000] do
    let started ← SourceCompilerFeatureSupport.get "lambda pair start" (prepared.runSource pairKey [.word (word 3)] spent)
    let completion := started.resume 300000
    if same : completion.entry.native.resultType = .product (CallableContract.functionType .word .word) (CallableContract.functionType .word .word) then
      match done : completion.result.native.observation with
      | .succeeded (.pair left right) store =>
          have typed : RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
              RuntimeValueHasType (store.map Core.Value.type) left (CallableContract.functionType .word .word) prepared.layouts.definitions ∧
              RuntimeValueHasType (store.map Core.Value.type) right (CallableContract.functionType .word .word) prepared.layouts.definitions := by
            obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed done
            have worlds := stored.world_eq
            subst world
            rw [same] at typed
            cases typed with | pair first second => exact ⟨stored, first, second⟩
          let first ← capture templates headers typed.1 typed.2.1 0
          let second ← capture templates headers typed.1 typed.2.2 0
          SourceCompilerFeatureSupport.require (first == second && first.length == 2) "shared lambda captures or unused lexical slot changed"
          let comparator ← SourceCompilerFeatureSupport.get "lambda comparison" (SourceCoreCompatibleDataEquality.prepare 500 automatic.checked (.function .word .word))
          SourceCompilerFeatureSupport.require (runStateful 100000 (.initial (CompatibleEquality.comparison comparator (.var 0) (.var 1)) [left, right] store) ==
            .done (.bool false) (CompatibleEquality.preparedStore comparator [left, right] store))
            "anonymous lambdas were assigned a named identity"
          let applyTwice := LocalSequence.pair .word .word
            (.apply (.second (.first (.var 1))) (.word (word 10)))
            (.apply (.second (.first (.var 0))) (.word (word 20)))
          match runStateful 100000 (.initial applyTwice [right, left] store) with
          | .done (.inRight .word (.pair (.word first) (.word second))) finalStore =>
            SourceCompilerFeatureSupport.require (first == word 13 && second == word 33) "shared captured source cell stopped aliasing"
            SourceCompilerFeatureSupport.require (finalStore[0]? == some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame .empty))
              "lambda invocation did not restore its caller"
          | other => throw (IO.userError s!"lambda native reuse {reprStr other}")
      | other => throw (IO.userError s!"lambda pair completion {reprStr other}")
    else throw (IO.userError "lambda pair projected type changed")
  let qualified ← SourceCompilerFeatureSupport.get "qualified lambda" (prepared.runSource qualifiedKey [.word (word 7)] 300000)
  if same : qualified.entry.native.resultType = CallableContract.functionType .word .word then
    match done : qualified.result.native.observation with
    | .succeeded native store =>
      have typed : RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
          RuntimeValueHasType (store.map Core.Value.type) native (CallableContract.functionType .word .word) prepared.layouts.definitions := by
        obtain ⟨world, stored, typed⟩ := qualified.result.native.success_typed done
        have worlds := stored.world_eq
        subst world
        rw [same] at typed
        exact ⟨stored, typed⟩
      let _ ← capture templates headers typed.1 typed.2 1
      pure ()
    | other => throw (IO.userError s!"qualified lambda completion {reprStr other}")
  else throw (IO.userError "qualified lambda projected type changed")
  IO.println "indexed lambda leaves: actual templates, ordered shared captures, retained dictionary, anonymous equality and resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaValues
