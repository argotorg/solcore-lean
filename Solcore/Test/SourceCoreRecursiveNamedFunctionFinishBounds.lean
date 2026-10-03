import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeFor
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual compiler equations and concrete builtin imperative trees discharge
both pointwise finish consumers. No flow/body meaning is an external premise.
The original native finish size chooses its real strict child, while the
reflected source body's independent grade is retained. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedFunctionFinishBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCallBounds (BodyTrace)
section Concrete
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {readFuel : Nat}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {type : Ty} {flow code : Expr}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word}
  (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt fellThrough escaped = .ok code)
  (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt true escaped = .ok flow)
  (tree : BuiltinImperativeFor.Tree layouts owner active frameLayout globals onError readFuel values function.source solved reasonAt
    ambient.definitions administrative context scope
    (.statements true function.body) function.resultType type flow)
  (projection : values.checked.catalog.project function.resultType = .ok type)
  {faults : FunctionCalls.FaultRep}
  (unique : NodeOccurrencesUnique function.source)
  (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (escapedFault : faults .controlEscapedFunction escaped)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include accepted generated tree projection unique errors definitions registered extension faithful observations runtimeViews uninitialized missing escapedFault transport in
theorem closed_preserves_at (size : Nat)
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  refine RecursiveNamedFunctionFinishBounds.preserves_at functions program accepted generated tree projection unique escapedFault transport size ?_
    valid environments heaps locals agrees typed reference read unmapped installed trace
  intro currentValid currentMap currentWorld currentContext currentEnvironment currentCanonical currentActual currentBefore currentAfter currentStore currentEmbedding currentLocation currentFrame currentOutcome currentFinalContext
    currentEnvironments currentHeaps currentLocals currentAgrees currentTyped currentReference currentRead currentUnmapped _ currentTrace
  exact BuiltinImperativeFor.Tree.preserves_reachable functions definitions registered extension program function.evidence
    uninitialized missing faithful observations runtimeViews tree errors currentValid unique
    currentEnvironments currentHeaps currentLocals currentAgrees currentTyped currentReference currentRead currentUnmapped currentTrace.sound

include accepted generated tree projection unique errors definitions registered extension faithful observations runtimeViews uninitialized missing escapedFault transport in
theorem closed_reflects_at (budget size : Nat) (within : size ≤ budget)
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  refine RecursiveNamedFunctionFinishBounds.reflects_at functions program accepted generated tree projection unique escapedFault transport budget size within ?_
    valid environments heaps locals agrees typed reference read unmapped installed evaluated
  intro child _ currentValid currentMap currentWorld currentContext currentEnvironment currentCanonical currentActual currentBefore currentStore currentFinalStore currentEmbedding currentLocation currentFrame currentValue
    currentEnvironments currentHeaps currentLocals currentAgrees currentTyped currentReference currentRead currentUnmapped _ currentEval
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    BuiltinImperativeFor.Tree.reflects_reachable functions definitions registered extension program function.evidence
      uninitialized missing faithful observations runtimeViews tree errors currentValid unique
      currentEnvironments currentHeaps currentLocals currentAgrees currentTyped currentReference currentRead currentUnmapped currentEval.sound
  obtain ⟨sourceSize, trace⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size trace
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩
end Concrete

private def content : String := String.intercalate "\n" [
  "function calculate() returns (Word) { let sum = 0; for (let i = 0; i < 5; i += 1) { if (i == 1) { continue; } sum += i; if (i == 3) { break; } } return sum; }",
  "function early() returns (Bool) { let prior = 21; while (true) { let inside = 22; return true; } let skipped = 99; return false; }",
  "function unitFallthrough() { let saved = 23; for (let i = 0; i < 2; i += 1) { let saved = i; } }",
  "function failBody() returns (Word) { let prior = 24; for (let i = 0; true; i += 1) { let saved = 25; let gap: Word; return gap; } let skipped = 26; return skipped; }",
  "function integerResult(left: Word, right: Word) returns (integer) { return integerSub(wordToInteger(left), wordToInteger(right)); }",
  "function mapped() returns (Bool) { let m: mapping(Bool => Word); m[true] = 27; let expected = 27; return m[true] == expected; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let arguments := if name == "integerResult" then [w 7, w 9] else []
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"function finish resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"function finish prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"function finish ordered cells changed {label}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "failBody"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "function finish fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "function finish exact fault binder missing")

def run : IO Unit := do
  let names := ["calculate", "early", "unitFallthrough", "failBody", "integerResult", "mapped"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named function finish bounds" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 829)⟩]}
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("calculate", w 5, [(.word, some (w 5)), (.word, some (w 3))]),
    ("early", .bool true, [(.word, some (w 21)), (.word, some (w 22))]),
    ("unitFallthrough", .unit,
      [(.word, some (w 23)), (.word, some (w 2)), (.word, some (w 0)), (.word, some (w 1))]),
    ("integerResult", .integer (-2), [(.word, some (w 7)), (.word, some (w 9))]),
    ("mapped", .bool true, [(.mapping .bool .word, some (.mapping .bool .word [(.bool true, w 27)])), (.word, some (w 27))])]
  let complete ← successes.mapM fun test => finish compiled test.1 300000 initial
  let failed ← finish compiled "failBody" 300000 initial
  let expectedFault ← faultBinder compiled
  for fuel in [0, 31, 300000] do
    for (test, baseline) in successes.zip complete do
      let (name, expected, expectedCells) := test
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"function finish full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"function finish result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue
          (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"function finish heap not deeply safe {name}"
      | other => throw (IO.userError s!"function finish {name}: {reprStr other}")
    let observation ← finish compiled "failBody" fuel initial
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr failed)
      "function finish full fault resume observation changed"
    match observation with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == expectedFault) "function finish first fault binder changed"
      cells initial final [(.word, some (w 24)), (.word, some (w 0)), (.word, some (w 25)), (.word, none)] "failBody"
    | other => throw (IO.userError s!"function finish fault: {reprStr other}")
  IO.println "recursive named function finish bounds: independent finite body consumers, return/unit/fault, loop transfers, exact source effects and public resume GREEN"

end Tests.SourceCoreRecursiveNamedFunctionFinishBounds
