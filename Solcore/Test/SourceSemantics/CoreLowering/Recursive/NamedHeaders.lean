import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinImperative
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.ForFinite
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConditionals
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchReady
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedFunctionLoops
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.PlaceAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalStatements
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues

/-!
# Recursive named header tests

Headers, parameters, matches, places, lambdas, programs and specialization of recursive named functions.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedFunctionFinishBounds
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedHeaderBounds
/-! Native prefix bounds and independently measured source prefixes. These
consumers preserve the actual derivation under the seven assignment and six
post slots. They do not establish bounded assignment child meaning or the
whole header/for semantic factor, which remain separate integration units. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedHeaderBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof RecursiveNamedHeaderContracts
open CallableIndexedHistory (NativeFrame)
open SourceCoreCompatibleDataPlaces
open DataPlaceExecution (referenceEnvironment keysEnvironment snapshotEnvironment rhsEnvironment modifiedEnvironment writtenEnvironment)

/-- A strict-only family cannot be applied to an unchanged empty prefix. -/
theorem strict_does_not_supply_equal (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget (fun size => size < budget) ∧
      ¬ AtMost budget (fun size => size < budget) := by
  exact ⟨fun _ smaller => smaller, fun inclusive => Nat.lt_irrefl _ (inclusive budget (Nat.le_refl _))⟩

section Nil
variable {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {program : SourceSemantics.Program}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {solved : List SolvedRequirement}
  {administrative : Core.Context} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {registry : SourceCoreRawMetadata.Registry} {type : Core.Ty} {faults : FunctionCalls.FaultRep}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
  {contextLocation : Location} {native : NativeFrame} {value : Core.Value} {finalStore : Store}

/-- The real same-size continuation can be consumed at the inclusive bound. -/
theorem nil_keeps_size {size : Nat}
    {meaning : Nat → SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}
    (tail : ProtectedForHeader.Tail (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native (ContinuationWithin size meaning) context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    ResultAt size (entry := entry) registry functions program source solved evidence administrative frame globals
      contextLocation native type faults (ContinuationWithin size meaning) context environment heap []
      tail.mapping tail.world tail.store value finalStore ∧ meaning size context tail.scope tail.code :=
  ⟨ResultAt.nil tail evaluated, tail_at_remaining tail (Nat.le_refl size) (Nat.le_refl size)⟩
end Nil

section SourceFault
variable {program : SourceSemantics.Program} {size : Nat} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {binder : TypedBinder} {initializer : ExpressionId}
  {items : List ForItemForm} {reason : Dynamic.SemanticFault}

/-- Initializer failure retains its actual effects without extending context or
allocating the declared binding. Its expression witness is strictly smaller. -/
theorem initializer_fault_context (mono : binder.scheme.quantified = [])
    (failed : SourceExecutionSize.ExpressionFaults program size context evidence source environment before initializer reason after) :
    SourceExecutionSize.ForItemsFault program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [size]])
      context evidence source environment before (.letDecl binder (some initializer) :: items) context reason after ∧
    size < SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [size]] := by
  exact ⟨.head (.letInitializer mono failed), Nat.lt_trans
    (SourceExecutionSize.child_lt_stepSize (children := [size]) (by simp))
    (SourceExecutionSize.child_lt_stepSize (children := [SourceExecutionSize.stepSize [size]]) (by simp))⟩
end SourceFault

theorem assignment_continuation_below {size budget : Nat} {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore modifiedStore setterStore written finalStore : Store}
    {location : Location} {keyValue snapshot right changed updated old result : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType location keyValue snapshot right changed environment) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word updated) setterStore)
    (read : setterStore.read? location = some old)
    (write : setterStore.write? location (.inRight .unit updated) = some written)
    (completed : EvaluationSize size environment before
      (execute prepared reference keys rhs next outputType operator bitNot invalidOperand) result finalStore) (bounded : size ≤ budget) :
    ∃ remainingSize, remainingSize < budget ∧
      EvaluationSize remainingSize
        (writtenEnvironment prepared.route.rootType location keyValue snapshot right changed updated environment)
        written (shift 7 next) result finalStore := by
  obtain ⟨remainingSize, smaller, remaining⟩ := ForHeaderNativeBounds.execute_continuation
    referenceSelected keysEvaluated snapshotEvaluated rhsEvaluated modifiedEvaluated setterEvaluated read write completed
  exact ⟨remainingSize, Nat.lt_of_lt_of_le smaller bounded, remaining⟩

/-- The post witness is a strict child of the original loop body. Renaming it
under the six concrete temporaries leaves its size unchanged. -/
theorem post_below_loop {size budget : Nat} {actual : Environment} {before conditionStore bodyStore after : Store}
    {type : Core.Ty} {location : Location} {condition body post : Expr} {reason : Word} {value : Core.Value}
    (continued : Bool)
    (completed : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) before
      (LocalLoop.loopBody type condition body post reason) value after)
    (conditionEval : Evaluates (Core.LoopExecution.entryEnvironment type location actual) before
      (Core.LoopExecution.conditionCode condition) (.inRight .word (.bool true)) conditionStore)
    (bodyEval : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) conditionStore
      (Core.LoopExecution.bodyCode body)
      (if continued then LocalLoop.continuingValue type else LocalLoop.fallthroughValue type) bodyStore)
    (bounded : size ≤ budget) :
    ∃ postSize postStore postValue, postSize < budget ∧
      EvaluationSize postSize (TypedImperativeFor.postValues type location continued ++ actual)
        bodyStore (ForLoop.postCode post) postValue postStore := by
  obtain ⟨branchSize, smaller, branch⟩ := completed.loop_true_branch conditionEval
  obtain ⟨postSize, postStore, postValue, postSmaller, evaluated⟩ :=
    ForHeaderNativeBounds.post_computation_sized continued branch bodyEval
  exact ⟨postSize, postStore, postValue, Nat.lt_of_lt_of_le (Nat.lt_trans postSmaller smaller) bounded, evaluated⟩

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function empty(raw: mapping(Word => Word)) returns (Word) { for (; false;) { raw[1] = 999; } return raw[1]; }",
  "function post(raw: mapping(Word => Word)) returns (Word) { let count = 0; for (let index: Word, index = 0, next(index); index < 3; let saved: Word, saved = next(index), let copy = saved, raw[1] += copy, index += 1) { count += 1; continue; } return raw[1] + count; }",
  "function initialFault(raw: mapping(Word => Word)) returns (Word) { for (raw[1] += 1, let stop = bad(0); true; raw[1] += 90) { raw[1] += 99; } return raw[1]; }",
  "function postFault(raw: mapping(Word => Word)) returns (Word) { for (let index = 0; index < 3; raw[1] += 1, let stop = bad(index), index += 1) { raw[1] += 2; } return raw[1]; }"
]
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(word 1, word n), (word 1, word 91)]

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "header actual size boundaries" content
    ["empty", "post", "initialFault", "postFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 819)⟩]}
  let badKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let bad ← SourceCoreUnifiedCorpusSupport.get "header fault body" (SourceCompilationPlan.exactSpecialization compiled.validationPlan badKey)
  let gap ← match (SourceCoreDataPlaces.declaredBinders bad.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "header fault binder missing")
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated) in [("empty", some 10, 10), ("post", some 19, 16), ("initialFault", none, 11), ("postFault", none, 13)] do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10] fuel initial
      let completed ← SourceCoreUnifiedCorpusSupport.get "header resume" (started.resume 400000)
      let observation := completed.observation
      let final ← match observation, result with
        | .done actual final, some expected =>
          SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (word expected)) s!"header result {name}"
          pure final
        | .fault (.uninitializedLocal id) final, none =>
          SourceCoreUnifiedCorpusSupport.assertTrue (id == gap) "header exact first fault"
          pure final
        | other, _ => throw (IO.userError s!"header unexpected {name}: {reprStr other}")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "header inert prefix"
      match final.heap[initial.heap.length]? with
      | some cell => SourceCoreUnifiedCorpusSupport.assertTrue (reprStr cell.value == reprStr (some (table updated))) s!"header ordered mapping/write prefix {name}"
      | none => throw (IO.userError "header mapping missing")
      current := current ++ [reprStr observation]
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "header resumed observation"
  IO.println "recursive header bounds: nil equality, independent source fault context, actual seven/six slot size witnesses, marked locals, duplicate writes and resume GREEN"

end Tests.SourceCoreRecursiveNamedHeaderBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedHeaderParameterProjections
/-! Actual Header consumers require neither an external packed-parameter
equation nor a native projection callback. Program typing, complete selected
metadata, catalog identity and invocation evidence stay independent. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedHeaderParameterProjections
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCatalog RecursiveNamedHeaderParameterProjections

section Formal
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment}
  {program : SourceSemantics.Program}
  (header : Header compiled.indexed.ancestry values definitions program)
  (programTyped : ProgramWellFormed program)

include programTyped

theorem actual_raw_type :
    header.instantiation.type = .function
      (TypeSystem.Ty.productMany (header.bindings.map (fun binding => binding.1.scheme.body)))
      header.function.resultType := header_type header programTyped

theorem actual_parameter_pack
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd) :=
  parameter_pack header programTyped matched

theorem actual_projections (sameChecked : values.checked = compiled.compatible.checked)
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := projections header sameChecked programTyped matched

theorem actual_record_projections (sameChecked : values.checked = compiled.compatible.checked)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      header.named.signature.key = .ok header.named.specialized) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := projections_of_record header sameChecked programTyped record

theorem actual_native_vector
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    header.bindings.map Prod.snd = header.named.inputs.map Prod.snd :=
  RecursiveNamedParameterPackingFacts.header_native_types header (parameter_pack header programTyped matched)

theorem actual_source_types {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
    {context : SourceSemantics.Context}
    (sameChecked : values.checked = compiled.compatible.checked)
    (sameSignatures : context.signatures = program.signatures)
    (records : ∀ selected, selected ∈ headers →
      SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan selected.named.signature.key =
        .ok selected.named.specialized)
    (evidence : ∀ selected, selected ∈ headers → selected.function.evidence = []) :
    RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context :=
  source_types sameChecked programTyped sameSignatures records evidence
end Formal

theorem unit_arity_boundary :
    SourceCoreCompatibleCatalog.packTypes [] = SourceCoreCompatibleCatalog.packTypes [.unit] ∧
      ([] : List Core.Ty) ≠ [.unit] := by decide

theorem product_arity_boundary :
    SourceCoreCompatibleCatalog.packTypes [.product .word .bool] =
      SourceCoreCompatibleCatalog.packTypes [.word, .bool] ∧
      ([.product .word .bool] : List Core.Ty) ≠ [.word, .bool] := by decide

private def content : String := String.intercalate "\n" [
  "function empty() {}",
  "function unitArg(value: Unit) returns (Unit) { return value; }",
  "function tupleArg(value: (Word, Bool)) returns (Word) { return 1; }",
  "function two(first: Word, second: Bool) returns (Word) { return first; }",
  "function duplicate(first: Word, middle: Bool, last: Word) returns (Word) { return first + last; }",
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function rootUnit() returns (Unit) { return unitArg(()); }",
  "function rootTuple() returns (Word) { return tupleArg((7, true)); }",
  "function rootTwo() returns (Word) { return two(7, true); }",
  "function rootDuplicate() returns (Word) { return duplicate(7, false, 7); }",
  "function rootWord() returns (Word) { return choose(9, true); }",
  "function rootBool() returns (Bool) { return choose(false, 9); }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- This inspection uses real compiled rows; it does not manufacture a source
ProgramWellFormed or Header certificate from the successful comparisons. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let representation := SourceCoreCompatibleFunctions.representation
    (.initial compiled.compatible.checked) compiled.compilationFuel
  let mut arities : List Nat := []
  let mut vectors : List (List Core.Ty) := []
  let mut generic : List (List TypeSystem.Ty) := []
  for (named, slot) in compiled.indexed.base.functions.zipIdx do
    let specialized ← match compiled.compatible.prepared.plan.specializations.reverse[slot]? with
      | some specialized => pure specialized
      | none => throw (IO.userError "header parameter preparation slot missing")
    let actual ← get "header parameter preparation"
      (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation compiled.sourceProgram representation specialized)
    require (reprStr actual == reprStr named) "header parameter full prepared row changed"
    let selected ← get "header parameter exact selected record"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (reprStr selected == reprStr named.specialized) "header parameter exact record changed"
    let raw := named.inputs.map (fun binding => binding.1.scheme.body)
    let native := named.inputs.map Prod.snd
    require (reprStr (named.inputs.map Prod.fst) == reprStr specialized.function.typedBody.inputs)
      "header parameter ordered source binders changed"
    let projected ← get "header parameter raw projections"
      (raw.mapM compiled.compatible.checked.catalog.project)
    require (projected == native) "header parameter ordered native vector changed"
    let parameter ← match specialized.function.type with
      | .function parameter result =>
        require (parameter == TypeSystem.Ty.productMany raw) "header parameter raw function shape changed"
        require (result == specialized.function.inferredBodyType) "header parameter raw result changed"
        pure parameter
      | _ => throw (IO.userError "header parameter expected actual function type")
    let projectedParameter ← get "header actual whole parameter projection"
      (representation.expressions.projectType (.declaration specialized.key.declaration) parameter)
    let packed := SourceCoreCompatibleCatalog.packTypes native
    require (projectedParameter == named.signature.parameterType && projectedParameter == packed)
      "header actual parameter pack equation changed"
    arities := arities ++ [raw.length]
    vectors := vectors ++ [native]
    if !specialized.parameterSubstitution.isEmpty then
      require (specialized.parameterSubstitution.map Prod.snd == raw)
        "header retained generic substitution/order changed"
      generic := generic ++ [raw]
  require (arities.count 0 == 7 && arities.count 1 == 2 && arities.count 2 == 3 && arities.count 3 == 1)
    s!"header parameter actual arity coverage changed {reprStr arities}"
  require (vectors.contains [] && vectors.contains [.unit] &&
      vectors.contains [.product .word .bool] && vectors.contains [.word, .bool] &&
      vectors.contains [.word, .bool, .word] && vectors.contains [.bool, .word])
    "header parameter Unit/product ambiguity or ordered vectors missing"
  require (generic.length == 2 && generic.contains [.word, .bool] && generic.contains [.bool, .word])
    "header parameter full specialized generic rows changed"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named header parameter projections" content
    ["empty", "rootUnit", "rootTuple", "rootTwo", "rootDuplicate", "rootWord", "rootBool"]
  inspect compiled
  IO.println "recursive named header parameters: actual full selected rows, source shape, ordered projections and parameter pack GREEN"

end Tests.SourceCoreRecursiveNamedHeaderParameterProjections
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedHeaderScopeDeclarations
/-! The actual Header supplies initial lexical declarations to accepted read
and expression certificates. Source typing and ordinary syntax stay explicit;
no native payload is used to invent a source scheme or successful lookup. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedHeaderScopeDeclarations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts
open RecursiveNamedHeaderScopeDeclarations

section ActualHeader
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program} (header : Header prepared values ambient.definitions program)

/-- The emitted read's actual root declaration is independently present in the
same source context, including its complete raw scheme. -/
theorem accepted_read {fuel : Nat} {id : ExpressionId} {reason : Word} {code : Expr}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values header.function.source
      (bodyScope header) id reason = .ok code) :
    ∃ certificate : CompatibleExpressionReads.Certificate fuel values header.function.source (bodyScope header) id reason code,
      Resolved.LocalScope.Lookup header.context.locals certificate.binder certificate.declared.scheme := by
  obtain ⟨certificate⟩ := CompatibleExpressionReads.of_accepted accepted
  exact ⟨certificate, header_scope header _ _ _ _ certificate.slot certificate.declaration⟩

/-- Initial scope declarations are internal to this actual compiler consumer;
ordinary syntax, policy identity and independent source typing remain inputs. -/
theorem accepted_scalar {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel fuel : Nat}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (policyFor : CompatibleExpressionConditionals.PolicyFor policy compilation readFuel values
      header.function.source (bodyScope header) header.reasonAt)
    (coercions : ∀ child original, CompatibleExpressionConditionals.Syntax header.function.source child →
      header.function.source.lookupExpression? child = some original → original.coercions = [])
    (syntaxTree : CompatibleExpressionConditionals.Syntax header.function.source id)
    (found : header.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType header.function.source header.context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation header.function.source
      (bodyScope header) id header.reasonAt = .ok lowered) :
    CompatibleExpressionConditionals.Tree readFuel values header.function.source header.context
      compilation.solvedRequirements header.reasonAt (bodyScope header) id lowered :=
  CompatibleExpressionConditionals.tree_of_functions header.unique (header_scope header)
    policyFor coercions syntaxTree found typed accepted

/-- Deriving declarations does not replace the real residual context. -/
theorem actual_context : header.context.residualTypeVariables = true ∧
    CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context :=
  ⟨RecursiveNamedSourceContextFacts.header_residual header, header_scope header⟩
end ActualHeader

section Boundaries
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"header_scope", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder :=
  {id := ⟨owner, index⟩, name := "same", scheme := .mono type}
private def first := binder 0 (.comptime .word)
private def second := binder 1 .bool
private def source : TypedSource := {owner, inputs := [first, second], roots := [], nodes := []}

/-- Real lookup retains staging and all metadata, not its erased native type. -/
theorem raw_input_identity (declared : TypedBinder)
    (accepted : SourceCoreDataPlaces.rootBinder source first.id = .ok declared) : declared = first :=
  input_identifies (by simp [source]) accepted

theorem same_name_ordered_slots :
    SourceCoreDataPlaces.rootBinder source first.id = .ok first ∧
    SourceCoreDataPlaces.rootBinder source second.id = .ok second ∧
    SourceCoreLocalCell.lookup? [(second.id, Core.Ty.word), (first.id, Core.Ty.bool)] first.id = some (1, .bool) ∧
    SourceCoreLocalCell.lookup? [(second.id, Core.Ty.word), (first.id, Core.Ty.bool)] second.id = some (0, .word) := by
  cbv

/-- Input membership alone does not promise the compiler's singleton lookup. -/
theorem duplicate_input_rejected :
    ∀ declared, SourceCoreDataPlaces.rootBinder {source with inputs := [first, first]} first.id ≠ .ok declared := by
  intro declared accepted
  cases accepted

/-- Even a scoped slot cannot authenticate a missing source declaration. -/
theorem missing_input_rejected :
    SourceCoreLocalCell.lookup? [(first.id, Core.Ty.word)] first.id = some (0, .word) ∧
    ∀ declared, SourceCoreDataPlaces.rootBinder {source with inputs := []} first.id ≠ .ok declared := by
  constructor
  · rfl
  · intro declared accepted; cases accepted
end Boundaries

private def content : String := String.intercalate "\n" [
  "function pick(first: Word, gate: Bool, last: Word) returns (Word) { if (gate) { return first; } else { return last; } }",
  "function second<A, B>(first: A, last: B) returns (B) { return last; }",
  "function shadow(value: Word) returns (Word) { { let value = 13; } return value; }",
  "function fail(first: Word, gate: Bool) returns (Word) { let missing: Word; return missing; }",
  "function empty() {}",
  "function rootPick() returns (Word) { return pick(7, false, 11); }",
  "function rootGeneric() returns (Bool) { return second(9, true); }",
  "function rootReverse() returns (Word) { return second(false, 17); }",
  "function rootShadow() returns (Word) { return shadow(19); }",
  "function rootFault() returns (Word) { return fail(23, true); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (SourceCoreUnifiedCorpusSupport.word n)

/-- Audit actual full compiler inputs and scopes without asserting a source
Header or source typing certificate from these runtime comparisons. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut sizes : List Nat := []
  let mut generics : List (List TypeSystem.Ty) := []
  let mut shadowed := false
  for named in compiled.indexed.base.functions do
    let selected ← get "header scope selected specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "header scope full selected record changed"
    let source := selected.function.typedBody
    require (reprStr source.inputs == reprStr (named.inputs.map Prod.fst))
      "header scope source inputs differ from actual prepared binders"
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    for (binding, index) in named.inputs.reverse.zipIdx do
      let declared ← get "header scope actual rootBinder" (SourceCoreDataPlaces.rootBinder source binding.1.id)
      require (reprStr declared == reprStr binding.1) "header scope raw full binder changed"
      require (SourceCoreLocalCell.lookup? scope binding.1.id == some (index, binding.2))
        "header scope reversed input order or native payload changed"
      require (binding.1.id.owner == source.owner) "header scope input owner changed"
      let projected ← get "header scope independent native projection" (compiled.compatible.checked.catalog.project declared.scheme.body)
      require (projected == binding.2) "header scope actual input projection changed"
    for input in source.inputs do
      for declared in SourceCoreDataPlaces.declaredBinders source do
        if declared.name == input.name && declared.id != input.id then
          shadowed := true
          let actual ← get "header scope shadowed binder" (SourceCoreDataPlaces.rootBinder source declared.id)
          require (reprStr actual == reprStr declared) "header scope same-name shadow changed source ID"
    sizes := sizes ++ [named.inputs.length]
    if !selected.parameterSubstitution.isEmpty then
      generics := generics ++ [named.inputs.map (fun binding => binding.1.scheme.body)]
  require (sizes.contains 0 && sizes.contains 1 && sizes.contains 2 && sizes.contains 3)
    "header scope actual arity coverage changed"
  require (generics.contains [.word, .bool] && generics.contains [.bool, .word])
    "header scope generic raw order changed"
  require shadowed "header scope same-name distinct binders not exercised"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"header scope full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "header scope declarations" content
    ["empty", "rootPick", "rootGeneric", "rootReverse", "rootShadow", "rootFault"]
  inspect compiled
  let faultBinder ← match (compiled.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "header scope fault binder not unique")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("empty", .unit, []),
    ("rootPick", word 11, [(.word, some (word 7)), (.bool, some (.bool false)), (.word, some (word 11))]),
    ("rootGeneric", .bool true, [(.word, some (word 9)), (.bool, some (.bool true))]),
    ("rootReverse", word 17, [(.bool, some (.bool false)), (.word, some (word 17))]),
    ("rootShadow", word 19, [(.word, some (word 19)), (.word, some (word 13))])]
  for budget in [0, 37, 151, 300000] do
    for (name, expected, heap) in successes do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] budget
      let finished ← get "header scope native resume" (started.resume 300000)
      match finished.observation with
      | .done actual state =>
        require (reprStr actual == reprStr expected) "header scope completed value changed"
        cells state heap
      | other => throw (IO.userError s!"header scope expected completion: {reprStr other}")
    let started ← SourceCoreUnifiedCorpusSupport.execute compiled "rootFault" [] budget
    let finished ← get "header scope fault resume" (started.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == faultBinder) "header scope wrong first source fault"
      cells state [(.word, some (word 23)), (.bool, some (.bool true)), (.word, none)]
    | other => throw (IO.userError s!"header scope expected source fault: {reprStr other}")
  IO.println "header scope declarations: actual ordered raw inputs, shadowed IDs, 6 roots/4 budgets/full heaps/resume GREEN"

end Tests.SourceCoreRecursiveNamedHeaderScopeDeclarations
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedHeaderSourceTyping
/-! These consumers obtain independent source body judgments from actual
instantiation receipts. They do not take a prior body typing package, change
residual source scope, or infer source authority from native values. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedHeaderSourceTyping
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference
open CallableAncestryPairedLookup RecursiveNamedCatalog

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : SourceSemantics.Program}

theorem header_raw_call_type (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    header.instantiation.type = .function (TypeSystem.Ty.productMany header.types) header.sourceBody.resultType := by
  obtain ⟨_, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header programTyped
  exact certified.callable_type

theorem original_header_body (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, BodyHasType header.function.source header.context header.function.resultType facts :=
  RecursiveNamedHeaderSourceTyping.body header programTyped

theorem actual_parameter_context (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, BodyHasType header.named.specialized.function.typedBody header.context
      header.named.specialized.function.inferredBodyType facts :=
  RecursiveNamedHeaderSourceTyping.prepared_body header programTyped

theorem original_statement_roots (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ final facts, StatementsHaveType header.function.source
      {returnType := header.function.resultType} header.context header.function.body final facts ∧
      BodyCompletes header.function.resultType facts :=
  RecursiveNamedHeaderSourceTyping.statements header programTyped

section ActualSpecialization
variable {compilerProgram : CheckedProgram} {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  (programTyped : ProgramWellFormed (Program.ofChecked compilerProgram))
  (signatureMember : signature ∈ compilerProgram.signatures.functions)
  (genericMember : generic ∈ compilerProgram.functions)
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
  (range : ParameterSubstitution.RangeWellFormed (Context.ofSignatures compilerProgram.signatures)
    specialized.parameterSubstitution)

include programTyped signatureMember genericMember accepted range in
theorem actual_canonical_body :
    ∃ types context facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compilerProgram)
      (CallableNamedMetadata.instantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compilerProgram specialized) types context facts := by
  exact (RecursiveNamedSpecializationValidity.instantiated signatureMember genericMember accepted
    (programTyped.signatures.function_parameters signature signatureMember).1 range).certificate programTyped

include programTyped signatureMember genericMember accepted range in
theorem actual_retained_body :
    ∃ types context facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compilerProgram)
      (CallableNamedCanonicalOrder.retainedInstantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compilerProgram specialized) types context facts := by
  exact (RecursiveNamedSpecializationValidity.retained_instantiated signatureMember genericMember accepted
    (programTyped.signatures.function_parameters signature signatureMember).1 range).certificate programTyped

end ActualSpecialization
end Tests.SourceCoreRecursiveNamedHeaderSourceTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedInitialContextValidity
/-! Initial context consumers start before a catalog Header. The whole actual
source must explicitly have no template IDs to obtain the old ordinary ledger
condition. Runtime/scoped validity retains templates and all unused rows.
Runtime audits are compiler observations, not proofs of program well-formedness. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedInitialContextValidity
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedInitialContextValidity GeneralHeap ReadOnly CompatiblePayload

section Frame
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  (frame : NamedCalls.SourceFrame program instantiation body function)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (programTyped : ProgramWellFormed program)

include frame extended programTyped

/-- Scoped and runtime validity remain available for template-bearing sources;
coverage is the same frame dictionary, with the entire ledger retained. -/
theorem complete_ledger : ScopedRequirementLedgerWellFormed context function.source ∧
    RuntimeRequirementLedgerValid context ∧ function.evidence.Covers context ∧
    context.solvedRequirements = function.context.solvedRequirements :=
  ⟨scoped_ledger frame extended programTyped, runtime frame extended programTyped,
    covers frame extended, (mono_fields extended).solvedRequirements⟩

/-- The concrete literal semantic leaf receives computed initial validity,
without a Header.valid input or an execution premise for the source body. -/
theorem literal_preserves {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (templatesEmpty : function.source.localSchemeTemplateIds = [])
    (unique : NodeOccurrencesUnique function.source) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context function.evidence function.source
      (fun _ id lowered => CompatibleExpressionLiterals.Certificate function.context.solvedRequirements
        function.source id lowered) faults :=
  CompatibleExpressionLiterals.preserves functions program context function.evidence
    (of_templates_empty frame extended programTyped rfl templatesEmpty) unique faults

/-- Reflection uses native completion only; preservation and a prior source
trace are absent from the theorem's premises. -/
theorem literal_reflects {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (templatesEmpty : function.source.localSchemeTemplateIds = []) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context function.evidence function.source
      (fun _ id lowered => CompatibleExpressionLiterals.Certificate function.context.solvedRequirements
        function.source id lowered) faults :=
  CompatibleExpressionLiterals.reflects functions program context function.evidence
    (of_templates_empty frame extended programTyped rfl templatesEmpty) function.source faults
end Frame

section ActualCompilation
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {named : SourceCoreGeneralFunctions.Function} {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
  {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  (programTyped : ProgramWellFormed (Program.ofChecked program))
  (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
  (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures program.signatures) named.specialized.parameterSubstitution)
  (closed : named.specialized.assumptions = [])
  (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (extended : MonoBindersExtend named.specialized.function.typedBody.owner
    (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized).context
    named.specialized.function.typedBody.inputs types context)
  (templatesEmpty : named.specialized.function.typedBody.localSchemeTemplateIds = [])

include programTyped signatureMember genericMember accepted range closed inputs compiled extended templatesEmpty

theorem canonical_initial : CompatibleExpressionLiterals.ContextValid
    named.specialized.function.solvedRequirements context [] := by
  have frame := (RecursiveNamedSpecializationValidity.of_compilation signatureMember genericMember accepted
    (programTyped.signatures.function_parameters signature signatureMember).1 range closed inputs compiled).2
  exact of_templates_empty frame extended programTyped rfl templatesEmpty

/-- Retained reverse substitution order produces the same complete body and
context; no equality of arbitrary dictionaries is used. -/
theorem retained_initial : CompatibleExpressionLiterals.ContextValid
    named.specialized.function.solvedRequirements context [] := by
  have frame := (RecursiveNamedSpecializationValidity.retained_of_compilation signatureMember genericMember accepted
    (programTyped.signatures.function_parameters signature signatureMember).1 range closed inputs compiled).2
  exact of_templates_empty frame extended programTyped rfl templatesEmpty
end ActualCompilation

section Boundary
/-- Runtime validity alone deliberately permits assumption rows. It cannot
supply the old all-rows-valid condition without source-scoped facts. -/
theorem runtime_not_ordinary (id : RequirementId) (predicate : ProgramPredicate) :
    let row : SolvedRequirement := ⟨id, predicate, .assumption predicate⟩
    let context := (SourceSemantics.Context.ofSignatures ⟨[], [], [], [], [], []⟩).withSolvedRequirements [row]
    RuntimeRequirementLedgerValid context ∧ ¬ RequirementLedgerWellFormed context := by
  dsimp only
  constructor
  · constructor
    · simp [RequirementIdsUnique, Context.withSolvedRequirements]
    · intro row evidence member actual
      have same : row = ⟨id, predicate, .assumption predicate⟩ := by
        simpa [Context.withSolvedRequirements] using member
      subst row
      cases actual
  · intro valid
    have rowValid := valid.entriesValid ⟨id, predicate, .assumption predicate⟩ (by simp [Context.withSolvedRequirements])
    cases rowValid with
    | intro retained =>
      cases retained with
      | intro represents evidence =>
        cases represents with
        | assumption =>
          cases evidence with
          | assumption member => simp only [Context.withSolvedRequirements, Context.ofSignatures, List.not_mem_nil] at member
end Boundary


private def content : String := String.intercalate "\n" [
  "function bump(value: Word) returns (Word) { let extra: Word = 3; return value + extra; }",
  "function keep<T>(value: T) returns (T) { return value; }",
  "function fail(value: Word) returns (Word) { let missing: Word; return missing; }",
  "function wordRoot() returns (Word) { let kept: Word = 5; return bump(keep(kept)); }",
  "function boolRoot() returns (Bool) { return keep(true); }",
  "function faultRoot() returns (Word) { let kept: Word = 7; return fail(kept); }",
  "function empty() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (SourceCoreUnifiedCorpusSupport.word n)

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut rows := 0
  let mut inputs := 0
  for named in compiled.indexed.base.functions do
    let selected ← get "initial validity actual selected record"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "initial validity changed the full selected record"
    let source := selected.function.typedBody
    let ledger := selected.function.solvedRequirements
    let context := (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram selected).context
    require (source.localSchemeTemplateIds.isEmpty && selected.assumptions.isEmpty)
      "initial validity ordinary fixture acquired templates or declaration assumptions"
    require (reprStr context.solvedRequirements == reprStr ledger &&
      reprStr context.assumptions == reprStr selected.assumptions && context.residualTypeVariables)
      "initial validity changed an ordered row, evidence or residual mode"
    require (decide (ledger.map (·.id)).Nodup) "initial validity duplicate requirement ID"
    require (reprStr source.inputs == reprStr (named.inputs.map Prod.fst))
      "initial validity prepared parameter order changed"
    for row in ledger do
      match row.evidence with
      | .implementation _ => pure ()
      | .assumption _ => throw (IO.userError "initial validity ordinary fixture retained an uncovered assumption")
    rows := rows + ledger.length
    inputs := inputs + source.inputs.length
  require (rows > 0 && inputs > 0) "initial validity did not exercise requirements and parameter installation"

/-- A real checked qualified local retains template assumption rows even when
its enclosing declaration has no assumptions. This is a checker-stage audit;
no full runtime compilation or Header is inferred for this fixture. -/
private def template_boundary : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] }
  let program ← get "initial validity checked template source" (checkProgram workspace)
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature
    | _ => throw (IO.userError "initial validity qualified signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic
    | _ => throw (IO.userError "initial validity qualified body missing")
  let specialized ← get "initial validity actual template specialization"
    (SourceSpecialization.specializeFunction signature generic [])
  let ids := specialized.function.typedBody.localSchemeTemplateIds
  require (!ids.isEmpty && signature.scheme.predicates.isEmpty && specialized.assumptions.isEmpty)
    "initial validity template boundary disappeared"
  require (specialized.function.solvedRequirements.map (·.id) == generic.solvedRequirements.map (·.id))
    "initial validity specialization removed or reordered template rows"
  for id in ids do
    let row ← match specialized.function.solvedRequirements.filter (·.id == id) with
      | [row] => pure row
      | _ => throw (IO.userError "initial validity template row lost its unique original ID")
    match row.evidence with
    | .assumption predicate =>
      require (predicate == row.predicate && !(specialized.assumptions.contains predicate))
        "initial validity template evidence was promoted to a declaration assumption"
    | _ => throw (IO.userError "initial validity unexpectedly rewrote a template to implementation evidence")

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"initial validity full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  template_boundary
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "initial context validity" content
    ["wordRoot", "boolRoot", "faultRoot", "empty"]
  inspect compiled
  let faultBinder ← match (compiled.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "initial validity fault binder missing")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("wordRoot", word 8, [(.word, some (word 5)), (.word, some (word 5)),
      (.word, some (word 5)), (.word, some (word 3))]),
    ("boolRoot", .bool true, [(.bool, some (.bool true))]),
    ("empty", .unit, [])]
  for budget in [0, 37, 151, 300000] do
    for (name, expected, heap) in successes do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] budget
      let finished ← get "initial validity public resume" (started.resume 300000)
      match finished.observation with
      | .done actual state =>
        require (reprStr actual == reprStr expected) "initial validity completed value changed"
        cells state heap
      | other => throw (IO.userError s!"initial validity expected completion: {reprStr other}")
    let started ← SourceCoreUnifiedCorpusSupport.execute compiled "faultRoot" [] budget
    let finished ← get "initial validity public fault resume" (started.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == faultBinder) "initial validity first fault changed"
      cells state [(.word, some (word 7)), (.word, some (word 7)), (.word, none)]
    | other => throw (IO.userError s!"initial validity expected fault: {reprStr other}")
  IO.println "initial context validity actual ledger / templates / heaps / resume GREEN"

end Tests.SourceCoreRecursiveNamedInitialContextValidity
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedLambdaFormationExpressions
/-! Formation is a leaf of the same whole expression tree and survives inside
actual named callees in one fixed runtime value model. The lambda body receipt
covers the concrete builtin statement grammar; indirect application and a
combined named/anonymous recursive body theorem remain separate boundaries.
Independent source frames, full history, actual compilation and static child
receipts are retained. Native typing supplies only used-prefix type agreement.
The original canonical and actual unused administrative suffixes remain full. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedLambdaFormationExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates
open RecursiveNamedLambdaFormationHeads
open RecursiveNamedLambdaFormationTreeMeaning

abbrev actual_contextual_site := @CallableIndexedLambdaGeneration.of_contextual
abbrev actual_static_body := @CallableIndexedLambdaRuntimeBody.Body.of_tree
abbrev same_site_head := @RecursiveNamedLambdaFormationHeads.Lambda.of_site
abbrev actual_body_extraction := @RecursiveNamedCatalogRuntimeProfileFactory.formation_provider

section Actual
variable {values : SourceCoreCompatibleValues.Context}
  {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program} {locations : Locations}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

abbrev Calls (authenticated : Bool) := Head (registry := registry) (faults := faults) caller context evidence
  (RecursiveNamedCallEvidenceHeads.Calls (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (if authenticated then some evidence else none) headers
    (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context)

abbrev Expressions (authenticated : Bool) :=
  RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor (Calls (caller := caller) (headers := headers)
    (context := context) (evidence := evidence) (registry := registry) (faults := faults) authenticated)
    fuel values caller.function.source context solved reasonAt

variable {expressionSyntax : Header indexed.ancestry values indexed.layouts.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : values.checked.catalog.callableContracts = true)
variable (authenticated : Bool)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (alignments : ∀ header, header ∈ headers → RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header
    (CallableIndexedNamedGeneration.context indexed header.named) 0)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers locations 0 (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry header
        arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost) →
      RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry entry →
      RecursiveNamedCatalogMutualMeaning.FormationProfile (headers := headers) (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) authenticated header
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))


include complete alignments extension owners uninitialized missing escaped profiles in
theorem actual_preserves_at
    (alignment : RecursiveNamedLambdaFormationEntries.FormationHeader
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
      (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {admitted : ExpressionId → Prop}
    (admission : AdmissionFor lambdaForm caller.function.source admitted) (coverage : ReachedCoverage headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers context)
    (emptyEvidence : SelectedEmptyEvidence (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → caller.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered (CallableIndexedNamedGeneration.context indexed caller.named).plan instantiation)
    (unique : NodeOccurrencesUnique caller.function.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations caller.function.source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context (CompatibleExpressionBuiltins.Syntax caller.function.source))
    (selectedValid : SelectedDeclarationLaw (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context admitted)
    (policyFor : PolicyForWith (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (headers := headers) (if authenticated then some evidence else none) policy (CallableIndexedNamedGeneration.context indexed caller.named) readFuel values caller.function.source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax caller.function.source id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (lambdas : ∀ fuel id node lowered, admitted id → caller.function.source.lookupExpression? id = some node →
      lambdaForm node.form → ExpressionHasType caller.function.source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
        (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered →
      Nonempty (Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered))
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : caller.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType caller.function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered)
    (valid : CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context indexed caller.named).solvedRequirements context evidence)
    (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (RecursiveNamedLambdaFormationEntries.protectedEntry
        (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  have receipt := RecursiveNamedLambdaFormationTreeMeaning.of_functions authenticated alignment
    admission coverage sourceTypes emptyEvidence order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active callableProfile fragmentCoercions coercions lambdas allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedCatalogMutualMeaning.expression_preserves_at_formation
    (locations := locations) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    profile authenticated complete alignments extension owners uninitialized missing escaped profiles
    alignment valid callerUninitialized callerMissing size receipt rootFound


include complete alignments extension uninitialized missing escaped profiles in
theorem actual_reflects_at
    (alignment : RecursiveNamedLambdaFormationEntries.FormationHeader
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
      (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {admitted : ExpressionId → Prop}
    (admission : AdmissionFor lambdaForm caller.function.source admitted) (coverage : ReachedCoverage headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers context)
    (emptyEvidence : SelectedEmptyEvidence (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → caller.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered (CallableIndexedNamedGeneration.context indexed caller.named).plan instantiation)
    (unique : NodeOccurrencesUnique caller.function.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations caller.function.source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context (CompatibleExpressionBuiltins.Syntax caller.function.source))
    (selectedValid : SelectedDeclarationLaw (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context admitted)
    (policyFor : PolicyForWith (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (headers := headers) (if authenticated then some evidence else none) policy (CallableIndexedNamedGeneration.context indexed caller.named) readFuel values caller.function.source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax caller.function.source id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (lambdas : ∀ fuel id node lowered, admitted id → caller.function.source.lookupExpression? id = some node →
      lambdaForm node.form → ExpressionHasType caller.function.source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
        (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered →
      Nonempty (Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered))
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : caller.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType caller.function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered)
    (valid : CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context indexed caller.named).solvedRequirements context evidence)
    (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (RecursiveNamedLambdaFormationEntries.protectedEntry
        (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  have receipt := RecursiveNamedLambdaFormationTreeMeaning.of_functions authenticated alignment
    admission coverage sourceTypes emptyEvidence order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active callableProfile fragmentCoercions coercions lambdas allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedCatalogMutualMeaning.expression_reflects_at_formation
    (locations := locations) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    profile authenticated complete alignments extension uninitialized missing escaped profiles
    alignment valid callerUninitialized callerMissing size receipt rootFound

end Actual

section Boundaries
/-- One global reference and a separate frame reference remain in the used
prefix while an arbitrary extra Bool or Unit field stays unconstrained. -/
theorem nonempty_global_unused_suffix :
    NativeExpressionContextSupport.Agrees 3
      [.word, .cell (.function .word .word), .cell .unit]
      [.word, .cell (.function .word .word), .cell .unit, .bool] ∧
    NativeExpressionContextSupport.Agrees 3
      [.word, .cell (.function .word .word), .cell .unit]
      [.word, .cell (.function .word .word), .cell .unit, .unit] ∧
    ([.word, .cell (.function .word .word), .cell .unit, .bool] : Core.Context) ≠
      [.word, .cell (.function .word .word), .cell .unit, .unit] := by
  refine ⟨?_, ?_, by decide⟩
  all_goals
    intro index smaller
    cases index with
    | zero => rfl
    | succ index =>
      cases index with
      | zero => rfl
      | succ index =>
        have same : index = 0 := by omega
        subst index
        rfl

abbrev aligned_callee := @RecursiveNamedLambdaFormationEntries.authorize
abbrev original_creation_reference := @RecursiveNamedLambdaFormationHeads.Lambda.reference_index
abbrev native_used_prefix := @RecursiveNamedLambdaFormationHeads.entry_prefix
abbrev full_actual_captures := @RecursiveNamedLambdaFormationHeads.captures
abbrev closed_callee_preserves := @RecursiveNamedCatalogMutualMeaning.preserves_at_formation
abbrev closed_callee_reflects := @RecursiveNamedCatalogMutualMeaning.reflects_at_formation
end Boundaries

private def content := String.intercalate "\n" [
  "type F = function(Word) returns (Word);",
  "function maker(seed: Word) returns(F) { return lam(item: Word) -> Word { return seed + item; }; }",
  "function keeper(value: F) returns(F) { return value; }",
  "function caller(seed: Word) returns(F) { return keeper(maker(seed)); }",
  "function stored(seed: Word) returns(F) { let value: F = maker(seed); return value; }",
  "function pair(seed: Word) returns(F,F) { return (maker(seed), lam(item: Word) -> Word { return seed + item; }); }",
  "function branch(seed: Word) returns(F) { if(seed == 0) { return lam(item: Word) -> Word { return item; }; } else { return lam(item: Word) -> Word { return seed + item; }; } }",
  "function zero(seed: Word) returns(function() returns(Word)) { return lam() -> Word { { return seed; } }; }",
  "function fail() returns(Word) { let written = 5; let gap: Word; return gap; }",
  "function firstFault(seed: Word) returns(Word,F,F) { return (fail(), maker(seed), maker(9)); }",
  "function laterFault(seed: Word) returns(F,Word,F) { return (maker(seed), fail(), maker(9)); }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- These are actual accepted contextual lambda leaves, with their original
callback, complete source metadata, physical globals and compiler child fuel. -/
private def leaf_codes (compiled : SourceCoreUnifiedCompilation.Compiled) : IO (List (Word × SourceCoreBasic.LoweredExpr × Core.Context)) := do
  let prepared := compiled.indexed
  require (!prepared.base.globals.isEmpty) "formation nonempty globals absent"
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "formation diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "formation original parent contexts" (SourceCoreStageCodebook.prepareContexts
    prepared.base.sourceProgram prepared.base.plan (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut leaves := []
  for named in prepared.base.functions do
    let own ← match diagnostics.base.find? named.signature.key with
      | some own => pure own | none => throw (IO.userError "formation own diagnostics missing")
    let source := CallableIndexedNamedGeneration.source named
    let compilation := CallableIndexedNamedGeneration.context prepared named
    require (compilation.administrativePrefix == 1 && compilation.globals == prepared.base.globals)
      "formation caller bundle prefix/full globals changed"
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
      prepared.base.callableContext none none
    let leading :=  SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
      prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
    for item in source.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .lambda parameters result body =>
          let code ← get "formation actual leaf acceptance" (lower prepared.fuel source scope node.id reasonAt)
          let descriptor ← get "formation actual descriptor" (SourceCoreCallableContracts.descriptor
            prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner node.id []))
          require (Core.infer? leading code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
            "formation used prefix typing failed"
          for suffix in [[.bool], [.unit, .function .unit .unit]] do
            require (Core.infer? (leading ++ suffix) code.expression prepared.layouts.definitions ==
              some (LanguageResult.resultType code.type)) "formation arbitrary unused admin suffix typing changed"
          require (node.requirements.isEmpty && node.coercions.isEmpty &&
            node.type == TypeSystem.Ty.function (TypeSystem.Ty.productMany (parameters.map (·.scheme.body))) result && !body.isEmpty)
            "formation original source annotation/requirements/body changed"
          require (scope.length == 1) "formation fixture exact lexical parameter scope changed"
          require ((SourceCoreSourceCells.copiedSlots source scope).length == 1)
            "formation fixture lambda no longer copies its lexical parameter"
          leaves := leaves ++ [(descriptor.id, code, leading)]
        | _ => pure ()
      | _ => pure ()
  require (leaves.length == 5) s!"formation actual accepted leaf count {leaves.length}"
  pure leaves

/-- Formation executes the original emitted leaf in the actual captured prefix,
with extra unused native fields retained. Closures capture by value: formation
first copies the leaf's one lexical slot into a fresh marked cell, saved between
the frame snapshot and the creation environment. This harness does not
construct source history or infer any Entry identity from the captured
environment. -/
private def formation_suffix (compiled : SourceCoreUnifiedCompilation.Compiled)
    (leaves : List (Word × SourceCoreBasic.LoweredExpr × Core.Context)) (native : Value) (store : Store) : IO Nat := do
  let prepared := compiled.indexed
  let rec visit (fuel : Nat) (native : Value) : IO Nat := do
    match fuel with
    | 0 => throw (IO.userError "formation native payload traversal budget")
    | fuel + 1 =>
      match native with
      | .pair (.pair marker (.closure parameter result executable (lexical :: saved))) (.word origin) =>
        match leaves.find? (fun leaf => leaf.1 == origin) with
        | none => throw (IO.userError "formation returned lambda origin lacks original leaf")
        | some leaf =>
          let canonicalTypes := leaf.2.2
          let actual := saved.drop 1
          let lexicalIndex := (actual.map Value.type).idxOf (canonicalTypes.headD .unit)
          let globalStart := actual.length - (prepared.base.globals.length + 1)
          let embedding : Renaming := fun index =>
            if index == 0 then lexicalIndex else if index == 1 then lexicalIndex + 1
            else globalStart + index - 2
          require (canonicalTypes.zipIdx.all (fun slot => (actual.map Value.type)[embedding slot.2]? == some slot.1))
            "formation actual original lexical/global/frame prefix types changed"
          let (copyType, copied) ← match saved.take 1, actual[lexicalIndex]? with
            | [.cellRef copyType copied], some (.cellRef lexicalType original) =>
              require (copyType == lexicalType && copied != original && store[copied]? == store[original]?)
                "formation snapshot is not a separate copy of the lexical slot"
              pure (copyType, copied)
            | _, _ => throw (IO.userError "formation snapshot copy absent")
          let location ← match actual[embedding (canonicalTypes.length - 1)]? with
            | some (.cellRef type location) =>
              require (type == prepared.ancestry.layout.frame.type) "formation physical frame type changed"
              pure location
            | _ => throw (IO.userError "formation actual frame reference absent")
          let installed := store.set location lexical
          let inert := Value.closure .unit .unit (.var 0) [.word (Word.ofNatModulo 991), .bool true]
          for suffix in [[.bool false], [.unit, inert]] do
            let environment := actual ++ suffix
            require (Core.infer? (environment.map Value.type) (leaf.2.1.expression.rename embedding) prepared.layouts.definitions ==
              some (LanguageResult.resultType leaf.2.1.type)) "formation full actual environment typing changed"
            match runStateful 300000 (.initial (leaf.2.1.expression.rename embedding) environment installed) with
            | .done (.inRight .word (.pair (.pair actualMarker (.closure actualParameter actualResult actualCode
                (actualLexical :: .cellRef freshType fresh :: captured))) (.word actualOrigin))) after =>
              -- Formation only appends one marked copy, three cells holding the
              -- lexical slot's value, and saves it after the frame snapshot.
              require (actualMarker == marker && actualParameter == parameter && actualResult == result &&
                actualCode == executable && actualOrigin == origin && actualLexical == lexical && captured == environment &&
                freshType == copyType && installed.length ≤ fresh && after[fresh]? == installed[copied]? &&
                after.take installed.length == installed && after.length == installed.length + 3)
                "formation lost its snapshot copy or full ordered actual captures/unused suffix/original code/store"
            | other => throw (IO.userError s!"formation original leaf did not complete {reprStr other}")
          pure 1
      | .pair left right => return (← visit fuel left) + (← visit fuel right)
      | _ => pure 0
  visit 100 native

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (root : SourceSpecialization.SpecializationKey)
    (fuel : Nat) : IO (String × String × Bool × Nat) := do
  let first ← get "formation original startup" (compiled.run root [.word (Word.ofNatModulo 3)] 1024 fuel)
  let final ← get "formation original resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution | none => throw (IO.userError "formation original execution missing")
  let native := execution.completion.result.native.observation
  match native with
  | .succeeded _ store => pure (reprStr final.observation, reprStr native, false, store.length)
  | .failed _ store => pure (reprStr final.observation, reprStr native, true, store.length)
  | _ => throw (IO.userError "formation original execution incomplete")

def run : IO Unit := do
  let program ← get "formation actual checker" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let names := ["maker", "caller", "stored", "pair", "branch", "zero", "firstFault", "laterFault"]
  let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let compiled ← get "formation actual public Core compiler" (SourceCoreCompiler.compileChecked program
    (roots.map fun key => SourceCoreCompiler.Seed.declaration key.declaration [])
    {specializationBudget := 512, compilationFuel := 1000})
  let cached ← match compiled.artifact? with
    | some cached => pure cached | none => throw (IO.userError "formation original cached artifact absent")
  require (cached.keys == roots) "formation actual ordered roots changed"
  let leaves ← leaf_codes cached
  let failureKey ← SourceCoreUnifiedCorpusSupport.key program "fail"
  let failureSource ← get "formation original fault source" (SourceCompilationPlan.exactSpecialization cached.indexed.base.plan failureKey)
  let missing ← match (SourceCoreDataPlaces.declaredBinders failureSource.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "formation original missing binder absent")
  let mut formed := 0
  let mut faultSizes := []
  for (name, root) in names.zip roots do
    let baseline ← finish cached root 300000
    require (baseline.2.2.1 == (name == "firstFault" || name == "laterFault")) "formation success/fault boundary changed"
    for fuel in [0, 1, 31, 300000] do
      require ((← finish cached root fuel) == baseline) "formation full source/native store or resume changed"
    let actual ← get "formation actual indexed invocation" (cached.indexed.runSource root [.word (Word.ofNatModulo 3)] 300000)
    match actual.result.native.observation with
    | .succeeded native store => formed := formed + (← formation_suffix cached leaves native store)
    | .failed token store =>
      let diagnostic ← match actual.result.diagnostics.diagnostic? token with
        | some diagnostic => pure diagnostic | none => throw (IO.userError "formation exact diagnostic absent")
      require (diagnostic.error == .uninitializedLocal missing) "formation exact first missing binder changed"
      let ledger ← get "formation original full ordered ledger" (SourceCoreAllocationLedger.scan cached.indexed.layouts [] store)
      require (ledger.pending.isNone && ledger.rows.any (fun row => row.entry.key.binder.name == "gap" && row.payload.isNone) &&
        ledger.rows.any (fun row => row.entry.key.binder.name == "written" && row.payload == some (.word (Word.ofNatModulo 5))))
        "formation first missing binder/prior ordered writes changed"
      -- `laterFault` first runs `maker`: its input and the snapshot its lambda
      -- takes of it follow `laterFault`'s own input.
      let expected := if name == "firstFault" then
          [("seed", some (Value.word (Word.ofNatModulo 3))), ("written", some (.word (Word.ofNatModulo 5))), ("gap", none)]
        else [("seed", some (Value.word (Word.ofNatModulo 3))), ("seed", some (.word (Word.ofNatModulo 3))),
          ("seed", some (.word (Word.ofNatModulo 3))), ("written", some (.word (Word.ofNatModulo 5))), ("gap", none)]
      require (ledger.rows.map (fun row => (row.entry.key.binder.name, row.payload)) == expected)
        "formation original first/later fault full ordered source cells changed"
      faultSizes := faultSizes ++ [(name, store.length)]
    | _ => throw (IO.userError "formation indexed invocation incomplete")
  require (formed == 7) s!"formation returned lambda audit count {formed}"
  require (faultSizes.length == 2) "formation first/later fault cases absent"
  IO.println "lambda formation: actual whole compiler and named callee; nonempty globals/caller bundle/frame; complete raw metadata/captures/unused admin suffix; original full store/fault/resume GREEN"

end Tests.SourceCoreRecursiveNamedLambdaFormationExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedMatchHeadBounds
/-! Concrete named expression Trees and actual selected For Trees close finite
match children. Reflection consumes no preservation law or prior source trace. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedMatchHeadBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {program : SourceSemantics.Program}
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {bodies : NamedCallExpressions.Bodies prepared compilation.values ambient.definitions program}
  {calls : SourceCoreFunctions.Context} {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
  {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionSyntax : ExpressionId → Prop} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
    (NamedCallExpressions.Tree bodies calls fuel source context solved reasonAt) (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (valid : CompatiblePatternLeaves.ContextValid compilation context)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
  {administrative : Core.Context} {faults : FunctionCalls.FaultRep}


  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compilation.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  (trees : ∀ request, request ∈ requests → ∀ childContext,
    ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
    NamedImperativeForStatements.Tree bodies layouts owner active frame globals onError calls fuel source expressionSyntax solved reasonAt administrative
      childContext request.scope (.statements false request.statements) expected type request.code)
  (errors : ∀ request member childContext related,
    GenericImperativeFor.Tree.ReachableErrors registry faults (trees request member childContext related))
include allocator definitions registered extension ordinary valid catalogValid found casesTyped defaultTyped faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing errors in
include owners in
theorem named_preserves (budget size : Nat) (bounded : size ≤ budget) :
    RecursiveNamedMatchSourceBounds.Head.HeadPreservesAt functions program evidence (values := compilation.values) (source := source) (context := context)
      (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults)
      (entry := NamedCallExpressions.Entry functions registry bodies calls.administrativePrefix)
      size (scope := scope) id expected type code := by
  apply GenericImperativeMatch.head_preserves_bounded onError allocator functions definitions registered extension receipt ordinary valid catalogValid found casesTyped defaultTyped unique budget size bounded
    (NamedCallExpressions.entry_transport functions registry bodies calls.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies calls.administrativePrefix)
  · intro contextValid child smaller
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence contextValid
        uninitialized missing bodyUninitialized bodyMissing unique owners) child
  · intro request member childContext related child smaller
    exact RecursiveNamedImperativeFor.preserves_below functions definitions registered extension program evidence
      (NamedCallExpressions.entry_transport functions registry bodies calls.administrativePrefix)
      (NamedCallExpressions.entry_binds functions registry bodies calls.administrativePrefix)
      budget
      (fun sourceContext contextValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
        (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence contextValid
          uninitialized missing bodyUninitialized bodyMissing unique owners) budget) faithful observations
      .reachable unique (trees request member childContext related) (errors request member childContext related) child smaller

include allocator definitions registered extension ordinary valid catalogValid found casesTyped defaultTyped faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing errors in
theorem named_reflects (budget size : Nat) (bounded : size ≤ budget) :
    RecursiveNamedMatchSourceBounds.Head.HeadReflectsAt functions program evidence (values := compilation.values) (source := source) (context := context)
      (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults)
      (entry := NamedCallExpressions.Entry functions registry bodies calls.administrativePrefix)
      size (scope := scope) id expected type code := by
  apply GenericImperativeMatch.head_reflects_bounded onError allocator functions definitions registered extension receipt ordinary valid catalogValid found casesTyped defaultTyped budget size bounded
    (NamedCallExpressions.entry_transport functions registry bodies calls.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies calls.administrativePrefix)
  · intro contextValid child smaller
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence contextValid
        uninitialized missing bodyUninitialized bodyMissing) child
  · intro request member childContext related child smaller
    exact RecursiveNamedImperativeFor.reflectsAt_for functions definitions registered extension program evidence
      (NamedCallExpressions.entry_transport functions registry bodies calls.administrativePrefix)
      (NamedCallExpressions.entry_binds functions registry bodies calls.administrativePrefix)
      budget
      (fun sourceContext contextValid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded
        (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence contextValid
          uninitialized missing bodyUninitialized bodyMissing) budget) faithful observations
      .reachable runtimeViews unique (trees request member childContext related) (errors request member childContext related) child smaller

private def content : String := String.intercalate "\n" [
  "function mark(value: Word) returns (Word) { let seen = value; return seen; }",
  "function fail(value: Word) returns (Word) { let seen = value; let gap: Word; return gap; }",
  "function choose(seed: Word) returns (Word) { let kept = 5; match ((mark(seed), mark(7))) { case (0, value) { let selected = mark(value); return selected; } default { let selected = mark(9); return selected; } } }",
  "function bodyFault(seed: Word) returns (Word) { match ((mark(seed), 19)) { case (0, value) { let prior = mark(value); return fail(prior); } default { return mark(23); } } }",
  "function scrutineeFault() returns (Word) { match (fail(3)) { case 0 { return mark(29); } default { return mark(31); } } }",
  "function emptyDefault(seed: Word) returns (Word) { match (seed) { case 0 { let selected = mark(1); } default {} } return mark(17); }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cell (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (word n))
private def pair (a b : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value :=
  (.product .word .word, some (.product (word a) (word b)))
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "match finite head public resume" (first.resume 400000)).observation

/-- Full ordered heaps distinguish scrutinee calls, selected-arm calls and
first faults. Unselected bodies execute no calls or source allocations. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive match head bounds" content
    ["choose", "bodyFault", "scrutineeFault", "emptyDefault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 907)⟩]}
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let failed ← get "actual failed callee" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  let gap ← match (SourceCoreDataPlaces.declaredBinders failed.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "match finite head fault binder missing")
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("choose", [word 0], word 7, [cell 0, cell 5, cell 0, cell 0, cell 7, cell 7, pair 0 7, cell 7, cell 7, cell 7, cell 7]),
    ("choose", [word 2], word 9, [cell 2, cell 5, cell 2, cell 2, cell 7, cell 7, pair 2 7, cell 9, cell 9, cell 9]),
    ("bodyFault", [word 1], word 23, [cell 1, cell 1, cell 1, pair 1 19, cell 23, cell 23]),
    ("emptyDefault", [word 0], word 17, [cell 0, cell 0, cell 1, cell 1, cell 1, cell 17, cell 17]),
    ("emptyDefault", [word 2], word 17, [cell 2, cell 2, cell 17, cell 17])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 400000 initial
    for fuel in [0, 17, 97, 400000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match head resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"match head result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"match head ordered source cells changed {name}: {reprStr final.heap}"
      | other => throw (IO.userError s!"match head expected success {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("bodyFault", [word 0], [cell 0, cell 0, cell 0, pair 0 19, cell 19, cell 19, cell 19, cell 19, cell 19, cell 19, (.word, none)]),
    ("scrutineeFault", [], [cell 3, cell 3, (.word, none)])]
  for (name, arguments, cells) in failures do
    let baseline ← finish compiled name arguments 400000 initial
    for fuel in [0, 17, 97, 400000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match head fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal id) final =>
        require (id == gap) "match head did not retain the actual first callee fault"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"match head fault cells changed {name}: {reprStr final.heap}"
      | other => throw (IO.userError s!"match head expected first fault {name}: {reprStr other}")
  IO.println "recursive named match head bounds: actual named scrutinee/arm/default calls, emptyDefault, exact first fault and ordered cells/resume GREEN"

end Tests.SourceCoreRecursiveNamedMatchHeadBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedMatchPrefixBounds
/-! Actual selected match prefixes retain the original strict native child,
ordered lexical additions, full runtime typing and protected entry. Tests keep
empty-prefix equality and ordinary agreement separate from strict bounds. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedMatchPrefixBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates DataMatchBranchPrefix
open CallableIndexedHistory CompatibleMatchSelectionPrefix RecursiveNamedMatchPrefixContracts

theorem actual_remaining
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical)
    {wholeSize : Nat} {result : Value} {endStore : Store}
    (completed : EvaluationSize wholeSize actual before (code.rename ξ) result endStore) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ∃ remainingSize, remainingSize < wholeSize ∧
        EvaluationSize remainingSize finalActual finalStore (body.rename finalEmbedding) result endStore := by
  obtain ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry, agreement⟩ :=
    success_prefix certificate ordinary onError allocator valid catalogValid definitions registered extended found uniqueExpression
      represented environments heaps agrees actualTyped reference read unmapped evaluated transport bindings initial
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry,
    agreement.remaining completed⟩

theorem empty_prefix {size : Nat} {environment : Environment} {store after : Store} {code : Expr} {value : Value}
    (original : EvaluationSize size environment store code value after) :
    ∃ remaining, remaining ≤ size ∧ EvaluationSize remaining environment store code value after :=
  (ContinuationSize.refl environment store code).remaining original

theorem empty_prefix_equal {size : Nat} {environment : Environment} {store after : Store} {code : Expr} {value : Value}
    (original : EvaluationSize size environment store code value after) :
    ∃ remaining, remaining = size ∧ EvaluationSize remaining environment store code value after :=
  ⟨size, rfl, original⟩

theorem agreement_does_not_force_strict :
    ContinuationAgreement [] [] .unit [] [] .unit ∧ ¬ ContinuationSize true [] [] .unit [] [] .unit := by
  refine ⟨.refl _ _ _, ?_⟩
  intro strict
  obtain ⟨child, smaller, original⟩ := strict.remaining EvaluationSize.unit
  cases original
  simp at smaller

theorem duplicate_prefix_order {α : Type} (scope : List α) (canonical : Environment)
    (same : α) (first second : Value) :
    CanonicalPrefix scope canonical (same :: same :: scope) (second :: first :: canonical) :=
  (CanonicalPrefix.cons scope canonical same first).trans (.cons _ _ same second)

theorem selected_entry {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (binds : ProtectedExpressionMeaning.Binds entry)
    {scope childScope : SourceCoreLocalCell.Scope} {canonical childCanonical : Environment}
    {mapping finalMap : LocationMap} {world finalWorld : StoreTyping} {before after : Dynamic.Heap}
    {store finalStore : Store} (initial : entry scope mapping world before store canonical)
    (spine : CanonicalPrefix scope canonical childScope childCanonical)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
    entry childScope finalMap finalWorld after finalStore childCanonical ∧
      entry scope finalMap finalWorld after finalStore canonical :=
  ⟨installed transport binds initial spine maps worlds frame metadata, restored transport initial maps worlds frame metadata⟩

private def content : String := String.intercalate "\n" [
  "function ordered(seed: Word) returns (Word) { let kept = seed + 1; match ((seed, (11, 13))) { case (0, (left, right)) { let result = left + right; return result; } case (1, (left, right)) { return right; } default { return kept; } } }",
  "function empty(seed: Word) returns (Word) { match (seed) { case 0 {} default {} } return 17; }",
  "function failed(seed: Word) returns (Word) { match ((seed, 19)) { case (0, value) { let prior = value; let gap: Word; return gap; } default { return 23; } } }",
  "function scrutineeFault() returns (Word) { let gap: Word; match (gap) { case 0 { return 29; } default { return 31; } } }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "match prefix public resume" (first.resume 300000)).observation

/-- Source-visible hidden cells and only the selected ordered arm bindings
survive. Native snapshots and markers are checked by actual typed-prefix
formal consumers above, separately from this public source-state observation. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive match prefix bounds" content
    ["ordered", "empty", "failed", "scrutineeFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 839)⟩]}
  let nested : SourceTypedRuntime.Value := .product (word 11) (word 13)
  let pairType : TypeSystem.Ty := .product .word (.product .word .word)
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", [word 0], word 24, [(.word, some (word 0)), (.word, some (word 1)), (pairType, some (.product (word 0) nested)),
      (.word, some (word 11)), (.word, some (word 13)), (.word, some (word 24))]),
    ("ordered", [word 1], word 13, [(.word, some (word 1)), (.word, some (word 2)), (pairType, some (.product (word 1) nested)),
      (.word, some (word 11)), (.word, some (word 13))]),
    ("ordered", [word 2], word 3, [(.word, some (word 2)), (.word, some (word 3)), (pairType, some (.product (word 2) nested))]),
    ("empty", [word 0], word 17, [(.word, some (word 0)), (.word, some (word 0))]),
    ("empty", [word 1], word 17, [(.word, some (word 1)), (.word, some (word 1))]),
    ("failed", [word 1], word 23, [(.word, some (word 1)), (.product .word .word, some (.product (word 1) (word 19)))])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 7, 53, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match prefix resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"match prefix result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"match prefix ordered source cells changed {name}"
      | other => throw (IO.userError s!"match prefix expected success {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("failed", [word 0], [(.word, some (word 0)), (.product .word .word, some (.product (word 0) (word 19))),
      (.word, some (word 19)), (.word, some (word 19)), (.word, none)]),
    ("scrutineeFault", [], [(.word, none)])]
  for (name, arguments, cells) in failures do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 7, 53, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match prefix fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"match prefix fault cells changed {name}"
      | other => throw (IO.userError s!"match prefix expected first fault {name}: {reprStr other}")
  IO.println "recursive named match prefix bounds: ordered arm/default cells, empty body, strict original native continuation, first faults and public resume GREEN"

end Tests.SourceCoreRecursiveNamedMatchPrefixBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedMatchProgramMeaning
/-! Public Match consumers retain real caller state, raw source admission and
argument-code evaluation. They obtain every callee law from the same static
BodyState-indexed Match profile. Existing runtime suites cover emitted calls,
recursive Match bodies, source faults and public resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedMatchProgramMeaning
open Solcore SourceSemantics SourceSemantics.CoreLowering
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem actual_call_has_fuel
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreCalls.call header.named.signature
          (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact RecursiveNamedProgramCallMeaning.emitted_call_has_sufficient_fuel_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller member represented heaps agrees argumentsEvaluated executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem actual_completed_call
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (SourceCoreCalls.call header.named.signature
        (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact RecursiveNamedProgramCallMeaning.completed_call_reflects_program_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller member represented heaps admitted heapTyped argumentsTyped agrees argumentsEvaluated completed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The original native body grade stays strictly below its enclosing call. -/
theorem original_body_reflects (budget size : Nat) (strict : size < budget)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (measured : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact RecursiveNamedCatalogFiniteCompletion.reflects_sized_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller member represented heaps
    budget size (Nat.le_of_lt strict) capture measured

/-- Program outcomes include success and language fault under the same profile. -/
abbrev program_has_fuel := @RecursiveNamedProgramOutcomeMeaning.program_has_sufficient_native_fuel_match

/-- Native completion supplies a source outcome without prior source execution. -/
abbrev program_reflects := @RecursiveNamedProgramOutcomeMeaning.completed_run_reflects_program_match

end Tests.SourceCoreRecursiveNamedMatchProgramMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedMatchResidualContexts
/-! Match extraction uses the actual declaration context without changing its
residual flag. Source admission, child certificates, emitted native typing and
interpretation of the returned diagnostics remain independent static inputs.
The recursive named match meaning is a separate boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedMatchResidualContexts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GenericImperativeMatch

section ActualHeader
variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program} {header : RecursiveNamedCatalog.Header prepared values ambient.definitions program}
  {administrative : Core.Context} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {matchCompilation : SourceCoreCompatibleDataMatches.Context}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- The real Header supplies lexical closure and residual=true. No false
context or source execution is used to reach the one extraction traversal. -/
theorem actual_header_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (matchPolicy : header.policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = ambient.definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (hidden : MatchHiddenFresh header.function.source)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : Syntax header.function.source expressionSyntax header.context (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (RecursiveNamedCatalogNativeContexts.bodyScope header) header.context)
    {nativeType : Ty}
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source (RecursiveNamedCatalogNativeContexts.bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (RecursiveNamedCatalogNativeContexts.bodyScope header) ++ administrative) header.body nativeType ambient.definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source (RecursiveNamedCatalogNativeContexts.bodyScope header) header.function.body header.output header.reasonAt true header.escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor diagnosticPolicy header.layouts header.owner header.active prepared.layout.frame header.globals header.onError values header.function.source expressionSyntax certificates ambient.definitions administrative matchCompilation.solvedRequirements
        header.context (RecursiveNamedCatalogNativeContexts.bodyScope header) (.statements true header.function.body) header.function.resultType header.output flow,
      header.body = LocalControl.finish header.output (LocalLoop.toControl header.output flow header.escaped)
        (if header.output = .unit then LanguageResult.success .unit else LanguageResult.failure header.output (.word header.fellThrough)) := by
  exact extraction_of_typed_body_with_residual true diagnosticPolicy factory matchPolicy matchValues matchDefinitions matchAllocator
    (MatchChildStatic.of_hidden hidden) readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy header.unique
    assignmentExpressions syntaxTree (RecursiveNamedSourceContextFacts.header_typeVariables header)
    (RecursiveNamedSourceContextFacts.header_residual header) sourceSignatures declarations projection accepted nativeTyped

/-- Only the returned receipt's own diagnostics construct its matching Ready. -/
theorem actual_ready {diagnosticPolicy : AssignmentDiagnosticPolicy} {flow : Expr}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (receipt : ExtractionFor diagnosticPolicy header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax certificates ambient.definitions administrative matchCompilation.solvedRequirements
      header.context (RecursiveNamedCatalogNativeContexts.bodyScope header) (.statements true header.function.body)
      header.function.resultType header.output flow)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (sameLedger : matchCompilation.solvedRequirements = header.solved)
    (interpreted : receipt.diagnostics registry faults) : Tree.ReadyFor diagnosticPolicy registry faults receipt.tree := by
  obtain ⟨errors, ledgers⟩ := receipt.materialize registry faults interpreted
  exact ledgers.ready (by simpa only [sameLedger] using initialValid) sourceSignatures

theorem actual_header_context : header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true :=
  RecursiveNamedSourceContextFacts.header_fields header

theorem old_false_excluded : header.context.residualTypeVariables ≠ false :=
  RecursiveNamedSourceContextFacts.header_not_false header
end ActualHeader

/-- Both arm binder extension and default preserve the source residual flag. -/
theorem scoped_context_mode {source : TypedSource} {parent child : SourceSemantics.Context}
    {hidden : List Resolved.LocalId} {type : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request} {mode : Bool}
    (context : GenericMatchChildren.ScopedContextFor source parent hidden type cases fallback request child)
    (same : parent.residualTypeVariables = mode) : child.residualTypeVariables = mode :=
  context.closed_fields.2.2.trans same

section DuplicateArms
open GenericMatchChildren
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"generic_match", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "generic_match.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutinee : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def pattern : TypedMatchPattern := {source := .wildcard span span, type := .unit, resolution := .wildcard}
private def arm : TypedMatchCase := ⟨span, pattern, []⟩
private def resolution : MatchResolution := ⟨scrutinee, hidden, [arm, arm], some [], []⟩
private def scrutineeNode : ExpressionNode := {id := scrutinee, span, type := .unit, form := .tuple []}
private def statementNode : StatementNode := ⟨site, span, .unit, .matchWith resolution⟩
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement site]
  nodes := [.statement statementNode, .expression scrutineeNode]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withResidualTypeVariables
private def control : ControlContext := ⟨.unit, 0⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.get catalogExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private def lowerExpression : SourceCoreCompatibleDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
  .ok ⟨.unit, LanguageResult.success .unit⟩
private def lowerBody : SourceCoreCompatibleDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ => .ok (LocalLoop.fallthrough .unit)
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def compiled : Expr := match SourceCoreCompatibleDataMatches.lowerWithReasons compilation lowerExpression lowerBody
    20 source [] site resolution .unit reasonAt Word.zero with | .ok code => code | .error _ => .unit
private theorem accepted : SourceCoreCompatibleDataMatches.lowerWithReasons compilation lowerExpression lowerBody
    20 source [] site resolution .unit reasonAt Word.zero = .ok compiled := by rfl

/-- Even equal request data appears three times: both source arms and default. -/
theorem finite_actual_children : ∃ requests,
    CompatibleMatchCertificates.Certificate compilation source [] site resolution .unit Word.zero
      (fun _ _ lowered => lowered = ⟨.unit, LanguageResult.success .unit⟩) (Occurs requests) compiled ∧
    requests.length = 3 ∧ ∀ request ∈ requests, ∃ fuel,
      lowerBody fuel source request.scope request.statements .unit reasonAt Word.zero = .ok request.code := by
  simpa only [resolution, List.length_cons, List.length_nil, Option.isSome_some, ↓reduceIte] using
    finite_of_lower (fun _ _ generated => Except.ok.inj generated.symm) accepted

private def request : Request := ⟨[(hidden, .unit)], [], LocalLoop.fallthrough .unit⟩
private def compiledPattern : SourceCoreCompatibleDataMatches.Pattern :=
  ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
example : armRequests [(hidden, .unit)] resolution.cases
    [(compiledPattern, LocalLoop.fallthrough .unit), (compiledPattern, LocalLoop.fallthrough .unit)] ++
    fallbackRequests [(hidden, .unit)] resolution.defaultBody (LocalLoop.fallthrough .unit) =
      [request, request, request] := rfl

private theorem patternTyped : TypedMatchPatternHasType context pattern .unit [] 0 :=
  ⟨rfl, .wildcard, .wildcard, ⟨by simp, by simp⟩⟩
private theorem casesTyped : MatchCasesHaveType source control context .unit resolution.cases
    [BodyFacts.empty, BodyFacts.empty] := by
  exact .cons (.intro patternTyped (.nil _) (.nil _ _))
    (.cons (.intro patternTyped (.nil _) (.nil _ _)) (.nil _ _ _))
private theorem sourceSelected : Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody (.arm [] []) :=
  .head (.intro .wildcard .wildcard)

theorem selected_context_is_source : ContextFor source context .unit resolution.cases resolution.defaultBody request context :=
  ContextFor.selected_arm_at request rfl casesTyped sourceSelected (.nil _)

private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem scrutineeTyped : ExpressionHasType source context scrutinee .unit := by
  have admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures, Context.withResidualTypeVariables])
  apply ExpressionHasType.ofOrdinary (node := scrutineeNode) (rawType := .unit) (lookupExpression?_sound (by cbv))
    (.tuple (.nil _)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private def expressionSyntax (id : ExpressionId) : Prop := id = scrutinee
private theorem syntaxTree (mode : Bool) : GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode [site]) .unit := by
  apply GenericImperativeMatch.Syntax.matchWith (expressionSyntax := expressionSyntax) (node := statementNode) (scrutineeNode := scrutineeNode)
    (control := control) (caseFacts := [BodyFacts.empty, BodyFacts.empty]) rfl rfl (.inl rfl) rfl scrutineeTyped rfl casesTyped
  · intro statements selected
    have same : statements = [] := Option.some.inj selected.symm
    subst statements
    exact ⟨context, _, .nil _ _⟩
  · rfl
  · intro arm member binder found; rfl
  · intro request childContext selected
    have empty : request.statements = [] := by
      cases selected with
      | @arm actualArm binders arity childContext member same typed extended =>
        have armEq : actualArm = arm := by simpa [resolution] using member
        exact same.trans (congrArg TypedMatchCase.body armEq)
      | default same => exact Option.some.inj same.symm
    rw [empty]
    exact .body (.nil (.inl rfl))
  · exact .body (.nil (.inr rfl))

private theorem hiddenSourceFresh : GenericImperativeMatch.MatchHiddenFresh source := by
  intro id node actualResolution found form
  have sameNode : node = statementNode := by
    have member := (lookupStatement?_sound found).1
    simpa [source] using member
  subst node
  have sameResolution : actualResolution = resolution := StatementForm.matchWith.inj form.symm
  subst actualResolution
  simp [SourceCoreDataPlaces.declaredBinders, SourceCoreDataPlaces.patternBinders,
    source, statementNode, scrutineeNode, resolution, arm, pattern]

section ActualFlow
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
  {policy : SourceCoreLoops.Policy} {matchCompilation : SourceCoreCompatibleDataMatches.Context}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
  (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
  (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
  (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
  (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
    source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → certificates sourceContext scope id lowered)
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
  (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
  (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures → CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    expressionSyntax id → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → certificates sourceContext scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (flowAccepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [site] .unit reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matchPolicy matchValues matchDefinitions matchAllocator readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy assignmentExpressions declarations flowAccepted nativeTyped in
/-- A real accepted emitted flow exposes finite recursive match children;
there is no semantic body assumption in this extraction. -/
theorem actual_flow_tree : GenericImperativeMatch.Tree layouts specialization active frame globals onError values source
    expressionSyntax certificates definitions administrative context scope (.statements mode [site]) .unit .unit code := by
  obtain ⟨receipt⟩ := GenericImperativeMatch.extraction_of_typed_flow_with_residual true .unconditional
    (AssignmentDiagnosticOrigins.Factory.unchanged .unconditional source invalidOperand) matchPolicy matchValues matchDefinitions matchAllocator (GenericImperativeMatch.MatchChildStatic.of_hidden hiddenSourceFresh)
    readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions
    (syntaxTree mode) rfl rfl rfl declarations (by cbv) flowAccepted (infer_sound nativeTyped)
  exact receipt.tree
end ActualFlow

end DuplicateArms


private def content : String := String.intercalate "\n" [
  "function choose(n: Word) returns (Word) { let result = 0; match (n) { case 0 { result = 5; } default { result = 7; } } return result; }",
  "function branch(n: Word) returns (Word) { match (n) { case 0 { { return 11; } } default { if (true) { return 13; } else { return 17; } } } return 19; }",
  "function loop(n: Word) returns (Word) { let result = 0; for (let i = 0; i < n; i += 1) { match (i) { case 0 { continue; } default { result += i; } } } return result; }",
  "function keyed(m: mapping(Bool => Word)) returns (Word) { match (m[true]) { case 31 { m[true] = 7; } default { m[false] = 9; } } return m[true]; }",
  "function fail(n: Word) returns (Word) { let result = 29; let gap: Word; match (n) { case 0 { result = 31; return gap; } default { result = 37; } } return result; }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "match declaration context resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"match context prefix changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"match context ordered cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual match declaration contexts" content
    ["choose", "branch", "loop", "keyed", "fail"]
  for named in compiled.indexed.base.functions do
    let context := declarationContext compiled.sourceProgram.signatures named.specialized.key.declaration []
      named.specialized.assumptions named.specialized.function.solvedRequirements
    require (context.residualTypeVariables && context.typeVariables.isEmpty) "real declaration context flags changed"
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31), (.bool true, w 91), (.bool false, w 4)]
  let updated : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 7), (.bool true, w 91), (.bool false, w 4)]
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("choose", [w 0], w 5, [(.word, some (w 0)), (.word, some (w 5)), (.word, some (w 0))]),
    ("choose", [w 3], w 7, [(.word, some (w 3)), (.word, some (w 7)), (.word, some (w 3))]),
    ("branch", [w 0], w 11, [(.word, some (w 0)), (.word, some (w 0))]),
    ("branch", [w 2], w 13, [(.word, some (w 2)), (.word, some (w 2))]),
    ("loop", [w 3], w 3, [(.word, some (w 3)), (.word, some (w 3)), (.word, some (w 3)), (.word, some (w 0)), (.word, some (w 1)), (.word, some (w 2))]),
    ("keyed", [mapping], w 7, [(.mapping .bool .word, some updated), (.word, some (w 31))]),
    ("fail", [w 3], w 37, [(.word, some (w 3)), (.word, some (w 37)), (.word, none), (.word, some (w 3))])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩, ⟨.bool, some (.bool false)⟩]}
  let baselines ← tests.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← finish compiled "fail" [w 0] 300000 initial
  for fuel in [0, 7, 43, 300000] do
    for (test, baseline) in tests.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match context public resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"match context result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"match context expected success {name}")
    let observed ← finish compiled "fail" [w 0] fuel initial
    require (reprStr observed == reprStr failed) "match context first fault/resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
      cells initial final [(.word, some (w 0)), (.word, some (w 31)), (.word, none), (.word, some (w 0))] "fail"
    | _ => throw (IO.userError "match context first fault lost")
  IO.println "match residual contexts: real true scopes, branch/default, terminal blocks/ifs, for-post, mapping order, fault cells/resume GREEN"
end Tests.SourceCoreRecursiveNamedMatchResidualContexts
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedParameterPackingFacts
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedParameterPackingFacts
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics.CoreLowering RecursiveNamedCatalog RecursiveNamedParameterPackingFacts

theorem ordered_row {left right : List Ty} (arity : left.length = right.length)
    (packed : SourceCoreCompatibleCatalog.packTypes left = SourceCoreCompatibleCatalog.packTypes right) :
    left = right := packed_eq_of_length arity packed

theorem zero_unit_ambiguity :
    SourceCoreCompatibleCatalog.packTypes [] = SourceCoreCompatibleCatalog.packTypes [.unit] ∧
    ([] : List Ty).length ≠ ([.unit] : List Ty).length := by decide

theorem tuple_arity_ambiguity :
    SourceCoreCompatibleCatalog.packTypes [.word, .bool] =
      SourceCoreCompatibleCatalog.packTypes [.product .word .bool] ∧
    ([.word, .bool] : List Ty).length ≠ ([.product .word .bool] : List Ty).length := by decide

variable {checked : CallableAncestryPairedLookup.Checked}
  {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment}
  {program : Solcore.SourceSemantics.Program}

theorem actual_header_native_row (header : Header prepared values definitions program)
    (packed : header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd)) :
    header.bindings.map Prod.snd = header.named.inputs.map Prod.snd :=
  header_native_types header packed

theorem actual_header_projections (header : Header prepared values definitions program)
    (packed : header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd))
    (projected : (header.named.inputs.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.named.inputs.map Prod.snd)) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := header_projections header packed projected

end Tests.SourceCoreRecursiveNamedParameterPackingFacts
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPlaceAssignmentBounds
/-! Projected assignment phases consume original source or Core size witnesses.
Successful reflection returns the real typed seven-slot continuation directly;
its independently reconstructed source size is not bounded by the Core budget.
Concrete named expression Trees close every key and RHS runtime premise. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedPlaceAssignmentBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup SourceCoreCompatibleDataPlaces
open CompatibleEquality CompatibleHeap CoreProof
abbrev ValuesContext := SourceCoreCompatibleValues.Context
section Static
variable {checked : CallableAncestryPairedLookup.Checked} {base : Base checked}
  {installedPlan : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {source : TypedSource} {program : SourceSemantics.Program}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {bodies : NamedCallExpressions.Bodies installedPlan values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {place : PlaceResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (runtimeViews : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


variable {targetPrepared : Prepared} {index : Nat} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {site : SourceCoreElaboration.ErrorSite} {codes : List SourceCoreBasic.LoweredExpr}
  {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values source
    (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
    scope site place targetPrepared codes sourceTypes leaf administrative)
  (ordinary : (∀ key value, targetPrepared.route.rootSourceType ≠ .mapping key value) → targetPrepared.route.rootMapping = none)
  (generated : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope rhs lowered)
  (found : source.lookupExpression? rhs = some node)
  (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
  (rhsCore : lowered.type = targetPrepared.route.leafType)
  (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
  (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, targetPrepared.route.rootType))
  (rootTyped : WritableLocal context place.root targetPrepared.route.rootSourceType)
  (missingTokens : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root targetPrepared.steps resolved reason token count → faults reason token)
  (invalidTokens : ∀ location, faults (.uninitializedLocation location) targetPrepared.invalidProjection)

include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing layout ordinary generated found rhsView rhsCore profile slot rootTyped unique owners in
/-- Original source children are below one fixed outer budget. -/
theorem named_preserves (budget : Nat) {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updated after) (bounded : size ≤ budget) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep values.checked registry functions finalMap finalWorld targetPrepared.route.rootSourceType updated updatedValue targetPrepared.route.rootType ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ actual)
        (ProtectedPlaceAssignmentSuccess.writtenContext targetPrepared (SourceCoreCalls.packArguments codes).type actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute targetPrepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (targetPrepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) :=
  ProtectedPlaceAssignmentSuccess.preserves_prefix_bounded budget layout ordinary extension
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    faithful observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped trace bounded invalid

include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing layout ordinary generated found rhsView rhsCore profile slot rootTyped unique owners missingTokens invalidTokens in
/-- Fault prefixes retain the effects of earlier keys and RHS calls. -/
theorem named_fault (budget : Nat) {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator rhs reason after)
    (bounded : size ≤ budget) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute targetPrepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (targetPrepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedPlaceAssignmentFaults.preserves_bounded budget layout ordinary extension
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    faithful observations missingTokens invalidTokens generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped trace bounded next outputType invalid

include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing layout ordinary generated found rhsView rhsCore profile slot rootTyped missingTokens invalidTokens in
/-- Reflection uses concrete named reflection only; source preservation is not
replayed to obtain the continuation slots or a native cost. -/
theorem named_reflects (budget : Nat) {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute targetPrepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
        (binaryOperator (targetPrepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore)
    (bounded : size ≤ budget) :
    RecursiveNamedPlaceAssignmentContracts.ResultAt size values.checked registry functions program context evidence source faults
      targetPrepared (SourceCoreCalls.packArguments codes).type actualContext place operator rhs environment actual
      before store mapping world (next.rename ξ) outputType value finalStore :=
  ProtectedPlaceAssignmentReflection.reflects_bounded budget layout ordinary extension
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing) budget)
    runtimeViews faithful observations missingTokens invalidTokens generated found rhsView rhsCore profile
    environments heaps agrees actualTyped installed locals slot rootTyped completed bounded
end Static

section SizedResults
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FunctionCalls.FaultRep}
  {prepared : Prepared} {place : PlaceResolution} {operator : Syntax.ValueAssignOp}
  {environment : Dynamic.Environment} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {rhs : ExpressionId}
  {actual : Environment} {actualContext : Core.Context} {keyType : Ty}
  {next : Expr} {output : Ty} {value : Value} {finalStore : Store} {size budget : Nat}

/-- The continuation is the actual native child, while the source derivation
has its own independent size. This is the input needed by a bounded Header. -/
theorem continuation_or_fault
    (result : RecursiveNamedPlaceAssignmentContracts.ResultAt size checked registry functions program context evidence source faults
      prepared keyType actualContext place operator rhs environment actual before store mapping world next output value finalStore)
    (within : size ≤ budget) :
    (∃ sourceSize reason after, SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source
      environment before place operator rhs reason after) ∨
    (∃ sourceSize updated after slots commitStore remainingSize finalWorld,
      SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual)
        (CompatibleRenamedPlaceSuccess.writtenContext prepared keyType actualContext) ambient.definitions ∧
      remainingSize < budget ∧ EvaluationSize remainingSize (slots ++ actual) commitStore (shift 7 next) value finalStore) := by
  cases result with
  | fault trace _ _ _ _ _ _ _ => exact .inl ⟨_, _, _, trace⟩
  | committed trace _ _ _ _ _ count typed strict remaining =>
    exact .inr ⟨_, _, _, _, _, _, _, trace, count, typed, Nat.lt_of_lt_of_le strict within, remaining⟩
end SizedResults

private def content : String := String.intercalate "\n" [
  "function mark(value: Word) returns (Word) { let copied = value; return copied; }",
  "function fail(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function nested(raw: mapping(Word => mapping(Word => Word)), a: Word, b: Word) returns (mapping(Word => mapping(Word => Word))) { raw[mark(a)][mark(b)] += mark(5); return raw; }",
  "function keyFault(raw: mapping(Word => mapping(Word => Word)), a: Word, b: Word) returns (Word) { raw[mark(a)][fail(b)] += mark(5); return 99; }",
  "function rhsFault(raw: mapping(Word => mapping(Word => Word)), a: Word, b: Word) returns (Word) { raw[mark(a)][mark(b)] += fail(5); return 99; }",
  "function afterWrite(raw: mapping(Word => mapping(Word => Word)), a: Word, b: Word) returns (Word) { raw[mark(a)][mark(b)] += mark(5); return fail(99); }",
  "function unitResult(raw: mapping(Word => mapping(Word => Word)), a: Word, b: Word) { raw[mark(a)][mark(b)] = mark(5); }"
]
private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (wordValue n))

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"bounded projected resume {name}" (first.resume 400000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"bounded projected prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"bounded projected ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "bounded projected gap binder" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "bounded projected exact fault binder missing")

/-- Runtime budgets exercise suspension independently of source proof sizes.
Every completed observation checks the complete ordered heap suffix. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "bounded projected assignments" content
    ["nested", "keyFault", "rhsFault", "afterWrite", "unitResult"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  let innerType : TypeSystem.Ty := .mapping (.comptime .word) (.comptime .word)
  let inner (first : Nat) : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(wordValue 3, wordValue first), (wordValue 3, wordValue 91)]
  let outer (first : Nat) : SourceTypedRuntime.Value := .mapping (.comptime .word) innerType
    [(wordValue 7, inner first), (wordValue 7, inner 113)]
  let raw := outer 37
  let changed := outer 42
  let replaced := outer 5
  let rootCell (value : SourceTypedRuntime.Value) : TypeSystem.Ty × Option SourceTypedRuntime.Value :=
    (.mapping .word (.mapping .word .word), some value)
  let args := [raw, wordValue 7, wordValue 3]
  for fuel in [0, 43, 211, 400000] do
    match ← finish compiled "nested" args fuel initial with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr changed) "bounded projected raw headers/duplicate priority changed"
      cells initial final (rootCell changed :: ([7,3,7,7,3,3,5,5].map present)) "nested"
    | other => throw (IO.userError s!"bounded projected nested: {reprStr other}")
    for (name, root, numbers) in [("keyFault", raw, [7,3,7,7,3]),
        ("rhsFault", raw, [7,3,7,7,3,3,5]), ("afterWrite", changed, [7,3,7,7,3,3,5,5,99])] do
      match ← finish compiled name args fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"bounded projected fault binder {name}"
        cells initial final (rootCell root :: numbers.map present ++ [(.word, none)]) name
      | other => throw (IO.userError s!"bounded projected fault {name}: {reprStr other}")
    match ← finish compiled "unitResult" args fuel initial with
    | .done .unit final => cells initial final (rootCell replaced :: ([7,3,7,7,3,3,5,5].map present)) "unitResult"
    | other => throw (IO.userError s!"bounded projected Unit: {reprStr other}")
  IO.println "bounded projected assignments: original strict continuation/typed seven slots, independent source sizes, ordered nested key/RHS faults, raw duplicate priority, write-before-fault, Unit and resume GREEN"

end Tests.SourceCoreRecursiveNamedPlaceAssignmentBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPlaceKeyBounds
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Ordered keys use fixed outer budgets and preserve actual child measures.
The native singleton pack has the same size as its child; longer packs expose
strict children. Concrete named Trees close the pointwise meaning inputs.
These are key-phase contracts, not bounded whole-assignment/recursive-call
soundness. Runtime fixtures separately exercise the cached compiler. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedPlaceKeyBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup

section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (leaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (caller : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context caller)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

variable {scope : SourceCoreLocalCell.Scope} {projections : List PlaceProjection}
  {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Core.Environment}
  {before : Dynamic.Heap} {store : Core.Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
    scope mapping world before store canonical)

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments heaps locals agrees typed installed in
/-- The concrete recursive Tree eliminates every child/body runtime premise.
The actual protected entry still has to be supplied at the key phase. -/
theorem named_key_preserves (budget size : Nat) (bounded : size ≤ budget) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (tree : DataExpressionSequence.Tree source
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    {evaluated : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context caller source environment before projections evaluated after) :
    ∃ sources native finalStore finalMap finalWorld,
      DataPlaceKeyOrder.Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues native)) finalStore ∧
      DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types (codes.map (·.type)) sources native ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedPlaceKeys.preserves_bounded budget
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) tree
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful leaves runtimeViews caller valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    environments heaps locals agrees typed installed trace bounded

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments heaps locals agrees typed installed in
/-- Key completion reconstructs source projection evaluation/fault in order,
using protected lookup/current-frame facts at the actual current key prefix. -/
theorem named_key_reflects (budget size : Nat) (bounded : size < budget)
    (tree : DataExpressionSequence.Tree source
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    {value : Core.Value} {finalStore : Core.Store}
    (complete : CoreProof.EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedPlaceKeyContracts.OutcomeAt program sourceSize context caller source environment before projections outcome after ∧
      DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types codes faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedPlaceKeys.reflects_bounded budget
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) tree
    (RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful leaves runtimeViews caller valid
        uninitialized missing bodyUninitialized bodyMissing) budget)
    environments heaps locals agrees typed installed complete bounded

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments heaps locals agrees typed installed in
/-- Actual successful key effects preceding the fault remain in the result. -/
theorem named_key_fault (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (tree : DataExpressionSequence.Tree source
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.SourceProjectionsFault program size context caller source environment before projections reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedPlaceKeys.preserves_fault_bounded budget
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) tree
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful leaves runtimeViews caller valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    environments heaps locals agrees typed installed trace bounded
end Static

/-- A singleton contains no pack wrapper, including under arbitrary renaming. -/
theorem singleton_same_size (code : SourceCoreBasic.LoweredExpr) (ξ : Renaming)
    (size : Nat) (environment : Core.Environment) (before after : Core.Store) (value : Core.Value) :
    CoreProof.EvaluationSize size environment before
      ((SourceCoreCalls.packArguments [code]).expression.rename ξ) value after ↔
    CoreProof.EvaluationSize size environment before (code.expression.rename ξ) value after := Iff.rfl

/-- Therefore strict child meaning needs an outer budget, not the pack size. -/
theorem singleton_requires_outer_budget (size : Nat) :
    (¬ size < size) ∧ size < size + 1 := ⟨Nat.lt_irrefl _, Nat.lt_succ_self _⟩

/-- A longer pack exposes the actual first computation as a strict child. -/
theorem cons_first_strict {size : Nat} {environment : Core.Environment} {before after : Core.Store}
    {value : Core.Value} (first second : SourceCoreBasic.LoweredExpr)
    (rest : List SourceCoreBasic.LoweredExpr) (ξ : Renaming)
    (complete : CoreProof.EvaluationSize size environment before
      ((SourceCoreCalls.packArguments (first :: second :: rest)).expression.rename ξ) value after) :
    ∃ childSize middle childValue, childSize < size ∧
      CoreProof.EvaluationSize childSize environment before (first.expression.rename ξ) childValue middle := by
  change CoreProof.EvaluationSize size environment before
    ((LocalSequence.pair first.type (SourceCoreCalls.packArguments (second :: rest)).type
      first.expression (SourceCoreCalls.packArguments (second :: rest)).expression).rename ξ) value after at complete
  rw [DataExpressionSequence.pair_rename] at complete
  exact complete.bind_computation

section SourceOrder
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before middle after : Dynamic.Heap} {key : ExpressionId} {first second : Dynamic.Value}
  {firstSize secondSize : Nat}

/-- Repeated key IDs still have two ordered evaluations and different values. -/
theorem repeated_key_order
    (left : SourceExecutionSize.ExpressionEvaluates program firstSize context evidence source environment before key first middle)
    (right : SourceExecutionSize.ExpressionEvaluates program secondSize context evidence source environment middle key second after) :
    ∃ size, SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before
      [.member "outer" 0, .index key, .member "inner" 1, .index key]
      [.member "outer" 0, .index first, .member "inner" 1, .index second] after :=
  ⟨_, .member (.index left (.member (.index right .nil)))⟩

/-- Faulting at the second key needs no evaluation of later keys. -/
theorem fault_keeps_successful_prefix {reason : Dynamic.SemanticFault} {later : ExpressionId}
    (left : SourceExecutionSize.ExpressionEvaluates program firstSize context evidence source environment before key first middle)
    (failed : SourceExecutionSize.ExpressionFaults program secondSize context evidence source environment middle key reason after) :
    ∃ size, SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before
      [.index key, .member "inner" 1, .index key, .index later] reason after ∧ firstSize < size ∧ secondSize < size := by
  refine ⟨_, .indexTail left (.memberTail (.indexHead failed)), ?_, ?_⟩
  all_goals simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
end SourceOrder

private def content : String := String.intercalate "\n" [
  "function key(value: Word) returns (Word) { let saved = value * 10; return value; }",
  "function bad(value: Word) returns (Word) { let saved = value * 10; let gap: Word; return gap; }",
  "function single(raw: mapping(Word => Word), seed: Word) returns (mapping(Word => Word)) { raw[key(seed)] = key(seed + 2); return raw; }",
  "function ordered(raw: mapping(Word => mapping(Word => Word)), seed: Word) returns (mapping(Word => mapping(Word => Word))) { raw[key(seed)][key(seed + 1)] = key(seed + 2); return raw; }",
  "function repeated(raw: mapping(Word => mapping(Word => Word)), seed: Word) returns (mapping(Word => mapping(Word => Word))) { raw[key(seed)][key(seed)] = key(seed + 2); return raw; }",
  "function firstFault(raw: mapping(Word => mapping(Word => Word)), seed: Word) returns (mapping(Word => mapping(Word => Word))) { raw[bad(seed)][key(seed + 1)] = key(seed + 2); return raw; }",
  "function secondFault(raw: mapping(Word => mapping(Word => Word)), seed: Word) returns (mapping(Word => mapping(Word => Word))) { raw[key(seed)][bad(seed + 1)] = key(seed + 2); return raw; }"
]
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def flat (first : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(word 1, word first), (word 1, word 91)]
private def inner (atOne atTwo : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(word 2, word atTwo), (word 2, word 91), (word 1, word atOne)]
private def nested (atOne atTwo : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.mapping .word .word)
    [(word 1, inner atOne atTwo), (word 1, inner 71 72)]

/-- One cached program exercises normal completion and resumptions. Allocated
callee parameters/locals record key order, and exact heaps detect a later key,
RHS or writeback incorrectly executed after failure. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "bounded ordered named keys" content
    ["single", "ordered", "repeated", "firstFault", "secondFault"]
  let initial : SourceTypedRuntime.RuntimeState :=
    {heap := [⟨.comptime .word, none⟩, ⟨.word, some (word 819)⟩]}
  let badKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let bad ← SourceCoreUnifiedCorpusSupport.get "key fault body" (SourceCompilationPlan.exactSpecialization compiled.validationPlan badKey)
  let gap ← match (SourceCoreDataPlaces.declaredBinders bad.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "key fault binder missing")
  let mapType : TypeSystem.Ty := .mapping .word .word
  let nestedType : TypeSystem.Ty := .mapping .word mapType
  let cases := [
    ("single", flat 8, some (flat 3), mapType, [some 1, some 10, some 3, some 30]),
    ("ordered", nested 9 8, some (nested 9 3), nestedType, [some 1, some 10, some 2, some 20, some 3, some 30]),
    ("repeated", nested 9 8, some (nested 3 8), nestedType, [some 1, some 10, some 1, some 10, some 3, some 30]),
    ("firstFault", nested 9 8, none, nestedType, [some 1, some 10, none]),
    ("secondFault", nested 9 8, none, nestedType, [some 1, some 10, some 2, some 20, none])]
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut observations : List String := []
    for (name, input, expected, inputType, tailCells) in cases do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [input, word 1] fuel initial
      let completed ← SourceCoreUnifiedCorpusSupport.get "key resume" (started.resume 400000)
      let observation := completed.observation
      let final ← match observation, expected with
        | .done actual final, some expected =>
          SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"key result/raw metadata {name}"
          pure final
        | .fault (.uninitializedLocal id) final, none =>
          SourceCoreUnifiedCorpusSupport.assertTrue (id == gap) s!"key exact fault {name}"
          pure final
        | other, _ => throw (IO.userError s!"key unexpected {name}: {reprStr other}")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "key inert prefix"
      let cells := [(inputType, some (expected.getD input)), (.word, some (word 1))] ++
        tailCells.map (fun value => (TypeSystem.Ty.word, value.map word))
      SourceCoreUnifiedCorpusSupport.assertTrue
        (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr cells)
        s!"key ordered effects/fault suppression {name}: {reprStr final.heap}"
      observations := observations ++ [reprStr observation]
    if fuel == 400000 then baseline := observations
    else SourceCoreUnifiedCorpusSupport.assertTrue (observations == baseline) "key resumed observations"
  IO.println "bounded ordered keys: same-size singleton, strict cons, source order/repetitions, failure prefix, raw duplicates and four budgets GREEN"

end Tests.SourceCoreRecursiveNamedPlaceKeyBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedProgramCallMeaning
/-! Formal consumers keep the actual caller layout, argument bundle receipt
and independent source entry conditions for emitted native calls. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedProgramCallMeaning
open Solcore.SourceSemantics.CoreLowering
abbrev emitted_call_has_sufficient_fuel :=
  @RecursiveNamedProgramCallMeaning.emitted_call_has_sufficient_fuel
abbrev completed_call_reflects_program :=
  @RecursiveNamedProgramCallMeaning.completed_call_reflects_program
end Tests.SourceCoreRecursiveNamedProgramCallMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedProgramEntrySource
/-! Formal consumers retain the complete public program-entry and native
completion signatures, including their independent entry conditions. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedProgramEntrySource
open Solcore.SourceSemantics.CoreLowering

abbrev program_has_sufficient_native_fuel :=
  @RecursiveNamedProgramEntrySource.program_has_sufficient_native_fuel

abbrev native_success_reflects_program :=
  @RecursiveNamedProgramEntrySource.native_success_reflects_program

end Tests.SourceCoreRecursiveNamedProgramEntrySource
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedProgramOutcomeMeaning
/-! The consumer covers both native result branches and keeps all actual
initial input, catalog authority and profile conditions in its signature. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedProgramOutcomeMeaning
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap

abbrev program_has_sufficient_native_fuel :=
  @RecursiveNamedProgramOutcomeMeaning.program_has_sufficient_native_fuel

abbrev completed_run_reflects_program :=
  @RecursiveNamedProgramOutcomeMeaning.completed_run_reflects_program

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty}
  {faults : FunctionCalls.FaultRep} {program : SourceSemantics.Program} {entry : Dynamic.ProgramEntry}
  {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}

theorem successful_result_observes_source_value {payload : Core.Value}
    (executed : Dynamic.ProgramOutcome program entry before outcome after)
    (represented : FunctionCalls.ResultRepresents model mapping world sourceType type faults
      outcome (.inRight .word payload)) :
    ∃ value, Dynamic.ProgramEvaluates program entry before value after ∧
      model.Represents mapping world sourceType value payload type := by
  cases represented with
  | value payload =>
    cases executed with
    | value evaluated => exact ⟨_, evaluated, payload⟩

theorem failed_result_observes_source_fault {token : Word}
    (executed : Dynamic.ProgramOutcome program entry before outcome after)
    (represented : FunctionCalls.ResultRepresents model mapping world sourceType type faults
      outcome (.inLeft type (.word token))) :
    ∃ reason, Dynamic.ProgramFaults program entry before reason after ∧ faults reason token := by
  cases represented with
  | fault related =>
    cases executed with
    | fault failed => exact ⟨_, failed, related⟩

end Tests.SourceCoreRecursiveNamedProgramOutcomeMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedSpecializationBodyFacts
/-! Consumers construct the independent canonical body judgment from the
actual specialization. They retain static validity and real invocation facts.
The runtime audit checks complete rewritten bodies and ordered solved rows. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSpecializationBodyFacts
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering TypeSystem
open RecursiveNamedSpecializationBodyFacts

section Formal
variable {program : CheckedProgram} {signature : ProgramFunctionSignature}
  {generic : CheckedFunction} {supplied : ParameterSubstitution}
  {specialized : SourceSpecialization.SpecializedFunction}
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)

include accepted

theorem actual_independent_body :
    specialized.function.typedBody = StructuralSubstitution.applyTypedSource
      specialized.parameterSubstitution generic.typedBody := body accepted

theorem actual_ordered_ledger :
    specialized.function.solvedRequirements = generic.solvedRequirements.map
      (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution) := ledger accepted

theorem actual_inputs :
    specialized.function.typedBody.inputs = generic.typedBody.inputs.map
      (StructuralSubstitution.applyBinder specialized.parameterSubstitution) := by
  rw [body accepted]
  rfl

theorem actual_roots : specialized.function.typedBody.roots = generic.typedBody.roots := by
  rw [body accepted]
  rfl

theorem canonical_instantiated
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized)) :
    Dynamic.FunctionInstantiates (Program.ofChecked program)
      (CallableNamedMetadata.instantiation specialized) (bodyInstance program specialized) :=
  instantiated signatureMember genericMember accepted valid

theorem canonical_source_frame {function : Dynamic.Closure}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized))
    (source : function.source = specialized.function.typedBody)
    (context : function.context = (bodyInstance program specialized).context)
    (parameters : function.parameters = specialized.function.typedBody.inputs)
    (result : function.resultType = specialized.function.inferredBodyType)
    (captured : function.captured = [])
    (roots : Dynamic.StatementRoots specialized.function.typedBody.roots function.body)
    (covers : function.evidence.Covers (bodyInstance program specialized).context) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation specialized)
      (bodyInstance program specialized) function :=
  source_frame signatureMember genericMember accepted valid source context parameters result captured roots covers
end Formal

theorem residual_context (program : CheckedProgram) (specialized : SourceSpecialization.SpecializedFunction) :
    (bodyInstance program specialized).context.residualTypeVariables = true := rfl

theorem wrong_declaration_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : signature.id ≠ generic.declaration) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (identities accepted).1

theorem wrong_raw_body_owner_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : generic.typedBody.owner ≠ generic.declaration) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (identities accepted).2.1

private def content : String := String.intercalate "\n" [
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function local<T>(value: T) returns (T) { let copied = value; return copied; }",
  "function calc(value: Word) returns (Word) { let first = value + 1; let second = first + 2; return second; }",
  "function wordRoot() returns (Word) { return choose(7, true); }",
  "function boolRoot() returns (Bool) { return choose(false, 9); }",
  "function localRoot() returns (Word) { return local(11); }",
  "function calcRoot() returns (Word) { return calc(5); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named specialization body facts" content
    ["wordRoot", "boolRoot", "localRoot", "calcRoot"]
  let mut genericRows := 0
  let mut solvedRows := 0
  let mut reversedRequests := 0
  for specialized in compiled.indexed.base.plan.specializations do
    let signature ← match compiled.sourceProgram.signatures.functions.find? (·.id == specialized.declaration) with
      | some value => pure value
      | none => throw (IO.userError "specialization body signature missing")
    let generic ← match compiled.sourceProgram.functions.find? (·.declaration == specialized.declaration) with
      | some value => pure value
      | none => throw (IO.userError "specialization body original checked function missing")
    let actual ← get "actual accepted body specialization"
      (SourceSpecialization.specializeFunction signature generic specialized.parameterSubstitution.reverse)
    require (reprStr actual == reprStr specialized) "specialization body complete canonical record changed"
    require (specialized.declaration == generic.declaration && signature.id == generic.declaration &&
      generic.typedBody.owner == generic.declaration) "specialization body actual declaration/owner changed"
    require (reprStr specialized.function.typedBody == reprStr
      (StructuralSubstitution.applyTypedSource specialized.parameterSubstitution generic.typedBody))
      "specialization body full independent source substitution changed"
    require (reprStr specialized.function.solvedRequirements == reprStr
      (generic.solvedRequirements.map (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution)))
      "specialization body full ordered solved ledger changed"
    require (specialized.function.inferredBodyType == specialized.parameterSubstitution.apply generic.inferredBodyType)
      "specialization body independent result substitution changed"
    require (specialized.parameterSubstitution.map Prod.fst == signature.scheme.parameters)
      "specialization body original complete canonical domain changed"
    let instantiatedBody := bodyInstance compiled.sourceProgram specialized
    require (instantiatedBody.context.residualTypeVariables && instantiatedBody.context.typeParameters.isEmpty)
      "specialization body declaration context flags changed"
    require (reprStr instantiatedBody.source == reprStr specialized.function.typedBody &&
      reprStr instantiatedBody.context == reprStr (declarationContext compiled.sourceProgram.signatures generic.declaration []
        (signature.scheme.predicates.map (ProgramPredicate.applyParameters specialized.parameterSubstitution))
        (generic.solvedRequirements.map (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution))))
      "specialization body full independent context/source changed"
    if !specialized.parameterSubstitution.isEmpty then genericRows := genericRows + 1
    if specialized.parameterSubstitution.length == 2 then
      require (specialized.parameterSubstitution != specialized.parameterSubstitution.reverse)
        "specialization body reverse request lost distinct full domain order"
      reversedRequests := reversedRequests + 1
    solvedRows := solvedRows + specialized.function.solvedRequirements.length
  require (genericRows == 3 && reversedRequests == 2 && solvedRows ≥ 2)
    s!"specialization body fixture coverage changed {genericRows}/{reversedRequests}/{solvedRows}"
  IO.println "named specialization bodies: actual pass, canonical independent instantiation, full bodies and ordered solved ledgers GREEN"

end Tests.SourceCoreRecursiveNamedSpecializationBodyFacts
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedSpecializationStageFacts
/-! The real specialization retains the complete stage analysis. Independent
source structural properties, rather than native runtime types, establish its
normative classification. Comptime values are not evaluated by these proofs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSpecializationStageFacts
open Solcore Frontend SourceInference TypeSystem SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedSpecializationStageFacts

section Formal
variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)

include accepted

theorem actual_analysis :
    SourceStageAnalysis.analyzeFunction specialized.function = .ok specialized.stageAnalysis := analyzed accepted

theorem actual_graph (closed : OccurrenceGraphClosed generic.typedBody) :
    OccurrenceGraphClosed specialized.function.typedBody := graph_closed accepted closed

theorem actual_local_identities (owned : LocalIdentityOwnership generic.typedBody) :
    LocalIdentityOwnership specialized.function.typedBody := local_identities accepted owned

theorem actual_source_stages (closed : OccurrenceGraphClosed generic.typedBody)
    (owned : LocalIdentityOwnership generic.typedBody) :
    Staging.FunctionHasStages specialized.function := has_stages accepted closed owned

theorem actual_program_stages {program : CheckedProgram}
    (programTyped : ProgramWellFormed (Program.ofChecked program)) (member : generic ∈ program.functions) :
    Staging.FunctionHasStages specialized.function := has_stages_of_program programTyped member accepted

/-- This exposes the independent input and root derivations produced by the
actual pass. Neither a prior FunctionHasStages nor a stage-evaluation law is an input. -/
theorem independent_inputs_and_roots (closed : OccurrenceGraphClosed generic.typedBody)
    (owned : LocalIdentityOwnership generic.typedBody) :
    ∃ inputScope finalScope,
      Staging.FunctionInputsStage specialized.function.typedBody specialized.function.returnComptime
        specialized.function.inferredBodyType inputScope ∧
      Staging.RootsStage specialized.function.typedBody inputScope specialized.function.typedBody.roots finalScope := by
  cases has_stages accepted closed owned with
  | intro _ _ _ inputs roots => exact ⟨_, _, inputs, roots⟩
end Formal

theorem raw_stage_marker_matters :
    Staging.ComptimeOnlyType (.comptime .word) ∧ ¬Staging.ComptimeOnlyType .word := by
  refine ⟨.marked _, ?_⟩
  intro marked
  cases marked

private def content : String := String.intercalate "\n" [
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function mutable(value: Word) returns (Word) { let saved = value; saved = saved + 1; return saved; }",
  "function identity(comptime value: Word) returns (Word) { return value; }",
  "function dec(comptime value: integer) returns (comptime<integer>) { return integerSub(value, 1); }",
  "function caller() returns (Word) { return wordFromInteger(dec(10)); }",
  "function normal(value: Word) returns (Word) { return mutable(value); }",
  "function empty() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

def run : IO Unit := do
  let program ← get "specialization stages checked program" (Frontend.checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let mut rows := 0
  let mut genericRows := 0
  let mut stagedInputs := 0
  let mut stagedReturns := 0
  let mut runtimeRows := 0
  let mut deferredRows := 0
  for generic in program.functions do
    let signature ← match program.signatures.functions.find? (·.id == generic.declaration) with
      | some signature => pure signature
      | none => throw (IO.userError "specialization stage signature missing")
    let supplied := signature.scheme.parameters.map fun parameter =>
      (parameter, if parameter.index % 2 == 0 then TypeSystem.Ty.word else TypeSystem.Ty.bool)
    let specialized ← get "specialization stages actual pass"
      (SourceSpecialization.specializeFunction signature generic supplied.reverse)
    let analyzed ← get "specialization stages actual retained analysis"
      (SourceStageAnalysis.analyzeFunction specialized.function)
    require (reprStr analyzed == reprStr specialized.stageAnalysis)
      "specialization stages full actual stage table changed"
    require (specialized.parameterSubstitution.map Prod.fst == signature.scheme.parameters &&
      specialized.function.returnComptime == generic.returnComptime &&
      specialized.function.typedBody.inputs.map (·.comptime) == generic.typedBody.inputs.map (·.comptime))
      "specialization stages full domain/raw input and result flags changed"
    require (reprStr specialized.function.typedBody == reprStr
      (StructuralSubstitution.applyTypedSource specialized.parameterSubstitution generic.typedBody))
      "specialization stages full independent source changed"
    require (specialized.function.typedBody.roots == generic.typedBody.roots &&
      specialized.function.typedBody.nodes.map (·.occurrenceId) == generic.typedBody.nodes.map (·.occurrenceId))
      "specialization stages original graph occurrence identities changed"
    if !supplied.isEmpty then genericRows := genericRows + 1
    if specialized.function.typedBody.inputs.any (·.comptime) then stagedInputs := stagedInputs + 1
    if specialized.function.returnComptime then stagedReturns := stagedReturns + 1
    if analyzed.expressions.any (fun row => row.stage == .runtime) then runtimeRows := runtimeRows + 1
    if analyzed.expressions.any (fun row => row.stage == .deferred) then deferredRows := deferredRows + 1
    rows := rows + 1
  require (rows == 7 && genericRows == 1 && stagedInputs == 2 && stagedReturns == 1 && runtimeRows ≥ 2 && deferredRows ≥ 1)
    s!"specialization stage fixture coverage changed {rows}/{genericRows}/{stagedInputs}/{stagedReturns}/{runtimeRows}/{deferredRows}"
  IO.println "named specialization stages: real retained analysis, independent source graph/identities and comptime/runtime/deferred classification GREEN"

end Tests.SourceCoreRecursiveNamedSpecializationStageFacts
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedSpecializationValidity
/-! Canonical validity consumers retain independent formation of every raw
replacement. Accepted specialization supplies the domain and all redundant
metadata, including staging flags. Ground unused nominal rows remain a
separate catalog-formation boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSpecializationValidity
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering TypeSystem
open RecursiveNamedSpecializationValidity

section Formal
variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)

include accepted

theorem actual_guards : signature.scheme.body = generic.type ∧
    signature.parameterComptime = generic.typedBody.inputs.map (·.comptime) ∧
    signature.returnComptime = generic.returnComptime := guards accepted

theorem actual_exact (unique : signature.scheme.parameters.Nodup) :
    SourceSemantics.ParameterSubstitution.Exact specialized.parameterSubstitution signature.scheme.parameters :=
  exact accepted unique

theorem actual_valid {context : SourceSemantics.Context}
    (member : signature ∈ context.signatures.functions)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context specialized.parameterSubstitution) :
    DeclarationInstantiation.Valid context (CallableNamedMetadata.instantiation specialized) :=
  canonical_valid accepted member unique range

theorem actual_program_valid {program : CheckedProgram}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (member : signature ∈ program.signatures.functions)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized) :=
  valid_of_program wellFormed member accepted range

theorem actual_body {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked program) (CallableNamedMetadata.instantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program specialized) :=
  instantiated signatureMember genericMember accepted unique range

theorem actual_retained_body {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program specialized) :=
  retained_instantiated signatureMember genericMember accepted unique range
end Formal

section Prepared
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {named : SourceCoreGeneralFunctions.Function}
  {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
  (signatureMember : signature ∈ program.signatures.functions)
  (genericMember : generic ∈ program.functions)
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
  (unique : signature.scheme.parameters.Nodup)
  (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures program.signatures) named.specialized.parameterSubstitution)
  (closed : named.specialized.assumptions = [])
  (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)

include signatureMember genericMember accepted unique range closed inputs compiled

theorem actual_prepared_frame :
    CompatibleNamedBody.NamedAgreement named
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized)
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) :=
  of_compilation signatureMember genericMember accepted unique range closed inputs compiled

theorem actual_prepared_retained_frame :
    CompatibleNamedBody.NamedAgreement named
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized)
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) :=
  retained_of_compilation signatureMember genericMember accepted unique range closed inputs compiled
end Prepared

theorem wrong_type_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : signature.scheme.body ≠ generic.type) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (guards accepted).1

theorem wrong_parameter_flags_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : signature.parameterComptime ≠ generic.typedBody.inputs.map (·.comptime)) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (guards accepted).2.1

theorem wrong_return_flag_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : signature.returnComptime ≠ generic.returnComptime) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (guards accepted).2.2

/-- A raw unused replacement is ground and does not change Word, yet its
missing nominal declaration prevents formation of the complete range. -/
theorem unused_nominal_boundary (owner : Resolved.DeclarationId) (parameter : TypeParameterId) :
    SourceSpecialization.firstNonConcrete (.constructor (.declaration owner)) = none ∧
      TypeSystem.ParameterSubstitution.apply [(parameter, .constructor (.declaration owner))] .word = .word ∧
      ¬ SourceSemantics.ParameterSubstitution.RangeWellFormed
        (Context.ofSignatures ⟨[], [], [], [], [], []⟩) [(parameter, .constructor (.declaration owner))] := by
  refine ⟨rfl, rfl, ?_⟩
  intro range
  have scopeProof := (range parameter (.constructor (.declaration owner)) (by simp)).typeWellScoped
  generalize typeEq : Ty.constructor (TypeConstructorId.declaration owner) = type at scopeProof
  cases scopeProof <;> simp_all [Context.ofSignatures]

private def content : String := String.intercalate "\n" [
  "function choose<A, B>(first: A, second: B) returns (A) { let saved = first; return saved; }",
  "function staged<T>(comptime value: T) returns (comptime<T>) { return value; }",
  "function unused<T>() returns (Word) { let value: Word = 3; return value; }",
  "function wordRoot() returns (Word) { return choose(9, false); }",
  "function boolRoot() returns (Bool) { return choose(true, 8); }",
  "function stagedRoot() returns (comptime<Word>) { return staged(5); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named specialization validity" content
    ["wordRoot", "boolRoot", "stagedRoot"]
  let mut rows := 0
  let mut genericRows := 0
  let mut stagedRows := 0
  for specialized in compiled.indexed.base.plan.specializations do
    let signature ← match compiled.sourceProgram.signatures.functions.find? (·.id == specialized.declaration) with
      | some signature => pure signature
      | none => throw (IO.userError "specialization validity signature missing")
    let original ← match compiled.sourceProgram.functions.find? (·.declaration == specialized.declaration) with
      | some original => pure original
      | none => throw (IO.userError "specialization validity checked body missing")
    let actual ← get "specialization validity actual reversed request"
      (SourceSpecialization.specializeFunction signature original specialized.parameterSubstitution.reverse)
    require (reprStr actual == reprStr specialized) "specialization validity full actual result changed"
    let instantiation := CallableNamedMetadata.instantiation specialized
    require (signature.scheme.body == original.type &&
      signature.parameterComptime == original.typedBody.inputs.map (·.comptime) &&
      signature.returnComptime == original.returnComptime) "specialization validity guard outputs changed"
    require (instantiation.declaration == signature.id &&
      instantiation.parameterSubstitution.map Prod.fst == signature.scheme.parameters &&
      decide signature.scheme.parameters.Nodup) "specialization validity complete canonical domain changed"
    require (instantiation.type == specialized.parameterSubstitution.apply signature.scheme.body &&
      reprStr instantiation.predicates == reprStr (signature.scheme.predicates.map
        (ProgramPredicate.applyParameters specialized.parameterSubstitution)) &&
      instantiation.parameterComptime == signature.parameterComptime &&
      instantiation.returnComptime == signature.returnComptime) "specialization validity full raw metadata changed"
    if !specialized.parameterSubstitution.isEmpty then genericRows := genericRows + 1
    if instantiation.returnComptime then stagedRows := stagedRows + 1
    rows := rows + 1
  require (rows == 6 && genericRows == 3 && stagedRows == 2)
    s!"specialization validity coverage changed {rows}/{genericRows}/{stagedRows}"
  let signature ← match compiled.sourceProgram.signatures.functions.find? (·.name == "unused") with
    | some signature => pure signature
    | none => throw (IO.userError "unused specialization signature missing")
  let original ← match compiled.sourceProgram.functions.find? (·.declaration == signature.id) with
    | some original => pure original
    | none => throw (IO.userError "unused specialization body missing")
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | _ => throw (IO.userError "unused specialization parameter coverage changed")
  let foreign := {signature.id with declarationIndex := 1000000}
  require (!(compiled.sourceProgram.signatures.dataTypes.any (·.id == foreign)) &&
    !(compiled.sourceProgram.signatures.contracts.any (·.id == foreign))) "unused nominal unexpectedly cataloged"
  let raw : TypeSystem.Ty := .constructor (.declaration foreign)
  require (SourceSpecialization.firstNonConcrete raw == none) "unused nominal should be syntactically ground"
  let phantom ← get "actual accepted unused foreign nominal specialization"
    (SourceSpecialization.specializeFunction signature original [(parameter, raw)])
  require (phantom.parameterSubstitution == [(parameter, raw)] && phantom.function.type == original.type &&
    reprStr phantom.function.typedBody == reprStr original.typedBody &&
    reprStr phantom.function.solvedRequirements == reprStr original.solvedRequirements)
    "unused full raw range was dropped or unexpectedly changed the source body"
  match SourceSpecialization.specializeFunction
      {signature with scheme := {signature.scheme with body := .bool}} original [(parameter, raw)] with
    | .error (.signatureTypeMismatch _ _) => pure ()
    | _ => throw (IO.userError "wrong original signature type passed specialization")
  match SourceSpecialization.specializeFunction
      {signature with parameters := [⟨"extra", .word, true⟩]} original [(parameter, raw)] with
    | .error (.parameterComptimeMismatch _ _) => pure ()
    | _ => throw (IO.userError "wrong parameter staging flags passed specialization")
  match SourceSpecialization.specializeFunction
      {signature with returnComptime := !signature.returnComptime} original [(parameter, raw)] with
    | .error (.returnComptimeMismatch _ _) => pure ()
    | _ => throw (IO.userError "wrong result staging flag passed specialization")
  IO.println "named specialization validity: actual guards/full canonical metadata, staging, unused foreign nominal boundary GREEN"

end Tests.SourceCoreRecursiveNamedSpecializationValidity
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedStaticExtraction
/-! The production compiler success supplies the existing Calls.Tree. Formal
consumers retain the actual inventory, ordered instantiation, independent source
judgments and admission filter; no runtime meaning occurs in these receipts.
Whole source Syntax, scopes and unrestricted compiler admission remain separate
obligations. Runtime audits actual contextual child code and ordered full global
rows, then checks source heap effects and resumed success/failure. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedStaticExtraction
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup RecursiveNamedCatalog
open RecursiveNamedCallSelectionCertificates RecursiveNamedExpressionCompilerCertificates
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
#check_failure SourceTypedRuntime.run
#check_failure RecursiveNamedExpressionCompilerCertificates.BodyMeaning
section Formal
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}

theorem actual_contextual_tree
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : SourceCoreGeneralFunctions.CallableContext}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    {caller : SourceSpecialization.SpecializedFunction}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers sourceContext)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary source locals compilation.owner admitted)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (unique : NodeOccurrencesUnique source)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source sourceContext compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_contextual admission coverage sourceTypes order ordinary callerSelected callerClosed
    unique closed residual declarations sourceSignatures allowed found typed readPolicy lowerPolicy leafPolicy accepted

/-- Full ordered source metadata follows from actual selected records, not
from agreement of native signatures or specialization keys alone. -/
theorem actual_selected_header {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation} {index : Nat}
    {signature : SourceCoreCalls.Signature}
    (coverage : Coverage headers compilation) (ordered : Ordered compilation.plan instantiation)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature)) :
    ∃ header, header ∈ headers ∧ header.slot = index ∧ header.named.signature = signature ∧
      instantiation = header.instantiation ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok header.named.specialized :=
  selected coverage ordered accepted
end Formal

theorem ordered_children_keep_duplicates (callee first second : ExpressionId) (instantiation : DeclarationInstantiation) :
    evaluationChildren (.call callee [first, second, first] (.declaration instantiation)) = [first, second, first] := rfl

theorem unsupported_product_arity (first second third : ExpressionId) :
    ¬ compositionForm (.tuple [first, second, third]) := by simp [compositionForm]

theorem indirect_calls_are_outside_admission (callee : ExpressionId) (arguments : List ExpressionId)
    (metadata : IndirectCallResolution) : ¬ compositionForm (.call callee arguments (.indirect metadata)) := by
  simp [compositionForm]

private def content : String := String.intercalate "\n" [
  "enum Box { Box(Bool) }",
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function truth(flag: Bool) returns (Bool) { return flag; }",
  "function pair<A, B>(a: A, b: B) returns (A) { return a; }",
  "function take(a: Word, b: Word) returns (Word) { return a - b; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function ordered() returns (Word) { return pair(side(7), truth(true)); }",
  "function duplicate() returns (Word) { return take(side(7), side(7)); }",
  "function grouped() returns (integer) { return ((integerSub(wordToInteger(side(7)), wordToInteger(side(9))))); }",
  "function choose() returns (integer) { return truth(true) ? integerAdd(wordToInteger(side(7)), wordToInteger(side(9))) : wordToInteger(fail()); }",
  "function boxed() returns (Box) { return Box(truth(integerEq(7, 7))); }",
  "function paired() returns ((Bool, Bool)) { return (truth(integerEq(7, 7)), truth(integerLt(7, 7))); }",
  "function indexed(m: mapping(Bool => Word)) returns (Word) { return m[truth(true)]; }",
  "function unary() returns (Bool) { return !truth(false); }",
  "function skip() returns (Bool) { return false && truth(integerEq(7, 7)); }",
  "function firstFault() returns (Word) { return take(fail(), side(99)); }",
  "function laterFault() returns (Word) { return take(side(7), fail()); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- Re-enter the actual compiler callback using the real named source, global
inventory and parameter scope. These checks do not synthesize static source
judgments or treat runtime observation as evidence for a formal Tree. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) (names : List String) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "static extraction diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "static extraction parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut callCount := 0
  let mut genericCount := 0
  let mut formCount := 0
  for named in prepared.base.functions do
    let original ← match prepared.base.sourceProgram.signatures.functions.find? (·.id == named.signature.key.declaration) with
      | some signature => pure signature | none => throw (IO.userError "static extraction source signature missing")
    if names.contains original.name then
      let own ← match diagnostics.base.find? named.signature.key with
        | some own => pure own | none => throw (IO.userError "static extraction own diagnostics missing")
      let source := CallableIndexedNamedGeneration.source named
      let compilation := CallableIndexedNamedGeneration.context prepared named
      let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
      let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
      let reasonAt := diagnostics.reasonAt named.signature.key
      let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
        prepared.base.callableContext none none
      for item in source.nodes do
        match item with
        | .expression node =>
          match node.form with
          | .reference _ (.declaration _) => pure ()
          | _ =>
            let code ← get "actual contextual expression" (lower prepared.fuel source scope node.id reasonAt)
            let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
              prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
            require (Core.infer? nativeContext code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
              "actual contextual expression lost native type"
            formCount := formCount + 1
            match node.form with
            | .call _ arguments (.declaration instantiation) =>
              let key ← get "actual static instantiation target" (SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation)
              let specialized ← get "actual full static record" (SourceCompilationPlan.exactSpecialization compilation.plan key)
              require (decide (instantiation = CallableNamedCanonicalOrder.retainedInstantiation specialized))
                "static extraction changed complete retained instantiation"
              require (decide (instantiation.parameterSubstitution.map Prod.fst = (specialized.parameterSubstitution.map Prod.fst).reverse))
                "static extraction changed retained domain order"
              let rows := compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key))
              let (signature, index) ← match rows with
                | [row] => pure row | _ => throw (IO.userError "static extraction actual full global row missing")
              require (compiled.indexed.base.functions[index]?.map (·.signature) == some signature)
                "static extraction header slot does not contain complete signature"
              let codes ← arguments.mapM (fun id => get "ordered actual child code" (lower (prepared.fuel - 1) source scope id reasonAt))
              require (codes.length == arguments.length && arguments.length == specialized.function.typedBody.inputs.length)
                "static extraction actual argument arity/order lost"
              require (code.expression == SourceCoreCalls.call signature
                (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments codes).expression compilation.internalReason)
                "static extraction ordered argument emission changed"
              callCount := callCount + 1
              if specialized.parameterSubstitution.length == 2 then genericCount := genericCount + 1
            | _ => pure ()
        | _ => pure ()
  require (callCount >= 20 && genericCount == 1 && formCount >= 60)
    s!"static extraction fixture coverage changed: calls={callCount}, generic={genericCount}, nodes={formCount}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "static extraction public resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"static extraction old heap changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"static extraction ordered source cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let names := ["ordered", "duplicate", "grouped", "choose", "boxed", "paired", "indexed", "unary", "skip", "firstFault", "laterFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named static extraction" content names
  inspect compiled names
  let box ← match compiled.sourceProgram.signatures.dataTypes with
    | [signature] => match signature.constructors with
      | [constructor] => pure (⟨constructor.id, [], constructor.payloadTypes, .nominal signature.id []⟩ : DataConstructorInstantiation)
      | _ => throw (IO.userError "static extraction constructor missing")
    | _ => throw (IO.userError "static extraction nominal signature missing")
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31)]
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", [], w 7, [(.word, some (w 7)), (.word, some (w 7)), (.bool, some (.bool true)), (.word, some (w 7)), (.bool, some (.bool true))]),
    ("duplicate", [], w 0, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7))]),
    ("grouped", [], .integer (-2), [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9))]),
    ("choose", [], .integer 16, [(.bool, some (.bool true)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9))]),
    ("boxed", [], .constructed box [.bool true], [(.bool, some (.bool true))]),
    ("paired", [], .product (.bool true) (.bool false), [(.bool, some (.bool true)), (.bool, some (.bool false))]),
    ("indexed", [mapping], w 31, [(.mapping .bool .word, some mapping), (.bool, some (.bool true))]),
    ("unary", [], .bool true, [(.bool, some (.bool false))]),
    ("skip", [], .bool false, [])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩]}
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← ["firstFault", "laterFault"].mapM (fun name => finish compiled name [] 300000 initial)
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"static extraction complete resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"static extraction result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"static extraction expected completion {name}")
    for (name, baseline) in ["firstFault", "laterFault"].zip failed do
      let observed ← finish compiled name [] fuel initial
      require (reprStr observed == reprStr baseline) s!"static extraction fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        let earlier := if name == "laterFault" then [(.word, some (w 7)), (.word, some (w 7))] else []
        cells initial final (earlier ++ [(.word, some (w 5)), (.word, none)]) name
      | _ => throw (IO.userError "static extraction lost ordered source fault")
  IO.println "recursive named static extraction: actual contextual success, existing call Tree, full ordered instantiation/header slots, child emission, complete heap/fault/resume GREEN"
end Tests.SourceCoreRecursiveNamedStaticExtraction
end
