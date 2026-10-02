import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Fixed-budget bare assignments retain independent source costs and the
original Core continuation size. Concrete named Trees close RHS meaning.
Projected assignments, common Heads, headers and recursive callees are separate
integration boundaries; no static certificate contains a runtime premise. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedBareAssignmentBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup SourceCoreCompatibleDataPlaces
open CompatibleEquality CompatibleHeap CoreProof CompatibleBareAssignment
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
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
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
  (layout : CompatibleBareAssignment.Layout values targetPrepared)
  (bare : assignment.target.projections = [])
  (generated : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope rhs lowered)
  (found : source.lookupExpression? rhs = some node)
  (rhsView : SourceCoreRawMetadata.runtimeType targetPrepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
  (rhsCore : lowered.type = targetPrepared.route.leafType)
  (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType targetPrepared.route.rootSourceType = .word ∨
    SourceCoreRawMetadata.runtimeType targetPrepared.route.rootSourceType = .integer)
  (slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, targetPrepared.route.rootType))
  (rootTyped : WritableLocal context assignment.target.root targetPrepared.route.rootSourceType)


include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing layout bare generated found rhsView rhsCore profile slot rootTyped unique owners in
theorem named_preserves (budget : Nat) {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) (bounded : size ≤ budget) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep values.checked registry functions finalMap finalWorld targetPrepared.route.rootSourceType updated updatedValue targetPrepared.route.rootType ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext targetPrepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute targetPrepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (targetPrepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) :=
  ProtectedBareAssignment.preserves_prefix_bounded budget layout bare extension
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped trace bounded invalid

include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing layout bare generated found rhsView rhsCore profile slot rootTyped unique owners in
theorem named_fault (budget : Nat) {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before assignment.target operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute targetPrepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (targetPrepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedBareAssignment.preserves_fault_reachable_bounded budget layout bare extension
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped trace bounded next outputType invalid invalidToken

include extension faithful observations environments heaps locals agrees actualTyped installed valid runtimeViews
  uninitialized missing bodyUninitialized bodyMissing layout bare generated found rhsView rhsCore profile slot rootTyped in
theorem named_reflects (budget : Nat) {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute targetPrepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (targetPrepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedBareAssignmentContracts.ResultAt size values registry functions program context evidence source faults targetPrepared assignment.target operator environment before store mapping world
      rhs actual actualContext ξ next outputType value finalStore :=
  ProtectedBareAssignment.reflects_reachable_bounded budget layout bare extension
    (RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing) budget)
    observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped invalidToken completed bounded

end Static

section SizedResults
variable {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FunctionCalls.FaultRep}
  {prepared : Prepared} {place : PlaceResolution} {operator : Syntax.ValueAssignOp}
  {environment : Dynamic.Environment} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {rhs : ExpressionId}
  {actual : Environment} {actualContext : Core.Context} {ξ : Renaming}
  {next : Expr} {output : Ty} {value : Value} {finalStore : Store} {size budget : Nat}

/-- A successful reflection exposes the original smaller continuation, including
its seven real slots. The reconstructed source cost has no native cost bound. -/
theorem continuation_or_fault
    (result : RecursiveNamedBareAssignmentContracts.ResultAt size values registry functions program context evidence source
      faults prepared place operator environment before store mapping world rhs actual actualContext ξ next output value finalStore)
    (within : size ≤ budget) :
    (∃ sourceSize reason after, SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source
      environment before place operator rhs reason after) ∨
    (∃ sourceSize updated after slots commitStore remainingSize finalWorld,
      SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      slots.length = 7 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      remainingSize < size ∧ remainingSize < budget ∧
      EvaluationSize remainingSize (slots ++ actual) commitStore (shift 7 (next.rename ξ)) value finalStore) := by
  cases result with
  | fault trace _ _ _ _ _ _ _ => exact .inl ⟨_, _, _, trace⟩
  | success trace _ _ _ _ _ _ count typed smaller remaining =>
    exact .inr ⟨_, _, _, _, _, _, _, trace, count, typed, smaller, Nat.lt_of_lt_of_le smaller within, remaining⟩

/-- The RHS fault follows the actual successful target prefix, preserving its
heap and both original source child costs. -/
theorem rhs_fault_keeps_prefix {targetSize rhsSize : Nat} {target : Dynamic.ResolvedPlace}
    {middle after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (resolved : SourceExecutionSize.SourcePlaceResolves program targetSize context evidence source environment before place target middle)
    (failed : SourceExecutionSize.ExpressionFaults program rhsSize context evidence source environment middle rhs reason after) :
    ∃ measured, SourceExecutionSize.SourcePlaceAssignmentFaults program measured context evidence source environment before
      place operator rhs reason after ∧ targetSize < measured ∧ rhsSize < measured := by
  exact ⟨_, .rhs resolved failed, SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩
end SizedResults

private def content : String := String.intercalate "\n" [
  "function copy(value: Word) returns (Word) { let copied = value; return copied; }",
  "function rawCopy(value: mapping(Word => Word)) returns (mapping(Word => Word)) { let copied = value; return copied; }",
  "function fail(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function chain(seed: Word) returns (Word) { let root: Word; root = copy(seed); root += copy(2); root = copy(root); return copy(root); }",
  "function shadow(seed: Word) returns (Word) { let root = copy(seed); { let root: Word; root = copy(2); root += copy(3); } root += copy(4); return copy(root); }",
  "function absent(seed: Word) returns (Word) { let root: Word; root += copy(seed); return copy(99); }",
  "function rhsFault(seed: Word) returns (Word) { let root = copy(10); root += fail(seed); return copy(99); }",
  "function afterWrite(seed: Word) returns (Word) { let root = copy(10); root += copy(seed); return fail(root); }",
  "function unitResult(seed: Word) { let root: Word; root = copy(seed); root += copy(2); }",
  "function rawResult(raw: mapping(Word => Word)) returns (mapping(Word => Word)) { let root: mapping(Word => Word); root = rawCopy(raw); return root; }"
]
private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (wordValue n))

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"bounded bare resume {name}" (first.resume 400000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"bounded bare prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"bounded bare ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "bounded bare gap binder" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "bounded bare exact fault binder missing")

/-- Actual cached compilation is tested separately from the pointwise proofs.
Costs are not equated with runner fuel or compared across source and Core. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "bounded bare assignments" content
    ["chain", "shadow", "absent", "rhsFault", "afterWrite", "unitResult", "rawResult"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  for fuel in [0, 43, 211, 400000] do
    for (name, result, numbers) in [("chain", 9, [7,9,7,7,2,2,9,9,9,9]),
        ("shadow", 11, [7,7,7,11,5,2,2,3,3,4,4,11,11])] do
      match ← finish compiled name [wordValue 7] fuel initial with
      | .done value final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr (wordValue result)) s!"bounded bare result {name}"
        cells initial final (numbers.map present) name
      | other => throw (IO.userError s!"bounded bare {name}: {reprStr other}")
    match ← finish compiled "absent" [wordValue 7] fuel initial with
    | .fault (.invalidAssignmentOperands operator left right) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (operator == .add && left == none && right == some .word) "bounded bare operand diagnostics changed"
      cells initial final [present 7, (.word, none), present 7, present 7] "absent"
    | other => throw (IO.userError s!"bounded bare absent compound: {reprStr other}")
    for (name, numbers) in [("rhsFault", [7,10,10,10,7]), ("afterWrite", [7,10,10,17,7,7,17])] do
      match ← finish compiled name [wordValue 7] fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"bounded bare fault binder {name}"
        cells initial final (numbers.map present ++ [(.word, none)]) name
      | other => throw (IO.userError s!"bounded bare fault {name}: {reprStr other}")
    match ← finish compiled "unitResult" [wordValue 7] fuel initial with
    | .done .unit final => cells initial final ([7,9,7,7,2,2].map present) "unitResult"
    | other => throw (IO.userError s!"bounded bare Unit: {reprStr other}")
    let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
      [(wordValue 1, wordValue 37), (wordValue 1, wordValue 91)]
    match ← finish compiled "rawResult" [raw] fuel initial with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr raw) "bounded bare raw mapping headers/order changed"
      let copied : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.mapping .word .word, some raw)
      cells initial final [copied, copied, copied, copied] "rawResult"
    | other => throw (IO.userError s!"bounded bare raw mapping: {reprStr other}")
  IO.println "bounded bare assignments: actual seven slots, original smaller continuation, independent source costs, named RHS effects/faults, shadowing, raw copies, prefix and resume GREEN"
end Tests.SourceCoreRecursiveNamedBareAssignmentBounds
