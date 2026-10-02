import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport

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
  (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
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
