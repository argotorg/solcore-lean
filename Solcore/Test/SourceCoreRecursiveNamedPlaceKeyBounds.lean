import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionBindings
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceKeys
import Solcore.Test.SourceCoreUnifiedCorpusSupport

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
