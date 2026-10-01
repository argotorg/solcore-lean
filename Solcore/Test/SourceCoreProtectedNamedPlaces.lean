import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionBindings
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceKeys
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceResolution
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Actual lexical binding and guarded key/RHS consumers retain the installed
named globals and caller frame. Native source fixtures additionally exercise
writeback, earlier effects on failure, raw headers/duplicates and escaped
captures through the cached Core pipeline. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedPlaces
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
theorem named_key_preserves (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (tree : DataExpressionSequence.Tree source
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    {evaluated : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
    (trace : Dynamic.SourceProjectionsEvaluate program context caller source environment before projections evaluated after) :
    ∃ sources native finalStore finalMap finalWorld,
      DataPlaceKeyOrder.Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues native)) finalStore ∧
      DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types (codes.map (·.type)) sources native ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedPlaceKeys.preserves
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) tree
    (NamedCallExpressions.Tree.preserves functions extension faithful leaves runtimeViews caller valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    environments heaps locals agrees typed installed trace

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments heaps locals agrees typed installed in
/-- Key completion reconstructs source projection evaluation/fault in order,
using protected lookup/current-frame facts at the actual current key prefix. -/
theorem named_key_reflects
    (tree : DataExpressionSequence.Tree source
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    {value : Core.Value} {finalStore : Core.Store}
    (complete : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      DataPlaceKeyOrder.OutcomeTrace program context caller source environment before projections outcome after ∧
      DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types codes faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedPlaceKeys.reflects
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) tree
    (NamedCallExpressions.Tree.reflects functions extension faithful leaves runtimeViews caller valid
      uninitialized missing bodyUninitialized bodyMissing)
    environments heaps locals agrees typed installed complete

variable {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
  {preparedPlace : SourceCoreCompatibleDataPlaces.Prepared} {leaf : TypeSystem.Ty}
  {targetHeap : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr}
  (resolution : CompatiblePlaceResolution.Execution values.checked registry functions preparedPlace
    (CompatibleRenamedPlace.renamedCodes codes ξ) types place leaf target actual store mapping world before targetHeap)

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments locals agrees typed installed in
/-- The concrete named Tree supplies RHS meaning after the real key/getter
prefix, including all three hidden slots and the live post-RHS root. -/
theorem named_rhs_preserves (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context caller source environment targetHeap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := caller)
        (source := source) (faults := faults) resolution id node (CompatibleRenamedPlace.renamed lowered ξ)
        environment outcome after value finalStore finalMap finalWorld :=
  ProtectedPlaceRhs.preserves resolution
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful leaves runtimeViews caller valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    tree found environments agrees typed locals installed trace

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments locals agrees typed installed in
/-- Actual RHS completion yields its independent source outcome and exact
post-prefix heap. No source execution or body meaning is a premise. -/
theorem named_rhs_reflects
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node)
    {value : Core.Value} {finalStore : Core.Store}
    (complete : Evaluates
      (DataPlaceExecution.snapshotEnvironment preparedPlace.route.rootType resolution.target
        (DataPatternValues.packValues resolution.values) (.inRight .unit resolution.snapshot) actual)
      resolution.store (SourceCoreCompatibleDataPlaces.shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := caller)
        (source := source) (faults := faults) resolution id node (CompatibleRenamedPlace.renamed lowered ξ)
        environment outcome after value finalStore finalMap finalWorld :=
  ProtectedPlaceRhs.reflects resolution
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.reflects functions extension faithful leaves runtimeViews caller valid
      uninitialized missing bodyUninitialized bodyMissing)
    tree found environments agrees typed locals installed complete

/-- Scope removal restores variable attribution and retains the new store,
world, source map, exact captured closure and administrative histories. -/
theorem bind_restore {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} {canonical : Core.Environment}
    (entry : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world heap store canonical)
    (id : Resolved.LocalId) (type : Core.Ty) (value : Core.Value) :
    NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world heap store canonical := by
  have binding := NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix
  exact binding.restore (id := id) (type := type) (value := value) (binding.prepend entry)
end Static

private def content : String := String.intercalate "\n" [
  "function key(value: Word) returns (Word) { return value; }",
  "function first(value: Word) returns (integer) { let copied = wordToInteger(value); return copied; }",
  "function normal(seed: Word) returns (integer) { let saved = seed; let other = first(saved); let m: mapping(Word => Word); m[key(saved)] = wordFromInteger(integerAdd(first(saved), first(3))); return wordToInteger(m[key(saved)]); }",
  "function scoped(seed: Word) returns (integer) { let saved = seed; { let hidden = first(saved); hidden; } let m: mapping(Word => Word); m[key(saved)] = wordFromInteger(integerAdd(first(saved), 1)); return wordToInteger(m[key(saved)]); }",
  "function failing(seed: Word) returns (integer) { let saved = seed; let m: mapping(Word => Word); let gap: Word; m[key(saved)] = wordFromInteger(integerAdd(first(saved), first(gap))); return wordToInteger(m[saved]); }",
  "function keyFail(seed: Word) returns (integer) { let saved = seed; let m: mapping(Word => Word); let gap: Word; m[key(gap)] = wordFromInteger(first(saved)); return wordToInteger(m[saved]); }",
  "function rawUpdate(raw: mapping(Word => Word), seed: Word) returns (mapping(Word => Word)) { raw[key(seed)] = key(seed) + 1; return raw; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let saved = seed; return lam(delta: Word) -> Word { let m: mapping(Word => Word); m[key(saved)] = key(saved) + key(delta); return m[key(saved)]; }; }",
  "function escaped(seed: Word, delta: Word) returns (integer) { let apply = make(seed); return wordToInteger(apply(delta)); }"
]
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected named resume {name}" (first.resume 300000)).observation

private def checkPrefix (initial final : SourceTypedRuntime.RuntimeState) : IO Unit :=
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    "protected named source prefix changed"

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  checkPrefix initial final
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"protected named ordered cells {name}: {reprStr final.heap}"

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected named fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected named exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named places" content
    ["normal", "scoped", "failing", "keyFail", "rawUpdate", "escaped"]
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  let three : SourceTypedRuntime.Value := .word (Word.ofNatModulo 3)
  let eight : SourceTypedRuntime.Value := .word (Word.ofNatModulo 8)
  let ten : SourceTypedRuntime.Value := .word (Word.ofNatModulo 10)
  let mapType : TypeSystem.Ty := .mapping .word .word
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, .word (Word.ofNatModulo 37)), (seven, .word (Word.ofNatModulo 91))]
  let updated : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, eight), (seven, .word (Word.ofNatModulo 91))]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 819))⟩]}
  let failingGap ← faultBinder compiled "failing"
  let keyGap ← faultBinder compiled "keyFail"
  for fuel in [0, 43, 300000] do
    match ← finish compiled "normal" [seven] fuel initial with
    | .done (.integer 10) final =>
      cells initial final [(.word, some seven), (.word, some seven), (.word, some seven),
        (.integer, some (.integer 7)), (.integer, some (.integer 7)),
        (mapType, some (.mapping .word .word [(seven, ten)])), (.word, some seven),
        (.word, some seven), (.integer, some (.integer 7)), (.word, some three),
        (.integer, some (.integer 3)), (.word, some seven)] "normal"
    | other => throw (IO.userError s!"protected named normal: {reprStr other}")
    match ← finish compiled "scoped" [seven] fuel initial with
    | .done (.integer 8) final => checkPrefix initial final
    | other => throw (IO.userError s!"protected named scope restore: {reprStr other}")
    match ← finish compiled "rawUpdate" [raw, seven] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr updated)
        "protected named raw header/duplicates changed"
      cells initial final [(mapType, some updated), (.word, some seven), (.word, some seven),
        (.word, some seven)] "rawUpdate"
    | other => throw (IO.userError s!"protected named raw update: {reprStr other}")
    match ← finish compiled "escaped" [seven, three] fuel initial with
    | .done (.integer 10) final =>
      checkPrefix initial final
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.any fun cell => reprStr cell.value == reprStr (some (.mapping .word .word [(seven, ten)]) : Option SourceTypedRuntime.Value))
        "protected named escaped capture lost written map"
    | other => throw (IO.userError s!"protected named escaped: {reprStr other}")
    match ← finish compiled "failing" [seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == failingGap) "protected named RHS fault lost source binder"
      cells initial final [(.word, some seven), (.word, some seven), (mapType, none),
        (.word, none), (.word, some seven), (.word, some seven), (.integer, some (.integer 7))] "failing"
    | other => throw (IO.userError s!"protected named RHS fault: {reprStr other}")
    match ← finish compiled "keyFail" [seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == keyGap) "protected named key fault lost source binder"
      cells initial final [(.word, some seven), (.word, some seven), (mapType, none), (.word, none)] "keyFail"
    | other => throw (IO.userError s!"protected named key fault: {reprStr other}")
  IO.println "protected named places: bindings/restore, guarded key/RHS, writeback/raw metadata, caller histories/captures, earlier faults and resume GREEN"
end Tests.SourceCoreProtectedNamedPlaces
