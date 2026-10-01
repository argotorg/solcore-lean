import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotTail

/-! Successful source bit-not assignments and every completed emitted Word
bit-not assignment agree. Index expressions use a universal induction premise;
there is no RHS source expression or assumed child/helper execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotMeaning
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    (functions : FunctionModel checked.catalog) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked registry functions program context evidence source faults place environment coreEnvironment
        before store mapping world next outputType result finalStore
  | committed {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before place updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (continuation : Evaluates (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      Result checked registry functions program context evidence source faults place environment coreEnvironment
        before store mapping world next outputType result finalStore

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel compilation.checked.catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}

/-- Every independent successful Word snapshot update has a finite actual
native execution, including real setter allocations and the mapped write. -/
theorem preserves
    (layout : CompatiblePlaceAssignmentSuccess.Layout compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before place updated after)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ finalStore finalMap finalWorld,
      Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments codes)
        (LanguageResult.success .unit) (LanguageResult.success .unit) .unit operator true invalid)
        (.inRight .word .unit) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases trace with
  | intro resolve write =>
    obtain ⟨resolution, reference⟩ := CompatiblePlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    obtain ⟨commit⟩ := CompatiblePlaceBitNotCommit.of_write layout registryExtension faithful observations profile environments resolution write operator invalid
    refine ⟨commit.finalStore, resolution.mapping, commit.finalWorld, ?_, commit.heaps, resolution.maps,
      resolution.worlds.trans commit.worlds, resolution.frame.trans commit.frame, resolution.metadata.trans commit.metadata⟩
    exact .letE (.var reference) (LanguageResult.bind_success _ resolution.keysEvaluated
      (LanguageResult.bind_success _ resolution.snapshotEvaluated (commit.plug
        (by simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] using
          (Evaluates.inRight (leftType := .word) (initialStore := commit.finalStore)
            (environment := writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) .unit commit.replacement commit.value coreEnvironment) Evaluates.unit)))))

/-- Reflection has no prior source trace: the actual key/getter prefix gives
resolution, then the saved Word leaf constructs the independent snapshot write.
The generated Unit RHS leaves both heaps untouched. -/
theorem reflects
    (layout : CompatiblePlaceAssignmentSuccess.Layout compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {operator : Option BinaryOp} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments codes)
      (LanguageResult.success .unit) next outputType operator true invalid) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults place environment coreEnvironment
      before store mapping world next outputType result finalStore := by
  have targetPhase := CompatiblePlacePrefixReflection.reflects layout ordinary registryExtension meaning functionTypes faithful observations
    missingTokens invalidTokens environments heaps locals slot rootTyped completed
  cases targetPhase with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault (.target sourceFault) resultEq tokenRep heaps maps worlds frame metadata
  | resolved sourceTrace resolution remainder =>
    obtain ⟨replacement, native, represented, applies, _, _⟩ :=
      CompatiblePlaceBitNotModifier.word_success observations profile resolution.snapshotRelated
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit coreEnvironment) (rhs := .var 0) (.var (index := 1) rfl)
        operator resolution.store invalid
    have applies := resolution.selectedEq.symm ▸ applies
    obtain ⟨updated, after, written⟩ := CompatiblePlaceBitNotModifier.write_exists sourceTrace applies
    obtain ⟨commit⟩ := CompatiblePlaceBitNotCommit.of_write layout registryExtension faithful observations profile environments resolution written operator invalid
    exact .committed (.intro sourceTrace written) commit.heaps resolution.maps (resolution.worlds.trans commit.worlds)
      (resolution.frame.trans commit.frame) (resolution.metadata.trans commit.metadata)
      (slots := [.unit, commit.value, commit.replacement, .unit, .inRight .unit resolution.snapshot,
        packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) rfl
      (commit.reflects remainder)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotMeaning
