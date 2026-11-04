import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceBitNot
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.PlaceAssignments

/-!
# Protected contracts: staged projected bit-not

Staged projected bit-not updates: commit, tail and faults.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotCommit
/-! Projected unary writeback consumes the actual key/getter state. Its Unit
slot is administrative; it creates no Source expression or Source RHS step. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleRenamedPlace
universe u v

def writtenContext (prepared : Prepared) (keyType : Ty) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.leafType :: .unit ::
    prepared.optionalLeaf :: keyType :: OptionalCell.referenceType prepared.route.rootType :: context

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

private theorem resolved_nonempty {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {sources : List Dynamic.Value} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved) (nonempty : steps ≠ []) : resolved ≠ [] := by
  have lengths : steps.length = resolved.length := by
    clear nonempty
    induction path generalizing sources resolved with
    | nil => cases shaped; rfl
    | member _ _ _ _ ih => cases shaped with | member tail => exact congrArg Nat.succ (ih tail)
    | index _ _ _ ih => cases shaped with | index tail => exact congrArg Nat.succ (ih tail)
  intro empty
  rw [empty, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

/-- Consume an independent snapshot write and derive its actual native
modifier, latest-root reconstruction and single mapped store update. -/
theorem typed_of_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before selectedHeap after : Dynamic.Heap} {store : Store} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before selectedHeap)
    (written : Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value) selectedHeap target updated after)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ commit : CompatiblePlaceBitNotCommit.Execution compilation.checked registry functions prepared (renamedCodes codes ξ)
        coreEnvironment resolution.store resolution.mapping resolution.world resolution.target resolution.values
        resolution.snapshot selectedHeap after updated operator invalid,
      RuntimeEnvironmentHasTypes commit.finalWorld
        (writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit commit.replacement commit.value coreEnvironment)
        (writtenContext prepared (SourceCoreCalls.packArguments codes).type actualContext) ambient.definitions := by
  have closed := virtual_closed layout ordinary
  have setterTyped := setter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  have snapshotRep := resolution.snapshotRelated
  have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) resolution.mapping resolution.world
      sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
    simpa only [renamedCodes_types] using resolution.keysRelated
  have reference := resolution.reference
  have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
  cases written with
  | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
    have cellEq := sourceRead.functional resolution.currentRead
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ resolution.currentType
    obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
    rw [resolution.selectedEq] at applies
    obtain ⟨replacement', replacementValue, replacementRep, applies', modifiedEvaluated, _⟩ :=
      CompatiblePlaceNumericBitNotModifier.success profile snapshotRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit coreEnvironment)
        (.var (index := 1) rfl) operator resolution.store invalid
    have same := CompatiblePlaceBitNotModifier.functional applies' applies
    subst replacement'
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions resolution.mapping resolution.world prepared selectedHeap resolution.store target.location resolution.target
          cell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root resolution.heaps reference sourceRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root resolution.heaps reference sourceRead
          (layout.virtual key value cellType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have typedEnvironment : RuntimeEnvironmentHasTypes resolution.world
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit replacementValue coreEnvironment)
        (prepared.route.leafType :: .unit :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons .unit (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken resolution.worlds)))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions resolution.mapping resolution.world source site resolution.values
        currentPath target.projections := by simpa only [cellType] using arguments
    obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
      helperRead, coreWritten, finalHeaps, extension, frame, metadata⟩ :=
      CompatiblePlaceWriteback.preserves root resolution.heaps currentArguments replacementRep changed sourceWrite layout.nonempty
        faithful observations (layout.keyTypes ▸ keyRep.length.2) typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
    refine ⟨⟨replacementValue, updatedValue, helperStore, finalStore, finalWorld,
      by simpa only [cellType] using updatedRep, finalHeaps, extension, frame, metadata,
      modifiedEvaluated, ?_, ⟨_, helperRead⟩, coreWritten⟩, ?_⟩
    · simpa only [packed_renamed_type] using setterEvaluated
    · exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension))

/-- Protected callers carry the actual post-write witness. -/
theorem of_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before selectedHeap after : Dynamic.Heap} {store : Store} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before selectedHeap)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : protocol.State ⟨scope, resolution.mapping, resolution.world, selectedHeap, resolution.store, canonical⟩)
    (related : protocol.Relates initial selected)
    (written : Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value) selectedHeap target updated after)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ commit : CompatiblePlaceBitNotCommit.Execution compilation.checked registry functions prepared (renamedCodes codes ξ)
        coreEnvironment resolution.store resolution.mapping resolution.world resolution.target resolution.values
        resolution.snapshot selectedHeap after updated operator invalid,
      RuntimeEnvironmentHasTypes commit.finalWorld
        (writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit commit.replacement commit.value coreEnvironment)
        (writtenContext prepared (SourceCoreCalls.packArguments codes).type actualContext) ambient.definitions ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, resolution.mapping, commit.finalWorld, after, commit.finalStore, canonical⟩ := by
  obtain ⟨commit, typed⟩ := typed_of_write layout ordinary registryExtension faithful observations profile
    environments agrees actualTyped resolution written operator invalid
  exact ⟨commit, typed, transport.extend selected (.refl _) commit.worlds commit.frame commit.metadata,
    protocol.trans related (transport.related selected (.refl _) commit.worlds commit.frame commit.metadata)⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotCommit
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotTail
/-! The generated Unit slot does not evaluate Source code. The exact unary
commit recovers a strictly smaller, seven-slot native continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr}
  {environment : Environment} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {target : Location} {keys : List Value} {snapshot : Value} {before after : Dynamic.Heap}
  {updated : Dynamic.Value} {operator : Option BinaryOp} {invalid : Word}

private theorem unit_rhs (environment : Environment) (store : Store) :
    Evaluates environment store (shift 3 (LanguageResult.success .unit)) (.inRight .word .unit) store := by
  simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] using
    (Evaluates.inRight (leftType := .word) (environment := environment) (initialStore := store) Evaluates.unit)

theorem Execution.reflects_size (execution : Execution checked registry functions prepared codes environment store mapping world
    target keys snapshot before after updated operator invalid)
    {next : Expr} {outputType : Ty} {result : Value} {finalStore : Store} {size : Nat}
    (completed : CoreProof.EvaluationSize size (snapshotEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) environment)
      store (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type
        (LanguageResult.success .unit) next outputType operator true invalid) result finalStore) :
    ∃ remainingSize, remainingSize < size ∧ CoreProof.EvaluationSize remainingSize (writtenEnvironment prepared.route.rootType target (packValues keys)
      (.inRight .unit snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) result finalStore := by
  cases completed with
  | caseLeft rhsEvaluated failed =>
    have impossible := (evaluation_deterministic rhsEvaluated.sound (unit_rhs _ _)).1
    cases impossible
  | caseRight rhsEvaluated remaining =>
    obtain ⟨same, stores⟩ := evaluation_deterministic rhsEvaluated.sound (unit_rhs _ _)
    cases same
    subst_vars
    cases remaining with
    | caseLeft modifiedEvaluated failed =>
      have impossible := (evaluation_deterministic modifiedEvaluated.sound execution.modified).1
      cases impossible
    | caseRight modifiedEvaluated remaining =>
      obtain ⟨same, stores⟩ := evaluation_deterministic modifiedEvaluated.sound execution.modified
      cases same
      subst_vars
      cases remaining with
      | caseLeft setterEvaluated failed =>
        have impossible := (evaluation_deterministic setterEvaluated.sound execution.setter).1
        cases impossible
      | caseRight setterEvaluated remaining =>
        obtain ⟨same, stores⟩ := evaluation_deterministic setterEvaluated.sound execution.setter
        cases same
        subst_vars
        cases remaining with
        | letE written continuation =>
          obtain ⟨optional, read⟩ := execution.read
          have actual : Evaluates
              (execution.value :: modifiedEnvironment prepared.route.rootType target (packValues keys)
                (.inRight .unit snapshot) .unit execution.replacement environment) execution.helperStore
              (.storeCell (.var 5) (.inRight .unit (.var 0))) .unit execution.finalStore :=
            .storeCell (.var rfl) read (.inRight (.var rfl)) execution.written
          obtain ⟨same, stores⟩ := evaluation_deterministic written.sound actual
          subst_vars
          exact ⟨_, by omega, continuation⟩

/-- Prefix composition uses only the actual key, getter and unary executions. -/
theorem Execution.prefix_agreement
    {sourceTypes : List TypeSystem.Ty} {place : PlaceResolution} {leaf : TypeSystem.Ty}
    {before selectedHeap : Dynamic.Heap} {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
    {sourceTarget : Dynamic.ResolvedPlace}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf sourceTarget
      environment initialStore initialMap initialWorld before selectedHeap)
    (execution : Execution checked registry functions prepared codes environment resolution.store resolution.mapping resolution.world
      resolution.target resolution.values resolution.snapshot selectedHeap after updated operator invalid)
    {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    (next : Expr) (output : Ty) :
    ContinuationAgreement environment initialStore
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) (LanguageResult.success .unit) next output operator true invalid)
      (writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) := by
  obtain ⟨optional, read⟩ := execution.read
  exact (ContinuationAgreement.letE (.var lookup)).trans
    ((ContinuationAgreement.bind resolution.keysEvaluated).trans
      ((ContinuationAgreement.bind resolution.snapshotEvaluated).trans
        ((ContinuationAgreement.bind (unit_rhs _ _)).trans
          ((ContinuationAgreement.bind execution.modified).trans
            ((ContinuationAgreement.bind execution.setter).trans
              (ContinuationAgreement.letE (.storeCell (.var rfl) read (.inRight (.var rfl)) execution.written)))))))

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotFaults
/-! Pure failure phases consume the actual completed key execution.
The live root, fault token, reached diagnostic receipt, and caller transition
remain tied to that execution; no child-meaning callback is introduced. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotFaults
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution
universe u v

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrativeContext actualContext : Core.Context} {ξ : Renaming}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
  {before after : Dynamic.Heap} {store : Store} {index : Nat}
  {location : Dynamic.Location} {initialCell currentCell : Dynamic.Cell}
  {resolved : List Dynamic.EvaluatedProjection}

theorem preserves_projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (keys : CompatiblePlaceTargetKeys.Execution compilation.checked registry functions prepared place
      (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index))
    (keyPost : ProtectedStateTransition.Transition protocol initialState
      ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (LanguageResult.success .unit) next outputType
          (binaryOperator (prepared.route.leafType = .integer) .equal) true invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedPlaceReachedDiagnostics.MissingPost compilation.checked registry functions protocol source site place prepared leaf initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ reason token := by
  have getterTyped := getter_typed layout (virtual_closed layout ordinary) (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨keyState, keyStateRelated⟩ := keyPost
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have present : ∃ sourceRoot, initial = some sourceRoot := by
    cases initial with
    | some value => exact ⟨value, rfl⟩
    | none => cases fault
  obtain ⟨sourceRoot, rfl⟩ := present
  have rootExists : ∃ optional rootValue,
      RootRead compilation.checked registry functions keys.keyMap keys.keyWorld prepared after keys.keyStore location keys.target
        currentCell optional sourceRoot rootValue := by
    cases initialValue with
    | initialized =>
      obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keys.heaps keys.reference currentRead
      exact ⟨_, value, root⟩
    | emptyMapping key value =>
      obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keys.heaps keys.reference currentRead
        (layout.virtual key value cellType.symm) registryExtension
      exact ⟨_, native, root⟩
  obtain ⟨optional, rootValue, root⟩ := rootExists
  have keyRelated : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keys.keyMap keys.keyWorld sourceTypes (codes.map (·.type)) keys.sources keys.values := by
    simpa only [renamedCodes_types] using keys.related
  have arguments := layout.views.arguments keys.shaped keyRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have currentPath : PreparedPath compilation.checked source site currentCell.type place.projections
      0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
  have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values
      currentPath resolved := by simpa only [cellType] using arguments
  obtain ⟨token, count, receipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
  have keyLength : prepared.keyTypes.length = keys.values.length := layout.keyTypes ▸ keyRelated.length.2
  obtain ⟨finalStore, administrative, _, _, evaluated, appended, _⟩ :=
    faultTree_at root tree layout.nonempty faithful observations keyLength
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
  have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext) ambient.definitions :=
    .cons (CompatiblePlaceResolution.values_typed keyRelated)
      (.cons (.cellRef keys.reference.typed) (actualTyped.weaken keys.worlds))
  obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
    evaluation_frame (mapping := keys.keyMap) keys.heaps.runtime_hasTypes typedEnvironment getterTyped evaluated appended
  let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  refine ⟨token, count, sourceRoot, finalStore, keys.keyMap, finalWorld,
    .target (.projectionRead lookup initialRead trace currentRead initialValue fault), initialValue, receipt, ?_,
    CompatibleHeap.HeapRepresents.after_snapshot keys.heaps extension typedStore appended,
    keys.maps, keys.worlds.trans extension, keys.frame.trans frame, keys.metadata,
    reached, protocol.trans keyStateRelated phaseRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, location, keys.target,
      currentCell, optional, sourceRoot, rootValue, keys.values, resolved, count, currentPath,
      keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame, root, cellType, currentArguments, fault, receipt, tree⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

theorem preserves_uninitialized
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (keys : CompatiblePlaceTargetKeys.Execution compilation.checked registry functions prepared place
      (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index))
    (keyPost : ProtectedStateTransition.Transition protocol initialState
      ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (LanguageResult.success .unit) next outputType
          (binaryOperator (prepared.route.leafType = .integer) .equal) true invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedPlaceReachedDiagnostics.UninitializedPost compilation.checked registry functions protocol environment place prepared initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ location := by
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have noVirtual : prepared.route.rootMapping = none := ordinary (fun key value same => notMapping ⟨key, value, cellType.trans same⟩)
  obtain ⟨optional, native, represented⟩ := CompatibleHeap.HeapRepresents.read_at keys.heaps keys.reference currentRead
  have absent : optional = .inLeft prepared.route.rootType .unit := by
    cases represented with
    | uninitialized => rfl
    | initialized => cases empty
  rw [absent] at native
  have evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      keys.keyStore (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) keys.keyStore := by
    apply Evaluates.apply .lambda (.pair (.loadCell (.var rfl) native) (.var rfl))
    cases steps : prepared.steps with
    | nil => exact (layout.nonempty steps).elim
    | cons head tail =>
      simp only [normalizeRoot, noVirtual, LanguageResult.failure]
      exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  obtain ⟨keyState, keyRelated⟩ := keyPost
  refine ⟨keys.keyStore, keys.keyMap, keys.keyWorld,
    .target (.uninitialized lookup initialRead trace currentRead empty notMapping hasProjection), ?_,
    keys.heaps, keys.maps, keys.worlds, keys.frame, keys.metadata,
    keyState, keyRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, keys.target, currentCell,
      .inLeft prepared.route.rootType .unit, keys.sources, resolved, keyRelated, protocol.refl keyState, rfl, rfl, rfl,
      .refl _, .refl _ _, lookup, currentRead, keys.reference, native, absent ▸ represented, cellType, empty, notMapping, layout.nonempty, keys.shaped, hasProjection⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotFaults
end
