import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceResolution
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceFaults


/-! Typed child meanings for the actual CompatiblePlaceTargetKeys phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentTargetKeys
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceTargetKeys CompatibleRenamedPlace

/-- Successful key expressions supply the current root after all their effects.
Exact declared source type comes from WritableLocal and environment agreement. -/
theorem preserves_bounded (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel checked registry functions) program context evidence source certificate faults entry))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget) :
    Nonempty (Execution checked registry functions prepared place (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index)) := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, evaluated, related, keyHeaps, maps, worlds, frame, metadata⟩ :=
    ProtectedPlaceKeys.preserves_bounded budget transport children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped) installed trace bounded
  obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  have locationEq := lookup.functional staticLookupRuntime
  subst staticLocation
  have cellEq := initialRead.functional staticRead
  subst staticCell
  obtain ⟨currentCell, currentRead, currentType, _⟩ := metadata _ _ initialRead
  exact ⟨⟨target, sources, values, keyStore, keyMap, keyWorld, currentCell, currentRead,
    currentType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected, shaped,
    by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
      packed_renamed_expression, List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated,
    by simpa only [renamedCodes_types] using related, keyHeaps, maps, worlds, frame, metadata⟩⟩

theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after) :
    Nonempty (Execution checked registry functions prepared place (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index)) := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsEvaluate.has_size trace
  exact preserves_bounded size
    children transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead sized (Nat.le_refl size)


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentTargetKeys


/-! Typed successful assignment prefixes expose their seven real temporary
values. Getter/setter typing and represented payloads type those slots in the
post-write world; no arbitrary slot list is assumed to be safe for captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentSuccess
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceAssignmentSuccess

def writtenContext (prepared : Prepared) (keyType : Ty) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.leafType :: prepared.route.leafType ::
    prepared.optionalLeaf :: keyType :: OptionalCell.referenceType prepared.route.rootType :: context

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

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

/- An independent successful transaction constructs every native phase.
Raw metadata and duplicate entries are retained by the full payload relation;
the native store additionally contains tracked administrative helper cells. -/
namespace Stateful
universe u v

theorem preserves_prefix_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after) (bounded : size ≤ budget)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        (∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ))) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have getterTyped := getter_typed layout closed respects
  have setterTyped := setter_typed layout closed respects
  cases trace with
  | @intro _ _ _ _ _ _ _ _ targetHeap rhsHeap _ _ sourceTarget _ right _ resolve evaluate written =>
    obtain ⟨resolution, coreLookup, resolutionPost⟩ := ProtectedPlaceResolution.Stateful.preserves_bounded budget layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped protocol transport meaning faithful observations
      environments heaps locals agrees actualTyped initialState slot rootTyped resolve (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
    obtain ⟨resolutionState, resolutionRelated⟩ := resolutionPost
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
      ProtectedPlaceRhs.Stateful.preserves_at resolution _ protocol (meaning _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)) rhsGenerated found environments agrees actualTyped locals resolutionState (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
      obtain ⟨rhsState, rhsRelated⟩ := rhsPost
      have snapshotRep := rhsResult.saved_snapshot
      have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) rhsMap rhsWorld sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
        simpa only [renamedCodes_types] using resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
      have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
      have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
      obtain ⟨latest⟩ := rhsResult.latest
      cases written with
      | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
        have cellEq := sourceRead.functional latest.read
        have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
        obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
        rw [resolution.selectedEq] at applies
        obtain ⟨replacementValue, replacementRep, modifiedEvaluated, _⟩ :=
          CompatiblePlaceModifier.preserves observations operatorProfile snapshotRep rightRep applies
            (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
        have present : ∃ sourceRoot, initial = some sourceRoot := by
          cases initial with
          | some value => exact ⟨value, rfl⟩
          | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
        obtain ⟨sourceRoot, rfl⟩ := present
        have rootExists : ∃ optional rootValue,
            RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
              cell optional sourceRoot rootValue := by
          cases initialValue with
          | initialized =>
            obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
            exact ⟨_, value, root⟩
          | emptyMapping key value =>
            obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
              (layout.virtual key value cellType.symm) registryExtension
            exact ⟨_, native, root⟩
        obtain ⟨optional, rootValue, root⟩ := rootExists
        have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
        have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
            (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
            (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
              OptionalCell.referenceType prepared.route.rootType :: actualContext)
            ambient.definitions :=
          .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
            (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
              (actualTyped.weaken (resolution.worlds.trans rhsResult.worlds))))))
        have currentPath : PreparedPath compilation.checked source site cell.type place.projections
            0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
        have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
            currentPath sourceTarget.projections := by simpa only [cellType] using arguments
        obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
          helperRead, coreWritten, finalHeaps, extension, frame, metadata⟩ :=
          CompatiblePlaceWriteback.preserves root rhsResult.heaps currentArguments replacementRep changed sourceWrite layout.nonempty
            faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
        refine ⟨updatedValue, finalStore, rhsMap, finalWorld,
          by simpa only [cellType] using updatedRep, finalHeaps, resolution.maps.trans rhsResult.maps,
          (resolution.worlds.trans rhsResult.worlds).trans extension, (resolution.frame.trans rhsResult.frame).trans frame,
          (resolution.metadata.trans rhsResult.metadata).trans metadata,
          [.unit, updatedValue, replacementValue, rightValue, .inRight .unit resolution.snapshot,
            packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target], rfl, ?_, ?_,
          transport.extend rhsState (.refl _) extension frame metadata,
          protocol.trans (protocol.trans resolutionRelated rhsRelated)
            (transport.related rhsState (.refl _) extension frame metadata)⟩
        · exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension))
        · intro next outputType
          rw [execute_rename layout.path closed]
          simp only [renamed_packed, Expr.rename]
          unfold execute
          simp only [packed_renamed_type]
          have snapshotEvaluated := resolution.snapshotEvaluated
          simp only [packed_renamed_type] at snapshotEvaluated
          exact (ContinuationAgreement.letE (.var coreLookup)).trans
            ((ContinuationAgreement.bind resolution.keysEvaluated).trans
              ((ContinuationAgreement.bind snapshotEvaluated).trans
                ((ContinuationAgreement.bind rhsResult.evaluated).trans
                  ((ContinuationAgreement.bind modifiedEvaluated).trans
                    ((ContinuationAgreement.bind setterEvaluated).trans
                      (ContinuationAgreement.letE (.storeCell (.var rfl) helperRead (.inRight (.var rfl)) coreWritten)))))))

end Stateful

theorem preserves_prefix_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after) (bounded : size ≤ budget)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        ∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨updatedValue, finalStore, finalMap, finalWorld, related, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation, _⟩ := Stateful.preserves_prefix_bounded budget layout ordinary registryExtension
    (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport)
    (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller)) faithful observations
    rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped ⟨installed⟩ slot rootTyped trace bounded invalidOperand
  exact ⟨updatedValue, finalStore, finalMap, finalWorld, related, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation⟩

theorem preserves_prefix {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        ∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourcePlaceAssignment.has_size trace
  exact preserves_prefix_bounded size
    layout ordinary registryExtension transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) faithful observations rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped installed slot rootTyped sized (Nat.le_refl size) invalidOperand


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentSuccess



/-! Whole emitted assignments short-circuit on key and RHS faults, retaining
all preceding source effects. The executions of children are obtained from the
protected expression theorem; neither phase accepts a child evaluation as its
static compiler contract. Structural missing-default guards are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentFailures
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

theorem keys_bounded (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel checked registry functions) program context evidence source certificate faults entry))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before place.projections reason after) (bounded : size ≤ budget)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
    ProtectedPlaceKeys.preserves_fault_bounded budget transport children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped) installed trace bounded
  refine ⟨token, finalStore, finalMap, finalWorld, .target (.projectionExpression lookup read trace.sound), ?_,
    tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  apply execute_key_failure prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
    (.cellRef (OptionalCell.cellType prepared.route.rootType) target) (.var (agrees coreLookup))
  simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, packed_renamed_type, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

theorem keys {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before place.projections reason after)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsFault.has_size trace
  exact keys_bounded size
    children transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) environments heaps locals agrees actualTyped installed slot lookup read sized (Nat.le_refl size) operator rhsId rhs next outputType invalid


/-- This composition consumes a semantic resolution result, produced by
ProtectedPlaceResolution.preserves, and the independent RHS fault. It derives
the actual RHS run and suppresses modifier, setter, write and continuation. -/
theorem rhs_at (size : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {sourceTarget : Dynamic.ResolvedPlace} {canonical coreEnvironment : Environment} {ξ : Renaming} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap after : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {index : Nat} (reference : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.ExpressionFaults program size context evidence source environment targetHeap id reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after ∧
      Evaluates coreEnvironment initialStore
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends initialMap finalMap ∧ WorldExtends initialWorld finalWorld ∧
      AdministrativePreserved initialMap initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, store, mapping, world, result⟩ :=
    ProtectedPlaceRhs.preserves_at resolution size transport meaning generated found environments agrees actualTyped locals installed (.fault failed)
  cases represented : result.represented with
  | @fault _ token tokenRep =>
    refine ⟨token, store, mapping, world, .rhs resolved failed.sound, ?_, tokenRep, result.heaps,
      resolution.maps.trans result.maps, resolution.worlds.trans result.worlds,
      resolution.frame.trans result.frame, resolution.metadata.trans result.metadata⟩
    apply SourceCoreCompatibleDataPlaces.execute_rhs_failure prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ))
      (lowered.expression.rename ξ) next outputType (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
      (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) (packValues resolution.values)
      (.inRight .unit resolution.snapshot) (.var reference) resolution.keysEvaluated resolution.snapshotEvaluated
    simpa only [renamed, coreType, snapshotEnvironment, keysEnvironment, referenceEnvironment] using result.evaluated

theorem rhs {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {sourceTarget : Dynamic.ResolvedPlace} {canonical coreEnvironment : Environment} {ξ : Renaming} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap after : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {index : Nat} (reference : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment targetHeap id reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after ∧
      Evaluates coreEnvironment initialStore
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends initialMap finalMap ∧ WorldExtends initialWorld finalWorld ∧
      AdministrativePreserved initialMap initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionFaults.has_size failed
  exact rhs_at size
    resolution transport (RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning size) generated found coreType environments agrees actualTyped installed locals resolved reference sized operator next outputType invalid


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentFailures


/-! Target-resolution faults before the RHS. The actual key runs are derived
from the protected expression theorem. The getter uses the live root after
those effects, preserving exact raw missing-default tokens and administrative
allocations. An absent ordinary root fails without allocating a helper. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentTargetFaults
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

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

/-- Independent structural failure determines the actual whole emitted
assignment's failure before its RHS, modifier, setter or continuation starts. -/
theorem projection_bounded (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have getterTyped := getter_typed layout (virtual_closed layout ordinary) (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨keys⟩ := ProtectedPlaceAssignmentTargetKeys.preserves_bounded budget layout.children transport meaning environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead trace bounded
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
  refine ⟨token, count, sourceRoot, finalStore, keys.keyMap, finalWorld,
    .target (.projectionRead lookup initialRead trace.sound currentRead initialValue fault), initialValue, receipt, ?_,
    CompatibleHeap.HeapRepresents.after_snapshot keys.heaps extension typedStore appended,
    keys.maps, keys.worlds.trans extension, keys.frame.trans frame, keys.metadata⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

theorem projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
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
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsEvaluate.has_size trace
  exact projection_bounded size
    layout ordinary transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead sized (Nat.le_refl size) currentRead registryExtension faithful observations initialValue fault operator rhsId rhs next outputType invalidOperand


/-- Actual describe supplies `ordinary`. It is a static route fact, not a
claim that native type equality recovers the source declaration. -/
theorem uninitialized_bounded (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨keys⟩ := ProtectedPlaceAssignmentTargetKeys.preserves_bounded budget layout.children transport meaning environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead trace bounded
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
  refine ⟨keys.keyStore, keys.keyMap, keys.keyWorld,
    .target (.uninitialized lookup initialRead trace.sound currentRead empty notMapping hasProjection), ?_,
    keys.heaps, keys.maps, keys.worlds, keys.frame, keys.metadata⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

theorem uninitialized
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsEvaluate.has_size trace
  exact uninitialized_bounded size
    layout transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead sized (Nat.le_refl size) currentRead ordinary empty notMapping hasProjection operator rhsId rhs next outputType invalidOperand


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentTargetFaults


/-! Structural missing-default failure after the RHS. The source specification
traverses the latest root before applying the modifier. For authenticated equal
or scalar numeric operands, the generated earlier modifier is total; therefore
the same structural fault wins and neither source nor native final write runs.
Exact raw key guards come from the source fault, not native projection equality.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentStructuralFault
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

/-- All key/RHS native evaluations come from their protected child theorem. The fault
receipt retains the raw mapping header and ordered selection where traversal
stopped; no decoder or source evaluator supplies the semantic result. -/
theorem preserves_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {resolveSize rhsSize : Nat}
    (resolve : SourceExecutionSize.SourcePlaceResolves program resolveSize context evidence source environment before place sourceTarget targetHeap)
    (evaluate : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right rhsHeap)
    (resolveBound : resolveSize ≤ budget) (rhsBound : rhsSize < budget)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have getterTyped := getter_typed layout closed respects
  have setterTyped := setter_typed layout closed respects
  have sourceFault := Dynamic.SourcePlaceAssignmentFaults.structuralUpdate (operator := operator) resolve.sound evaluate.sound sourceRead rootType initialValue fault
  obtain ⟨resolution, coreLookup⟩ := ProtectedPlaceResolution.preserves_bounded budget layout.path layout.views layout.children layout.keyTypes
    layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped transport meaning faithful observations
    environments heaps locals agrees actualTyped installed slot rootTyped resolve resolveBound
  obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
    ProtectedPlaceRhs.preserves_at resolution _ transport (meaning _ rhsBound) rhsGenerated found environments agrees actualTyped locals installed (.value evaluate)
  cases represented : rhsResult.represented with
  | @value _ rightValue rightRep =>
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
      .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
    have snapshotRep := rhsResult.saved_snapshot
    have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) rhsMap rhsWorld sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
      simpa only [renamedCodes_types] using resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
    have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
    have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
    obtain ⟨latest⟩ := rhsResult.latest
    have cellEq := sourceRead.functional latest.read
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
    obtain ⟨replacement, replacementValue, replacementRep, _, modifiedEvaluated, valid⟩ :=
      CompatiblePlaceModifier.initialized_success observations operatorProfile snapshotRep rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases fault
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
          cell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
          (layout.virtual key value cellType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken (resolution.worlds.trans rhsResult.worlds))))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
        currentPath sourceTarget.projections := by simpa only [cellType] using arguments
    obtain ⟨token, count, finalStore, administrative, finalWorld, receipt, setterEvaluated,
      finalHeaps, extension, frame, _, _, _⟩ :=
      CompatiblePlaceSetterFault.preserves root rhsResult.heaps currentArguments fault layout.nonempty
        faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
    refine ⟨token, count, sourceRoot, finalStore, rhsMap, finalWorld, sourceFault, initialValue, receipt, ?_, finalHeaps,
      resolution.maps.trans rhsResult.maps, (resolution.worlds.trans rhsResult.worlds).trans extension,
      (resolution.frame.trans rhsResult.frame).trans frame, resolution.metadata.trans rhsResult.metadata⟩
    unfold execute
    simp only [packed_renamed_type]
    have snapshotEvaluated := resolution.snapshotEvaluated
    simp only [packed_renamed_type] at snapshotEvaluated
    exact .letE (.var coreLookup)
      (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ snapshotEvaluated
          (LanguageResult.bind_success _ rhsResult.evaluated
            (LanguageResult.bind_success _ modifiedEvaluated
              (LanguageResult.bind_failure _ setterEvaluated)))))

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap := by
  obtain ⟨resolveSize, resolveSized⟩ := SourceExecutionSize.SourcePlaceResolves.has_size resolve
  obtain ⟨rhsSize, rhsSized⟩ := SourceExecutionSize.ExpressionEvaluates.has_size evaluate
  exact preserves_bounded (resolveSize + rhsSize + 1)
    layout ordinary registryExtension transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning (resolveSize + rhsSize + 1)) faithful observations rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped installed slot rootTyped resolveSized rhsSized (by omega) (by omega) sourceRead rootType initialValue fault next outputType invalidOperand


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentStructuralFault


/-! Every independently specified assignment fault in the nonempty equal or
numeric profile is preserved. Unbound/dangling roots contradict actual lexical
and heap agreement. Invalid operands contradict the represented snapshot and
RHS values; neither exclusion is inferred from native type equality alone. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentFaults
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

theorem preserves_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  simp only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename]
  have getterTyped := getter_typed layout (virtual_closed layout ordinary) (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨sourceLocation, sourceCell, sourceLookup, sourceRead, _, _⟩ := locals.lookup staticLookup
  cases trace with
  | target fault =>
    cases fault with
    | unbound missing => exact (missing.excludes_lookup sourceLookup).elim
    | dangling lookup missing =>
      have same := lookup.functional sourceLookup
      cases same
      exact (missing.excludes_read sourceRead).elim
    | projectionExpression lookup read fault =>
      obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
        ProtectedPlaceAssignmentFailures.keys_bounded budget layout.children transport meaning environments heaps locals agrees actualTyped installed slot lookup read fault (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          operator rhs (lowered.expression.rename ξ) (next.rename ξ) outputType invalid
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
    | danglingAfterProjections lookup read evaluated missing =>
      obtain ⟨keys⟩ := ProtectedPlaceAssignmentTargetKeys.preserves_bounded budget layout.children transport meaning environments heaps locals agrees actualTyped installed slot rootTyped lookup read evaluated (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
      exact (missing.excludes_read keys.read).elim
    | projectionRead lookup initialRead evaluate currentRead initialValue fault =>
      obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
        ProtectedPlaceAssignmentTargetFaults.projection_bounded budget layout ordinary transport meaning environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead evaluate (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) currentRead
          registryExtension faithful observations initialValue fault operator rhs (lowered.expression.rename ξ) (next.rename ξ) outputType invalid
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingTokens receipt, finalHeaps, maps, worlds, frame, metadata⟩
    | uninitialized lookup initialRead evaluate currentRead empty notMapping projected =>
      obtain ⟨finalStore, finalMap, finalWorld, _, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
        ProtectedPlaceAssignmentTargetFaults.uninitialized_bounded budget layout transport meaning environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead evaluate (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) currentRead
          ordinary empty notMapping projected operator rhs (lowered.expression.rename ξ) (next.rename ξ) outputType invalid
      exact ⟨prepared.invalidProjection, finalStore, finalMap, finalWorld, evaluated, invalidTokens _, finalHeaps, maps, worlds, frame, metadata⟩
  | rhs resolve fault =>
    obtain ⟨resolution, coreLookup⟩ := ProtectedPlaceResolution.preserves_bounded budget layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped transport meaning faithful observations
      environments heaps locals agrees actualTyped installed slot rootTyped resolve (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
    obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
      ProtectedPlaceAssignmentFailures.rhs_at _ resolution transport (meaning _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)) rhsGenerated found rhsCoreType environments agrees actualTyped installed locals resolve.sound coreLookup fault
        operator (next.rename ξ) outputType invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  | operands resolve evaluate _ _ _ _ invalidOperands =>
    obtain ⟨resolution, coreLookup⟩ := ProtectedPlaceResolution.preserves_bounded budget layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped transport meaning faithful observations
      environments heaps locals agrees actualTyped installed slot rootTyped resolve (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
      ProtectedPlaceRhs.preserves_at resolution _ transport (meaning _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)) rhsGenerated found environments agrees actualTyped locals installed (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf _ rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
      obtain ⟨_, _, _, _, _, valid⟩ := CompatiblePlaceModifier.initialized_success observations operatorProfile
        rhsResult.saved_snapshot rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid
      rw [resolution.selectedEq] at invalidOperands
      exact (valid invalidOperands).elim
  | structuralUpdate resolve evaluate currentRead sameType initialValue fault =>
    obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
      ProtectedPlaceAssignmentStructuralFault.preserves_bounded budget layout ordinary registryExtension transport meaning faithful observations rhsGenerated found rhsView rhsCoreType
        operatorProfile environments heaps locals agrees actualTyped installed slot rootTyped resolve evaluate (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) currentRead sameType initialValue fault (next.rename ξ) outputType invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingTokens receipt, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourcePlaceAssignmentFaults.has_size trace
  exact preserves_bounded size
    layout ordinary registryExtension transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) faithful observations missingTokens invalidTokens rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped installed slot rootTyped sized (Nat.le_refl size) next outputType invalid


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentFaults
