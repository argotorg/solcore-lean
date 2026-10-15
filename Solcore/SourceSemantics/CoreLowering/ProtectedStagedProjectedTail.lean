import Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedResolution

/-! Native writeback reflection keeps the already established staged keys and
RHS outside its pure suffix. Its result is the real latest-root write or the
structural fault at that RHS heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedTail
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceTailReflection CompatibleRenamedPlace
universe u v

inductive ResultAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (faults : FaultRep)
    (prepared : Prepared) (keyType : Ty) (actualContext : Core.Context)
    (operator : Syntax.ValueAssignOp) (target : Dynamic.ResolvedPlace) (right : Dynamic.Value) (rhsHeap : Dynamic.Heap)
    (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.ProjectedTarget.WriteFault operator target right rhsHeap reason)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld rhsHeap finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before rhsHeap)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, rhsHeap, finalStore, canonical⟩) :
      ResultAt protocol size checked registry functions faults prepared keyType actualContext operator target right rhsHeap coreEnvironment
        before store mapping world scope canonical initialState next outputType result finalStore
  | committed {remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement) rhsHeap target updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleRenamedPlaceSuccess.writtenContext prepared keyType actualContext) ambient.definitions)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      ResultAt protocol size checked registry functions faults prepared keyType actualContext operator target right rhsHeap coreEnvironment
        before store mapping world scope canonical initialState next outputType result finalStore
private theorem resolved_type {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before targetHeap : Dynamic.Heap} {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
    {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads targetHeap target.location cell) : target.rootType = cell.type := by
  cases trace with
  | intro _ _ _ currentRead _ _ => exact congrArg Dynamic.Cell.type (currentRead.functional read)

private theorem absent_initial {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions} {mapping : LocationMap} {world : StoreTyping}
    {cell : Dynamic.Cell} {optional : Value} {type : Ty}
    (related : GenericHeap.CellRepresents model mapping world cell optional type)
    (empty : cell.value = none) (notMapping : ¬ ∃ k v, cell.type = .mapping k v) :
    Dynamic.RootInitialValue cell none := by
  cases related with
  | initialized => cases empty
  | uninitialized => exact .uninitialized notMapping

theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    {target : Dynamic.ResolvedPlace}
    {sourceSize rhsSize size : Nat}
    (sourceTrace : SourceExecutionSize.SourcePlaceResolves program sourceSize context evidence source environment before place target targetHeap)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before targetHeap)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (right : CompatiblePlaceRhsReflection.Execution compilation.checked registry functions program context evidence source faults environment
      prepared (renamedCodes codes ξ) sourceTypes place leaf target coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
    (rhsTrace : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right.right right.heap)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (rhsState : protocol.State ⟨scope, right.mapping, right.world, right.heap, right.store, canonical⟩)
    (rhsRelated : protocol.Relates initialState rhsState)
    (missingFor : ProtectedPlaceReachedDiagnostics.MissingFor compilation.checked registry functions protocol
      source site place prepared leaf initialState faults)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : CoreProof.EvaluationSize size (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
      (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
      (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
    ResultAt protocol size compilation.checked registry functions faults
      prepared (SourceCoreCalls.packArguments codes).type actualContext operator target right.right right.heap coreEnvironment
      before store mapping world scope canonical initialState next outputType result finalStore := by
  have closed := virtual_closed layout ordinary
  have setterTyped := setter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  have snapshotRep := right.meaning.saved_snapshot
  have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) right.mapping right.world sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
    simpa only [renamedCodes_types] using resolution.keysRelated.extend right.meaning.maps right.meaning.worlds
  have reference := resolution.reference.extend right.meaning.maps right.meaning.worlds
  have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have targetType := (resolved_type sourceTrace.sound resolution.currentRead).trans resolution.currentType
  obtain ⟨latest⟩ := right.meaning.latest
  have cellType : latest.cell.type = target.rootType := latest.type.trans targetType.symm
  obtain ⟨replacement, replacementValue, replacementRep, applied, modified, _⟩ :=
    CompatiblePlaceModifier.initialized_success observations profile snapshotRep right.related
      (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) right.value coreEnvironment)
      (.var (index := 1) rfl) (.var (index := 0) rfl) right.store invalid
  cases completed with
  | caseLeft modifiedEvaluated failed =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic modifiedEvaluated.sound modified
    cases impossible
  | caseRight modifiedEvaluated remaining =>
    obtain ⟨same, storeEq⟩ := evaluation_deterministic modifiedEvaluated.sound modified
    cases same
    subst_vars
    have typedEnvironment : RuntimeEnvironmentHasTypes right.world
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) right.value replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons right.related.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken (resolution.worlds.trans right.meaning.worlds))))))
    have currentPath : PreparedPath compilation.checked source site latest.cell.type place.projections 0 prepared.steps prepared.keys leaf :=
      latest.type ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions right.mapping right.world source site resolution.values
        currentPath target.projections := by simpa only [latest.type] using arguments
    have reflectSetter := fun {actual : Value} {after : Store}
        (ran : Evaluates (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) right.value replacementValue coreEnvironment) right.store
          (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) actual after) =>
      CompatiblePlaceSetterReflection.reflects currentArguments replacementRep
        (fun k v same => layout.virtual k v (latest.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (latest.type.trans same))) registryExtension layout.nonempty
        functionTypes faithful observations (layout.keyTypes ▸ keyRep.length.2) right.meaning.heaps reference latest.read
        typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl) ran
    cases remaining with
    | caseLeft setterEvaluated failed =>
      obtain ⟨futureWorld, _, represented, finalHeaps, extension, frame, _⟩ := reflectSetter setterEvaluated.sound
      cases represented with
      | @missing sourceRoot reason token count root fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            obtain ⟨optional, rootValue, live⟩ := ProtectedPlaceReachedDiagnostics.root_of_initial
              right.meaning.heaps reference latest.read root
              (fun k v same => layout.virtual k v (latest.type.symm.trans same)) registryExtension
            obtain ⟨otherToken, otherCount, otherReceipt, tree⟩ := currentArguments.faultTree live.payload fault prepared
            obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
            let reached := transport.extend rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl right.heap)
            have phaseRelated := transport.related rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl right.heap)
            have witness : ProtectedPlaceReachedDiagnostics.MissingWitness compilation.checked registry functions protocol
                source site place prepared leaf initialState reached reason token :=
              ⟨⟨scope, right.mapping, right.world, right.heap, right.store, canonical⟩, rhsState,
                target.location, resolution.target, latest.cell, optional, sourceRoot, rootValue,
                resolution.values, target.projections, count, currentPath, rhsRelated, phaseRelated,
                rfl, rfl, rfl, extension, frame, live, latest.type, currentArguments, fault, receipt, tree⟩
            exact .fault (.structural latest.read cellType root fault) rfl
              (missingFor reached (protocol.trans rhsRelated phaseRelated) witness)
              finalHeaps (resolution.maps.trans right.meaning.maps) ((resolution.worlds.trans right.meaning.worlds).trans extension)
              ((resolution.frame.trans right.meaning.frame).trans frame) (resolution.metadata.trans right.meaning.metadata)
              ⟨reached, protocol.trans rhsRelated phaseRelated⟩
      | uninitialized empty notMapping nonempty =>
        have absent := absent_initial latest.related empty notMapping
        exact (DataPlaceSourceOrder.latest_uninitialized_impossible sourceTrace.sound rhsTrace.sound latest.read cellType absent nonempty).elim
    | caseRight setterEvaluated remaining =>
      rename_i helperStore helperType updatedValue
      obtain ⟨futureWorld, _, represented, helperHeaps, extension, helperFrame, _⟩ := reflectSetter setterEvaluated.sound
      cases represented with
      | updated root changed updatedRep =>
        cases remaining with
        | letE writeEvaluated continuation =>
          obtain ⟨after, resultEq, sourceWritten, finalHeaps, writeFrame, metadata, _⟩ :=
            CompatiblePlaceCommitReflection.reflects_storeCell helperHeaps (reference.extend (.refl _) extension) latest.read
              updatedRep (.var (index := 5) rfl) (.var (index := 0) rfl) writeEvaluated.sound
          subst_vars
          have changed := DataPlaceCommitReflection.update_of_replacement changed (fun _ => resolution.selectedEq.symm ▸ applied)
          let helperState := transport.extend rhsState (.refl _) extension helperFrame (Dynamic.HeapMetadataExtend.refl right.heap)
          exact .committed (.intro latest.read cellType root changed sourceWritten)
            finalHeaps (resolution.maps.trans right.meaning.maps) ((resolution.worlds.trans right.meaning.worlds).trans extension)
            (((resolution.frame.trans right.meaning.frame).trans helperFrame).trans writeFrame)
            ((resolution.metadata.trans right.meaning.metadata).trans metadata) (slots :=
              [.unit, updatedValue, replacementValue, right.value, .inRight .unit resolution.snapshot, packValues resolution.values,
                .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) rfl
              (by
                change RuntimeEnvironmentHasTypes futureWorld
                  (.unit :: updatedValue :: _) _ _
                exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension)))
              ⟨transport.extend helperState (.refl _) (.refl _) writeFrame metadata,
                protocol.trans (protocol.trans rhsRelated
                  (transport.related rhsState (.refl _) extension helperFrame (Dynamic.HeapMetadataExtend.refl right.heap)))
                  (transport.related helperState (.refl _) (.refl _) writeFrame metadata)⟩
              (by omega) continuation

end Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedTail
