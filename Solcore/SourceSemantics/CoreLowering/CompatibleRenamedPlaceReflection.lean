import Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignmentContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceAssignmentContracts
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTailReflection
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhsReflection
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterReflection
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCommitReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceSourceOrder
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlacePrefixReflection
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceSuccess

/-! Reconstruct the independent latest-root update and mapped write from a
completed compatible assignment tail. Scalar modifiers use the old snapshot;
structural reconstruction uses the post-RHS root. Actual child traces enter
only as the outputs of prefix/RHS reflection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceTail
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution

open CompatiblePlaceTailReflection CompatibleRenamedPlace

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

/- The profile is an explicit source scalar/equal constraint. It makes the
native-first modifier total, so a later structural fault has the same source
priority. Raw default/token metadata remain authenticated throughout. -/
namespace Stateful
universe u v

theorem reflects_ready_sized {compilation : SourceCoreCompatibleDataPlaces.Context}
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
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
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
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : CoreProof.EvaluationSize size (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
      (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
      (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
    ProtectedStatePlaceAssignmentContracts.ResultAt protocol size compilation.checked registry functions program context evidence source faults
      prepared (SourceCoreCalls.packArguments codes).type actualContext place operator rhs environment coreEnvironment
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
      | missing root fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.structuralUpdate sourceTrace rhsTrace latest.read cellType root fault) rfl (missingTokens receipt)
              finalHeaps (resolution.maps.trans right.meaning.maps) ((resolution.worlds.trans right.meaning.worlds).trans extension)
              ((resolution.frame.trans right.meaning.frame).trans frame) (resolution.metadata.trans right.meaning.metadata)
              ⟨transport.extend rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl right.heap),
                protocol.trans rhsRelated (transport.related rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl right.heap))⟩
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
          exact .committed (.intro sourceTrace rhsTrace (.intro latest.read cellType root changed sourceWritten))
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

end Stateful

theorem reflects_ready_sized {compilation : SourceCoreCompatibleDataPlaces.Context}
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
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
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
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : CoreProof.EvaluationSize size (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
      (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
      (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
    RecursiveNamedPlaceAssignmentContracts.ResultAt size compilation.checked registry functions program context evidence source faults
      prepared (SourceCoreCalls.packArguments codes).type actualContext place operator rhs environment coreEnvironment
      before store mapping world next outputType result finalStore := by
  let observer : ProtectedExpressionMeaning.Transport (fun _ _ _ _ _ _ => True) :=
    ⟨fun _ _ _ _ _ => trivial⟩
  exact (Stateful.reflects_ready_sized (ProtectedStatePlaceAssignment.legacyProtocol (fun _ _ _ _ _ _ => True))
    (ProtectedStatePlaceAssignment.legacyTransport observer) layout ordinary registryExtension functionTypes faithful observations missingTokens
    profile environments agrees actualTyped sourceTrace resolution right rhsTrace ⟨trivial⟩ ⟨trivial⟩ trivial completed).forget

theorem reflects_ready {compilation : SourceCoreCompatibleDataPlaces.Context}
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
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    {target : Dynamic.ResolvedPlace}
    (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf target
      coreEnvironment store mapping world before targetHeap)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (right : CompatiblePlaceRhsReflection.Execution compilation.checked registry functions program context evidence source faults environment
      prepared (renamedCodes codes ξ) sourceTypes place leaf target coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : Evaluates (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
      (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
      (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults place operator rhs environment coreEnvironment
      before store mapping world next outputType result finalStore := by
  obtain ⟨sourceSize, sourceSized⟩ := SourceExecutionSize.SourcePlaceResolves.has_size sourceTrace
  have rhsTrace : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right.right right.heap := by
    cases right.meaning.trace with | value trace => exact trace
  obtain ⟨rhsSize, rhsSized⟩ := SourceExecutionSize.ExpressionEvaluates.has_size rhsTrace
  obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size completed
  exact (reflects_ready_sized layout ordinary registryExtension functionTypes faithful observations missingTokens profile
    environments agrees actualTyped sourceSized resolution right rhsSized sized).erase

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceTail


/-! Completed emitted assignment reconstructs independent target/RHS/write
traces using typed children. On success the reconstructed finite prefix also
certifies the actual seven continuation slots, before any next statement runs.
The profile retains a static nonempty path layout, raw key views, diagnostics,
and equal/Word/Integer operator admission. Bare-root writes are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceReflection
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceRhsReflection

/-- Source and Core RHS types are connected by the retained raw runtime view,
not by inverting the many-to-one native type projection. -/
private theorem rhs_reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (coreType : lowered.type = prepared.route.leafType)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {next : Expr} {outputType : Ty} {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value}
    (resolution : CompatiblePlacePrefixReflection.Result checked registry functions program context evidence source faults prepared (renamedCodes codes ξ) sourceTypes
      place leaf environment coreEnvironment before store mapping world (lowered.expression.rename ξ) next outputType
      (binaryOperator (prepared.route.leafType = .integer) operator) false invalid result finalStore) :
    Result checked registry functions program context evidence source faults prepared (renamedCodes codes ξ) sourceTypes place leaf environment
      coreEnvironment before store mapping world id node (renamed lowered ξ) next outputType operator invalid result finalStore := by
  cases resolution with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault (.target sourceFault) resultEq tokenRep heaps maps worlds frame metadata
  | resolved sourceTrace resolution remaining =>
    cases remaining with
    | caseLeft rhsEvaluated failed =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, rhsResult⟩ :=
        CompatibleRenamedPlaceRhs.reflects resolution meaning generated found environments agrees actualTyped locals rhsEvaluated
      cases represented : rhsResult.represented with
      | fault tokenRep =>
        cases rhsResult.trace with
        | fault sourceRhs =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.rhs sourceTrace sourceRhs) rfl tokenRep rhsResult.heaps
                (resolution.maps.trans rhsResult.maps) (resolution.worlds.trans rhsResult.worlds)
                (resolution.frame.trans rhsResult.frame) (resolution.metadata.trans rhsResult.metadata)
    | caseRight rhsEvaluated remaining =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, rhsResult⟩ :=
        CompatibleRenamedPlaceRhs.reflects resolution meaning generated found environments agrees actualTyped locals rhsEvaluated
      cases represented : rhsResult.represented with
      | value payload =>
        exact .ready sourceTrace resolution
          { right := _
            value := _
            heap := rhsHeap
            store := _
            mapping := rhsMap
            world := rhsWorld
            meaning := rhsResult
            related := .compatible rhsView (by simpa only [payloadModel, renamed, coreType] using payload) } remaining

theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
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
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (preservation : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
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
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) result finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after ∧
      result = .inLeft outputType (.word token) ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleRenamedPlaceSuccess.writtenContext prepared (SourceCoreCalls.packArguments codes).type
          actualContext) ambient.definitions ∧
      Evaluates (slots ++ coreEnvironment) written (shift 7 (next.rename ξ)) result finalStore) := by
  have nativeCompleted := completed
  rw [execute_rename layout.path (virtual_closed layout ordinary)] at nativeCompleted
  simp only [renamed_packed, Expr.rename] at nativeCompleted
  have resolution := CompatibleRenamedPlacePrefixReflection.reflects layout ordinary registryExtension meaning functionTypes faithful observations
    missingTokens invalidTokens environments heaps locals agrees actualTyped slot rootTyped nativeCompleted
  have rhsResult := rhs_reflects meaning rhsGenerated found rhsView rhsCoreType environments agrees actualTyped locals resolution
  -- Keep the historical argument; the actual tail now supplies its own typed slots.
  have _legacyPreservation := @preservation
  cases rhsResult with
  | fault sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata =>
    exact .inl ⟨_, _, _, _, _, sourceFault, resultEq, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  | @ready target targetHeap sourceTrace resolution right continuation =>
    simp only [packed_renamed_type] at continuation
    obtain ⟨sourceSize, sourceSized⟩ := SourceExecutionSize.SourcePlaceResolves.has_size sourceTrace
    have rhsTrace : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right.right right.heap := by
      cases right.meaning.trace with | value trace => exact trace
    obtain ⟨rhsSize, rhsSized⟩ := SourceExecutionSize.ExpressionEvaluates.has_size rhsTrace
    obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size continuation
    have observed := CompatibleRenamedPlaceTail.reflects_ready_sized layout ordinary registryExtension functionTypes
      faithful observations missingTokens operatorProfile environments agrees actualTyped sourceSized resolution right rhsSized sized
    cases observed with
    | fault trace resultEq matched finalHeaps maps worlds frame metadata =>
      exact .inl ⟨_, _, _, _, _, trace.sound, resultEq, matched, finalHeaps, maps, worlds, frame, metadata⟩
    | committed trace finalHeaps maps worlds frame metadata count typed _ remaining =>
      exact .inr ⟨_, _, _, _, _, _, trace.sound, finalHeaps, maps, worlds, frame, metadata, count, typed, remaining.sound⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceReflection
