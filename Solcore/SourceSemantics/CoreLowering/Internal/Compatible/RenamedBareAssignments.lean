import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StatePlaceAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.TypedPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures

/-!
# Compatible profile: renamed bare assignments

Assignment statements under renaming: trees, certificates, meaning and bit-not updates.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceReflection
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

theorem reflects_ready_sized_with_diagnostics {compilation : SourceCoreCompatibleDataPlaces.Context}
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
    [FunctionCalls.FaultTokens faults] {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
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
  obtain ⟨replacement, replacementValue, replacementRep, modified, outcome⟩ :=
    CompatiblePlaceModifier.initialized_outcome observations profile snapshotRep right.related
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
            exact .fault (.structuralUpdate sourceTrace rhsTrace latest.read cellType root fault) rfl
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
        rcases DataPlaceGuard.inv_sized remaining with ⟨passes, child, bound, remaining⟩ |
          ⟨operation, selected, zero, resultEq, storeEq⟩
        · rcases outcome with ⟨applied, _⟩ | ⟨operation, selected, zero, _⟩
          · cases remaining with
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
          · -- The check passed, so the divisor is not zero.
            rw [selected, zero] at passes
            cases passes with
            | total total => cases total _ rfl
            | nonzero nonzero => exact (nonzero rfl).elim
        · rcases outcome with ⟨applied, _⟩ | ⟨_, _, _, panicked⟩
          · -- An applied source operation has a nonzero divisor, so the check passed.
            have passes := CompatiblePlaceModifier.passes_of_applies observations profile right.related applied
              (prepared.route.leafType = .integer)
            rw [selected, zero] at passes
            cases passes with
            | total total => cases total _ rfl
            | nonzero nonzero => exact (nonzero rfl).elim
          · -- The latest root is traversable, so the source panics on its operands.
            obtain ⟨_, read⟩ := changed.readable
            have panicked : Dynamic.AssignmentOperandsPanic operator target.selected right.right
                SourceCorePanics.divisionByZero := by
              rw [resolution.selectedEq]; exact panicked
            subst resultEq storeEq
            let reached := transport.extend rhsState (.refl _) extension helperFrame (Dynamic.HeapMetadataExtend.refl right.heap)
            have phaseRelated := transport.related rhsState (.refl _) extension helperFrame (Dynamic.HeapMetadataExtend.refl right.heap)
            exact .fault (.panic sourceTrace rhsTrace latest.read cellType root read panicked) rfl
              (FunctionCalls.FaultTokens.panic _) helperHeaps (resolution.maps.trans right.meaning.maps)
              ((resolution.worlds.trans right.meaning.worlds).trans extension)
              ((resolution.frame.trans right.meaning.frame).trans helperFrame)
              (resolution.metadata.trans right.meaning.metadata) ⟨reached, protocol.trans rhsRelated phaseRelated⟩


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
    [FunctionCalls.FaultTokens faults] {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
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
  exact reflects_ready_sized_with_diagnostics protocol transport layout ordinary registryExtension functionTypes faithful observations
    profile environments agrees actualTyped sourceTrace resolution right rhsTrace initialState rhsState rhsRelated
    (ProtectedPlaceReachedDiagnostics.MissingFor.of_uniform missingTokens) completed

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
    [FunctionCalls.FaultTokens faults] {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
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
    [FunctionCalls.FaultTokens faults] {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
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
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceFaults
/-! Whole emitted assignments short-circuit on key and RHS faults, retaining
all preceding source effects. The executions of children are obtained from the
universal expression IH; neither phase accepts a child evaluation as its
static compiler contract. Structural missing-default guards are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceFailures
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

theorem keys {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
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
  obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
    TypedDataPlaceKeyOrder.preserves_fault children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped) trace
  refine ⟨token, finalStore, finalMap, finalWorld, .target (.projectionExpression lookup read trace), ?_,
    tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  apply execute_key_failure prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
    (.cellRef (OptionalCell.cellType prepared.route.rootType) target) (.var (agrees coreLookup))
  simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, packed_renamed_type, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- This composition consumes a semantic resolution result, produced by
CompatibleRenamedPlaceResolution.preserves, and the independent RHS fault. It derives
the actual RHS run and suppresses modifier, setter, write and continuation. -/
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
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
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
  obtain ⟨value, store, mapping, world, result⟩ :=
    CompatibleRenamedPlaceRhs.preserves resolution meaning generated found environments agrees actualTyped locals (.fault failed)
  cases represented : result.represented with
  | @fault _ token tokenRep =>
    refine ⟨token, store, mapping, world, .rhs resolved failed, ?_, tokenRep, result.heaps,
      resolution.maps.trans result.maps, resolution.worlds.trans result.worlds,
      resolution.frame.trans result.frame, resolution.metadata.trans result.metadata⟩
    apply SourceCoreCompatibleDataPlaces.execute_rhs_failure prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ))
      (lowered.expression.rename ξ) next outputType (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
      (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) (packValues resolution.values)
      (.inRight .unit resolution.snapshot) (.var reference) resolution.keysEvaluated resolution.snapshotEvaluated
    simpa only [renamed, coreType, snapshotEnvironment, keysEnvironment, referenceEnvironment] using result.evaluated

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceFailures


/-! Target-resolution faults before the RHS. The actual key runs are derived
from the universal expression theorem. The getter uses the live root after
those effects, preserving exact raw missing-default tokens and administrative
allocations. An absent ordinary root fails without allocating a helper. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceTargetFaults
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
theorem projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
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
  have getterTyped := getter_typed layout (virtual_closed layout ordinary) (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨keys⟩ := CompatibleRenamedPlaceTargetKeys.preserves layout.children meaning environments heaps locals agrees actualTyped slot rootTyped lookup initialRead trace
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
    .target (.projectionRead lookup initialRead trace currentRead initialValue fault), initialValue, receipt, ?_,
    CompatibleHeap.HeapRepresents.after_snapshot keys.heaps extension typedStore appended,
    keys.maps, keys.worlds.trans extension, keys.frame.trans frame, keys.metadata⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

/-- Actual describe supplies `ordinary`. It is a static route fact, not a
claim that native type equality recovers the source declaration. -/
theorem uninitialized
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
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
  obtain ⟨keys⟩ := CompatibleRenamedPlaceTargetKeys.preserves layout.children meaning environments heaps locals agrees actualTyped slot rootTyped lookup initialRead trace
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
    .target (.uninitialized lookup initialRead trace currentRead empty notMapping hasProjection), ?_,
    keys.heaps, keys.maps, keys.worlds, keys.frame, keys.metadata⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceTargetFaults


/-! Structural missing-default failure after the RHS. The source specification
traverses the latest root before applying the modifier. For authenticated equal
or scalar numeric operands, the generated earlier modifier is total; therefore
the same structural fault wins and neither source nor native final write runs.
Exact raw key guards come from the source fault, not native projection equality.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceStructuralFault
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

/-- All key/RHS native evaluations come from their universal IH. The fault
receipt retains the raw mapping header and ordered selection where traversal
stopped; no decoder or source evaluator supplies the semantic result. -/
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
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
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
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have getterTyped := getter_typed layout closed respects
  have setterTyped := setter_typed layout closed respects
  have sourceFault := Dynamic.SourcePlaceAssignmentFaults.structuralUpdate (operator := operator) resolve evaluate sourceRead rootType initialValue fault
  obtain ⟨resolution, coreLookup⟩ := CompatibleRenamedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
    layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped meaning faithful observations
    environments heaps locals agrees actualTyped slot rootTyped resolve
  obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
    CompatibleRenamedPlaceRhs.preserves resolution meaning rhsGenerated found environments agrees actualTyped locals (.value evaluate)
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
    obtain ⟨replacement, replacementValue, replacementRep, modifiedEvaluated, _⟩ :=
      CompatiblePlaceModifier.initialized_outcome observations operatorProfile snapshotRep rightRep
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

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceStructuralFault

/-! A compound operation that panics after the RHS: the native setter runs on the
traversed latest root, and the modifier's check fails before the write. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlacePanic
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

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

private theorem none_read {projections : List Dynamic.EvaluatedProjection} {selected : Option Dynamic.Value}
    (read : Dynamic.ProjectionsRead none projections selected) : projections = [] := by
  cases read
  rfl

/-- A source panic on the operands runs the setter on the readable latest root, then
fails at the modifier's check before the write. -/
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
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial currentSelected : Option Dynamic.Value} {code : UInt8}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (pathRead : Dynamic.ProjectionsRead initial sourceTarget.projections currentSelected)
    (panics : Dynamic.AssignmentOperandsPanic operator sourceTarget.selected right code)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word (SourceCorePanics.reason code))) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have getterTyped := getter_typed layout closed respects
  have setterTyped := setter_typed layout closed respects
  obtain ⟨resolution, coreLookup⟩ := CompatibleRenamedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
    layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped meaning faithful observations
    environments heaps locals agrees actualTyped slot rootTyped resolve
  obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
    CompatibleRenamedPlaceRhs.preserves resolution meaning rhsGenerated found environments agrees actualTyped locals (.value evaluate)
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
    obtain ⟨replacement, replacementValue, replacementRep, modifiedEvaluated, outcome⟩ :=
      CompatiblePlaceModifier.initialized_outcome observations operatorProfile snapshotRep rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
    rw [resolution.selectedEq] at panics
    -- The panic fixes a panicking modifier, a zero divisor and its code.
    obtain ⟨operation, selected, zero, sameCode⟩ : ∃ operation,
        binaryOperator (prepared.route.leafType = .integer) operator = some ⟨operation, true⟩ ∧
          rightValue = .word Word.zero ∧ code = SourceCorePanics.divisionByZero := by
      rcases outcome with ⟨applied, _⟩ | ⟨operation, selected, zero, other⟩
      · exact (CompatiblePlaceModifier.panic_excludes_applies panics applied).elim
      · exact ⟨operation, selected, zero, CompatiblePlaceModifier.panic_functional panics other⟩
    subst zero sameCode
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_read pathRead)).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    obtain ⟨_, changed⟩ := DataPlaceUpdateTotality.read_update pathRead replacement
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
          (.inRight .unit resolution.snapshot) (.word Word.zero) replacementValue coreEnvironment)
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
    obtain ⟨_, helperStore, futureWorld, setterEvaluated, helperHeaps, extension, frame⟩ :=
      CompatiblePlaceWriteback.setter_preserves root rhsResult.heaps currentArguments replacementRep changed layout.nonempty
        faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
    refine ⟨helperStore, rhsMap, futureWorld, ?_, helperHeaps,
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
              (LanguageResult.bind_success _ setterEvaluated (DataPlaceGuard.panic_of_selected selected))))))

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlacePanic


/-! Every independently specified assignment fault in the nonempty equal or
numeric profile is preserved. Unbound/dangling roots contradict actual lexical
and heap agreement. Invalid operands contradict the represented snapshot and
RHS values; neither exclusion is inferred from native type equality alone. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceFaults
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

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
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
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
        CompatibleRenamedPlaceFailures.keys layout.children meaning environments heaps locals agrees actualTyped slot lookup read fault
          operator rhs (lowered.expression.rename ξ) (next.rename ξ) outputType invalid
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
    | danglingAfterProjections lookup read evaluated missing =>
      obtain ⟨keys⟩ := CompatibleRenamedPlaceTargetKeys.preserves layout.children meaning environments heaps locals agrees actualTyped slot rootTyped lookup read evaluated
      exact (missing.excludes_read keys.read).elim
    | projectionRead lookup initialRead evaluate currentRead initialValue fault =>
      obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleRenamedPlaceTargetFaults.projection layout ordinary meaning environments heaps locals agrees actualTyped slot rootTyped lookup initialRead evaluate currentRead
          registryExtension faithful observations initialValue fault operator rhs (lowered.expression.rename ξ) (next.rename ξ) outputType invalid
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingTokens receipt, finalHeaps, maps, worlds, frame, metadata⟩
    | uninitialized lookup initialRead evaluate currentRead empty notMapping projected =>
      obtain ⟨finalStore, finalMap, finalWorld, _, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleRenamedPlaceTargetFaults.uninitialized layout meaning environments heaps locals agrees actualTyped slot rootTyped lookup initialRead evaluate currentRead
          ordinary empty notMapping projected operator rhs (lowered.expression.rename ξ) (next.rename ξ) outputType invalid
      exact ⟨prepared.invalidProjection, finalStore, finalMap, finalWorld, evaluated, invalidTokens _, finalHeaps, maps, worlds, frame, metadata⟩
  | rhs resolve fault =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleRenamedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped meaning faithful observations
      environments heaps locals agrees actualTyped slot rootTyped resolve
    obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
      CompatibleRenamedPlaceFailures.rhs resolution meaning rhsGenerated found rhsCoreType environments agrees actualTyped locals resolve coreLookup fault
        operator (next.rename ξ) outputType invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  | operands resolve evaluate _ _ _ _ invalidOperands =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleRenamedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped meaning faithful observations
      environments heaps locals agrees actualTyped slot rootTyped resolve
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
      CompatibleRenamedPlaceRhs.preserves resolution meaning rhsGenerated found environments agrees actualTyped locals (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf _ rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
      have valid := CompatiblePlaceModifier.initialized_valid observations operatorProfile rhsResult.saved_snapshot rightRep
      rw [resolution.selectedEq] at invalidOperands
      exact (valid invalidOperands).elim
  | panic resolve evaluate currentRead _ initialValue pathRead panics =>
    obtain ⟨finalStore, finalMap, finalWorld, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
      CompatibleRenamedPlacePanic.preserves layout ordinary registryExtension meaning faithful observations rhsGenerated found rhsView rhsCoreType
        operatorProfile environments heaps locals agrees actualTyped slot rootTyped resolve evaluate currentRead initialValue pathRead panics
        (next.rename ξ) outputType invalid
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, FunctionCalls.FaultTokens.panic _, finalHeaps, maps, worlds, frame, metadata⟩
  | structuralUpdate resolve evaluate currentRead sameType initialValue fault =>
    obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
      CompatibleRenamedPlaceStructuralFault.preserves layout ordinary registryExtension meaning faithful observations rhsGenerated found rhsView rhsCoreType
        operatorProfile environments heaps locals agrees actualTyped slot rootTyped resolve evaluate currentRead sameType initialValue fault (next.rename ξ) outputType invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingTokens receipt, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentPreservation
/-! Forward finite meaning of bare assignments. These laws preserve the exact
independent source trace, including a fault after RHS effects. The returned
continuation runs in its real renamed seven-slot environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {certificate : Certificate} {faults : FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp} {identities : Dynamic.Value → Word → Prop}

private theorem writes_functional {heap left right : Dynamic.Heap} {location : Dynamic.Location} {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes heap location value left) (second : Dynamic.Heap.Writes heap location value right) : left = right := by
  have cells : ∀ {before first second : List Dynamic.Cell} {index : Nat} {value : Dynamic.Cell},
      Dynamic.Heap.CellsWrite before index value first → Dynamic.Heap.CellsWrite before index value second → first = second := by
    intro before first second index value left
    induction left generalizing second with
    | head => intro right; cases right; rfl
    | tail _ ih => intro right; cases right with | tail rest => exact congrArg (List.cons _) (ih rest)
  cases first with
  | intro firstRead firstWrite =>
    cases second with
    | intro secondRead secondWrite =>
      have same := firstRead.functional secondRead
      cases same
      exact congrArg Dynamic.Heap.mk (cells firstWrite secondWrite)

theorem preserves_prefix
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place id updated after) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  cases trace with
  | intro resolved evaluated written =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolved
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result⟩ :=
      rhs_preserves snapshot meaning generated found environments heaps locals agrees actualTyped (.value evaluated)
    cases related : result.represented with
    | @value _ rightValue payload =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType _ rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      have saved := snapshot.represented.extend result.maps result.worlds
      cases written with
      | intro read sameType initial update written =>
        cases update with
        | leaf applied =>
          rcases modifier_total observations profile saved rightRep
            (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
            ⟨invalidOperands, _⟩ | ⟨replacement, updatedValue, replacementRep, outcome, modified⟩
          · exact (DataPlaceModifier.assignment_excludes_invalid applied invalidOperands).elim
          · rcases outcome with generatedApply | ⟨_, _, _, panics⟩
            case inr => exact (CompatiblePlaceModifier.panic_excludes_applies panics applied).elim
            have same := DataPlaceModifier.assignment_functional generatedApply applied
            subst replacement
            have passes := CompatiblePlaceModifier.passes_of_applies observations profile rightRep applied
              (prepared.route.leafType = .integer)
            obtain ⟨generatedHeap, finalStore, _, generatedWrite, finalHeaps, frame, metadata, typed, agreement⟩ :=
              commit layout snapshot bare result rightRep replacementRep applied (by simpa only [layout.sameType] using modified)
                passes actualTyped
            have same := writes_functional generatedWrite written
            subst generatedHeap
            exact ⟨updatedValue, finalStore, rhsMap, rhsWorld,
              [.unit, updatedValue, updatedValue, rightValue, snapshot.value, .unit,
                .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target],
              replacementRep, finalHeaps, result.maps, result.worlds, frame, metadata, rfl, typed, agreement⟩

private theorem no_target_fault
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
    (bare : place.projections = []) {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after) : False := by
  cases fault with
  | unbound missing => exact missing.excludes_lookup snapshot.lookup
  | dangling lookup missing =>
    have same := lookup.functional snapshot.lookup
    cases same
    exact missing.excludes_read snapshot.read
  | projectionExpression _ _ fault => rw [bare] at fault; cases fault
  | danglingAfterProjections lookup _ evaluated missing =>
    rw [bare] at evaluated
    cases evaluated
    have same := lookup.functional snapshot.lookup
    cases same
    exact missing.excludes_read snapshot.read
  | projectionRead _ _ evaluated _ _ fault =>
    rw [bare] at evaluated
    cases evaluated
    cases fault
  | uninitialized _ _ evaluated _ _ _ nonempty =>
    rw [bare] at evaluated
    cases evaluated
    exact nonempty rfl

/-- All independently specified bare assignment faults retain RHS prefix
state. A target fault or structural traversal fault contradicts the empty
path and live lexical reference, rather than being silently reclassified. -/
theorem preserves_fault_reachable
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after)
    (next : Expr) (outputType : Ty) (invalid : Word)
    [FunctionCalls.FaultTokens faults] (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  have phase := snapshot_prefix layout snapshot lowered.expression next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) invalid
  cases trace with
  | target fault => exact (no_target_fault snapshot bare fault).elim
  | rhs resolve fault =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result⟩ :=
      rhs_preserves snapshot meaning generated found environments heaps locals agrees actualTyped (.fault fault)
    cases represented : result.represented with
    | fault token =>
      exact ⟨_, rhsStore, rhsMap, rhsWorld, phase.wrap (LanguageResult.bind_failure outputType result.evaluated), token,
        result.heaps, result.maps, result.worlds, result.frame, result.metadata⟩
  | operands resolve evaluated _ _ _ _ invalidOperands =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result⟩ :=
      rhs_preserves snapshot meaning generated found environments heaps locals agrees actualTyped (.value evaluated)
    cases represented : result.represented with
    | @value _ rightValue payload =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType _ rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      rcases modifier_total observations profile (snapshot.represented.extend result.maps result.worlds) rightRep
        (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
          ⟨_, failed⟩ | ⟨_, _, _, outcome, _⟩
      · have failed : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
            (modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
            (.inLeft prepared.route.leafType (.word invalid)) rhsStore := by simpa only [layout.sameType] using failed
        exact ⟨invalid, rhsStore, rhsMap, rhsWorld,
          phase.wrap (LanguageResult.bind_success outputType result.evaluated (LanguageResult.bind_failure outputType failed)),
          invalidToken _ _ invalidOperands, result.heaps, result.maps, result.worlds, result.frame, result.metadata⟩
      · rcases outcome with applied | ⟨_, _, _, panics⟩
        · exact (DataPlaceModifier.assignment_excludes_invalid applied invalidOperands).elim
        · exact (DataPlaceModifier.panic_excludes_invalid panics invalidOperands).elim
  | panic resolve evaluated _ _ _ _ panics =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result⟩ :=
      rhs_preserves snapshot meaning generated found environments heaps locals agrees actualTyped (.value evaluated)
    cases represented : result.represented with
    | @value _ rightValue payload =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType _ rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      rcases modifier_total observations profile (snapshot.represented.extend result.maps result.worlds) rightRep
        (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
          ⟨invalidOperands, _⟩ | ⟨_, updatedValue, _, outcome, modified⟩
      · exact (DataPlaceModifier.panic_excludes_invalid panics invalidOperands).elim
      · rcases outcome with applied | ⟨operation, selected, zero, other⟩
        · exact (CompatiblePlaceModifier.panic_excludes_applies panics applied).elim
        · -- The setter runs and the check fails before the write.
          have sameCode := CompatiblePlaceModifier.panic_functional panics other
          subst sameCode zero
          have selected : binaryOperator (prepared.route.leafType = .integer) operator = some ⟨operation, true⟩ := by
            simpa only [layout.sameType] using selected
          have nativeModified : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value
              (.word Word.zero) actual) rhsStore
              (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType
                (binaryOperator (prepared.route.leafType = .integer) operator) false
                (.var 1) (.var 0) invalid) (.inRight .word updatedValue) rhsStore := by
            simpa only [layout.sameType] using modified
          obtain ⟨latest⟩ := result.latest
          exact ⟨_, rhsStore, rhsMap, rhsWorld,
            phase.wrap (LanguageResult.bind_success outputType result.evaluated
              (LanguageResult.bind_success outputType nativeModified
                (LanguageResult.bind_success outputType
                  (setter_evaluates layout snapshot.value (.word Word.zero) updatedValue latest.nativeRead)
                  (DataPlaceGuard.panic_of_selected selected)))),
            FunctionCalls.FaultTokens.panic _, result.heaps, result.maps, result.worlds, result.frame, result.metadata⟩
  | structuralUpdate resolve _ _ _ _ fault =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve
    cases fault

/-- Compatibility entry point retaining the original unconditional token law. -/
theorem preserves_fault
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after)
    (next : Expr) (outputType : Ty) (invalid : Word)
    [FunctionCalls.FaultTokens faults] (invalidToken : faults (.invalidAssignmentOperands operator) invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact preserves_fault_reachable layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped slot rootTyped trace next outputType invalid
    (AssignmentOperandDiagnostics.of_unconditional invalidToken)

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementTree
/-! Static ordinary assignment heads and lexical continuations. Bare and
projected destinations retain their distinct source rules. Each head contains
concrete typed expression trees and compiler layout receipts, never execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Shape (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) (administrative : Core.Context)
    (definitions : DataEnvironment) (place : PlaceResolution) (prepared : Prepared) :
    List SourceCoreBasic.LoweredExpr → TypeSystem.Ty → Prop where
  | bare (empty : place.projections = []) (layout : CompatibleBareAssignment.Layout values prepared) :
      Shape readFuel values source context solved reasonAt scope administrative definitions place prepared [] prepared.route.rootSourceType
  | projected {codes leaf sourceTypes site}
      (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source
        (CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt) scope site place prepared codes sourceTypes leaf administrative)
      (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none) :
      Shape readFuel values source context solved reasonAt scope administrative definitions place prepared codes leaf

structure Head (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) (administrative : Core.Context)
    (definitions : DataEnvironment) (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (rhs : ExpressionId) where
  prepared : Prepared
  index : Nat
  codes : List SourceCoreBasic.LoweredExpr
  leaf : TypeSystem.Ty
  lowered : SourceCoreBasic.LoweredExpr
  node : ExpressionNode
  invalid : Word
  shape : Shape readFuel values source context solved reasonAt scope administrative definitions assignment.target prepared codes leaf
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType)
  writable : WritableLocal context assignment.target.root prepared.route.rootSourceType
  found : source.lookupExpression? rhs = some node
  right : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope rhs lowered
  rightView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type
  rightType : lowered.type = prepared.route.leafType
  profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false

namespace Head
variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : Scope} {administrative : Core.Context}
  {definitions : DataEnvironment} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

def emit (head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
    (next : Expr) (output : Ty) : Expr :=
  execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) head.lowered.expression next output
    (binaryOperator (head.prepared.route.leafType = .integer) operator) false head.invalid

def writtenContext (head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
    (actual : Core.Context) : Core.Context :=
  CompatibleRenamedPlaceSuccess.writtenContext head.prepared (SourceCoreCalls.packArguments head.codes).type actual

/-- The diagnostic table separately authenticates each emitted failure token. -/
structure Errors (head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token
  uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection
  operands : faults (.invalidAssignmentOperands operator) head.invalid
end Head

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (context : SourceSemantics.Context) (scope : Scope)
    (administrative : Core.Context) (definitions : DataEnvironment) :
    Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | tail {mode statements expected type code}
      (body : TypedLexicalControl.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope mode statements expected type code) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
        mode statements expected type code
  | assign {mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
        mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
        mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type))

namespace Tree
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context} {scope : Scope}
  {administrative : Core.Context} {definitions : DataEnvironment}

inductive Errors (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {mode : Bool} → {statements : List StatementId} → {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
      mode statements expected type code → Prop where
  | tail {mode statements expected type code}
      (body : TypedLexicalControl.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope mode statements expected type code) : Errors registry faults (.tail body)
  | assign {mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node} {form : node.form = .assignValue assignment operator rhs}
      {head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
        mode rest expected type body}
      (current : head.Errors registry faults) (tail : Errors registry faults remaining) :
      Errors registry faults (.assign found form head remaining)
end Tree
end Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementCertificates
/-! Assignment certificates follow the successful production place callback
and flow branch. Independent source typing and native site typing remain
explicit static inputs; no child execution is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open CompatibleEncoding (bind_ok)

private theorem stored_type {source : TypedSource} {context : SourceSemantics.Context} {rhs : ExpressionId}
    {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? rhs = some node)
    (typed : ExpressionHasType source context rhs type) : node.type = type := by
  obtain ⟨actual, contains, same⟩ := typed.stored_type
  have identical := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
  exact identical ▸ same

theorem Head.of_lower {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output result : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ id lowered, expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs,
      code = head.emit next output := by
  classical
  by_cases bare : assignment.target.projections = []
  · obtain ⟨binder, prepared, index, lowered, binding, rootType, rawView, slot, layout, generated, sameType, _, codeEq⟩ :=
      CompatibleBareAssignment.of_lower bare accepted
    obtain ⟨node, found, tree, _⟩ := extract rhs lowered generated
    have rawType := stored_type unique found rightTyped
    refine ⟨⟨prepared, index, [], prepared.route.rootSourceType, lowered, node, invalidOperand,
      .bare bare layout, slot, rootType ▸ writable binder binding, found, tree,
      by simpa only [rawType] using rawView, sameType, ?_⟩, codeEq⟩
    rcases profile with equal | word | ⟨integer, notWordOnly⟩
    · exact .inl equal
    · exact .inr (.inl (rawView.trans word))
    · exact .inr (.inr ⟨rawView.trans integer, notWordOnly⟩)
  · obtain ⟨binder, leaf, prepared, codes, sourceTypes, index, lowered, node, _, binding, rootType, slot, layout, ordinary,
      _, found, tree, rawView, sameType, codeEq⟩ :=
      CompatiblePlaceLayoutCertificates.of_lower unique signatures sourceTyped rightTyped bare extract accepted typed
    have rawType := stored_type unique found rightTyped
    refine ⟨⟨prepared, index, codes, leaf, lowered, node, invalidOperand,
      .projected layout ordinary, slot, rootType ▸ writable binder binding, found, tree, rawView, sameType, ?_⟩, codeEq⟩
    rw [rawType] at rawView
    rcases profile with equal | word | ⟨integer, notWordOnly⟩
    · exact .inl equal
    · exact .inr (.inl (rawView.trans word))
    · exact .inr (.inr ⟨rawView.trans integer, notWordOnly⟩)

/-- Static source obligations for the ordinary assignment branch. General
functions, unary assignments and loop syntax are deliberately separate. -/
inductive Syntax (source : TypedSource) (context : SourceSemantics.Context) : Bool → List StatementId → TypeSystem.Ty → Prop where
  | tail {mode statements expected} (body : TypedLexicalControl.Syntax source context mode statements expected) :
      Syntax source context mode statements expected
  | assign {mode id node assignment operator rhs rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

/-- Field equalities identify the real compatible callback. They permit source
cell/layout instrumentation of other policy fields without changing assignment. -/
structure AssignmentPolicy (policy : SourceCoreLoops.Policy) (values : ValuesContext)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word)
    (missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) : Prop where
  read : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  equal : policy.assignEqual = some (fun expression fuel source scope site assignment rhs output next reasonAt =>
    lower values values.checked.signatures expression fuel source scope site assignment .equal (some rhs) output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root .equal) (missing site assignment.target.root))
  value : policy.assignValue = some (fun expression fuel source scope site assignment operator rhs output next reasonAt =>
    lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs) output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator) (missing site assignment.target.root))

/-- The ordinary shared compatible factory supplies these exact callbacks. -/
theorem AssignmentPolicy.actual (values : ValuesContext) (solved : List SolvedRequirement)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (owner : SourceSpecialization.SpecializationKey) (expression : ExpressionLowerer)
    (cells : Option SourceCoreSourceCells.Allocator) (definitions : Option DataEnvironment) :
    AssignmentPolicy (SourceCoreCompatibleDataMatches.loopPolicy values solved assignments diagnostics owner expression cells definitions)
      values (fun site root => diagnostics.placeReason owner site root none)
      (fun site root operator => if operator = .equal then Word.zero else assignments.reasonAt site root (.value operator))
      (fun site root type => diagnostics.placeReason owner site root (some type)) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

/-- Successful flow lowering is followed recursively. Static expression and
site typing callbacks are accepted compiler certificates, not meaning IHs. -/
theorem tree_of_flow {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context} {scope : Scope}
    {administrative : Core.Context} {definitions : DataEnvironment} {policy : SourceCoreLoops.Policy}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    (matched : AssignmentPolicy policy values invalidProjection invalidOperand missing)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (expressions : ∀ fuel id lowered, policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (sites : ∀ {fuel statements type mode selfReason code},
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code (LocalLoop.resultType type) definitions)
    (tails : ∀ {mode statements expected fuel type selfReason code},
      TypedLexicalControl.Syntax source context mode statements expected →
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code →
      TypedLexicalControl.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode statements expected type code)
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context mode statements expected)
    {fuel : Nat} {type : Ty} {selfReason : Word} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code) :
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
      mode statements expected type code := by
  induction syntaxTree generalizing fuel code with
  | tail body => exact .tail (tails body accepted)
  | @assign id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      have typed := sites accepted
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (matched.read ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
      have compiled : lower values values.checked.signatures policy.lowerExpression fuel source scope (.occurrence id.occurrence)
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection (.occurrence id.occurrence) assignment.target.root)
          (invalidOperand (.occurrence id.occurrence) assignment.target.root operator)
          (missing (.occurrence id.occurrence) assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, matched.equal, matched.value] using accepted
      obtain ⟨head, rfl⟩ := Head.of_lower unique signatures sourceTyped writable rightTyped profile (expressions fuel) compiled typed
      exact .assign found form head (ih compiledBody)
end Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotMeaning
/-! A numeric bare snapshot creates a real mapped commit and an exact typed
seven-slot continuation in the actual renamed environment. Its Unit RHS has
no source child. Every native phase is constructed from a represented live cell. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {location : Dynamic.Location} {target : Location} {sourceValue : Dynamic.Value} {value : Value}
  {actual : Environment} {actualContext : Core.Context} {index : Nat} {ξ : Renaming}

/-- A source snapshot operation supplies no native execution witness. This
construction derives the modifier, setter, store write and both directions of
the continuation agreement from that independent operation. -/
theorem initialized_prefix (layout : Layout prepared)

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨prepared.route.rootSourceType, some sourceValue, none⟩)
    (nativeRead : store.read? target = some (.inRight .unit value))
    (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType sourceValue value prepared.route.rootType)
    (lookup : actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word)
    (passes : SourceCoreDataPlaces.Passes operator .unit) :
    ∃ updated replacement after finalStore slots,
      Dynamic.BitNotSnapshot (some sourceValue) updated ∧
      Dynamic.Heap.Writes heap location (some updated) after ∧
      ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      HeapRepresents checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨updated, replacement, after, finalStore, slots, applies, written, related, finalHeaps,
    frame, metadata, count, typed, agreement, _⟩ :=
    initialized_prefix_sized layout profile heaps reference read nativeRead represented lookup actualTyped operator invalid
  exact ⟨updated, replacement, after, finalStore, slots, applies, written, related, finalHeaps,
    frame, metadata, count, typed, agreement passes⟩

/-- Absence returns the unary token in the actual environment and skips every
continuation. The physical store, including unrelated captured cells, is exact. -/
theorem absent_evaluates (layout : Layout prepared)
    (lookup : actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some (.inLeft prepared.route.rootType .unit))
    (next : Expr) (output : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ) (.inLeft output (.word invalid)) store := by
  rw [execute_rename layout]
  exact CompatibleBareBitNotNative.absent_evaluates layout lookup read _ _ _ _

/-- Completed absent runs do not introduce a source child or a store change. -/
theorem absent_reflects (layout : Layout prepared)
    (lookup : actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some (.inLeft prepared.route.rootType .unit))
    {next : Expr} {output : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word} {result : Value} {after : Store}
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ) result after) :
    result = .inLeft output (.word invalid) ∧ after = store :=
  evaluation_deterministic completed (absent_evaluates layout lookup read next output operator invalid)

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotSource
/-! Independent bare unary source updates and completed actual renamed Core
code agree. Successful reflection returns all seven typed slots, with a Unit
RHS; preservation uses the exact source write and supports any continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (faults : FaultRep) (prepared : Prepared) (place : PlaceResolution)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (store : Store) (mapping : LocationMap)
    (world : StoreTyping) (actual : Environment) (actualContext : Core.Context) (ξ : Renaming)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word}
      (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason before)
      (result : value = .inLeft output (.word token)) (represented : faults reason token)
      (storeEq : finalStore = store) :
      Result checked registry functions program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore
  | success {updated : Dynamic.Value} {replacement : Value} {after : Dynamic.Heap}
      {written : Store} {slots : Environment}
      (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before place updated after)
      (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType)
      (heaps : HeapRepresents checked registry functions mapping world after written)
      (frame : AdministrativePreserved mapping store mapping written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (continuation : Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) :
      Result checked registry functions program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore

inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (faults : FaultRep) (prepared : Prepared) (place : PlaceResolution)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (store : Store) (mapping : LocationMap)
    (world : StoreTyping) (actual : Environment) (actualContext : Core.Context) (ξ : Renaming)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word}
      (trace : SourceExecutionSize.SourcePlaceBitNotFaults program sourceSize context evidence source environment before place reason before)
      (result : value = .inLeft output (.word token)) (represented : faults reason token)
      (storeEq : finalStore = store) :
      ResultAt size checked registry functions program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {replacement : Value} {after : Dynamic.Heap}
      {written : Store} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceSnapshotUpdate program sourceSize context evidence source Dynamic.BitNotSnapshot
        environment before place updated after)
      (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType)
      (heaps : HeapRepresents checked registry functions mapping world after written)
      (frame : AdministrativePreserved mapping store mapping written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) :
      ResultAt size checked registry functions program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {prepared : Prepared} {place : PlaceResolution} {scope : Scope}
  {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {index : Nat} {ξ : Renaming}


/-- Erasing sizes preserves the independent source outcome and actual seven slots. -/
theorem ResultAt.erase {size : Nat} {faults : FaultRep} {next : Expr} {output : Ty}
    {result : Value} {finalStore : Store}
    (receipt : ResultAt size compilation.checked registry functions program context evidence source faults prepared place
      environment before store mapping world actual actualContext ξ next output result finalStore) :
    Result compilation.checked registry functions program context evidence source faults prepared place
      environment before store mapping world actual actualContext ξ next output result finalStore := by
  cases receipt with
  | fault trace same represented stores => exact .fault trace.sound same represented stores
  | success trace represented heaps frame metadata count typed _ continuation =>
    exact .success trace.sound represented heaps frame metadata count typed continuation.sound

private theorem writes_functional {heap left right : Dynamic.Heap} {location : Dynamic.Location} {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes heap location value left) (second : Dynamic.Heap.Writes heap location value right) : left = right := by
  have cells : ∀ {before first second : List Dynamic.Cell} {index : Nat} {value : Dynamic.Cell},
      Dynamic.Heap.CellsWrite before index value first → Dynamic.Heap.CellsWrite before index value second → first = second := by
    intro before first second index value left
    induction left generalizing second with
    | head => intro right; cases right; rfl
    | tail _ ih => intro right; cases right with | tail rest => exact congrArg (List.cons _) (ih rest)
  cases first with
  | intro firstRead firstWrite =>
    cases second with
    | intro secondRead secondWrite =>
      have same := firstRead.functional secondRead
      cases same
      exact congrArg Dynamic.Heap.mk (cells firstWrite secondWrite)

theorem preserves_prefix (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before place updated after) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word)
    (passes : SourceCoreDataPlaces.Passes operator .unit) :
    ∃ replacement finalStore slots,
      ValueRep compilation.checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  cases trace with
  | intro resolve written =>
    cases resolve with
    | @intro _ _ _ _ _ _ _ location initialCell currentCell resolved initial selected lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases written with
      | intro writeRead typeEq writeInitial changed sourceWrite =>
        cases changed with
        | leaf applies =>
          obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
          obtain ⟨staticLocation, staticCell, staticLookup, staticRead, staticType, _⟩ := locals.lookup schemeLookup
          have sameLocation := lookup.functional staticLookup
          subst staticLocation
          have sameCell := currentRead.functional staticRead
          subst staticCell
          have cellType := staticType.trans bodyEq
          obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
          cases root with
          | emptyMapping key value =>
            have impossible := cellType ▸ profile
            rcases impossible with impossible | impossible <;> cases impossible
          | uninitialized => cases applies
          | initialized =>
            obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
            cases represented with
            | @initialized rawType payload sourceValue nativeValue related =>
              simp only at cellType
              subst_vars
              obtain ⟨replacement, native, generatedAfter, finalStore, slots, generated, generatedWrite,
                related, finalHeaps, frame, metadata, count, typed, agreement⟩ :=
                initialized_prefix layout profile heaps reference currentRead nativeRead related
                  (agrees nativeLookup) actualTyped operator invalid passes
              have same := CompatiblePlaceBitNotModifier.functional generated applies
              subst replacement
              have same := writes_functional generatedWrite sourceWrite
              subst generatedAfter
              exact ⟨native, finalStore, slots, related, finalHeaps, frame, metadata, count, typed, agreement⟩

/-- The sole runtime premise is completion of the real renamed code. It
produces an independent source fault/write and the actual typed continuation. -/
theorem reflects_sized (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {faults : FaultRep} {next : Expr} {output : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word}
    {result : Value} {finalStore : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ) result finalStore) :
    ResultAt size compilation.checked registry functions program context evidence source faults prepared place environment before store
      mapping world actual actualContext ξ next output result finalStore := by
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨sourceLocation, cell, sourceLookup, sourceRead, cellType, _⟩ := locals.lookup schemeLookup
  have cellType := cellType.trans bodyEq
  obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible sourceLookup slot
  obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference sourceRead
  cases represented with
  | uninitialized projected =>
    have initial : Dynamic.RootInitialValue _ none := .uninitialized (by
      rintro ⟨key, value, same⟩
      have impossible : prepared.route.rootSourceType = .mapping key value := cellType.symm.trans same
      rw [impossible] at profile
      rcases profile with impossible | impossible <;> cases impossible)
    have trace := CompatibleBareBitNotMeaning.resolves (program := program) (context := context)
      (evidence := evidence) (source := source) bare sourceLookup sourceRead initial
    obtain ⟨resultEq, storeEq⟩ := absent_reflects layout (agrees nativeLookup) nativeRead completed.sound
    obtain ⟨sourceSize, sourceTrace⟩ := SourceExecutionSize.SourcePlaceBitNotFaults.has_size (.uninitialized trace rfl)
    exact .fault sourceTrace resultEq token storeEq
  | @initialized type _payload sourceValue value related =>
    simp only at cellType
    subst type
    have trace := CompatibleBareBitNotMeaning.resolves (program := program) (context := context)
      (evidence := evidence) (source := source) bare sourceLookup sourceRead Dynamic.RootInitialValue.initialized
    obtain ⟨updated, replacement, after, written, slots, applies, sourceWrite, represented, finalHeaps,
      frame, metadata, count, typed, _agreement, remaining⟩ := initialized_prefix_sized layout profile heaps
        reference sourceRead nativeRead related (agrees nativeLookup) actualTyped operator invalid
    obtain ⟨sourceSize, sourceTrace⟩ := SourceExecutionSize.SourcePlaceSnapshotUpdate.has_size
      (.intro trace (.intro sourceRead rfl .initialized (.leaf applies) sourceWrite))
    obtain ⟨remainingSize, smaller, continuation⟩ := remaining completed
    exact .success sourceTrace represented finalHeaps frame metadata count typed smaller continuation

theorem reflects (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {faults : FaultRep} {next : Expr} {output : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word}
    {result : Value} {finalStore : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults prepared place environment before store
      mapping world actual actualContext ξ next output result finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size completed
  exact (reflects_sized layout bare profile environments heaps locals agrees actualTyped slot rootTyped token sized).erase

private theorem excludes_target_fault {heap after : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    {reason : Dynamic.SemanticFault}
    (bare : place.projections = []) (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (read : Dynamic.Heap.Reads heap location cell)
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment heap place reason after) : False := by
  cases fault with
  | unbound missing => exact missing.excludes_lookup lookup
  | dangling found missing => exact missing.excludes_read (found.functional lookup ▸ read)
  | projectionExpression found initialRead fault => rw [bare] at fault; cases fault
  | danglingAfterProjections found initialRead keys missing =>
    rw [bare] at keys
    cases keys
    exact missing.excludes_read initialRead
  | projectionRead found initialRead keys currentRead root fault =>
    rw [bare] at keys
    cases keys
    cases fault
  | uninitialized found initialRead keys currentRead empty notMapping nonempty =>
    rw [bare] at keys
    cases keys
    exact nonempty rfl

/-- Every independent fault of a live numeric bare root is the absent unary
operand. Generated helpers and the continuation do not alter either heap. -/
theorem preserves_fault (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
    (next : Expr) (output : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ) (.inLeft output (.word invalid)) store := by
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookup, staticRead, staticType, _⟩ := locals.lookup schemeLookup
  cases trace with
  | target fault => exact (excludes_target_fault bare staticLookup staticRead fault).elim
  | uninitialized resolve empty =>
    cases resolve with
    | intro lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases empty
      cases root with
      | uninitialized notMapping =>
        obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
        obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
        cases represented with
        | uninitialized projected => exact ⟨rfl, rfl,
            absent_evaluates layout (agrees nativeLookup) nativeRead next output operator invalid⟩
  | operand resolve selected invalidOperand =>
    cases resolve with
    | intro lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases selected
      have sameLocation := lookup.functional staticLookup
      subst staticLocation
      have sameCell := currentRead.functional staticRead
      subst staticCell
      have cellType := staticType.trans bodyEq
      cases root with
      | emptyMapping key value =>
        have impossible := cellType ▸ profile
        rcases impossible with impossible | impossible <;> cases impossible
      | initialized =>
        obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
        obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
        cases represented with
        | initialized related =>
          have profile := cellType ▸ profile
          obtain ⟨_, _, _, _, _, valid⟩ := CompatiblePlaceNumericBitNotModifier.success profile related
            (environment := [_]) (rhs := .unit) (.var (index := 0) rfl) operator store invalid
          exact (valid invalidOperand).elim

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotLowering
/-! Actual absent-RHS lowering supplies the bare numeric layout and its lexical
slot. The source/runtime interface names the real inserted environment and
seven typed continuation slots. No source-expression child or helper execution
is an input to these consumers. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {assignment : AssignmentResolution} {site : SourceCoreElaboration.ErrorSite}
  {expression : ExpressionLowerer} {fuel : Nat} {operator : Syntax.ValueAssignOp} {next lowered : Expr} {output : Ty}
  {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
  {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}

  (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body)
  (bare : assignment.target.projections = [])
  (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)

  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
    mapping world administrativeContext scope environment canonical)
  (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)

include rootTyped bare profile environments heaps locals agrees

theorem reflects_of_lower
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      output next reasonAt invalid invalidOperand missing = .ok lowered)
    {faults : FaultRep} {value : Value} {finalStore : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalidOperand)
    (completed : Evaluates actual store (lowered.rename ξ) value finalStore) :
    ∃ prepared, Result compilation.checked registry functions program context evidence source faults prepared assignment.target
      environment before store mapping world actual actualContext ξ next output value finalStore := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  refine ⟨prepared, ?_⟩
  exact reflects layout bare (view ▸ profile) environments heaps locals agrees actualTyped slot
    (rootEq ▸ rootTyped binder binding) token (lowering ▸ completed)

theorem preserves_prefix_of_lower
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (total : operator.mayPanic = false)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      output next reasonAt invalid invalidOperand missing = .ok lowered)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ prepared replacement finalStore slots,
      ValueRep compilation.checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ContinuationAgreement actual store (lowered.rename ξ) (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  obtain ⟨replacement, finalStore, slots, represented, finalHeaps, frame, metadata, count, typed, agreement⟩ :=
    preserves_prefix layout bare (view ▸ profile) environments heaps locals agrees actualTyped slot
      (rootEq ▸ rootTyped binder binding) trace (binaryOperator (prepared.route.leafType = .integer) operator) invalidOperand
      (CompatiblePlaceModifier.passes_of_total total _ _)
  exact ⟨prepared, replacement, finalStore, slots, represented, finalHeaps, frame, metadata, count, typed,
    lowering.symm ▸ agreement next output⟩

theorem preserves_fault_of_lower
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      output next reasonAt invalid invalidOperand missing = .ok lowered)
    {after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates actual store (lowered.rename ξ) (.inLeft output (.word invalidOperand)) store := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  rw [lowering]
  exact preserves_fault layout bare (view ▸ profile) environments heaps locals agrees slot
    (rootEq ▸ rootTyped binder binding) trace _ _ _ _

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementHeadMeaning
/-! Ordinary assignment heads instantiate concrete typed expression trees.
Seven actual temporary values are returned with their post-write typing, so a
later statement proof can insert them without changing captured closure values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

namespace Head
variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : Head readFuel values source context solved reasonAt scope administrative ambient.definitions assignment operator rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include extension valid unique uninitialized missing faithful observations environments heaps locals agrees actualTyped in
theorem preserves_prefix [FunctionCalls.FaultTokens faults] {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  have meaning : TypedGenericExpressionMeaning.Preserves (payloadModel values.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt) faults := CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    obtain ⟨_, finalStore, finalMap, finalWorld, slots, _, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
      CompatibleBareAssignment.preserves_prefix layout empty extension meaning observations right found rightView rightType profile
        environments heaps locals agrees actualTyped slot writable trace invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, by simpa [Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext, Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed, continuation⟩
  | projected layout ordinary =>
    obtain ⟨_, finalStore, finalMap, finalWorld, _, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation⟩ :=
      CompatibleRenamedPlaceSuccess.preserves_prefix layout ordinary extension meaning faithful observations right found rightView rightType profile
        environments heaps locals agrees actualTyped slot writable trace invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩

include extension valid unique uninitialized missing faithful observations environments heaps locals agrees actualTyped in
theorem preserves_fault [FunctionCalls.FaultTokens faults] (errors : head.Errors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have meaning : TypedGenericExpressionMeaning.Preserves (payloadModel values.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt) faults := CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    exact CompatibleBareAssignment.preserves_fault layout empty extension meaning observations right found rightView rightType profile
      environments heaps locals agrees actualTyped slot writable trace next output invalid errors.operands
  | projected layout ordinary =>
    exact CompatibleRenamedPlaceFaults.preserves layout ordinary extension meaning faithful observations
      errors.missing errors.uninitialized right found rightView rightType profile environments heaps locals agrees actualTyped slot writable trace next output invalid

include extension valid unique uninitialized missing faithful observations environments heaps locals agrees actualTyped in
theorem reflects [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions) (errors : head.Errors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  have preservation : TypedGenericExpressionMeaning.Preserves (payloadModel values.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt) faults := CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing
  have reflection : TypedGenericExpressionMeaning.Reflects (payloadModel values.checked registry functions) program context evidence source
      (CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt) faults := CompatibleExpressionTyped.reflects functions extension program evidence valid uninitialized missing
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    have result := CompatibleBareAssignment.reflects layout empty extension reflection observations right found rightView rightType profile
      environments heaps locals agrees actualTyped slot writable errors.operands completed
    cases result with
    | fault trace same matched finalHeaps maps worlds frame metadata => exact .inl ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩
    | success trace _ finalHeaps maps worlds frame metadata count typed continuation =>
      exact .inr ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, by simpa [Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext, Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed, continuation⟩
  | projected layout ordinary =>
    rcases CompatibleRenamedPlaceReflection.reflects layout ordinary extension reflection preservation functionTypes faithful observations
      errors.missing errors.uninitialized right found rightView rightType profile environments heaps agrees actualTyped locals slot writable completed with
      ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
      ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
    · exact .inl ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩
    · exact .inr ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
/-! Actual callable origins at compatible function leaves supply the retained
stage dispatch rows under the same ambient model. Data and heap relations keep
their original representation; source provenance comes from explicit factory
receipts and never from native callable typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
open Core Frontend SourceInference
open GeneralHeap CoreProof ReadOnly
open CompatiblePayload RecursiveNamedPreparedStageContracts

variable {checked : SourceCoreCompatibleCatalog.Checked} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}

/-- This condition records actual origin receipts only for represented function
leaves. It contains no heap relation or execution premise. -/
def FunctionOrigins (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (sidecar : SourceCoreStageContracts.Sidecar)
    (site : SourceCoreCallableContracts.Callsite) : Prop :=
  ∀ {mapping world sourceType source carrier type},
    functions.Represents registry mapping world sourceType source carrier type →
    CallableLedger.OriginRep sidecar.plan site.table source carrier

/-- Refinement affects only function leaves. Its value properties and all
world extensions are inherited from the same ambient function model. -/
def with_origins (functions : FunctionModel checked.catalog ambient)
    (sidecar : SourceCoreStageContracts.Sidecar) (site : SourceCoreCallableContracts.Callsite) :
    FunctionModel checked.catalog ambient where
  Represents registry mapping world sourceType source carrier type :=
    functions.Represents registry mapping world sourceType source carrier type ∧
      CallableLedger.OriginRep sidecar.plan site.table source carrier
  projection related := functions.projection related.1
  runtime_hasType related := functions.runtime_hasType related.1
  source_function related := functions.source_function related.1
  extend related registry maps worlds := ⟨functions.extend related.1 registry maps worlds, related.2⟩

theorem supplied_origins : FunctionOrigins (with_origins functions sidecar site) rawRegistry sidecar site :=
  fun related => related.2

/-- Forgetting provenance never strengthens a value relation. -/
theorem forget_origin {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType source carrier type) :
    functions.Represents rawRegistry mapping world sourceType source carrier type := represented.1

/-- The converse requires the static origin supply for this exact function
model. It is not inferred from a related heap or native typing. -/
theorem refinement_iff (origins : FunctionOrigins functions rawRegistry sidecar site)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty} :
    (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType source carrier type ↔
      functions.Represents rawRegistry mapping world sourceType source carrier type :=
  ⟨forget_origin, fun represented => ⟨represented, origins represented⟩⟩

theorem related_origin
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : ValueRep checked rawRegistry functions mapping world sourceType source carrier type)
    (callable : Staging.CallBoundary.UserCallable source) :
    CallableLedger.OriginRep sidecar.plan site.table source carrier := by
  induction represented using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | fixed | product | proxy | constructed | mappingValue => cases callable
  | function related => exact origins related
  | compatible _ _ ih => exact ih callable
  | nil | cons | empty | entry | absent | present => trivial

theorem covers_from_rows {call : ExpressionId} {arguments : List ExpressionId}
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (rows : CallableLedger.Rows sidecar site call arguments)
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      (CallableLedger.frame sidecar) site call arguments sourceType type := by
  intro mapping world source carrier contract represented bound
  exact CallableLedger.dispatch rows (related_origin origins represented (CallableLedger.Binds.userCallable bound)) bound

/-- The real public artifact supplies every original guard row. Only actual
function-leaf provenance remains separate from that compiler receipt. -/
theorem actual_coverage {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiled native)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      (CallableLedger.frame sidecar) site node.id arguments sourceType type :=
  covers_from_rows origins (prepared.rows issued caller contains form) sourceType type

/-- Actual source selection and descriptor preparation supply the extra
function-leaf receipt while its original code/capture relation stays explicit. -/
theorem actual_named_leaf {program : CheckedProgram}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {key : SourceCoreStageCodebook.Key} {function : Dynamic.GlobalFunction}
    (accepted : SourceCoreStageCodebook.prepareWithProjection program sidecar.plan project limits firstId = .ok site.table)
    (descriptor : SourceCoreCallableContracts.Descriptor site.table (.named key))
    (selected : SourceCompilationPlan.exactInstantiationKey sidecar.plan function.instantiation = .ok key)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {raw : Value} {type : Ty}
    (represented : functions.Represents rawRegistry mapping world sourceType (.global function)
      (.pair raw (.word descriptor.id)) type) :
    (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType (.global function)
      (.pair raw (.word descriptor.id)) type :=
  ⟨represented, RecursiveStageProjection.named_origin accepted descriptor selected raw⟩

theorem actual_lambda_origin {program : CheckedProgram}
    {plan : SourceCoreStageCodebook.Plan}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat} {table : SourceCoreStageCodebook.Table}
    {owner : SourceCoreStageCodebook.Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    {function : Dynamic.Closure} {view : TypedSource} {node : ExpressionNode}
    (accepted : SourceCoreStageCodebook.prepareWithProjection program plan project limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda owner id active))
    (receipt : LambdaSourceAlignment.SourceReceipt program plan owner active function.source)
    (metadata : LambdaMetadataViews.MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (found : view.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body) (raw : Value) :
    CallableLedger.OriginRep plan table (.closure function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨actual⟩ := RecursiveStageProjection.lambda_site_of_descriptor accepted descriptor
  have origin := LambdaMetadataViews.lambda_origin receipt actual.original metadata unique found form
  have represented := CallableLedger.OriginRep.closure (raw := raw)
    actual.member actual.origin actual.retained origin
  simpa only [actual.id_eq] using represented

abbrev actual_builtin_origin := @RecursiveStageProjection.builtin_origin


end Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementMeaning
/-! Closed assignment spines feed their actual typed temporary values to the
remaining lexical statement tree. Faults stop at the source-specified phase;
completed native execution constructs its source trace without a prior trace. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces
open TypedScopedStatements (Executes FlowRep source_view prepend head_fault terminal_intro)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)

include definitions registered extension valid uninitialized missing faithful observations in
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt context scope administrative ambient.definitions
      mode statements expected type code) (errors : Tree.Errors registry faults tree)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  induction errors generalizing mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext with
  | tail body =>
    exact body.preserves functions definitions registered extension program evidence uninitialized missing valid unique
      environments heaps locals agrees actualTyped reference read unmapped trace
  | @assign id node assignment operator rhs rest expected type body found form head remaining headErrors tailErrors ih =>
    have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
        (first : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
        (tail : Executes mode program middleContext evidence source next middle rest resultContext outcome after) :
        ∃ value finalStore finalMap finalWorld,
          Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
          FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
          HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
          LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
          AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
          TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
            context scope environment resultContext after := by
      obtain ⟨rfl, same, updated, assigned⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
      cases same
      obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
        head.preserves_prefix functions extension program evidence valid unique uninitialized missing faithful observations
          environments heaps locals agrees actualTyped assigned
      obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 tail
      exact ⟨value, finalStore, finalMap, finalWorld,
        (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩
    cases source_view trace with
    | control executed =>
      rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) executed with
        ⟨_, _, _, first, tail⟩ | ⟨first, terminal⟩
      · exact go first (by cases mode <;> exact .control tail)
      · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
        cases terminal
    | fault failed =>
      rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
        ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
      · have assigned := ScalarStatementViews.assignValue_fault unique (lookupStatement?_sound found) form first
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
          head.preserves_fault functions extension program evidence valid unique uninitialized missing faithful observations
            environments heaps locals agrees actualTyped headErrors assigned body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      · exact go first (by cases mode <;> exact .fault tail)

include definitions registered extension valid uninitialized missing faithful observations in
theorem Tree.reflects [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions)
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt context scope administrative ambient.definitions
      mode statements expected type code) (errors : Tree.Errors registry faults tree)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  induction errors generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native finalStore value with
  | tail body =>
    exact body.reflects functions definitions registered extension program evidence uninitialized missing valid
      environments heaps locals agrees actualTyped reference read unmapped evaluated
  | @assign id node assignment operator rhs rest expected type body found form head remaining headErrors tailErrors ih =>
    rcases head.reflects functions extension program evidence valid unique uninitialized missing faithful observations
      environments heaps locals agrees actualTyped functionTypes headErrors evaluated with
      ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
      ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
    · exact ⟨context, .fault reason, after, finalMap, finalWorld,
        head_fault mode rest (.assignValue (lookupStatement?_sound found) form trace), .fault matched,
        finalHeaps, maps, worlds, frame, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
          ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
      exact ⟨resultContext, outcome, after, finalMap, finalWorld,
        prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignValue (lookupStatement?_sound found) form trace) tailTrace,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩
end Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
end
