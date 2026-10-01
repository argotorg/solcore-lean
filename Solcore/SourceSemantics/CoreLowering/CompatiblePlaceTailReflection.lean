import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhsReflection
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterReflection
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCommitReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceSourceOrder

/-! Reconstruct the independent latest-root update and mapped write from a
completed compatible assignment tail. Scalar modifiers use the old snapshot;
structural reconstruction uses the post-RHS root. Actual child traces enter
only as the outputs of prefix/RHS reflection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTailReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked registry functions program context evidence source faults place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore
  | committed {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (continuation : Evaluates (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      Result checked registry functions program context evidence source faults place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore

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

/-- The profile is an explicit source scalar/equal constraint. It makes the
native-first modifier total, so a later structural fault has the same source
priority. Raw default/token metadata remain authenticated throughout. -/
theorem reflects_ready {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
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
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    {target : Dynamic.ResolvedPlace}
    (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared codes sourceTypes place leaf target
      coreEnvironment store mapping world before targetHeap)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (right : CompatiblePlaceRhsReflection.Execution compilation.checked registry functions program context evidence source faults environment
      prepared codes sourceTypes place leaf target coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : Evaluates (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
      (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
      (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults place operator rhs environment coreEnvironment
      before store mapping world next outputType result finalStore := by
  have rhsTrace : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right.right right.heap := by
    cases right.meaning.trace with | value trace => exact trace
  have snapshotRep := right.meaning.saved_snapshot
  have keyRep := resolution.keysRelated.extend right.meaning.maps right.meaning.worlds
  have reference := resolution.reference.extend right.meaning.maps right.meaning.worlds
  have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have targetType := (resolved_type sourceTrace resolution.currentRead).trans resolution.currentType
  obtain ⟨latest⟩ := right.meaning.latest
  have cellType : latest.cell.type = target.rootType := latest.type.trans targetType.symm
  obtain ⟨replacement, replacementValue, replacementRep, applied, modified, _⟩ :=
    CompatiblePlaceModifier.initialized_success observations profile snapshotRep right.related
      (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) right.value coreEnvironment)
      (.var (index := 1) rfl) (.var (index := 0) rfl) right.store invalid
  cases completed with
  | caseLeft modifiedEvaluated failed =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic modifiedEvaluated modified
    cases impossible
  | caseRight modifiedEvaluated remaining =>
    obtain ⟨same, storeEq⟩ := evaluation_deterministic modifiedEvaluated modified
    cases same
    subst_vars
    have typedEnvironment : RuntimeEnvironmentHasTypes right.world
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) right.value replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons right.related.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          ((environments.extend (resolution.maps.trans right.meaning.maps) (resolution.worlds.trans right.meaning.worlds)).runtime_hasTypes)))))
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
        typedEnvironment layout.setterTyped (.var rfl) (.var rfl) (.var rfl) ran
    cases remaining with
    | caseLeft setterEvaluated failed =>
      obtain ⟨futureWorld, _, represented, finalHeaps, extension, frame, _⟩ := reflectSetter setterEvaluated
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
      | uninitialized empty notMapping nonempty =>
        have absent := absent_initial latest.related empty notMapping
        exact (DataPlaceSourceOrder.latest_uninitialized_impossible sourceTrace rhsTrace latest.read cellType absent nonempty).elim
    | caseRight setterEvaluated remaining =>
      rename_i helperStore helperType updatedValue
      obtain ⟨futureWorld, _, represented, helperHeaps, extension, helperFrame, _⟩ := reflectSetter setterEvaluated
      cases represented with
      | updated root changed updatedRep =>
        cases remaining with
        | letE writeEvaluated continuation =>
          obtain ⟨after, resultEq, sourceWritten, finalHeaps, writeFrame, metadata, _⟩ :=
            CompatiblePlaceCommitReflection.reflects_storeCell helperHeaps (reference.extend (.refl _) extension) latest.read
              updatedRep (.var (index := 5) rfl) (.var (index := 0) rfl) writeEvaluated
          subst_vars
          have changed := DataPlaceCommitReflection.update_of_replacement changed (fun _ => resolution.selectedEq.symm ▸ applied)
          exact .committed (.intro sourceTrace rhsTrace (.intro latest.read cellType root changed sourceWritten))
            finalHeaps (resolution.maps.trans right.meaning.maps) ((resolution.worlds.trans right.meaning.worlds).trans extension)
            (((resolution.frame.trans right.meaning.frame).trans helperFrame).trans writeFrame)
            ((resolution.metadata.trans right.meaning.metadata).trans metadata) (slots :=
              [.unit, updatedValue, replacementValue, right.value, .inRight .unit resolution.snapshot, packValues resolution.values,
                .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) rfl continuation

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTailReflection
