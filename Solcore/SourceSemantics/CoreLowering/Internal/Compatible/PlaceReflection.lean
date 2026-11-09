import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive

/-!
# Compatible places: reflection

Reflection of right-hand sides, setters, tails and lowering, with place certificates.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhsReflection
/-! Reflect the real three-slot RHS continuation after target resolution.
The source RHS outcome, latest heap and four-slot modifier continuation are
outputs obtained from the universal expression induction hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhsReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

def remainder (prepared : Prepared) (keyType : Ty) (next : Expr) (outputType : Ty)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) : Expr :=
  LanguageResult.bind outputType
    (modified prepared.route.leafType operator false (.var 1) (.var 0) invalid)
    (LanguageResult.bind outputType
      (.apply (setter prepared keyType) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (Frontend.SourceCoreDataPlaces.guard outputType operator
        (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next))))

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (environment : Dynamic.Environment) (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr)
    (sourceTypes : List TypeSystem.Ty) (place : PlaceResolution) (leaf : TypeSystem.Ty)
    (target : Dynamic.ResolvedPlace) (coreEnvironment : Environment)
    (initialStore : Store) (initialMap : LocationMap) (initialWorld : StoreTyping) (before targetHeap : Dynamic.Heap)
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr) where
  right : Dynamic.Value
  value : Value
  heap : Dynamic.Heap
  store : Store
  mapping : LocationMap
  world : StoreTyping
  meaning : CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := evidence) (source := source)
    (faults := faults) resolution id node lowered environment (.value right) heap (.inRight .word value) store mapping world
  related : ValueRep checked registry functions mapping world leaf right value prepared.route.leafType

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr) (next : Expr) (outputType : Ty)
    (operator : Syntax.ValueAssignOp) (invalid : Word) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore
  | ready {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
      (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
      (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap)
      (right : Execution checked registry functions program context evidence source faults environment prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
      (continuation : Evaluates (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
        (remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
      Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore

/-- Source and Core RHS types are connected by the retained raw runtime view,
not by inverting the many-to-one native type projection. -/
theorem reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (meaning : Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (coreType : lowered.type = prepared.route.leafType)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {next : Expr} {outputType : Ty} {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value}
    (resolution : CompatiblePlacePrefixReflection.Result checked registry functions program context evidence source faults prepared codes sourceTypes
      place leaf environment coreEnvironment before store mapping world lowered.expression next outputType
      (binaryOperator (prepared.route.leafType = .integer) operator) false invalid result finalStore) :
    Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
      coreEnvironment before store mapping world id node lowered next outputType operator invalid result finalStore := by
  cases resolution with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault (.target sourceFault) resultEq tokenRep heaps maps worlds frame metadata
  | resolved sourceTrace resolution remaining =>
    cases remaining with
    | caseLeft rhsEvaluated failed =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, rhsResult⟩ :=
        CompatiblePlaceRhs.reflects resolution meaning generated found environments locals rhsEvaluated
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
        CompatiblePlaceRhs.reflects resolution meaning generated found environments locals rhsEvaluated
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
            related := .compatible rhsView (by simpa only [payloadModel, coreType] using payload) } remaining

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhsReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterReflection
/-! Every actual completed live compatible setter has an independent source
update, exact raw missing-default fault, or absent-root fault. The source outcome
is constructed from static path/authentication receipts and the common heap;
no source update trace or helper execution is supplied by the caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open CompatibleMapping CompatibleMapping.MixedPaths SourceCoreCompatibleDataPlaces

inductive ResultRep (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (cell : Dynamic.Cell) (resolved : List Dynamic.EvaluatedProjection)
    (replacement : Dynamic.Value) : Value → Prop where
  | updated {sourceRoot updated : Dynamic.Value} {native : Value}
      (initial : Dynamic.RootInitialValue cell (some sourceRoot))
      (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacement) (some sourceRoot) resolved updated)
      (represented : ValueRep checked registry functions mapping world cell.type updated native prepared.route.rootType) :
      ResultRep checked registry functions mapping world prepared cell resolved replacement (.inRight .word native)
  | missing {sourceRoot : Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
      (initial : Dynamic.RootInitialValue cell (some sourceRoot))
      (fault : Dynamic.ProjectionsFaults (some sourceRoot) resolved reason)
      (receipt : FaultToken checked registry sourceRoot prepared.steps resolved reason token count) :
      ResultRep checked registry functions mapping world prepared cell resolved replacement (.inLeft prepared.route.rootType (.word token))
  | uninitialized
      (empty : cell.value = none)
      (ordinary : ¬ ∃ key value, cell.type = .mapping key value)
      (nonempty : resolved ≠ []) :
      ResultRep checked registry functions mapping world prepared cell resolved replacement (.inLeft prepared.route.rootType (.word prepared.invalidProjection))

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {prepared : Prepared}
  {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell}
  {projections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
  {path : PreparedPath compilation.checked source site cell.type projections position prepared.steps keySites leaf}
  {keys : List Value} {resolved : List Dynamic.EvaluatedProjection}
  {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression replacementExpression : Expr}
  {replacement : Dynamic.Value} {replacementValue : Value}
  {identities : Dynamic.Value → Word → Prop}

private theorem present_evaluates
    {optional rootValue : Value} {sourceRoot : Dynamic.Value}
    (root : RootRead compilation.checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (replacementRep : ValueRep compilation.checked registry functions mapping world leaf replacement replacementValue prepared.route.leafType)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    (replacementSelected : DataEquality.Selects environment replacementExpression replacementValue) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved replacement result ∧
      HeapRepresents compilation.checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  rcases CompatiblePlaceReadTotality.read_or_fault arguments functionTypes root.payload replacementRep.projection with
      ⟨selected, _, read, _⟩ | ⟨reason, fault⟩
  · obtain ⟨updated, changed⟩ := DataPlaceUpdateTotality.read_update read replacement
    have tree := arguments.updateTree root.payload replacementRep changed prepared
    obtain ⟨native, after, administrative, represented, evaluated, appended, _⟩ :=
      CompatiblePlaceWriteback.setter_at root tree nonempty faithful observations keyLength environment keyType
        referenceExpression keyExpression replacementExpression referenceSelected keysSelected replacementSelected
    obtain ⟨futureWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := mapping) heaps.runtime_hasTypes environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated,
      .updated root.input.initial changed (represented.extend (.refl _) (.refl _) extension),
      CompatibleHeap.HeapRepresents.after_snapshot heaps extension typedStore appended, extension, frame, appended⟩
  · obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
    obtain ⟨after, administrative, evaluated, appended, _⟩ :=
      CompatiblePlaceSetterFault.setter_at root tree nonempty faithful observations keyLength environment keyType
        referenceExpression keyExpression replacementExpression replacementValue referenceSelected keysSelected replacementSelected
    obtain ⟨futureWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := mapping) heaps.runtime_hasTypes environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated, .missing root.input.initial fault receipt,
      CompatibleHeap.HeapRepresents.after_snapshot heaps extension typedStore appended, extension, frame, appended⟩

private theorem resolved_nonempty
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (nonempty : prepared.steps ≠ []) : resolved ≠ [] := by
  have general : ∀ {root leaf projections position steps sites}
      {path : PreparedPath compilation.checked source site root projections position steps sites leaf} {resolved},
      Arguments compilation.checked registry functions mapping world source site keys path resolved → steps.length = resolved.length := by
    intro root leaf projections position steps sites path resolved arguments
    induction arguments with
    | nil => rfl
    | member _ ih | index _ _ _ ih => exact congrArg Nat.succ ih
  have length := general arguments
  intro empty
  rw [empty, List.length_nil] at length
  exact nonempty (List.eq_nil_of_length_eq_zero length)

/-- Construct finite execution of the real live setter, including its source
classification and any administrative suffix, from authenticated live inputs. -/
theorem evaluates
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (replacementRep : ValueRep compilation.checked registry functions mapping world leaf replacement replacementValue prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    (replacementSelected : DataEquality.Selects environment replacementExpression replacementValue) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved replacement result ∧
      HeapRepresents compilation.checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨optional, native, represented⟩ := CompatibleHeap.HeapRepresents.read_at heaps reference read
  cases represented with
  | initialized related =>
    exact present_evaluates (.initialized read reference native related) arguments replacementRep nonempty functionTypes
      faithful observations keyLength heaps environmentTyped helperTyped referenceSelected keysSelected replacementSelected
  | @uninitialized sourceType payload projected =>
    by_cases mappingRoot : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingRoot
      obtain ⟨rootValue, root⟩ := RootRead.virtual (virtual key value rfl) registryExtension projected read reference native
      exact present_evaluates root arguments replacementRep nonempty functionTypes faithful observations keyLength
        heaps environmentTyped helperTyped referenceSelected keysSelected replacementSelected
    · have noVirtual := ordinary (fun key value same => mappingRoot ⟨key, value, same⟩)
      have evaluated : Evaluates environment store (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
          (.inLeft prepared.route.rootType (.word prepared.invalidProjection)) store := by
        apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) native) (.pair (keysSelected.evaluates store) (replacementSelected.evaluates store)))
        cases steps : prepared.steps with
        | nil => exact (nonempty steps).elim
        | cons head tail =>
          simp only [normalizeRoot, noVirtual, LanguageResult.failure]
          exact .caseLeft (.first (.var rfl)) (.inLeft .word)
      exact ⟨_, store, world, [], evaluated, .uninitialized rfl mappingRoot (resolved_nonempty arguments nonempty),
        heaps, .refl _, .refl _ _, by simp⟩

/-- Actual completed native execution determines an independent source
outcome without a prior source trace or a helper-execution certificate. -/
theorem reflects
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (replacementRep : ValueRep compilation.checked registry functions mapping world leaf replacement replacementValue prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    (replacementSelected : DataEquality.Selects environment replacementExpression replacementValue)
    {result : Value} {after : Store}
    (completed : Evaluates environment store (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))) result after) :
    ∃ futureWorld administrative,
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved replacement result ∧
      HeapRepresents compilation.checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨actual, actualStore, futureWorld, administrative, evaluated, resultRep, heaps, worlds, frame, appended⟩ :=
    evaluates arguments replacementRep virtual ordinary registryExtension nonempty functionTypes faithful observations keyLength
      heaps reference read environmentTyped helperTyped referenceSelected keysSelected replacementSelected
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
  exact ⟨futureWorld, administrative, resultRep, heaps, worlds, frame, appended⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTailReflection
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
    [FunctionCalls.FaultTokens faults] {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
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
  obtain ⟨replacement, replacementValue, replacementRep, modified, outcome⟩ :=
    CompatiblePlaceModifier.initialized_outcome observations profile snapshotRep right.related
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
        rcases SourceCoreDataPlaces.guard_inv remaining with ⟨passes, remaining⟩ | ⟨operation, selected, zero, resultEq, storeEq⟩
        · rcases outcome with ⟨applied, _⟩ | ⟨operation, selected, zero, _⟩
          · cases remaining with
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
            exact .fault (.panic sourceTrace rhsTrace latest.read cellType root read panicked) rfl
              (FunctionCalls.FaultTokens.panic _) helperHeaps (resolution.maps.trans right.meaning.maps)
              ((resolution.worlds.trans right.meaning.worlds).trans extension)
              ((resolution.frame.trans right.meaning.frame).trans helperFrame)
              (resolution.metadata.trans right.meaning.metadata)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTailReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates
/-! Actual compatible place lowering receipts. These follow production Except
branches and reuse the common child/key certificate relations. The compiler is
not duplicated, and no source or native evaluation is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues
open DataPlaceCertificates CompatibleMixedRoute

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

inductive Generated (compilation : SourceCoreCompatibleDataPlaces.Context) (signatures : ProgramSignatures) (expression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : Option ExpressionId)
    (outputType : Ty) (next : Expr) (reasonAt : ExpressionId → Word)
    (invalidProjection invalidOperand : Word) (missing : TypeSystem.Ty → Word) : Expr → Prop where
  | intro (route : Route) (prepared : Prepared) (index : Nat)
      (keys : List SourceCoreBasic.LoweredExpr) (value : Expr)
      (described : describe compilation signatures source site assignment = .ok route)
      (lookup : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, route.rootType))
      (preparedBy : prepare compilation fuel route invalidProjection missing = .ok prepared)
      (keysGenerated : ListRel (KeyGenerated expression fuel source scope reasonAt) prepared.keys keys)
      (operatorValid : operator = .equal ∧ rhs.isNone = false ∨ route.leafType = .word ∨ route.leafType = Core.Ty.integer ∧ operator.wordOnly = false)
      (rhsGenerated : RhsGenerated expression fuel source scope reasonAt route.leafType rhs value) :
      Generated compilation signatures expression fuel source scope site assignment operator rhs outputType next
        reasonAt invalidProjection invalidOperand missing
        (execute prepared (.var index) (SourceCoreCalls.packArguments keys) value next outputType
          (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)

/-- The receipt follows actual successful compiler branches. It does not
replace or reinterpret the executable place compiler. -/
theorem generated_of_lower {compilation : SourceCoreCompatibleDataPlaces.Context} {signatures : ProgramSignatures} {expression : ExpressionLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {outputType : Ty} {next : Expr} {reasonAt : ExpressionId → Word}
    {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word} {lowered : Expr}
    (accepted : lower compilation signatures expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand missing = .ok lowered) :
    Generated compilation signatures expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand missing lowered := by
  unfold lower at accepted
  obtain ⟨route, described, accepted⟩ := bind_ok accepted
  cases lookup : SourceCoreLocalCell.lookup? scope assignment.target.root with
  | none => simp [lookup, throw, bind, Except.bind] at accepted
  | some pair =>
    obtain ⟨index, storedType⟩ := pair
    simp only [lookup, pure, Except.pure, bind, Except.bind] at accepted
    cases typed : SourceCoreBasic.ensureType site route.rootType storedType with
    | error error => simp [typed] at accepted
    | ok checkedUnit =>
      cases checkedUnit
      have types := ensureType_ok typed
      subst storedType
      simp only [typed] at accepted
      obtain ⟨prepared, preparedBy, accepted⟩ := bind_ok accepted
      obtain ⟨keys, keysCompiled, accepted⟩ := bind_ok accepted
      have keyCertificate := keys_generated keysCompiled
      have finish (operatorValid : operator = .equal ∧ rhs.isNone = false ∨ route.leafType = .word ∨ route.leafType = Core.Ty.integer ∧ operator.wordOnly = false)
          (completed : (show Except SourceCoreBasic.Error Expr from match rhs with
            | none => .ok (execute prepared (.var index) (SourceCoreCalls.packArguments keys)
                (LanguageResult.success .unit) next outputType
                (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)
            | some id => do
                let value ← expression fuel source scope id reasonAt
                SourceCoreBasic.ensureType site route.leafType value.type
                pure (execute prepared (.var index) (SourceCoreCalls.packArguments keys) value.expression next outputType
                  (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)) = .ok lowered) :
          Generated compilation signatures expression fuel source scope site assignment operator rhs outputType next
            reasonAt invalidProjection invalidOperand missing lowered := by
        cases rhs with
        | none =>
          simp only [Except.ok.injEq] at completed
          subst lowered
          exact .intro route prepared index keys _ described lookup preparedBy keyCertificate operatorValid .absent
        | some id =>
          obtain ⟨value, valueCompiled, completed⟩ := bind_ok completed
          obtain ⟨checkedUnit, typeChecked, completed⟩ := bind_ok completed
          cases checkedUnit
          simp only [pure, Except.pure, Except.ok.injEq] at completed
          subst lowered
          exact .intro route prepared index keys _ described lookup preparedBy keyCertificate operatorValid
            (.present valueCompiled (ensureType_ok typeChecked))
      by_cases same : operator = .equal
      · cases rhs with
        | none =>
          by_cases word : route.leafType = .word
          · apply finish (.inr (.inl word)); simpa [same, word, pure, Except.pure, bind, Except.bind] using accepted
          · by_cases integer : route.leafType = Core.Ty.integer
            · apply finish (.inr (.inr ⟨integer, by rw [same]; rfl⟩))
              simpa [same, integer, Syntax.ValueAssignOp.wordOnly, pure, Except.pure, bind, Except.bind] using accepted
            · simp [same, word, integer, throw] at accepted
        | some id =>
          apply finish (.inl ⟨same, rfl⟩)
          simpa [same, pure, Except.pure, bind, Except.bind] using accepted
      · by_cases word : route.leafType = .word
        · apply finish (.inr (.inl word)); cases rhs <;> simpa [same, word, pure, Except.pure, bind, Except.bind] using accepted
        · by_cases integer : route.leafType = Core.Ty.integer
          · cases shift : operator.wordOnly
            · apply finish (.inr (.inr ⟨integer, shift⟩))
              cases rhs <;> simpa [same, integer, shift, pure, Except.pure, bind, Except.bind] using accepted
            · simp [same, integer, shift, throw] at accepted
          · simp [same, word, integer, throw] at accepted


theorem PreparedPath.key_ids {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) :
    keys.map Prod.fst = DataPlaceKeyOrder.sourceKeys projections := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih => exact ih
  | index _ _ _ ih => exact congrArg (List.cons _) ih

theorem PreparedPath.steps_length {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) : steps.length = projections.length := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih | index _ _ _ ih => exact congrArg Nat.succ ih

/-- Ordered child certificates come from the actual mapM receipt and path
occurrences, so repeated index occurrences remain repeated evaluations. -/
theorem tree_of_keys {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {expression : ExpressionLowerer} {fuel : Nat} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code) :
    ∃ types, DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes ∧
      keys.map Prod.snd = codes.map (·.type) := by
  have collect : ∀ {keys codes}, ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes →
      ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code)
        (keys.map Prod.fst) codes ∧ keys.map Prod.snd = codes.map (·.type) := by
    intro keys codes generated
    induction generated with
    | nil => exact ⟨.nil, rfl⟩
    | cons head tail ih => exact ⟨.cons (extract _ _ head.1) ih.1, by simp only [List.map_cons, head.2, ih.2]⟩
  have receipts := collect generated
  obtain ⟨types, tree⟩ := DataExpressionSequence.Tree.of_children receipts.1
  rw [PreparedPath.key_ids path] at tree
  exact ⟨types, tree, receipts.2⟩

/-- The checked wrapper retains the exact accepted production lowering. Its
public typed field refers to the caller's actual definitions and context. -/
theorem lower_of_lowerChecked {compilation : SourceCoreCompatibleDataPlaces.Context} {signatures : ProgramSignatures}
    {expression : ExpressionLowerer} {fuel : Nat} {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {outputType : Ty} {next : Expr} {reasonAt : ExpressionId → Word}
    {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word} {definitions : DataEnvironment} {environment : Core.Context}
    {certified : Certified definitions environment outputType}
    (accepted : lowerChecked compilation signatures expression fuel source scope site assignment operator rhs outputType next reasonAt
      invalid invalidOperand missing definitions environment = .ok certified) :
    lower compilation signatures expression fuel source scope site assignment operator rhs outputType next reasonAt
      invalid invalidOperand missing = .ok certified.expression := by
  unfold lowerChecked at accepted
  obtain ⟨expression, generated, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted; exact generated
  · cases accepted

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentReflection
/-! Whole emitted compatible assignment reflection, from static layout receipts
and the universal child expression IH. Target, RHS, modifier, setter and write
executions are recovered here; no prior source execution or runtime helper
certificate is required. The remaining statement continuation is an output. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentReflection
open Core Frontend SourceInference GeneralHeap GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces

theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
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
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
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
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid) result finalStore) :
    CompatiblePlaceTailReflection.Result compilation.checked registry functions program context evidence source faults place operator rhs
      environment coreEnvironment before store mapping world next outputType result finalStore := by
  have resolution := CompatiblePlacePrefixReflection.reflects layout ordinary registryExtension meaning functionTypes faithful observations
    missingTokens invalidTokens environments heaps locals slot rootTyped completed
  have rhs := CompatiblePlaceRhsReflection.reflects meaning rhsGenerated found rhsView rhsCoreType environments locals resolution
  cases rhs with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault sourceFault resultEq tokenRep heaps maps worlds frame metadata
  | ready sourceTrace resolution right continuation =>
    exact CompatiblePlaceTailReflection.reflects_ready layout ordinary registryExtension functionTypes faithful observations missingTokens
      operatorProfile environments sourceTrace resolution right continuation

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLayoutCertificates
/-! Static assignment layouts from actual compatible compilation and the final
Core checker. Independent retained source typing supplies raw key/leaf views;
child compiler typing supplies the RHS's exact binder type. No semantic child
execution, helper execution, or source/native type injectivity is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLayoutCertificates
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues
open DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates

/-- The actual path, retained source typing and final Core checker discharge
all fields of the semantic Layout. The RHS typing is a static child-compiler
obligation under the original context. -/
theorem of_describe_prepare {compilation : SourceCoreCompatibleDataPlaces.Context} {definitions : DataEnvironment}
    {source : TypedSource} {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route} {prepared : Prepared}
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word}
    {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    {administrativeContext : Core.Context} {reference rhs next : Expr} {outputType resultType : Ty}
    {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand : Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (nonempty : assignment.target.projections ≠ [])
    (described : describe compilation compilation.checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation fuel route invalid missing = .ok prepared)
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) prepared.keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      (execute prepared reference (SourceCoreCalls.packArguments codes) rhs next outputType operator bitNot invalidOperand)
      resultType definitions)
    (rhsTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) rhs
      (LanguageResult.resultType prepared.route.leafType) definitions) :
    ∃ binder leaf sourceTypes,
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType assignment.target.type ∧
      CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) compilation source certificate scope site assignment.target prepared codes sourceTypes leaf administrativeContext ∧
      ((∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none) := by
  obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
  obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
  obtain ⟨sourceTypes, tree, keyTypes⟩ := tree_of_keys path generated extract
  obtain ⟨views, leafView⟩ := CompatiblePlaceKeyTyping.of_typing unique signatures path rfl (sourceTyped binder description.binding) tree
  have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
  have actualPath : PreparedPath compilation.checked source site prepared.route.rootSourceType assignment.target.projections
      0 prepared.steps prepared.keys leaf := rootEq ▸ path
  refine ⟨binder, leaf, sourceTypes, description.binding, rootEq, leafView, ?_, ?_⟩
  · refine ⟨actualPath, by simpa only [rootEq] using views, tree, keyTypes, ?_, ?_, ?_,
      CompatiblePlaceHelperTyping.getter_of_execute typed,
      CompatiblePlaceHelperTyping.setter_of_execute typed (CompatiblePlaceHelperTyping.rhs_shift_typed rhsTyped)⟩
    · rw [← compilation.checked.catalog.project_runtimeType leaf, description.selectedType,
        compilation.checked.catalog.project_runtimeType, routeEq]
      exact description.leafProjected
    · intro k v declared
      rw [routeEq]
      exact description.virtual k v (rootEq.symm.trans declared)
    · intro empty
      have length := PreparedPath.steps_length path
      rw [empty, List.length_nil] at length
      exact nonempty (List.eq_nil_of_length_eq_zero length.symm)
  · intro notMapping
    rw [routeEq]
    exact description.ordinary (fun k v same => notMapping k v (rootEq.trans same))

/-- A real successful lower call with an explicit RHS yields the execution
shape, all helper typing, exact child compiler receipt and raw RHS view.
Independent source typing is retained explicitly until the enclosing checked
statement induction supplies it. -/
theorem of_lower {compilation : SourceCoreCompatibleDataPlaces.Context} {definitions : DataEnvironment}
    {source : TypedSource} {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {fuel : Nat} {expression : ExpressionLowerer} {scope : Scope}
    {reasonAt : ExpressionId → Word} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {next lowered : Expr} {outputType resultType : Ty} {invalid invalidOperand : Word}
    {missing : TypeSystem.Ty → Word} {certificate : GenericExpressionMeaning.Certificate} {administrativeContext : Core.Context}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (nonempty : assignment.target.projections ≠ [])
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code.expression (LanguageResult.resultType code.type)
        definitions)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator (some rhs) outputType
      next reasonAt invalid invalidOperand missing = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered resultType definitions) :
    ∃ binder leaf prepared codes sourceTypes index right node,
      (∃ route, describe compilation compilation.checked.signatures source site assignment = .ok route ∧
        prepare compilation fuel route invalid missing = .ok prepared) ∧
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType) ∧
      CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) compilation source certificate scope site assignment.target prepared codes sourceTypes leaf administrativeContext ∧
      ((∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none) ∧
      expression fuel source scope rhs reasonAt = .ok right ∧
      source.lookupExpression? rhs = some node ∧ certificate scope rhs right ∧
      SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type ∧
      right.type = prepared.route.leafType ∧
      lowered = execute prepared (.var index) (SourceCoreCalls.packArguments codes) right.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand := by
  have receipt := CompatiblePlaceCompilerCertificates.generated_of_lower accepted
  cases receipt with
  | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | @present id right rhsGenerated rhsType =>
      obtain ⟨node, found, certified, rhsTyped⟩ := extract rhs right rhsGenerated
      have routeEq := (CompatibleMixedPreparation.of_prepare preparedBy).1
      have rhsType : right.type = prepared.route.leafType := by simpa only [routeEq] using rhsType.symm
      obtain ⟨binder, leaf, sourceTypes, binding, rootEq, leafView, layout, ordinary⟩ :=
        of_describe_prepare unique signatures sourceTyped nonempty described preparedBy generated
          (fun id code compiled => let ⟨node, found, certified, _⟩ := extract id code compiled; ⟨node, found, certified⟩)
          typed (by simpa only [rhsType] using rhsTyped)
      obtain ⟨typedNode, contains, nodeType⟩ := rightTyped.stored_type
      have same := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
      have nodeType : node.type = assignment.target.type := by simpa only [same] using nodeType
      exact ⟨binder, leaf, prepared, codes, sourceTypes, index, right, node, ⟨route, described, preparedBy⟩, binding, rootEq,
        by simpa only [routeEq] using lookup, layout, ordinary, rhsGenerated, found, certified,
        by simpa only [nodeType] using leafView, rhsType, by simp [routeEq]⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLayoutCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges
/-! Static range receipts follow actual allocation and reuse of diagnostic
reasons. The original preparation performs each checked conversion. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingDiagnosticAssociation

private structure Bounds (capacity next : Nat) (bases blocked : List Word) : Prop where
  positive : ∀ base, base ∈ bases → 0 < base.val
  reserved : ∀ base, base ∈ bases → base.val + capacity < wordModulus
  issued : ∀ base, base ∈ bases → base.val + capacity < next
  blockedBelow : ∀ token, token ∈ blocked → token.val < next
  separated : ∀ left, left ∈ bases → ∀ right, right ∈ bases →
    left = right ∨ left.val + capacity < right.val ∨ right.val + capacity < left.val
  outside : ∀ base, base ∈ bases → ∀ token, token ∈ blocked →
    token.val ≤ base.val ∨ base.val + capacity < token.val

private theorem Bounds.mono {capacity next : Nat} {bases blocked : List Word}
    (bounds : Bounds capacity next bases blocked) {later : Nat} (grows : next ≤ later)
    {otherBases otherBlocked : List Word}
    (sameBases : ∀ base, base ∈ otherBases ↔ base ∈ bases)
    (sameBlocked : ∀ token, token ∈ otherBlocked ↔ token ∈ blocked) :
    Bounds capacity later otherBases otherBlocked := by
  refine ⟨fun base member => bounds.positive base ((sameBases base).mp member),
    fun base member => bounds.reserved base ((sameBases base).mp member),
    ?_, ?_, ?_, ?_⟩
  · intro base member
    have issued := bounds.issued base ((sameBases base).mp member)
    omega
  · intro token member
    have issued := bounds.blockedBelow token ((sameBlocked token).mp member)
    omega
  · intro left leftMember right rightMember
    exact bounds.separated left ((sameBases left).mp leftMember) right ((sameBases right).mp rightMember)
  · intro base baseMember token tokenMember
    exact bounds.outside base ((sameBases base).mp baseMember) token ((sameBlocked token).mp tokenMember)

private theorem Bounds.range {capacity next : Nat} {bases blocked : List Word}
    (bounds : Bounds capacity next bases blocked) (positive : 0 < next)
    {reason : Word} (number : reason.val = next) (reserved : next + capacity < wordModulus)
    {otherBases : List Word} (members : ∀ base, base ∈ otherBases ↔ base ∈ bases ∨ base = reason) :
    Bounds capacity (next + capacity + 1) otherBases blocked := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro base member
    rcases (members base).mp member with old | rfl
    · exact bounds.positive base old
    · omega
  · intro base member
    rcases (members base).mp member with old | rfl
    · exact bounds.reserved base old
    · omega
  · intro base member
    rcases (members base).mp member with old | rfl
    · have issued := bounds.issued base old; omega
    · omega
  · intro token member
    have issued := bounds.blockedBelow token member; omega
  · intro left leftMember right rightMember
    rcases (members left).mp leftMember with leftOld | rfl
    · rcases (members right).mp rightMember with rightOld | rfl
      · exact bounds.separated left leftOld right rightOld
      · exact .inr (.inl (by have issued := bounds.issued left leftOld; omega))
    · rcases (members right).mp rightMember with rightOld | rfl
      · exact .inr (.inr (by have issued := bounds.issued right rightOld; omega))
      · exact .inl rfl
  · intro base baseMember token tokenMember
    rcases (members base).mp baseMember with old | rfl
    · exact bounds.outside base old token tokenMember
    · exact .inl (by have issued := bounds.blockedBelow token tokenMember; omega)

private theorem Bounds.fixed {capacity next : Nat} {bases blocked : List Word}
    (bounds : Bounds capacity next bases blocked) {reason : Word} (number : reason.val = next)
    {otherBlocked : List Word} (members : ∀ token, token ∈ otherBlocked ↔ token ∈ blocked ∨ token = reason) :
    Bounds capacity (next + 1) bases otherBlocked := by
  refine ⟨bounds.positive, bounds.reserved, ?_, ?_, bounds.separated, ?_⟩
  · intro base member
    have issued := bounds.issued base member; omega
  · intro token member
    rcases (members token).mp member with old | rfl
    · have issued := bounds.blockedBelow token old; omega
    · omega
  · intro base baseMember token tokenMember
    rcases (members token).mp tokenMember with old | rfl
    · exact bounds.outside base baseMember token old
    · exact .inr (by have issued := bounds.issued base baseMember; omega)

private def bases (indices : List SourceCoreDataFaultSites.IndexSite)
    (places : List SourceCoreDataPlaceFaultSites.Site) : List Word :=
  indices.map (·.reason) ++ places.filterMap (fun place => place.missingType.map (fun _ => place.reason))

private structure Inventory (capacity next : Nat) (indices : List SourceCoreDataFaultSites.IndexSite)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite)
    (blocked : List Word) : Prop where
  positive : 0 < next
  bounds : Bounds capacity next (bases indices places) blocked
  missing : ∀ site, site ∈ missing → site.base ∈ bases indices places

private theorem Inventory.mono {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked)
    {later : Nat} (grows : next ≤ later) : Inventory capacity later indices places missing blocked := by
  exact ⟨by have := inventory.positive; omega,
    inventory.bounds.mono grows (fun _ => Iff.rfl) (fun _ => Iff.rfl), inventory.missing⟩

private theorem Inventory.append_missing {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked) {site : MissingSite}
    (issued : site.base ∈ bases indices places) :
    Inventory capacity next indices places (missing ++ [site]) blocked := by
  refine ⟨inventory.positive, inventory.bounds, ?_⟩
  intro current member
  rcases List.mem_append.mp member with old | fresh
  · exact inventory.missing current old
  · exact List.mem_singleton.mp fresh ▸ issued

private theorem Inventory.index_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked) {index : SourceCoreDataFaultSites.IndexSite}
    (number : index.reason.val = next) (reserved : next + capacity < wordModulus) :
    Inventory capacity (next + capacity + 1) (indices ++ [index]) places missing blocked := by
  have members : ∀ base, base ∈ bases (indices ++ [index]) places ↔ base ∈ bases indices places ∨ base = index.reason := by
    intro base
    simp only [bases, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    grind
  refine ⟨by omega, inventory.bounds.range inventory.positive number reserved members, ?_⟩
  intro site member
  exact (members site.base).mpr (.inl (inventory.missing site member))

private theorem Inventory.place_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked) {place : SourceCoreDataPlaceFaultSites.Site}
    {type : TypeSystem.Ty} (kind : place.missingType = some type)
    (number : place.reason.val = next) (reserved : next + capacity < wordModulus) :
    Inventory capacity (next + capacity + 1) indices (places ++ [place]) missing blocked := by
  have members : ∀ base, base ∈ bases indices (places ++ [place]) ↔ base ∈ bases indices places ∨ base = place.reason := by
    intro base
    simp only [bases, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, kind, Option.map_some,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    grind
  refine ⟨by omega, inventory.bounds.range inventory.positive number reserved members, ?_⟩
  intro site member
  exact (members site.base).mpr (.inl (inventory.missing site member))

private theorem Inventory.place_fixed {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked) {place : SourceCoreDataPlaceFaultSites.Site}
    (kind : place.missingType = none) (number : place.reason.val = next) :
    Inventory capacity (next + 1) indices (places ++ [place]) missing (blocked ++ [place.reason]) := by
  have same : bases indices (places ++ [place]) = bases indices places := by
    simp only [bases, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, kind, Option.map_none,
      List.append_nil]
  refine ⟨by omega, ?_, ?_⟩
  · rw [same]
    exact inventory.bounds.fixed number (fun _ => by simp only [List.mem_append, List.mem_singleton])
  · rw [same]
    exact inventory.missing

private theorem Inventory.reused_index {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (_inventory : Inventory capacity next indices places missing blocked) {index : SourceCoreDataFaultSites.IndexSite}
    (member : index ∈ indices) : index.reason ∈ bases indices places := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨index, member, rfl⟩)

private theorem Inventory.reused_place {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (_inventory : Inventory capacity next indices places missing blocked) {place : SourceCoreDataPlaceFaultSites.Site}
    (member : place ∈ places) {type : TypeSystem.Ty} (kind : place.missingType = some type) :
    place.reason ∈ bases indices places := by
  apply List.mem_append_right
  apply List.mem_filterMap.mpr
  exact ⟨place, member, by simp only [kind, Option.map_some]⟩

private theorem foldl_max_initial (values : List Nat) (start : Nat) : start ≤ values.foldl max start := by
  induction values generalizing start with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem foldl_max_member (values : List Nat) {value : Nat} (member : value ∈ values) (start : Nat) :
    value ≤ values.foldl max start := by
  induction values generalizing start with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_initial tail _)
    · exact ih member _

private theorem word_number {number : Nat} {reason : Word}
    (accepted : (match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok reason) :
    reason.val = number := by
  split at accepted
  · rename_i converted
    have same := Except.ok.inj accepted
    subst reason
    unfold Word.ofNat? at converted
    split at converted
    · exact congrArg Fin.val (Option.some.inj converted).symm
    · cases converted
  · cases accepted

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem checked_word {number : Nat} {endpoint : PUnit}
    (accepted : discard (match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok endpoint) :
    number < wordModulus := by
  cases converted : Word.ofNat? number with
  | none =>
    rw [converted] at accepted
    change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok endpoint at accepted
    cases accepted
  | some reason =>
    unfold Word.ofNat? at converted
    split at converted
    · assumption
    · cases converted

private theorem expression_receipt {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {mapping key : ExpressionId}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {seen : List ExpressionId}
    {original : List Word} {reason : Word}
    (inventory : Inventory capacity next indices places missing (original ++ fixed.map Prod.fst))
    (issued : reason ∈ bases indices places)
    {outcome : ForInStep (Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic) × List ExpressionId)}
    (ran : (do
      let baseNode ← match source.lookupExpression? mapping with
        | some base => pure base
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression mapping))
      let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
        | .mapping keyType valueType => pure (keyType, valueType)
        | _ => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      unless SourceCoreRawMetadata.runtimeType node.type = valueType do
        throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression node.id))
      pure (.yield (next, indices, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩],
        fixed, node.id :: seen))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated row, outcome = .yield updated ∧
      Inventory capacity updated.1 updated.2.1 updated.2.2.1 updated.2.2.2.1
        (original ++ updated.2.2.2.2.1.map Prod.fst) ∧
      updated = (next, indices, places, missing ++ [row], fixed, node.id :: seen) ∧
      CompatibleExpressionMissingSourceReceipts.ExpressionSuffix source node mapping reason row owner := by
  split at ran
  · rename_i base found
    try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    split at ran
    · rename_i keyType valueType mappingView
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · rename_i valueView
        exact ⟨_, _, (Except.ok.inj ran).symm, inventory.append_missing issued, rfl,
          base, keyType, valueType, found, mappingView, valueView, rfl⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
    · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
      cases ran
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

private theorem expression_resume {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {mapping key : ExpressionId}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {seen : List ExpressionId}
    {original : List Word} {reason : Word}
    (inventory : Inventory capacity next indices places missing (original ++ fixed.map Prod.fst))
    (issued : reason ∈ bases indices places)
    {outcome : ForInStep (Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic) × List ExpressionId)}
    (ran : (do
      let baseNode ← match source.lookupExpression? mapping with
        | some base => pure base
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression mapping))
      let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
        | .mapping keyType valueType => pure (keyType, valueType)
        | _ => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      unless SourceCoreRawMetadata.runtimeType node.type = valueType do
        throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression node.id))
      pure (.yield (next, indices, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩],
        fixed, node.id :: seen))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated, outcome = .yield updated ∧
      Inventory capacity updated.1 updated.2.1 updated.2.2.1 updated.2.2.2.1
        (original ++ updated.2.2.2.2.1.map Prod.fst) := by
  obtain ⟨updated, row, same, numeric, _tuple, _suffix⟩ := expression_receipt inventory issued ran
  exact ⟨updated, same, numeric⟩

private theorem place_receipt {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution} {key : ExpressionId} {valueType : TypeSystem.Ty}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)}
    {original : List Word} {reason : Word}
    (inventory : Inventory capacity next indices places missing (original ++ fixed.map Prod.fst))
    (issued : reason ∈ bases indices places)
    {outcome : ForInStep (Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite)}
    (ran : (do
      let keyNode ← match source.lookupExpression? key with
        | some keyNode => pure keyNode
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      pure (.yield (next, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
          keyNode.type, valueType, node.span, reason⟩]))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated keyNode, outcome = .yield updated ∧
      Inventory capacity updated.1 indices updated.2.1 updated.2.2 (original ++ fixed.map Prod.fst) ∧ source.lookupExpression? key = some keyNode ∧
      updated = (next, places, missing ++ [⟨owner, .occurrence node.id.occurrence,
        some assignment.target.root, keyNode.type, valueType, node.span, reason⟩]) := by
  split at ran
  · rename_i keyNode found
    try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    exact ⟨_, keyNode, (Except.ok.inj ran).symm, inventory.append_missing issued, found, rfl⟩
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

private theorem place_resume {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution} {key : ExpressionId} {valueType : TypeSystem.Ty}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)}
    {original : List Word} {reason : Word}
    (inventory : Inventory capacity next indices places missing (original ++ fixed.map Prod.fst))
    (issued : reason ∈ bases indices places)
    {outcome : ForInStep (Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite)}
    (ran : (do
      let keyNode ← match source.lookupExpression? key with
        | some keyNode => pure keyNode
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      pure (.yield (next, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
          keyNode.type, valueType, node.span, reason⟩]))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated, outcome = .yield updated ∧
      Inventory capacity updated.1 indices updated.2.1 updated.2.2 (original ++ fixed.map Prod.fst) := by
  obtain ⟨updated, keyNode, same, numeric, _found, _tuple⟩ := place_receipt inventory issued ran
  exact ⟨updated, same, numeric⟩

private theorem route_receipt {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {original : List Word}
    {steps : List SourceCoreCompatibleDataPlaces.Step}
    {issue : Nat → Except SourceCoreCompatibleDataPlaceFaultSites.Error Word}
    (wordEq : ∀ number, issue number = match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted)
    (inventory : Inventory capacity next indices places missing (original ++ fixed.map Prod.fst))
    {result : Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite}
    (ran : forIn steps (next, places, missing) (fun step current => do
      let mut next := current.1
      let mut places := current.2.1
      let mut missing := current.2.2
      match step with
      | .index _ key valueType =>
          let reason ← match places.find? (fun previous => decide
              (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
               previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) with
            | some previous => pure previous.reason
            | none => do
                let reason ← issue next
                discard <| issue (next + (capacity + 1) - 1)
                next := next + (capacity + 1)
                let diagnostic : Diagnostic := ⟨.typeMismatch valueType none,
                  .occurrence node.id.occurrence, some node.span⟩
                places := places ++ [⟨owner, .occurrence node.id.occurrence, assignment.target.root,
                  some valueType, reason, diagnostic⟩]
                pure reason
          let keyNode ← match source.lookupExpression? key with
            | some keyNode => pure keyNode | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
          missing := missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
            keyNode.type, valueType, node.span, reason⟩]
      | _ => pure ()
      pure (.yield (next, places, missing))) = Except.ok result) :
    Inventory capacity result.1 indices result.2.1 result.2.2 (original ++ fixed.map Prod.fst) ∧
      CompatibleExpressionMissingSourceReceipts.RouteChanges owner source node assignment next
        places result.2.1 missing result.2.2 ∧ next ≤ result.1 := by
  apply CompatibleMemberCertificates.forIn_preserves ran (fun _ current =>
    Inventory capacity current.1 indices current.2.1 current.2.2 (original ++ fixed.map Prod.fst) ∧
      CompatibleExpressionMissingSourceReceipts.RouteChanges owner source node assignment next
        places current.2.1 missing current.2.2 ∧ next ≤ current.1)
    ⟨inventory, CompatibleExpressionMissingSourceReceipts.RouteChanges.refl _ _ _ _ _ _ _, Nat.le_refl _⟩
  intro seen step remaining current outcome _split previous ran
  obtain ⟨numeric, changes, grows⟩ := previous
  obtain ⟨currentNext, currentPlaces, currentMissing⟩ := current
  dsimp only at ran
  cases step with
  | member => exact ⟨_, (Except.ok.inj ran).symm, numeric, changes, grows⟩
  | index layout key valueType =>
    dsimp only at ran
    split at ran
    · rename_i prior found
      have member := List.mem_of_find?_eq_some found
      have sameSite := of_decide_eq_true (List.find?_some (p := fun previous : SourceCoreDataPlaceFaultSites.Site =>
        decide (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
          previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) found)
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      obtain ⟨updated, keyNode, same, numeric, lookup, tuple⟩ :=
        place_receipt numeric (numeric.reused_place member sameSite.2.2.2) ran
      subst updated
      refine ⟨_, same, numeric, ?_, grows⟩
      apply changes.trans (middle := currentNext) _ grows
      refine ⟨⟨[], by simp, ?_⟩, ⟨[_], rfl, ?_⟩⟩
      · intro place member; cases member
      · intro row rowMember
        cases List.mem_singleton.mp rowMember
        exact ⟨prior, key, keyNode, valueType, member, sameSite.1, sameSite.2.1,
          sameSite.2.2.1, sameSite.2.2.2, lookup, rfl⟩
    · obtain ⟨reason, generated, ran⟩ := bind_ok ran
      rw [wordEq] at generated
      have number := word_number generated
      obtain ⟨endpoint, checked, ran⟩ := bind_ok ran
      rw [wordEq] at checked
      have within : currentNext + capacity < wordModulus := by
        have bounded := checked_word checked
        omega
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      let place : SourceCoreDataPlaceFaultSites.Site := ⟨owner, .occurrence node.id.occurrence,
        assignment.target.root, some valueType, reason,
        ⟨.typeMismatch valueType none, .occurrence node.id.occurrence, some node.span⟩⟩
      have issued := numeric.place_range (place := place) rfl number within
      simp only [Nat.add_assoc] at issued
      obtain ⟨updated, keyNode, same, numeric, lookup, tuple⟩ :=
        place_receipt issued (issued.reused_place (List.mem_append_right _ (List.mem_singleton_self _)) rfl) ran
      subst updated
      refine ⟨_, same, numeric, ?_, by omega⟩
      apply changes.trans (middle := currentNext) _ grows
      refine ⟨⟨[place], rfl, ?_⟩, ⟨[_], rfl, ?_⟩⟩
      · intro selected selectedMember
        cases List.mem_singleton.mp selectedMember
        change currentNext ≤ reason.val
        omega
      · intro row rowMember
        cases List.mem_singleton.mp rowMember
        exact ⟨place, key, keyNode, valueType, List.mem_append_right _ (List.mem_singleton_self _),
          rfl, rfl, rfl, rfl, lookup, rfl⟩

private theorem route_ranges {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {original : List Word}
    {steps : List SourceCoreCompatibleDataPlaces.Step}
    {issue : Nat → Except SourceCoreCompatibleDataPlaceFaultSites.Error Word}
    (wordEq : ∀ number, issue number = match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted)
    (inventory : Inventory capacity next indices places missing (original ++ fixed.map Prod.fst))
    {result : Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite}
    (ran : forIn steps (next, places, missing) (fun step current => do
      let mut next := current.1
      let mut places := current.2.1
      let mut missing := current.2.2
      match step with
      | .index _ key valueType =>
          let reason ← match places.find? (fun previous => decide
              (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
               previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) with
            | some previous => pure previous.reason
            | none => do
                let reason ← issue next
                discard <| issue (next + (capacity + 1) - 1)
                next := next + (capacity + 1)
                let diagnostic : Diagnostic := ⟨.typeMismatch valueType none,
                  .occurrence node.id.occurrence, some node.span⟩
                places := places ++ [⟨owner, .occurrence node.id.occurrence, assignment.target.root,
                  some valueType, reason, diagnostic⟩]
                pure reason
          let keyNode ← match source.lookupExpression? key with
            | some keyNode => pure keyNode | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
          missing := missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
            keyNode.type, valueType, node.span, reason⟩]
      | _ => pure ()
      pure (.yield (next, places, missing))) = Except.ok result) :
    Inventory capacity result.1 indices result.2.1 result.2.2 (original ++ fixed.map Prod.fst) := by
  exact (route_receipt wordEq inventory ran).1

/-- The same preparation proof retains numeric bounds and the literal source
issuer of every selected index, including actual ordered prefix coverage. -/
theorem prepare_missing_origins {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program) :
    CompatibleExpressionMissingSourceReceipts.Receipt plan root sources program := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, _baseAccepted, accepted⟩ := bind_ok accepted
  have baseAccepted : SourceCoreProgramFaultSites.prepare plan root = .ok base := by
    cases prepared : SourceCoreProgramFaultSites.prepare plan root with
    | error error => simp only [prepared, Except.mapError] at _baseAccepted; cases _baseAccepted
    | ok value =>
      simp only [prepared, Except.mapError] at _baseAccepted
      cases _baseAccepted
      rfl
  have initialSafe : CompatiblePlaceMissingReservedReceipts.ReadSafe base.rootTable.reads base.rootTable.additional := by
    intro read member row rowMember same
    have absent := (SourceCoreProgramFaultSites.prepare_read_diagnostic baseAccepted member).2.2.1
    have avoids := List.find?_eq_none.mp absent row rowMember
    exact avoids (by simp only [same, decide_true])
  obtain ⟨state, loop, accepted⟩ := bind_ok accepted
  let original := base.rootTable.reads.map (·.reason) ++ [base.rootTable.escapedReason]
  let capacity := context.registry.limits.maxEntries
  let actualSources := plan.specializations.map (fun specialized =>
    (specialized.key, specialized.function.typedBody)) ++ sources
  let invariant := fun (seen : List (Key × TypedSource))
    (state : Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic)) =>
    ((Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 (original ++ state.2.2.2.2.map Prod.fst) ∧
      CompatiblePlaceMissingReservedReceipts.ReadSafe base.rootTable.reads state.2.2.2.2) ∧
      CompatibleExpressionIndexSourceReceipts.Inventory actualSources seen state.2.1) ∧
      CompatibleExpressionMissingSourceReceipts.Inventory actualSources seen state.2.1 state.2.2.1 state.2.2.2.1
  have generated : invariant (plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources) state := by
    apply CompatibleMemberCertificates.forIn_preserves loop invariant
    · refine ⟨⟨⟨?_, initialSafe⟩, CompatibleExpressionIndexSourceReceipts.Inventory.empty actualSources⟩,
        CompatibleExpressionMissingSourceReceipts.Inventory.empty actualSources⟩
      change Inventory capacity _ [] [] [] (original ++ base.rootTable.additional.map Prod.fst)
      refine ⟨by omega, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro token member; cases member
        · intro token member; cases member
        · intro token member; cases member
        · intro token member
          have used : token.val ∈ base.rootTable.reads.map (·.reason.val) ++
              base.rootTable.additional.map (·.1.val) ++ [base.rootTable.escapedReason.val] := by
            simp only [original, List.mem_append, List.mem_map, List.mem_singleton] at member ⊢
            grind
          have bounded := foldl_max_member _ used 0
          omega
        · intro left member; cases member
        · intro token member; cases member
      · intro site member; cases member
    · intro seen item remaining current outcome sourceSplit previous ran
      obtain ⟨⟨previous, sourceOrigins⟩, missingOrigins⟩ := previous
      obtain ⟨next, indices, places, missing, fixed⟩ := current
      obtain ⟨owner, source⟩ := item
      dsimp only at ran
      by_cases ownerMismatch : source.owner ≠ owner.declaration
      · rw [if_pos ownerMismatch] at ran
        change (Except.error (.sourceOwnerMismatch owner.declaration source.owner) :
          Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
      · rw [if_neg ownerMismatch] at ran
        have issuer : (owner, source) ∈ actualSources := by
          change (owner, source) ∈ plan.specializations.map (fun specialized =>
            (specialized.key, specialized.function.typedBody)) ++ sources
          rw [sourceSplit]
          exact List.mem_append_right _ List.mem_cons_self
        have owns : source.owner = owner.declaration := Classical.not_not.mp ownerMismatch
        obtain ⟨current, nodesLoop, finished⟩ := bind_ok ran
        refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
        let nodeInvariant := fun (seenNodes : List Node)
          (state : Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
            List MissingSite × List (Word × Diagnostic) × List ExpressionId) =>
          ((Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 (original ++ state.2.2.2.2.1.map Prod.fst) ∧
            CompatiblePlaceMissingReservedReceipts.ReadSafe base.rootTable.reads state.2.2.2.2.1) ∧
            CompatibleExpressionIndexSourceReceipts.NodeInventory actualSources seen owner seenNodes state.2.1) ∧
            CompatibleExpressionMissingSourceReceipts.NodeInventory actualSources seen owner source seenNodes
              state.2.1 state.2.2.1 state.2.2.2.1
        have nodesGenerated : nodeInvariant source.nodes current := by
          apply CompatibleMemberCertificates.forIn_preserves nodesLoop nodeInvariant
            ⟨⟨previous, CompatibleExpressionIndexSourceReceipts.NodeInventory.start sourceOrigins owner⟩,
              CompatibleExpressionMissingSourceReceipts.NodeInventory.start missingOrigins owner source⟩
          intro seenNodes retained remaining current outcome nodeSplit previous ran
          obtain ⟨⟨previous, nodeOrigins⟩, missingOrigins⟩ := previous
          obtain ⟨next, indices, places, missing, fixed, seenIndices⟩ := current
          dsimp only at ran
          cases retained with
          | expression node =>
            cases form : node.form <;> simp only [form] at ran
            all_goals first
              | refine ⟨_, (Except.ok.inj ran).symm, ⟨previous, nodeOrigins.step ?_⟩,
                  missingOrigins.step ?_⟩
                all_goals
                  intro actual same base key actualForm
                  cases same
                  rw [form] at actualForm
                  cases actualForm
              | skip
            case index mapping key =>
              have contains : SourceSemantics.ContainsExpression source node.id node := by
                refine ⟨?_, rfl⟩
                rw [nodeSplit]
                exact List.mem_append_right _ List.mem_cons_self
              by_cases nodeOwner : node.id.occurrence.owner ≠ source.owner
              · rw [if_pos nodeOwner] at ran
                change (Except.error (.ownerMismatch node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                cases ran
              · rw [if_neg nodeOwner] at ran
                by_cases mappingOwner : mapping.occurrence.owner ≠ source.owner
                · rw [if_pos mappingOwner] at ran
                  change (Except.error (.ownerMismatch mapping) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                  cases ran
                · rw [if_neg mappingOwner] at ran
                  by_cases keyOwner : key.occurrence.owner ≠ source.owner
                  · rw [if_pos keyOwner] at ran
                    change (Except.error (.ownerMismatch key) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                    cases ran
                  · rw [if_neg keyOwner] at ran
                    by_cases duplicate : seenIndices.contains node.id = true
                    · rw [if_pos duplicate] at ran
                      change (Except.error (.duplicateOccurrence node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                      cases ran
                    · rw [if_neg duplicate] at ran
                      split at ran
                      · rename_i prior found
                        have member := List.mem_of_find?_eq_some found
                        try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                        obtain ⟨updated, row, same, numeric, tuple, suffix⟩ :=
                          expression_receipt previous.1 (previous.1.reused_index member) ran
                        subst updated
                        have rowAt := suffix.at_index indices form found rfl
                        have retained := missingOrigins.inventory.append_expression issuer owns contains rowAt
                        have updatedOrigins := missingOrigins.replace [] (by simpa only [List.append_nil] using retained)
                          (fun _ member => List.mem_append_left _ member)
                        refine ⟨_, same, ⟨⟨numeric, previous.2⟩, nodeOrigins.step ?_⟩,
                          (by
                            apply CompatibleExpressionMissingSourceReceipts.NodeInventory.step
                              (by simpa only [List.append_nil] using updatedOrigins)
                            intro actual same base key actualForm
                            cases same
                            exact ⟨row, List.mem_append_right _ (List.mem_singleton_self _), rowAt⟩)⟩
                        · intro actual same base key actualForm
                          cases same
                          exact ⟨prior, found⟩
                      · rename_i absent
                        obtain ⟨reason, generated, ran⟩ := bind_ok ran
                        have number : reason.val = next := word_number generated
                        obtain ⟨endpoint, checked, ran⟩ := bind_ok ran
                        have within : next + capacity < wordModulus := by
                          have bounded := checked_word checked
                          omega
                        try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                        let selected : SourceCoreDataFaultSites.IndexSite := ⟨owner, node.id, reason,
                          ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩
                        have issued := previous.1.index_range (index := selected) number within
                        simp only [Nat.add_assoc] at issued
                        have extended := missingOrigins.inventory.append_index selected
                          (by
                            intro old member same
                            have below := previous.1.bounds.issued old.reason (previous.1.reused_index member)
                            have eq := congrArg Fin.val same
                            change old.reason.val = reason.val at eq
                            omega)
                          (by
                            intro old member type kind same
                            have below := previous.1.bounds.issued old.reason (previous.1.reused_place member kind)
                            have eq := congrArg Fin.val same
                            change old.reason.val = reason.val at eq
                            omega)
                        obtain ⟨updated, row, same, numeric, tuple, suffix⟩ := expression_receipt issued
                          (issued.reused_index (List.mem_append_right _ (List.mem_singleton_self _))) ran
                        subst updated
                        have found : (indices ++ [selected]).find?
                            (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = some selected := by
                          rw [List.find?_append, absent]
                          simp [selected]
                        have rowAt := suffix.at_index (indices ++ [selected]) form found rfl
                        have retained := extended.append_expression issuer owns contains rowAt
                        have updatedOrigins := missingOrigins.replace [selected] retained
                          (fun _ member => List.mem_append_left _ member)
                        refine ⟨_, same, ⟨⟨numeric, previous.2⟩,
                          nodeOrigins.append_index issuer owns contains form absent reason⟩,
                          updatedOrigins.step ?_⟩
                        intro actual same base key actualForm
                        cases same
                        exact ⟨row, List.mem_append_right _ (List.mem_singleton_self _), rowAt⟩
          | statement node =>
            have statementContains : SourceSemantics.ContainsStatement source node.id node := by
              refine ⟨?_, rfl⟩
              rw [nodeSplit]
              exact List.mem_append_right _ List.mem_cons_self
            obtain ⟨current, targetsLoop, finished⟩ := bind_ok ran
            refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
            have targetsGenerated : (Inventory capacity current.1 indices current.2.1 current.2.2.1
                (original ++ current.2.2.2.map Prod.fst) ∧
                CompatiblePlaceMissingReservedReceipts.ReadSafe base.rootTable.reads current.2.2.2) ∧
                CompatibleExpressionMissingSourceReceipts.NodeInventory actualSources seen owner source seenNodes
                  indices current.2.1 current.2.2.1 := by
              apply CompatibleMemberCertificates.forIn_preserves targetsLoop (fun _ current =>
                (Inventory capacity current.1 indices current.2.1 current.2.2.1
                  (original ++ current.2.2.2.map Prod.fst) ∧
                  CompatiblePlaceMissingReservedReceipts.ReadSafe base.rootTable.reads current.2.2.2) ∧
                  CompatibleExpressionMissingSourceReceipts.NodeInventory actualSources seen owner source seenNodes
                    indices current.2.1 current.2.2.1) ⟨previous, missingOrigins⟩
              intro seen assignment remaining current outcome _split previous ran
              obtain ⟨previous, missingOrigins⟩ := previous
              obtain ⟨next, places, missing, fixed⟩ := current
              dsimp only at ran
              split at ran
              · obtain ⟨route, _described, ran⟩ := bind_ok ran
                split at ran
                · obtain ⟨current, stepsLoop, finished⟩ := bind_ok ran
                  have result := route_receipt (owner := owner) (source := source) (node := node)
                    (assignment := assignment) (steps := route.steps) (fun _ => rfl) previous.1 stepsLoop
                  have retained := result.2.1.apply missingOrigins.inventory issuer owns statementContains (by
                    intro index member
                    have below := previous.1.bounds.issued index.reason (previous.1.reused_index member)
                    omega)
                  obtain ⟨added, missingEq, _⟩ := result.2.1.missing
                  have updatedOrigins := missingOrigins.replace [] (by simpa only [List.append_nil] using retained)
                    (fun _ member => missingEq ▸ List.mem_append_left _ member)
                  exact ⟨_, (Except.ok.inj finished).symm, ⟨result.1, previous.2⟩,
                    by simpa only [List.append_nil] using updatedOrigins⟩
                · obtain ⟨reason, generated, ran⟩ := bind_ok ran
                  have number := word_number generated
                  let place : SourceCoreDataPlaceFaultSites.Site := ⟨owner, .occurrence node.id.occurrence,
                    assignment.target.root, none, reason,
                    ⟨.invalidPlaceProjection, .occurrence node.id.occurrence, some node.span⟩⟩
                  have issued := previous.1.place_fixed (place := place) rfl number
                  have issuedMissing := missingOrigins.inventory.fixed_place place rfl
                  try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                  obtain ⟨current, stepsLoop, finished⟩ := bind_ok ran
                  have result := route_receipt (capacity := capacity) (indices := indices)
                    (original := original) (fixed := fixed ++ [(reason, place.diagnostic)])
                    (owner := owner) (source := source) (node := node)
                    (assignment := assignment) (steps := route.steps) (fun _ => rfl)
                    (by simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc] using issued) stepsLoop
                  have retained := result.2.1.apply issuedMissing issuer owns statementContains (by
                    intro index member
                    have below := issued.bounds.issued index.reason (issued.reused_index member)
                    omega)
                  obtain ⟨added, missingEq, _⟩ := result.2.1.missing
                  have updatedOrigins := missingOrigins.replace [] (by simpa only [List.append_nil] using retained)
                    (fun _ member => missingEq ▸ List.mem_append_left _ member)
                  refine ⟨_, (Except.ok.inj finished).symm, ⟨result.1, ?_⟩,
                    by simpa only [List.append_nil] using updatedOrigins⟩
                  apply CompatiblePlaceMissingReservedReceipts.ReadSafe.append previous.2 _ number
                  intro read member
                  exact previous.1.bounds.blockedBelow read.reason
                    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨read, member, rfl⟩)))
              · exact ⟨_, (Except.ok.inj ran).symm, previous, missingOrigins⟩
            refine ⟨⟨targetsGenerated.1, nodeOrigins.step
              (CompatibleExpressionIndexSourceReceipts.NodeSelected.statement owner node indices)⟩,
              targetsGenerated.2.step ?_⟩
            intro expression same
            cases same
        exact ⟨⟨nodesGenerated.1.1, nodesGenerated.1.2.finish⟩, nodesGenerated.2.finish⟩
  obtain ⟨extra, _extraAccepted, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst program
  obtain ⟨next, indices, places, missing, fixed⟩ := state
  change ((Inventory capacity next indices places missing (original ++ fixed.map Prod.fst) ∧
    CompatiblePlaceMissingReservedReceipts.ReadSafe base.rootTable.reads fixed) ∧
    CompatibleExpressionIndexSourceReceipts.Inventory actualSources actualSources indices) ∧
    CompatibleExpressionMissingSourceReceipts.Inventory actualSources actualSources indices places missing at generated
  refine ⟨⟨?_, generated.1.2⟩, generated.2⟩
  obtain ⟨generated, _⟩ := generated.1
  refine ⟨base, extra, baseAccepted, rfl, rfl, rfl, rfl, _extraAccepted, ?_,
    generated.1.positive, ?_, ?_, ?_, ?_, ?_, generated.2⟩
  ·
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro site member
      exact generated.1.bounds.reserved site.base (generated.1.missing site member)
    · intro left leftMember right rightMember
      exact generated.1.bounds.separated left.base (generated.1.missing left leftMember) right.base (generated.1.missing right rightMember)
    · intro site member
      exact generated.1.bounds.positive site.base (generated.1.missing site member)
    · intro site member row rowMember
      exact generated.1.bounds.outside site.base (generated.1.missing site member) row.1
        (List.mem_append_right _ (List.mem_map.mpr ⟨row, rowMember, rfl⟩))
    · intro site member
      exact generated.1.bounds.outside site.base (generated.1.missing site member) base.rootTable.escapedReason
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · intro site member
    exact generated.1.bounds.issued site.base (generated.1.missing site member)
  · intro row member
    exact generated.1.bounds.blockedBelow row.1
      (List.mem_append_right _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  · intro read member
    exact generated.1.bounds.blockedBelow read.reason
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨read, member, rfl⟩)))
  · exact generated.1.bounds.blockedBelow base.rootTable.escapedReason
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · intro site member read readMember
    exact generated.1.bounds.outside site.base (generated.1.missing site member) read.reason
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨read, readMember, rfl⟩)))

theorem prepare_index_origins {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program) :
    CompatibleExpressionIndexSourceReceipts.Receipt plan root sources program := by
  exact (prepare_missing_origins accepted).1

/-- The original numeric receipt is the finite projection of the same producer. -/
theorem prepare_reserved_receipt {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program) :
    CompatiblePlaceMissingReservedReceipts.ReservedReceipt context plan root program := by
  exact (prepare_index_origins accepted).1

/-- The accepted producer checks all actual reserved ranges, including reused
reasons, and separates them from its original and later fixed diagnostics. -/
theorem prepare_ranges {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program) :
    Ranges context.registry.limits.maxEntries program.missing ∧
    (∀ site, site ∈ program.missing → 0 < site.base.val) ∧
    (∀ site, site ∈ program.missing → ∀ row, row ∈ program.fixed →
      row.1.val ≤ site.base.val ∨ site.base.val + context.registry.limits.maxEntries < row.1.val) ∧
    (∀ site, site ∈ program.missing →
      program.program.rootTable.escapedReason.val ≤ site.base.val ∨
        site.base.val + context.registry.limits.maxEntries < program.program.rootTable.escapedReason.val) := by
  obtain ⟨base, extra, receipt⟩ := prepare_reserved_receipt accepted
  exact receipt.legacy

/-- The real preparation and actual table rebuild discharge all decoder range
and priority checks for an authenticated member of their missing inventory. -/
theorem table_diagnostic {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (prepared : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {site : MissingSite} (member : site ∈ program.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType) :
    ∃ diagnostic, table.diagnostic? (site.base.add header) = some diagnostic ∧
      diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨ranges, positive, fixed, escaped⟩ := prepare_ranges prepared
  have limits : registry.limits.maxEntries = context.registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  have actualRanges : Ranges registry.limits.maxEntries program.missing := limits.symm ▸ ranges
  have budget := CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata) budget
  have reserved := actualRanges.reserved site member
  have sameEscape : table.escapedReason = program.program.rootTable.escapedReason := by
    unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at rebuilt
    obtain ⟨extra, _, finished⟩ := bind_ok rebuilt
    cases finished
    rfl
  have headerPositive : 0 < header.val := by
    by_cases zero : header.val = 0
    · exact False.elim (metadata.nonzero (Fin.ext zero))
    · omega
  have number := token_nonWrapping site.base header registry.limits.maxEntries reserved bounded
  apply CompatiblePlaceMissingDiagnosticAssociation.table_diagnostic rebuilt actualRanges member metadata keyView valueView
  · intro row rowMember
    simpa only [limits] using fixed site member row rowMember
  · intro zero
    have same := congrArg Fin.val zero
    have positive := positive site member
    rw [number] at same
    change site.base.val + header.val = 0 at same
    omega
  · intro same
    have same := congrArg Fin.val same
    rw [number, sameEscape] at same
    have separate := escaped site member
    rw [← limits] at separate
    rcases separate with before | after <;> omega

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationCoverage
/-! Accepted preparation retains a missing site for each actual described index
of a concrete assignment occurrence. The receipt uses the first matching place
entry that the original producer retains. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationCoverage
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites

/-- The exact assignment occurrences visited by the original producer. -/
def targets (node : StatementNode) : List AssignmentResolution :=
  match node.form with
  | .assignValue assignment _ _ | .assignBitNot assignment => [assignment]
  | .forLoop initial _ post _ => (initial ++ post).filterMap fun
      | .assignValue assignment _ _ | .assignBitNot assignment => some assignment
      | _ => none
  | _ => []

/-- Preparation's concrete gate at this actual full Source occurrence. -/
def concrete (source : TypedSource) (assignment : AssignmentResolution) : Bool :=
  SourceCoreDataCatalog.closed assignment.target.type &&
    ((SourceCoreDataPlaces.declaredBinders source).filter (fun binder =>
      decide (binder.id = assignment.target.root))).any (fun binder =>
        SourceCoreDataCatalog.closed binder.scheme.body)

private def selects (owner : Key) (node : StatementNode) (assignment : AssignmentResolution)
    (valueType : TypeSystem.Ty) (entry : SourceCoreDataPlaceFaultSites.Site) : Bool :=
  decide (entry.owner = owner ∧ entry.location = .occurrence node.id.occurrence ∧
    entry.binder = assignment.target.root ∧ entry.missingType = some valueType)

private structure Growth (places later : List SourceCoreDataPlaceFaultSites.Site)
    (missing more : List MissingSite) : Prop where
  places : ∃ suffix, later = places ++ suffix
  missing : ∃ suffix, more = missing ++ suffix

private theorem Growth.refl (places : List SourceCoreDataPlaceFaultSites.Site)
    (missing : List MissingSite) : Growth places places missing missing :=
  ⟨⟨[], (List.append_nil _).symm⟩, ⟨[], (List.append_nil _).symm⟩⟩

private theorem Growth.trans {first middle last : List SourceCoreDataPlaceFaultSites.Site}
    {before current after : List MissingSite}
    (one : Growth first middle before current) (two : Growth middle last current after) :
    Growth first last before after := by
  obtain ⟨left, rfl⟩ := one.places
  obtain ⟨right, rfl⟩ := two.places
  obtain ⟨leftMissing, rfl⟩ := one.missing
  obtain ⟨rightMissing, rfl⟩ := two.missing
  exact ⟨⟨left ++ right, List.append_assoc _ _ _⟩,
    ⟨leftMissing ++ rightMissing, List.append_assoc _ _ _⟩⟩

/-- An actual key lookup and emitted inventory member, together with the real
first matching place entry used to emit its base. -/
structure Receipt (owner : Key) (source : TypedSource) (node : StatementNode)
    (assignment : AssignmentResolution) (key : ExpressionId) (valueType : TypeSystem.Ty)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite) : Prop where
  retained : ∃ keyNode entry site,
    source.lookupExpression? key = some keyNode ∧
    places.find? (selects owner node assignment valueType) = some entry ∧
    site ∈ missing ∧
    site = ⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
      keyNode.type, valueType, node.span, entry.reason⟩

private theorem Receipt.grows {owner : Key} {source : TypedSource} {node : StatementNode}
    {assignment : AssignmentResolution} {key : ExpressionId} {valueType : TypeSystem.Ty}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : Receipt owner source node assignment key valueType places missing)
    (growth : Growth places later missing more) :
    Receipt owner source node assignment key valueType later more := by
  obtain ⟨keyNode, entry, site, lookup, found, member, actual⟩ := receipt.retained
  obtain ⟨placeSuffix, rfl⟩ := growth.places
  obtain ⟨missingSuffix, rfl⟩ := growth.missing
  exact ⟨⟨keyNode, entry, site, lookup,
    by rw [List.find?_append, found]; rfl,
    List.mem_append_left _ member, actual⟩⟩

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_receipts {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)}
    (accepted : forIn items initial step = .ok final)
    (grows : β → β → Prop) (reflexive : ∀ state, grows state state)
    (transitive : ∀ first middle last, grows first middle → grows middle last → grows first last)
    (receipt : α → β → Prop)
    (transport : ∀ item before after, receipt item before → grows before after → receipt item after)
    (next : ∀ seen item remaining state outcome,
      items = seen ++ item :: remaining → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ grows state updated ∧ receipt item updated) :
    grows initial final ∧ ∀ item, item ∈ items → receipt item final := by
  apply CompatibleMemberCertificates.forIn_preserves accepted
    (fun seen state => grows initial state ∧ ∀ item, item ∈ seen → receipt item state)
  · exact ⟨reflexive _, fun _ member => False.elim (List.not_mem_nil member)⟩
  · intro seen item remaining state outcome split previous ran
    obtain ⟨updated, actual, growth, current⟩ := next seen item remaining state outcome split ran
    refine ⟨updated, actual, transitive _ _ _ previous.1 growth, ?_⟩
    intro prior member
    rcases List.mem_append.mp member with old | new
    · exact transport prior state updated (previous.2 prior old) growth
    · exact List.mem_singleton.mp new ▸ current

private def StepReceipt (owner : Key) (source : TypedSource) (node : StatementNode)
    (assignment : AssignmentResolution) (step : SourceCoreCompatibleDataPlaces.Step)
    (state : Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite) : Prop :=
  match step with
  | .index _ key valueType => Receipt owner source node assignment key valueType state.2.1 state.2.2
  | .member .. => True

private theorem route_receipts {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {steps : List SourceCoreCompatibleDataPlaces.Step}
    {issue : Nat → Except SourceCoreCompatibleDataPlaceFaultSites.Error Word}
    {result : Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite}
    (ran : forIn steps (next, places, missing) (fun step current => do
      let mut next := current.1
      let mut places := current.2.1
      let mut missing := current.2.2
      match step with
      | .index _ key valueType =>
          let reason ← match places.find? (fun previous => decide
              (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
               previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) with
            | some previous => pure previous.reason
            | none => do
                let reason ← issue next
                discard <| issue (next + (capacity + 1) - 1)
                next := next + (capacity + 1)
                let diagnostic : Diagnostic := ⟨.typeMismatch valueType none,
                  .occurrence node.id.occurrence, some node.span⟩
                places := places ++ [⟨owner, .occurrence node.id.occurrence, assignment.target.root,
                  some valueType, reason, diagnostic⟩]
                pure reason
          let keyNode ← match source.lookupExpression? key with
            | some keyNode => pure keyNode | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
          missing := missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
            keyNode.type, valueType, node.span, reason⟩]
      | _ => pure ()
      pure (.yield (next, places, missing))) = Except.ok result) :
    Growth places result.2.1 missing result.2.2 ∧
      ∀ step, step ∈ steps → StepReceipt owner source node assignment step result := by
  apply forIn_receipts ran (fun before after => Growth before.2.1 after.2.1 before.2.2 after.2.2)
    (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
    (StepReceipt owner source node assignment)
  · intro step before after receipt growth
    cases step with
    | member => trivial
    | index => exact receipt.grows growth
  · intro seen step remaining current outcome _split ran
    obtain ⟨next, places, missing⟩ := current
    dsimp only at ran
    cases step with
    | member => exact ⟨_, (Except.ok.inj ran).symm, Growth.refl _ _, True.intro⟩
    | index layout key valueType =>
      dsimp only at ran
      split at ran
      · rename_i prior found
        try dsimp only [pure, Except.pure, bind, Except.bind] at ran
        split at ran
        · rename_i keyNode lookup
          try dsimp only [pure, Except.pure, bind, Except.bind] at ran
          refine ⟨_, (Except.ok.inj ran).symm, ⟨⟨[], (List.append_nil _).symm⟩,
            ⟨[_], rfl⟩⟩, ?_⟩
          exact ⟨⟨keyNode, prior, _, lookup, found, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩⟩
        · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
          cases ran
      · rename_i absent
        obtain ⟨reason, _generated, ran⟩ := bind_ok ran
        obtain ⟨endpoint, _checked, ran⟩ := bind_ok ran
        try dsimp only [pure, Except.pure, bind, Except.bind] at ran
        split at ran
        · rename_i keyNode lookup
          try dsimp only [pure, Except.pure, bind, Except.bind] at ran
          refine ⟨_, (Except.ok.inj ran).symm, ⟨⟨[_], rfl⟩, ⟨[_], rfl⟩⟩, ?_⟩
          refine ⟨⟨keyNode, ⟨owner, .occurrence node.id.occurrence, assignment.target.root,
            some valueType, reason, ⟨.typeMismatch valueType none, .occurrence node.id.occurrence, some node.span⟩⟩,
            _, lookup, ?_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩⟩
          change places.find? (selects owner node assignment valueType) = none at absent
          rw [List.find?_append, absent]
          simp [selects]
        · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
          cases ran

private def AssignmentReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (owner : Key) (source : TypedSource) (node : StatementNode) (assignment : AssignmentResolution)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite) : Prop :=
  ∀ route, concrete source assignment = true →
    SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route →
    ∀ layout key valueType, .index layout key valueType ∈ route.steps →
      Receipt owner source node assignment key valueType places missing

private def NodeReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (owner : Key) (source : TypedSource) (retained : Node)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite) : Prop :=
  match retained with
  | .statement node => ∀ assignment, assignment ∈ targets node →
      AssignmentReceipt context owner source node assignment places missing
  | .expression _ => True

private def SourceReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (item : Key × TypedSource) (places : List SourceCoreDataPlaceFaultSites.Site)
    (missing : List MissingSite) : Prop :=
  ∀ retained, retained ∈ item.2.nodes → NodeReceipt context item.1 item.2 retained places missing

private theorem AssignmentReceipt.grows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {owner : Key} {source : TypedSource} {node : StatementNode} {assignment : AssignmentResolution}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : AssignmentReceipt context owner source node assignment places missing)
    (growth : Growth places later missing more) :
    AssignmentReceipt context owner source node assignment later more := by
  intro route concrete described layout key valueType member
  exact (receipt route concrete described layout key valueType member).grows growth

private theorem NodeReceipt.grows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {owner : Key} {source : TypedSource} {retained : Node}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : NodeReceipt context owner source retained places missing)
    (growth : Growth places later missing more) :
    NodeReceipt context owner source retained later more := by
  cases retained with
  | expression => trivial
  | statement => exact fun assignment member => (receipt assignment member).grows growth

private theorem SourceReceipt.grows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {item : Key × TypedSource}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : SourceReceipt context item places missing)
    (growth : Growth places later missing more) : SourceReceipt context item later more :=
  fun retained member => (receipt retained member).grows growth

private theorem expression_growth {next : Nat} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {mapping key : ExpressionId}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {seen : List ExpressionId}
    {reason : Word}
    {outcome : ForInStep (Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic) × List ExpressionId)}
    (ran : (do
      let baseNode ← match source.lookupExpression? mapping with
        | some base => pure base
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression mapping))
      let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
        | .mapping keyType valueType => pure (keyType, valueType)
        | _ => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      unless SourceCoreRawMetadata.runtimeType node.type = valueType do
        throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression node.id))
      pure (.yield (next, indices, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩],
        fixed, node.id :: seen))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated, outcome = .yield updated ∧ Growth places updated.2.2.1 missing updated.2.2.2.1 := by
  split at ran
  · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    split at ran
    · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · exact ⟨_, (Except.ok.inj ran).symm, ⟨⟨[], (List.append_nil _).symm⟩, ⟨[_], rfl⟩⟩⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
    · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
      cases ran
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

/-- Every actual concrete assignment index visited by the accepted producer
has a retained missing site with the real final place-reason lookup. -/
theorem prepare_coverage {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {owner : Key} {source : TypedSource}
    (collected : (owner, source) ∈ plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources)
    {node : StatementNode} (statement : .statement node ∈ source.nodes)
    {assignment : AssignmentResolution} (target : assignment ∈ targets node)
    (gate : concrete source assignment = true)
    {route : SourceCoreCompatibleDataPlaces.Route}
    (described : SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route)
    {layout : OrderedMapping.Layout} {key : ExpressionId} {valueType : TypeSystem.Ty}
    (index : .index layout key valueType ∈ route.steps) :
    ∃ keyNode site,
      source.lookupExpression? key = some keyNode ∧ site ∈ program.missing ∧
      site = ⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
        keyNode.type, valueType, node.span,
        program.program.placeReason owner (.occurrence node.id.occurrence) assignment.target.root (some valueType)⟩ := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, _baseAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨state, loop, accepted⟩ := bind_ok accepted
  have generated :
      ∀ item, item ∈ plan.specializations.map (fun specialized =>
        (specialized.key, specialized.function.typedBody)) ++ sources →
      SourceReceipt context item state.2.2.1 state.2.2.2.1 := by
    apply (forIn_receipts loop
      (fun before after => Growth before.2.2.1 after.2.2.1 before.2.2.2.1 after.2.2.2.1)
      (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
      (fun item state => SourceReceipt context item state.2.2.1 state.2.2.2.1)
      (fun _ _ _ receipt growth => receipt.grows growth) ?_).2
    intro seen item remaining current outcome _split ran
    obtain ⟨next, indices, places, missing, fixed⟩ := current
    obtain ⟨owner, source⟩ := item
    dsimp only at ran
    by_cases ownerMismatch : source.owner ≠ owner.declaration
    · rw [if_pos ownerMismatch] at ran
      change (Except.error (.sourceOwnerMismatch owner.declaration source.owner) :
        Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
      cases ran
    · rw [if_neg ownerMismatch] at ran
      obtain ⟨current, nodesLoop, finished⟩ := bind_ok ran
      have nodes : Growth places current.2.2.1 missing current.2.2.2.1 ∧
          ∀ retained, retained ∈ source.nodes →
            NodeReceipt context owner source retained current.2.2.1 current.2.2.2.1 := by
        apply forIn_receipts nodesLoop
          (fun before after => Growth before.2.2.1 after.2.2.1 before.2.2.2.1 after.2.2.2.1)
          (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
          (fun retained state => NodeReceipt context owner source retained state.2.2.1 state.2.2.2.1)
        · exact fun _ _ _ receipt growth => receipt.grows growth
        · intro seen retained remaining current outcome _split ran
          obtain ⟨next, indices, places, missing, fixed, seenIndices⟩ := current
          dsimp only at ran
          cases retained with
          | expression node =>
            cases form : node.form <;> simp only [form] at ran
            all_goals first
              | exact ⟨_, (Except.ok.inj ran).symm, Growth.refl _ _, True.intro⟩
              | skip
            case index mapping key =>
              by_cases nodeOwner : node.id.occurrence.owner ≠ source.owner
              · rw [if_pos nodeOwner] at ran
                change (Except.error (.ownerMismatch node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                cases ran
              · rw [if_neg nodeOwner] at ran
                by_cases mappingOwner : mapping.occurrence.owner ≠ source.owner
                · rw [if_pos mappingOwner] at ran
                  change (Except.error (.ownerMismatch mapping) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                  cases ran
                · rw [if_neg mappingOwner] at ran
                  by_cases keyOwner : key.occurrence.owner ≠ source.owner
                  · rw [if_pos keyOwner] at ran
                    change (Except.error (.ownerMismatch key) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                    cases ran
                  · rw [if_neg keyOwner] at ran
                    by_cases duplicate : seenIndices.contains node.id = true
                    · rw [if_pos duplicate] at ran
                      change (Except.error (.duplicateOccurrence node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                      cases ran
                    · rw [if_neg duplicate] at ran
                      split at ran
                      · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                        obtain ⟨updated, actual, growth⟩ := expression_growth ran
                        exact ⟨updated, actual, growth, True.intro⟩
                      · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
                        obtain ⟨endpoint, _checked, ran⟩ := bind_ok ran
                        try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                        obtain ⟨updated, actual, growth⟩ := expression_growth ran
                        exact ⟨updated, actual, growth, True.intro⟩
          | statement node =>
            obtain ⟨current, targetsLoop, finished⟩ := bind_ok ran
            have assignments : Growth places current.2.1 missing current.2.2.1 ∧
                ∀ assignment, assignment ∈ targets node →
                  AssignmentReceipt context owner source node assignment current.2.1 current.2.2.1 := by
              apply forIn_receipts targetsLoop
                (fun before after => Growth before.2.1 after.2.1 before.2.2.1 after.2.2.1)
                (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
                (fun assignment state => AssignmentReceipt context owner source node assignment state.2.1 state.2.2.1)
              · exact fun _ _ _ receipt growth => receipt.grows growth
              · intro seen assignment remaining current outcome _split ran
                obtain ⟨next, places, missing, fixed⟩ := current
                dsimp only at ran
                split at ran
                · rename_i visited
                  obtain ⟨route, actualDescription, ran⟩ := bind_ok ran
                  split at ran
                  · obtain ⟨updated, stepsLoop, finished⟩ := bind_ok ran
                    obtain ⟨growth, receipts⟩ := route_receipts (owner := owner) (source := source)
                      (node := node) (assignment := assignment) (steps := route.steps) stepsLoop
                    refine ⟨_, (Except.ok.inj finished).symm, growth, ?_⟩
                    intro requested _concrete described layout key valueType member
                    rw [described] at actualDescription
                    have same := Except.ok.inj actualDescription
                    subst route
                    exact receipts _ member
                  · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
                    try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                    obtain ⟨updated, stepsLoop, finished⟩ := bind_ok ran
                    obtain ⟨growth, receipts⟩ := route_receipts (owner := owner) (source := source)
                      (node := node) (assignment := assignment) (steps := route.steps) stepsLoop
                    refine ⟨_, (Except.ok.inj finished).symm,
                      (Growth.mk ⟨[_], rfl⟩ ⟨[], (List.append_nil _).symm⟩).trans growth, ?_⟩
                    intro requested _concrete described layout key valueType member
                    rw [described] at actualDescription
                    have same := Except.ok.inj actualDescription
                    subst route
                    exact receipts _ member
                · rename_i skipped
                  refine ⟨_, (Except.ok.inj ran).symm, Growth.refl _ _, ?_⟩
                  intro route required
                  change concrete source assignment ≠ true at skipped
                  exact False.elim (skipped required)
            exact ⟨_, (Except.ok.inj finished).symm, assignments.1, assignments.2⟩
      exact ⟨_, (Except.ok.inj finished).symm, nodes.1, nodes.2⟩
  obtain ⟨extra, _extraAccepted, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst program
  obtain ⟨next, indices, places, missing, fixed⟩ := state
  have receipt := generated (owner, source) collected (.statement node) statement assignment target
    route gate described layout key valueType index
  obtain ⟨keyNode, entry, site, lookup, found, member, actual⟩ := receipt.retained
  refine ⟨keyNode, site, lookup, member, ?_⟩
  rw [actual]
  unfold SourceCoreDataPlaceFaultSites.Program.placeReason
  change places.find? (selects owner node assignment valueType) = some entry at found
  change (⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
    keyNode.type, valueType, node.span, entry.reason⟩ : MissingSite) =
    ⟨owner, .occurrence node.id.occurrence, some assignment.target.root, keyNode.type, valueType, node.span,
      match places.find? (selects owner node assignment valueType) with
      | some candidate => candidate.reason | none => Word.zero⟩
  rw [found]


end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationCoverage
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLowerReflection
/-! The production compatible place lowerer is connected to whole assignment
reflection. Only universal child typing/meaning and independent checked source
facts remain; no manually supplied path or helper-typing layout is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLowerReflection
open Core Frontend SourceInference GeneralHeap GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces

theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {assignment : AssignmentResolution}
    {administrativeContext : Core.Context} {expression : ExpressionLowerer} {fuel : Nat}
    {rhs : ExpressionId} {operator : Syntax.ValueAssignOp} {next lowered : Expr} {outputType resultType : Ty}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (nonempty : assignment.target.projections ≠ [])
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code.expression (LanguageResult.resultType code.type)
        ambient.definitions)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator (some rhs) outputType
      next reasonAt invalid invalidOperand missing = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered resultType ambient.definitions)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {prepared root resolved reason token count},
      (∃ route, describe compilation compilation.checked.signatures source site assignment = .ok route ∧
        prepare compilation fuel route invalid missing = .ok prepared) →
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) invalid)
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {result : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (completed : Evaluates coreEnvironment store lowered result finalStore) :
    CompatiblePlaceTailReflection.Result compilation.checked registry functions program context evidence source faults assignment.target operator rhs
      environment coreEnvironment before store mapping world next outputType result finalStore := by
  obtain ⟨binder, leaf, prepared, codes, sourceTypes, index, right, node, actualPreparation, binding, rootEq, slot, layout, ordinary,
      generated, found, certified, rhsView, rhsType, lowering⟩ :=
    CompatiblePlaceLayoutCertificates.of_lower unique signatures sourceTyped rightTyped nonempty extract accepted typed
  obtain ⟨typedNode, contains, nodeType⟩ := rightTyped.stored_type
  have same := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
  have leafView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType assignment.target.type := by
    simpa only [same, nodeType] using rhsView
  have profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false := by
    simpa only [leafView] using operatorProfile
  have invalidEq : prepared.invalidProjection = invalid := by
    obtain ⟨route, _, preparedBy⟩ := actualPreparation
    exact (CompatibleMixedPreparation.of_prepare preparedBy).2.1
  exact CompatiblePlaceAssignmentReflection.reflects layout ordinary registryExtension meaning functionTypes faithful observations
    (fun receipt => missingTokens actualPreparation receipt) (by simpa only [invalidEq] using invalidTokens)
    certified found rhsView rhsType profile environments heaps locals slot (rootEq ▸ rootTyped binder binding) (lowering ▸ completed)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLowerReflection
end
