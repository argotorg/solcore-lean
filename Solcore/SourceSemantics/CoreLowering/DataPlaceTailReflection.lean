import Solcore.SourceSemantics.CoreLowering.DataPlaceRhsReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceSourceOrder

/-! Reflection of the actual modifier, latest-root setter and final mapped
write. The input RHS execution is the semantic output of prefix/RHS reflection.
Successful assignment exposes the real seven-slot continuation; all failure
branches terminate before that continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceTailReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution DataEquality

inductive Result (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked signatures functions program context evidence source faults place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore
  | committed {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (continuation : Evaluates (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      Result checked signatures functions program context evidence source faults place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore

private theorem initial_exists {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {optional : Value} {type : Ty}
    (related : GenericHeap.CellRepresents model mapping world cell optional type) :
    ∃ initial, Dynamic.RootInitialValue cell initial := by
  cases related with
  | initialized => exact ⟨_, .initialized⟩
  | @uninitialized sourceType _ projected =>
    by_cases mappingType : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingType
      exact ⟨_, .emptyMapping key value⟩
    · exact ⟨none, .uninitialized mappingType⟩

private theorem missing_token {faults : FaultRep} {missing : TypeSystem.Ty → Word}
    (tokens : ∀ type, faults (.missingMappingDefault type) (missing type))
    {initial : Option Dynamic.Value} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.ProjectionsFaults initial projections reason) : faults reason (DataPlaceExactFault.token missing reason) := by
  induction fault with
  | indexDefaultUnavailable => exact tokens _
  | indexFound _ _ _ ih | indexDefault _ _ _ _ ih | member _ _ ih => exact ih

/-- Complete the already reflected target and RHS. Source traversal order is
respected even though Core computes the scalar modifier first: initialized
modifiers succeed, while an absent snapshot implies an empty source path. -/
theorem reflects_ready {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {administrativeContext : Core.Context}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : IdentityFaithful identities)
    {steps : List Step}
    (raw : DataPlaceRouteCertificates.RawPath checked signatures source prepared.route.rootSourceType prepared.route.rootType
      steps place.projections place.type prepared.route.leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    (rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared prepared.route.rootSourceType)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (missingTokens : ∀ type, faults (.missingMappingDefault type) (missing type))
    {operator : Syntax.ValueAssignOp} {invalid : Word}
    (operatorProfile : operator = .equal ∨ place.type = .word ∨ place.type = .integer)
    (invalidToken : faults (.invalidAssignmentOperands operator) invalid)
    (setterTyped : HasType
      (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
        OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    {target : Dynamic.ResolvedPlace}
    (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
    (rootType : target.rootType = prepared.route.rootSourceType)
    (resolution : DataPlaceResolvedTarget.Execution checked signatures functions prepared codes sourceTypes place target
      coreEnvironment store mapping world before targetHeap)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (right : DataPlaceRhsReflection.Execution checked signatures functions program context evidence source environment prepared codes sourceTypes place target
      coreEnvironment store mapping world before targetHeap resolution rhs lowered)
    {next : Expr} {outputType : Ty} {result : Value}
    (completed : Evaluates (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        resolution.snapshot right.value coreEnvironment) right.store
      (DataPlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
    Result checked signatures functions program context evidence source faults place operator rhs environment coreEnvironment
      before store mapping world next outputType result finalStore := by
  have snapshotRep := resolution.snapshotRelated.extend right.maps right.worlds
  have keysRep := resolution.keysRelated.extend right.maps right.worlds
  have reference := resolution.reference.extend right.maps right.worlds
  have oldRead : ∃ cell, Dynamic.Heap.Reads targetHeap target.location cell ∧ cell.type = target.rootType := by
    cases sourceTrace with
    | intro _ _ _ read _ _ => exact ⟨_, read, rfl⟩
  obtain ⟨oldCell, oldRead, oldType⟩ := oldRead
  obtain ⟨cell, currentRead, currentType, _⟩ := right.metadata target.location oldCell oldRead
  have cellType : cell.type = target.rootType := currentType.trans oldType
  have sourceType : cell.type = prepared.route.rootSourceType := cellType.trans rootType
  have currentRaw : DataPlaceRouteCertificates.RawPath checked signatures source cell.type prepared.route.rootType
      steps place.projections place.type prepared.route.leafType sourceTypes := by rw [sourceType]; exact raw
  have currentLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared cell.type := by rw [sourceType]; exact rootLayout
  have keyLength : prepared.keyTypes.length = resolution.values.length := keyTypes ▸ keysRep.length.2
  cases completed with
  | caseLeft modifiedEvaluated failed =>
    obtain ⟨sameStore, represented⟩ := DataPlaceModifierReflection.reflects operatorProfile snapshotRep right.related
      (.var (index := 1) rfl) (.var (index := 0) rfl) modifiedEvaluated
    subst_vars
    cases represented with
    | uninitialized absent notEqual =>
      have empty := DataPlaceSourceOrder.resolve_none sourceTrace absent
      obtain ⟨_, _, cellRep⟩ := DataPlaceSnapshot.read_at right.heaps reference currentRead
      obtain ⟨initial, root⟩ := initial_exists cellRep
      have read : Dynamic.ProjectionsRead initial target.projections initial := empty ▸ .nil
      have fault : Dynamic.AssignmentOperandsInvalid operator target.selected right.right := absent ▸ .uninitialized notEqual
      cases failed with
      | inLeft valueEvaluated =>
        cases valueEvaluated with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst_vars
          exact .fault (.operands sourceTrace right.sourceTrace currentRead cellType root read fault) rfl invalidToken
            right.heaps (resolution.maps.trans right.maps) (resolution.worlds.trans right.worlds)
            (resolution.frame.trans right.frame) (resolution.metadata.trans right.metadata)
  | caseRight modifiedEvaluated remaining =>
    rename_i modifiedStore modifiedType modifiedValue
    obtain ⟨sameStore, represented⟩ := DataPlaceModifierReflection.reflects operatorProfile snapshotRep right.related
      (.var (index := 1) rfl) (.var (index := 0) rfl) modifiedEvaluated
    subst_vars
    cases represented with
    | @applied replacement _ applies replacementRep =>
      have typedEnvironment : RuntimeEnvironmentHasTypes right.world
          (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            resolution.snapshot right.value modifiedValue coreEnvironment)
          (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
            OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
          checked.catalog.definitions :=
        .cons replacementRep.runtime_hasType (.cons right.related.runtime_hasType (.cons snapshotRep.runtime_hasType
          (.cons (DataPlaceResolvedTarget.values_typed keysRep) (.cons (.cellRef reference.typed)
            ((environments.extend (resolution.maps.trans right.maps) (resolution.worlds.trans right.worlds)).runtime_hasTypes)))))
      have reflectSetter := fun {actual : Value} {after : Store}
          (ran : Evaluates (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              resolution.snapshot right.value modifiedValue coreEnvironment) right.store
            (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) actual after) =>
        DataPlaceSetterReflection.reflects_at functionTypes layouts observations faithful currentRaw preparation
          resolution.shaped keysRep keyLength currentLayout replacementRep right.heaps reference currentRead
          typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl) ran
      cases remaining with
      | caseLeft setterEvaluated failed =>
        obtain ⟨futureWorld, administrative, represented, extension, finalHeaps, _, frame, _⟩ := reflectSetter setterEvaluated
        cases represented with
        | missing root fault =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.structuralUpdate sourceTrace right.sourceTrace currentRead cellType root fault) rfl
                (missing_token missingTokens fault) finalHeaps (resolution.maps.trans right.maps)
                ((resolution.worlds.trans right.worlds).trans extension)
                ((resolution.frame.trans right.frame).trans frame) (resolution.metadata.trans right.metadata)
        | uninitialized root nonempty =>
          exact (DataPlaceSourceOrder.latest_uninitialized_impossible sourceTrace right.sourceTrace currentRead cellType root nonempty).elim
      | caseRight setterEvaluated remaining =>
        rename_i helperStore helperType updatedValue
        obtain ⟨futureWorld, administrative, represented, extension, helperHeaps, _, helperFrame, _⟩ := reflectSetter setterEvaluated
        cases represented with
        | @updated initial updated _ root changed updatedRep =>
          cases remaining with
          | letE writeEvaluated continuation =>
            obtain ⟨after, resultEq, sourceWritten, finalHeaps, writeFrame, metadata, _⟩ :=
              DataPlaceCommitReflection.reflects_storeCell helperHeaps (reference.extend (.refl _) extension) currentRead
                updatedRep (.var (index := 5) rfl) (.var (index := 0) rfl) writeEvaluated
            subst_vars
            have changed := DataPlaceCommitReflection.update_of_replacement changed (fun _ => applies)
            exact .committed (.intro sourceTrace right.sourceTrace (.intro currentRead cellType root changed sourceWritten))
              finalHeaps (resolution.maps.trans right.maps) ((resolution.worlds.trans right.worlds).trans extension)
              (((resolution.frame.trans right.frame).trans helperFrame).trans writeFrame)
              ((resolution.metadata.trans right.metadata).trans metadata) (slots :=
                [.unit, updatedValue, modifiedValue, right.value, resolution.snapshot, packValues resolution.values,
                  .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) rfl continuation

end Solcore.SourceSemantics.CoreLowering.DataPlaceTailReflection
