import Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentPrefix
import Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentWriteBack
import Solcore.SourceSemantics.CoreLowering.DataPlaceModifier

/-! Success of the full emitted assignment transaction. Child expressions use
their universal semantic IH; getter, modifier, latest-root setter and mapped
write are derived. The terminal continuation returns Unit. Statement-list
induction and automatic extraction of every static path layout remain separate.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentSuccess
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

theorem modifier_preserves {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {snapshot : Option Dynamic.Value}
    {right result : Dynamic.Value} {snapshotCore rightCore : Value} {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ sourceType = .word ∨ sourceType = .integer)
    (snapshotRep : DataPlaceSnapshot.OptionalRep catalog signatures functions mapping world sourceType type snapshot snapshotCore)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    (applied : Dynamic.AssignmentValueApplies operator snapshot right result)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : DataEquality.Selects environment snapshotExpression snapshotCore)
    (rightSelected : DataEquality.Selects environment rightExpression rightCore) (store : Store) (invalid : Word) :
    ∃ value, ValueRep catalog signatures functions mapping world sourceType result value type ∧
      Evaluates environment store
        (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inRight .word value) store := by
  by_cases equal : operator = .equal
  · subst operator
    cases applied
    exact ⟨rightCore, rightRep, DataPlaceModifier.equal_modified rightSelected store invalid⟩
  · have numeric : sourceType = .word ∨ sourceType = .integer := profile.resolve_left equal
    cases snapshotRep with
    | absent => cases applied; exact (equal rfl).elim
    | present represented =>
      obtain ⟨value, resultRep, evaluated, _⟩ := DataPlaceModifier.initialized_preserves numeric represented rightRep
        applied snapshotSelected rightSelected store invalid
      exact ⟨value, resultRep, evaluated⟩

/-- A successful independently specified source assignment has a matching
whole Core execution. No actual key/RHS/helper evaluation is a premise.
The complete payload relation retains callable leaves and ordered mapping keys.
Static helper typing and path-layout receipts remain explicit obligations. -/
theorem preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    (meaning : Preserves (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsSourceType : node.type = place.type) (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ place.type = .word ∨ place.type = .integer)
    (setterTyped : HasType
      (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
        OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap rhsHeap after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    {right updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootType : sourceTarget.rootType = prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (written : Dynamic.ResolvedPlaceWrites
      (fun _ updated => Dynamic.AssignmentValueApplies operator sourceTarget.selected right updated)
      rhsHeap sourceTarget updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updatedRoot after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression (LanguageResult.success .unit) .unit
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inRight .word .unit) finalStore ∧
      ValueRep checked.catalog signatures functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have sourceAssignment := Dynamic.SourcePlaceAssignment.intro resolve evaluate written
  obtain ⟨target, coreLookup⟩ := DataPlaceResolvedTarget.preserves layout meaning observations faithful layouts
    environments heaps locals slot rootType resolve
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i v selected; exact selected
  obtain ⟨rightValue, rhsStore, rhsMap, rhsWorld, evaluated, rightRep, rhsHeaps, rhsMaps, rhsWorlds, rhsFrame, rhsMetadata⟩ :=
    DataPlaceChildExpressions.preserves meaning rhsGenerated found
      (environments.extend target.maps target.worlds) target.heaps (locals.mono target.metadata) sameEnvironment
      [target.snapshot, packValues target.values, .cellRef (OptionalCell.cellType prepared.route.rootType) target.target]
      (.value evaluate)
  cases rightRep with
  | @value _ rightValue rightRep =>
    have rhsEvaluated : Evaluates
        (snapshotEnvironment prepared.route.rootType target.target (packValues target.values) target.snapshot coreEnvironment)
        target.store (shift 3 lowered.expression) (.inRight .word rightValue) rhsStore := by
      simpa only [Expr.rename_id, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
        snapshotEnvironment, keysEnvironment, referenceEnvironment] using evaluated
    have rightRep : ValueRep checked.catalog signatures functions rhsMap rhsWorld place.type right rightValue prepared.route.leafType := by
      simpa only [payloadModel, rhsSourceType, rhsCoreType] using rightRep
    have snapshotRep := target.snapshotRelated.extend rhsMaps rhsWorlds
    have keyRep := target.keysRelated.extend rhsMaps rhsWorlds
    have reference := target.reference.extend rhsMaps rhsWorlds
    cases written with
    | @intro _ _ cell initial _ sourceRead cellType initialValue update sourceWrite =>
      obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
      obtain ⟨replacementValue, replacementRep, modifiedEvaluated⟩ :=
        modifier_preserves operatorProfile snapshotRep rightRep applies
          (environment := rhsEnvironment prepared.route.rootType target.target (packValues target.values)
            target.snapshot rightValue coreEnvironment) (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
      obtain ⟨count, path⟩ := layout.paths target.shaped keyRep
      have sourceType : cell.type = prepared.route.rootSourceType := cellType.trans rootType
      have rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared cell.type := by
        simpa only [sourceType] using layout.root
      have currentPath : DataPayloadReadPaths.Path checked signatures functions rhsMap rhsWorld target.values
          cell.type prepared.route.rootType prepared.steps sourceTarget.projections place.type prepared.route.leafType count := by
        simpa only [sourceType] using path
      have keyLength : prepared.keyTypes.length = target.values.length := layout.keyTypes ▸ keyRep.length.2
      have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
          (modifiedEnvironment prepared.route.rootType target.target (packValues target.values) target.snapshot rightValue replacementValue coreEnvironment)
          (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
            OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
          checked.catalog.definitions :=
        .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons snapshotRep.runtime_hasType
          (.cons (DataPlaceResolvedTarget.values_typed keyRep) (.cons (.cellRef reference.typed)
            ((environments.extend (target.maps.trans rhsMaps) (target.worlds.trans rhsWorlds)).runtime_hasTypes)))))
      obtain ⟨updatedValue, helperStore, finalStore, finalWorld, old, updatedRep, setterEvaluated,
        helperRead, coreWritten, extension, finalHeaps, frame, metadata⟩ :=
        DataPlaceAssignmentWriteBack.preserves observations faithful layouts prepared keyLength rhsHeaps reference sourceRead
          rootLayout initialValue changed sourceWrite currentPath replacementRep typedEnvironment setterTyped
          (.var rfl) (.var rfl) (.var rfl)
      refine ⟨updatedValue, finalStore, rhsMap, finalWorld, sourceAssignment, ?_,
        by simpa only [sourceType] using updatedRep, finalHeaps, target.maps.trans rhsMaps,
        (target.worlds.trans rhsWorlds).trans extension, (target.frame.trans rhsFrame).trans frame,
        (target.metadata.trans rhsMetadata).trans metadata⟩
      apply execute_success (.var coreLookup) target.keysEvaluated target.snapshotEvaluated rhsEvaluated
        modifiedEvaluated setterEvaluated helperRead coreWritten
      simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] using
        (Evaluates.inRight (environment := writtenEnvironment prepared.route.rootType target.target
          (packValues target.values) target.snapshot rightValue replacementValue updatedValue coreEnvironment)
          (initialStore := finalStore) (leftType := .word) Evaluates.unit)

end Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentSuccess
