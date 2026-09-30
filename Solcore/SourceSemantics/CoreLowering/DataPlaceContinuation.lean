import Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentSuccess

/-! A completed assignment prefix can be followed by a universally certified
expression under execute's seven real administrative values. Closure captures
use that actual extended environment; no exact-value weakening is assumed.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceContinuation
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces

/-- Successful terminal Unit exposes the actual seven values and admits an
arbitrary continuation at the resulting store. All prefix evaluations are
reused exactly once, including the latest-root load and final write. -/
theorem plug {prepared : Prepared} {reference rhs : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    {environment : Environment} {before after : Store}
    (completed : Evaluates environment before
      (execute prepared reference keys rhs (LanguageResult.success .unit) .unit operator bitNot invalid)
      (.inRight .word .unit) after) :
    ∃ slots : Environment, slots.length = 7 ∧
      ∀ {next : Expr} {outputType : Ty} {value : Value} {finalStore : Store},
        Evaluates (slots ++ environment) after (shift 7 next) value finalStore →
        Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalid) value finalStore := by
  cases completed with
  | letE referenceEvaluated tail =>
    rename_i referenceStore referenceValue
    cases tail with
    | caseLeft _ impossible => cases impossible
    | caseRight keysEvaluated tail =>
      rename_i keyStore keyType keyValue
      cases tail with
      | caseLeft _ impossible => cases impossible
      | caseRight snapshotEvaluated tail =>
        rename_i snapshotStore snapshotType snapshotValue
        cases tail with
        | caseLeft _ impossible => cases impossible
        | caseRight rhsEvaluated tail =>
          rename_i rhsStore rhsType rightValue
          cases tail with
          | caseLeft _ impossible => cases impossible
          | caseRight modifiedEvaluated tail =>
            rename_i modifiedStore modifiedType modifiedValue
            cases tail with
            | caseLeft _ impossible => cases impossible
            | caseRight setterEvaluated tail =>
              rename_i setterStore setterType updatedValue
              cases tail with
              | letE writeEvaluated terminal =>
                rename_i writtenStore writtenValue
                simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] at terminal
                cases terminal with
                | inRight unitEvaluated =>
                  cases unitEvaluated
                  refine ⟨[writtenValue, updatedValue, modifiedValue, rightValue, snapshotValue, keyValue, referenceValue], rfl, ?_⟩
                  intro next outputType value finalStore continuation
                  exact .letE referenceEvaluated (.caseRight keysEvaluated (.caseRight snapshotEvaluated
                    (.caseRight rhsEvaluated (.caseRight modifiedEvaluated (.caseRight setterEvaluated
                      (.letE writeEvaluated continuation))))))

/-- A universal expression IH supplies the continuation evaluation at the
actual temporary slots. `completed` is an already proved assignment result,
not a child-runtime assumption or a field of a static compilation receipt. -/
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (meaning : Preserves model program context evidence source certificate faults)
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    {prepared : Prepared} {reference rhs : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    {coreEnvironment : Environment} {initialStore store : Store}
    (completed : Evaluates coreEnvironment initialStore
      (execute prepared reference keys rhs (LanguageResult.success .unit) .unit operator bitNot invalid)
      (.inRight .word .unit) store)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates coreEnvironment initialStore
        (execute prepared reference keys rhs lowered.expression lowered.type operator bitNot invalid) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨slots, length, finish⟩ := plug completed
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i v selected; exact selected
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, rest⟩ :=
    DataPlaceChildExpressions.preserves meaning generated found environments heaps locals sameEnvironment slots trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    finish (by simpa only [length, Expr.rename_id] using evaluated), rest⟩

/-- Full source-to-Core composition for an assignment followed by a certified
expression. The completed prefix passed to the algebraic plugging law above
is constructed here from source semantics, never assumed by the caller. -/
theorem preserves_from_source {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
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
    (invalidOperand : Word)
    {nextId : ExpressionId} {next : SourceCoreBasic.LoweredExpr} {nextNode : ExpressionNode}
    (nextGenerated : certificate scope nextId next) (nextFound : source.lookupExpression? nextId = some nextNode)
    {outcome : Dynamic.ExpressionOutcome} {finalHeap : Dynamic.Heap}
    (nextTrace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment after nextId outcome finalHeap) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updatedRoot after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next.expression next.type
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand) value finalStore ∧
      ResultRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld nextNode.type next.type faults outcome value ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before finalHeap := by
  obtain ⟨_, prefixStore, prefixMap, prefixWorld, sourceAssignment, completed, _, prefixHeaps,
    prefixMaps, prefixWorlds, prefixFrame, prefixMetadata⟩ :=
    DataPlaceAssignmentSuccess.preserves layout meaning observations faithful layouts rhsGenerated found rhsSourceType rhsCoreType
      operatorProfile setterTyped environments heaps locals slot rootType resolve evaluate written invalidOperand
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    preserves meaning nextGenerated nextFound completed (environments.extend prefixMaps prefixWorlds)
      prefixHeaps (locals.mono prefixMetadata) nextTrace
  exact ⟨value, finalStore, finalMap, finalWorld, sourceAssignment, evaluated, represented, finalHeaps,
    prefixMaps.trans maps, prefixWorlds.trans worlds, prefixFrame.trans frame, prefixMetadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceContinuation
