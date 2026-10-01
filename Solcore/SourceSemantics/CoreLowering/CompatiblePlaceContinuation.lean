import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentSuccess

/-! A completed assignment prefix can be followed by a universally certified
expression under execute's seven real administrative values. Closure captures
use that actual extended environment; no exact-value weakening is assumed.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceContinuation
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues CompatiblePayload CompatibleEquality CompatibleHeap
open GenericExpressionMeaning SourceCoreCompatibleDataPlaces

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
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {model : GenericHeap.PayloadModel catalog projects}
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
    meaning generated found environments heaps locals (DataPlaceChildExpressions.prefix_agrees sameEnvironment slots) trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    finish (by simpa only [DataPlaceChildExpressions.rename_prefix, length, Expr.rename_id, SourceCoreDataPlaces.shift, shift] using evaluated), rest⟩

/-- Whole assignment followed by a child outcome under the actual seven
hidden slots. The completed prefix is constructed from independent source
semantics here; it is not a caller-supplied execution assumption. -/
theorem preserves_from_source {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel compilation.checked.catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after)
    (invalidOperand : Word)
    {nextId : ExpressionId} {next : SourceCoreBasic.LoweredExpr} {nextNode : ExpressionNode}
    (nextGenerated : certificate scope nextId next) (nextFound : source.lookupExpression? nextId = some nextNode)
    {outcome : Dynamic.ExpressionOutcome} {finalHeap : Dynamic.Heap}
    (nextTrace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment after nextId outcome finalHeap) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next.expression next.type
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand) value finalStore ∧
      ResultRepresents (payloadModel compilation.checked registry functions) finalMap finalWorld nextNode.type next.type faults outcome value ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before finalHeap := by
  obtain ⟨_, prefixStore, prefixMap, prefixWorld, completed, _, prefixHeaps,
    prefixMaps, prefixWorlds, prefixFrame, prefixMetadata⟩ :=
    CompatiblePlaceAssignmentSuccess.preserves layout registryExtension meaning faithful observations rhsGenerated found rhsView rhsCoreType
      operatorProfile environments heaps locals slot rootTyped trace invalidOperand
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    preserves meaning nextGenerated nextFound completed (environments.extend prefixMaps prefixWorlds)
      prefixHeaps (locals.mono prefixMetadata) nextTrace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    prefixMaps.trans maps, prefixWorlds.trans worlds, prefixFrame.trans frame, prefixMetadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceContinuation
