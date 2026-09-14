import Solcore.Frontend.ExpectedComputationLambdaOwnerProperties
import Solcore.Frontend.ExpectedDataLambdaInvocationProperties
import Solcore.Frontend.ClosedSourceOwnerCoreBodyProperties

/- Lift the checked saved-body image through injective owner relabeling.  The
mapped callee is still a source closure; it is never identified with Core. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- The mapped saved checker and identifier layout succeed; actual mapped caller
prefixes and every mapped call endpoint reflect to the original checked body
image.  Injectivity, but not surjectivity, is required. -/
theorem closedSourceExpectedDataLambda_invocation_mapOwners_core_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {types : TypeNameTable} {savedOwner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {savedEnvironment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types savedOwner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameSavedIds : Resolved.LocalScope.ids savedEnvironment =
      Resolved.LocalScope.ids inputs.context)
    {callerOwner : Resolved.DeclarationId} {callerNames : LocalNameTable}
    {callerCaptured : List (Resolved.LocalId × RuntimeValue)}
    {initialStore calleeStore : List RuntimeValue}
    {callSpan argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
    {argumentValue : Core.Value} {bodyStore : Core.Store}
    (calleeEvaluation : ClosedSourceExpressionEvaluates (mapping callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
      (mapRuntimeCapturedOwners mapping callerCaptured)
      (initialStore.map (RuntimeValue.mapOwners mapping)) callee
      (.sourceClosure source (mapping savedOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
        ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) savedEnvironment).map
          (fun row => (row.1, RuntimeValue.ofCore row.2))))
      (calleeStore.map (RuntimeValue.mapOwners mapping)))
    (argumentEvaluation : ClosedSourceExpressionEvaluates (mapping callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
      (mapRuntimeCapturedOwners mapping callerCaptured)
      (calleeStore.map (RuntimeValue.mapOwners mapping)) argument
      (RuntimeValue.ofCore argumentValue) (bodyStore.map RuntimeValue.ofCore))
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    elaborateExpectedComputationLambda? elaborateLocalExpression? types (mapping savedOwner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
        source (.function parameterType returnType) =
          some (.lambda parameterType returnType bodyCore) ∧
      Resolved.LocalScope.ids
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) savedEnvironment) =
        Resolved.LocalScope.ids
          (inputs.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).context ∧
      (ClosedSourceExpressionEvaluates (mapping callerOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
        (mapRuntimeCapturedOwners mapping callerCaptured)
        (initialStore.map (RuntimeValue.mapOwners mapping))
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
      ∃ value finalStore,
        actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates (argumentValue :: Resolved.LocalScope.values savedEnvironment)
          bodyStore bodyCore value finalStore) := by
  have mappedChecked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types (mapping savedOwner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
      source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore) := by
    rw [elaborateExpectedComputationLambda?_mapOwner mapping injective elaborateLocalExpression?
      (elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective))]
    exact checked
  have mappedSameIds : Resolved.LocalScope.ids
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) savedEnvironment) =
      Resolved.LocalScope.ids
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).context := by
    simpa only [LocalTypeInputs.mapIds_context, Resolved.LocalScope.ids_mapIds] using
      congrArg (List.map (ownerLocalIdMap mapping)) sameSavedIds
  have mappedCallee : ClosedSourceExpressionEvaluates (mapping callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
      (mapRuntimeCapturedOwners mapping callerCaptured)
      (initialStore.map (RuntimeValue.mapOwners mapping)) callee
      ((.sourceClosure source savedOwner inputs.names
        (savedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) : RuntimeValue).mapOwners mapping)
      (calleeStore.map (RuntimeValue.mapOwners mapping)) := by
    simpa only [RuntimeValue.mapOwners_sourceClosure, mapRuntimeCapturedOwners_ofCore] using calleeEvaluation
  have originalCallee :=
    (ClosedSourceExpressionEvaluates.mapOwners_iff mapping injective).mp mappedCallee
  have mappedArgument : ClosedSourceExpressionEvaluates (mapping callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
      (mapRuntimeCapturedOwners mapping callerCaptured)
      (calleeStore.map (RuntimeValue.mapOwners mapping)) argument
      ((RuntimeValue.ofCore argumentValue).mapOwners mapping)
      ((bodyStore.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping)) := by
    simpa only [RuntimeValue.mapOwners_ofCore, mapRuntimeStoreOwners_ofCore] using argumentEvaluation
  have originalArgument :=
    (ClosedSourceExpressionEvaluates.mapOwners_iff mapping injective).mp mappedArgument
  refine ⟨mappedChecked, mappedSameIds, ?_⟩
  constructor
  · intro actual
    obtain ⟨before, beforeStore, original, values, stores⟩ :=
      (ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective).mp actual
    obtain ⟨value, finalStore, beforeEq, beforeStoreEq, evaluated⟩ :=
      (closedSourceExpectedDataLambda_invocation_core_iff
        (callSpan := callSpan) (argumentsSpan := argumentsSpan)
        shape fragment checked sameSavedIds originalCallee originalArgument).mp original
    refine ⟨value, finalStore, ?_, ?_, evaluated⟩
    · simpa only [beforeEq, RuntimeValue.mapOwners_ofCore] using values
    · simpa only [beforeStoreEq, mapRuntimeStoreOwners_ofCore] using stores
  · rintro ⟨value, finalStore, rfl, rfl, evaluated⟩
    have original := (closedSourceExpectedDataLambda_invocation_core_iff
      (callSpan := callSpan) (argumentsSpan := argumentsSpan)
      shape fragment checked sameSavedIds originalCallee originalArgument).mpr
        ⟨value, finalStore, rfl, rfl, evaluated⟩
    simpa only [RuntimeValue.mapOwners_ofCore, mapRuntimeStoreOwners_ofCore] using
      original.mapOwners mapping injective

end Solcore.Frontend
