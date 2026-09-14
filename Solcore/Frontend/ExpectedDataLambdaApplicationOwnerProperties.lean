import Solcore.Frontend.ExpectedComputationLambdaOwnerProperties
import Solcore.Frontend.ExpectedDataLambdaInvocationOwnerProperties
import Solcore.Frontend.ExpectedDataLambdaApplicationProperties
import Solcore.Frontend.ClosedSourceOwnerCoreExpressionProperties

/- Direct application keeps the original checked lambda and argument lowering.
The owner map changes identities only, while the Core application stays literal. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- The mapped checker, identifier layout and argument stages all succeed, and
the mapped direct source application has exactly the old Core application image.
No argument runtime typing or closure conversion is asserted. -/
theorem closedSourceExpectedDataLambda_application_mapOwners_core_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types owner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {argument : Syntax.Expr} {resolvedArgument : Resolved.Expr} {argumentCore : Core.Expr}
    (argumentFragment : ClosedSourceDataExpression argument)
    (argumentResolution : ResolvesLocalExpression inputs.names argument resolvedArgument)
    (argumentLowering : Resolved.Lowers (Resolved.LocalScope.ids environment)
      resolvedArgument argumentCore)
    {initialStore : Core.Store} {callSpan argumentsSpan : Syntax.SourceSpan}
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    elaborateExpectedComputationLambda? elaborateLocalExpression? types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
        source (.function parameterType returnType) =
          some (.lambda parameterType returnType bodyCore) ∧
      Resolved.LocalScope.ids
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
        Resolved.LocalScope.ids
          (inputs.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).context ∧
      ResolvesLocalExpression (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
        argument (resolvedArgument.renameIds (ownerLocalIdMap mapping)) ∧
      Resolved.Lowers
          (Resolved.LocalScope.ids (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment))
          (resolvedArgument.renameIds (ownerLocalIdMap mapping)) argumentCore ∧
        (ClosedSourceExpressionEvaluates (mapping owner)
          (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
          ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map
            (fun row => (row.1, RuntimeValue.ofCore row.2)))
          (initialStore.map RuntimeValue.ofCore)
          ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
        ∃ value finalStore,
          actualValue = RuntimeValue.ofCore value ∧
          actualFinal = finalStore.map RuntimeValue.ofCore ∧
          Core.Evaluates (Resolved.LocalScope.values environment) initialStore
            (.apply (.lambda parameterType returnType bodyCore) argumentCore) value finalStore) := by
  have argumentStages := argumentFragment.mapOwners_core_evaluates_iff mapping injective
    (owner := owner) (names := inputs.names) (environment := environment)
    (initialStore := initialStore) (actualValue := actualValue) (actualFinal := actualFinal)
    argumentResolution argumentLowering
  have mappedChecked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
      source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore) := by
    rw [elaborateExpectedComputationLambda?_mapOwner mapping injective elaborateLocalExpression?
      (elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective))]
    exact checked
  have mappedSameIds : Resolved.LocalScope.ids
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
      Resolved.LocalScope.ids
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).context := by
    simpa only [LocalTypeInputs.mapIds_context, Resolved.LocalScope.ids_mapIds] using
      congrArg (List.map (ownerLocalIdMap mapping)) sameIds
  refine ⟨mappedChecked, mappedSameIds, argumentStages.1, argumentStages.2.1, ?_⟩
  constructor
  · intro actual
    have mapped : ClosedSourceExpressionEvaluates (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
        (mapRuntimeCapturedOwners mapping
          (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))))
        ((initialStore.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping))
        ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal := by
      simpa only [mapRuntimeCapturedOwners_ofCore, mapRuntimeStoreOwners_ofCore] using actual
    obtain ⟨before, beforeStore, original, values, stores⟩ :=
      (ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective).mp mapped
    obtain ⟨value, finalStore, beforeEq, beforeStoreEq, evaluated⟩ :=
      (closedSourceExpectedDataLambda_application_core_iff
        (callSpan := callSpan) (argumentsSpan := argumentsSpan)
        shape fragment checked sameIds argumentFragment argumentResolution argumentLowering).mp original
    refine ⟨value, finalStore, ?_, ?_, evaluated⟩
    · simpa only [beforeEq, RuntimeValue.mapOwners_ofCore] using values
    · simpa only [beforeStoreEq, mapRuntimeStoreOwners_ofCore] using stores
  · rintro ⟨value, finalStore, rfl, rfl, evaluated⟩
    have original := (closedSourceExpectedDataLambda_application_core_iff
      (callSpan := callSpan) (argumentsSpan := argumentsSpan)
      shape fragment checked sameIds argumentFragment argumentResolution argumentLowering).mpr
        ⟨value, finalStore, rfl, rfl, evaluated⟩
    simpa only [mapRuntimeCapturedOwners_ofCore, mapRuntimeStoreOwners_ofCore,
      RuntimeValue.mapOwners_ofCore] using original.mapOwners mapping injective

end Solcore.Frontend
