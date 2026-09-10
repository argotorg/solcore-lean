import Solcore.Frontend.ExpectedComputationLambda
import Solcore.Frontend.ClosedSourceDataBodyProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

/- Exact checked saved-body evidence, with caller prefixes kept separate. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem shape_unique {source : Syntax.Expr} {leftName rightName : Syntax.Identifier}
    {leftBody rightBody : Syntax.Block}
    (left : SourceUnaryLambdaShape source leftName leftBody)
    (right : SourceUnaryLambdaShape source rightName rightBody) :
    leftName = rightName ∧ leftBody = rightBody :=
  Prod.mk.inj (Option.some.inj
    ((sourceUnaryLambdaShape?_iff.mpr left).symm.trans (sourceUnaryLambdaShape?_iff.mpr right)))

private theorem checked_body {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types owner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore)) :
    elaborateComputationReturnTree? elaborateLocalExpression? types owner
      (inputs.bindFresh owner name.value parameterType) body = some (bodyCore, returnType) := by
  have elaboration := (elaborateExpectedComputationLambda?_iff
    (ChildElab := fun table context expression core type =>
      elaborateLocalExpression? table context expression = some (core, type))
    (fun {_ _ _ _ _} => Iff.rfl)).mp checked
  obtain ⟨header, compiled, declared, _, _, bodyElaboration, coreShape⟩ := elaboration.provenance
  obtain ⟨parameterSame, returnSame, bodySame⟩ := Core.Expr.lambda.inj coreShape
  cases declared with
  | lambda parameterDeclaration returnMeaning =>
      cases parameterDeclaration with
      | inferred =>
          cases shape
          cases parameterSame; cases returnSame; cases bodySame
          exact (elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr bodyElaboration
      | typed meaning =>
          cases shape
          cases parameterSame; cases returnSame; cases bodySame
          exact (elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr bodyElaboration

private theorem body_image {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body) (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types owner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {argument : Core.Value} {store : Core.Store} {actual : RuntimeValue} {final : List RuntimeValue} :
    ClosedSourceBodyEvaluates owner
      ((name.value, Resolved.freshLocalId owner (inputs.names.map Prod.snd)) :: inputs.names)
      ((Resolved.freshLocalId owner (inputs.names.map Prod.snd), RuntimeValue.ofCore argument) ::
        environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) body actual final ↔
    ∃ value finalStore, actual = RuntimeValue.ofCore value ∧
      final = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (argument :: Resolved.LocalScope.values environment) store bodyCore value finalStore := by
  have extendedIds : Resolved.LocalScope.ids
      ((Resolved.freshLocalId owner inputs.ids, argument) :: environment) =
      Resolved.LocalScope.ids (inputs.bindFresh owner name.value parameterType).context := by
    simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons, Prod.fst]
      using congrArg (fun ids => Resolved.freshLocalId owner inputs.ids :: ids) sameIds
  have image := fragment.core_evaluates_iff (checked_body shape checked) extendedIds
    (actualValue := actual) (actualFinal := final) (initialStore := store)
  simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids, List.map_cons,
    Resolved.LocalScope.values, Prod.fst, Prod.snd] using image

/-- Actual caller prefixes invoke the checked original saved data body exactly. -/
theorem closedSourceExpectedDataLambda_invocation_core_iff
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
    (calleeEvaluation : ClosedSourceExpressionEvaluates callerOwner callerNames
      callerCaptured initialStore callee
      (.sourceClosure source savedOwner inputs.names
        (savedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))) calleeStore)
    (argumentEvaluation : ClosedSourceExpressionEvaluates callerOwner callerNames
      callerCaptured calleeStore argument (RuntimeValue.ofCore argumentValue)
      (bodyStore.map RuntimeValue.ofCore))
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (argumentValue :: Resolved.LocalScope.values savedEnvironment)
        bodyStore bodyCore value finalStore := by
  have image := body_image shape fragment checked sameSavedIds
    (argument := argumentValue) (store := bodyStore) (actual := actualValue) (final := actualFinal)
  constructor
  · intro evaluated
    cases evaluated with
    | creation impossible => cases impossible
    | call actualShape actualCallee actualArgument actualBody =>
        obtain ⟨sameCallee, sameCalleeStore⟩ := actualCallee.deterministic calleeEvaluation
        cases sameCallee; cases sameCalleeStore
        obtain ⟨sameArgument, sameArgumentStore⟩ := actualArgument.deterministic argumentEvaluation
        cases sameArgument; cases sameArgumentStore
        obtain ⟨sameName, sameBody⟩ := shape_unique actualShape shape
        cases sameName; cases sameBody
        exact image.mp actualBody
  · intro evaluated
    exact .call shape calleeEvaluation argumentEvaluation (image.mpr evaluated)

end Solcore.Frontend
