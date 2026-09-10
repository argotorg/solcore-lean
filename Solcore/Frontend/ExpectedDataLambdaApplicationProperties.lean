import Solcore.Frontend.ExpectedDataLambdaInvocationProperties

/- Direct original creation and an unprojected argument compose the whole Core application. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- A direct checked data lambda and original gated argument have the exact Core application image. -/
theorem closedSourceExpectedDataLambda_application_core_iff
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
    ClosedSourceExpressionEvaluates owner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore)
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore
        (.apply (.lambda parameterType returnType bodyCore) argumentCore) value finalStore := by
  have creation : ClosedSourceExpressionEvaluates owner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source
      (.sourceClosure source owner inputs.names
        (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))))
      (initialStore.map RuntimeValue.ofCore) := .creation shape
  constructor
  · intro evaluated
    cases evaluated with
    | creation impossible => cases impossible
    | call actualShape actualCallee actualArgument actualBody =>
        obtain ⟨sameCallee, sameStore⟩ := actualCallee.deterministic creation
        cases sameCallee; cases sameStore
        obtain ⟨argumentValue, argumentStore, sameArgument, sameArgumentStore, argumentCoreEvaluation⟩ :=
          (argumentFragment.core_evaluates_iff argumentResolution argumentLowering).mp actualArgument
        cases sameArgument; cases sameArgumentStore
        have callEvaluation := ClosedSourceExpressionEvaluates.call
          (span := callSpan) (argumentsSpan := argumentsSpan) actualShape actualCallee actualArgument actualBody
        obtain ⟨value, finalStore, sameValue, sameFinal, bodyCoreEvaluation⟩ :=
          (closedSourceExpectedDataLambda_invocation_core_iff shape fragment checked sameIds
            creation actualArgument).mp callEvaluation
        exact ⟨value, finalStore, sameValue, sameFinal, .apply .lambda argumentCoreEvaluation bodyCoreEvaluation⟩
  · rintro ⟨value, finalStore, rfl, rfl, evaluated⟩
    cases evaluated with
    | apply functionEvaluation argumentEvaluation bodyEvaluation =>
        cases functionEvaluation
        have argumentOriginal := (argumentFragment.core_evaluates_iff argumentResolution argumentLowering
          (owner := owner)).mpr ⟨_, _, rfl, rfl, argumentEvaluation⟩
        exact (closedSourceExpectedDataLambda_invocation_core_iff shape fragment checked sameIds
          creation argumentOriginal).mpr ⟨value, finalStore, rfl, rfl, bodyEvaluation⟩

end Solcore.Frontend
