import Solcore.SourceSemantics.CoreLowering.FunctionCodeCertificates

/-! Actual lambda compilation with a callable representation hook. The raw
lambda code certificate is retained beneath the hook's exact accepted result.
The parameter wrapper uses ordinary source-cell allocation. The hook is not
assumed to preserve meaning: the concrete representation layer
must authenticate its decoration separately. Special-expression handling must
fall through at this occurrence; a successful special hook is another branch. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DecoratedFunctionCode
open Frontend Frontend.SourceInference FunctionCode

/-- Exact static fallthrough from the optional special-expression compiler. -/
def SpecialPasses (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Core.Word) : Prop :=
  (match policy.lowerSpecial? with
    | none => pure none
    | some lower => lower context (children policy lowerBody fuel context) (fuel + 1) source scope id reasonAt) = .ok none

structure LambdaCertificate (bodyCertificate : BodyCertificate)
    (policy : SourceCoreFunctions.Policy) (context : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (resultType : TypeSystem.Ty) (statements : List StatementId)
    (reportedType : Core.Ty) (lowered : SourceCoreBasic.LoweredExpr) where
  rawLowered : SourceCoreBasic.LoweredExpr
  raw : FunctionCode.LambdaCertificate bodyCertificate policy source scope id node parameters resultType
    statements reportedType rawLowered
  expression : Core.Expr
  checkedType : SourceCoreBasic.ensureType (.occurrence id.occurrence) reportedType
    (policy.callables.functionType raw.parameterCore raw.resultCore) = .ok ()
  decoration : policy.callables.decorateCallable context source node (.lambda id)
    raw.parameterCore raw.resultCore rawLowered.expression = .ok expression
  emitted : lowered = ⟨reportedType, expression⟩

/-- Successful ordinary traversal supplies the real metadata, parameter/body
certificates and exact hook result. No child execution is a premise. -/
theorem lambda_of_accepted
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : SpecialPasses policy lowerBody fuel context source scope id reasonAt)
    (ordinaryCells : policy.sourceCells = none)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, reportedType))
    (form : node.form = .lambda parameters resultType statements)
    (extractBody : ∀ budget bodyScope type code,
      lowerBody (children policy lowerBody budget context) budget source bodyScope statements type
        reasonAt context.internalReason context.internalReason = .ok code →
      bodyCertificate source bodyScope statements type code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) context source scope id reasonAt = .ok lowered) :
    Nonempty (LambdaCertificate bodyCertificate policy context source scope id node parameters resultType statements reportedType lowered) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  change (match policy.lowerSpecial? with
    | none => pure none
    | some lower => lower context (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
          childSource childScope childId childReasonAt) (fuel + 1) source scope id reasonAt) = .ok none at ordinary
  simp only [pure, Except.pure] at ordinary
  cases hook : policy.lowerSpecial? <;> simp only [hook] at ordinary accepted
  all_goals
    try rw [ordinary] at accepted
    by_cases owned : id.occurrence.owner = source.owner
    · simp only [owned, ne_eq, not_true_eq_false, ↓reduceIte, found, read, form,
        bind, Except.bind, pure, Except.pure] at accepted
      cases type : node.type with
      | function parameter result =>
        simp only [type] at accepted
        by_cases bundle : TypeSystem.Ty.productMany (parameters.map (·.scheme.body)) = parameter
        · by_cases resultSame : resultType = result
          · subst result
            simp only [bundle, not_true_eq_false, ↓reduceIte] at accepted
            cases parameterProjection : policy.projectType (.occurrence id.occurrence) parameter with
            | error error => simp [parameterProjection] at accepted
            | ok parameterCore =>
              cases resultProjection : policy.projectType (.occurrence id.occurrence) resultType with
              | error error => simp [parameterProjection, resultProjection] at accepted
              | ok resultCore =>
                cases compiledParameters : SourceCoreFunctions.lambdaParameters policy source scope parameters with
                | error error => simp [parameterProjection, resultProjection, compiledParameters] at accepted
                | ok pair =>
                  obtain ⟨loweredParameters, bodyScope⟩ := pair
                  simp only [parameterProjection, resultProjection, compiledParameters] at accepted
                  cases compiledBody : lowerBody (children policy lowerBody fuel context) fuel source bodyScope
                      statements resultCore reasonAt context.internalReason context.internalReason with
                  | error error =>
                    change lowerBody (fun budget childSource childScope childId childReasonAt =>
                      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
                        childSource childScope childId childReasonAt) fuel source bodyScope statements resultCore
                          reasonAt context.internalReason context.internalReason = _ at compiledBody
                    simp [compiledBody] at accepted
                  | ok bodyCode =>
                    change lowerBody (fun budget childSource childScope childId childReasonAt =>
                      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
                        childSource childScope childId childReasonAt) fuel source bodyScope statements resultCore
                          reasonAt context.internalReason context.internalReason = _ at compiledBody
                    simp only [compiledBody, ordinaryCells] at accepted
                    cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) reportedType
                        (policy.callables.functionType parameterCore resultCore) with
                    | error error => simp [checked] at accepted
                    | ok doneUnit =>
                      cases doneUnit
                      simp only [checked] at accepted
                      let rawExpression := Core.LanguageResult.success (Core.TaggedFunction.anonymous
                        (.lambda parameterCore (Core.LanguageResult.resultType resultCore)
                          (SourceCoreFunctions.bindParameters loweredParameters resultCore
                            (bodyCode.weakenAt loweredParameters.length))))
                      cases decorated : policy.callables.decorateCallable context source node (.lambda id)
                          parameterCore resultCore rawExpression with
                      | error error => simp [rawExpression] at decorated; simp [decorated] at accepted
                      | ok expression =>
                        simp only [rawExpression] at decorated
                        simp only [decorated, Except.ok.injEq] at accepted
                        subst lowered
                        exact ⟨⟨_, ⟨parameter, parameterCore, resultCore, loweredParameters, bodyScope, bodyCode,
                          found, read, form, type, bundle, parameterProjection, resultProjection,
                          Parameters.of_accepted compiledParameters, extractBody _ _ _ _ compiledBody, rfl⟩,
                          expression, checked, decorated, rfl⟩⟩
          · simp [bundle, resultSame, throw] at accepted
        · simp [bundle, throw] at accepted
      | «variable» | parameter | constructor | application | product | mapping | proxy | comptime | error =>
        simp [type] at accepted
    · simp [owned, bind, Except.bind, throw] at accepted


/-- The successful branch supplies its own metadata read. The profile's read
soundness law identifies that metadata with the actual occurrence. -/
theorem lambda_of_accepted_metadata
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : SpecialPasses policy lowerBody fuel context source scope id reasonAt)
    (ordinaryCells : policy.sourceCells = none)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType statements)
    (readSound : ∀ selected type, policy.readExpression source id = .ok (selected, type) →
      source.lookupExpression? id = some selected)
    (extractBody : ∀ budget bodyScope type code,
      lowerBody (children policy lowerBody budget context) budget source bodyScope statements type
        reasonAt context.internalReason context.internalReason = .ok code →
      bodyCertificate source bodyScope statements type code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) context source scope id reasonAt = .ok lowered) :
    ∃ reportedType, Nonempty
      (LambdaCertificate bodyCertificate policy context source scope id node parameters resultType statements reportedType lowered) := by
  cases read : policy.readExpression source id with
  | error error =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    change (match policy.lowerSpecial? with
      | none => pure none
      | some lower => lower context (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
            childSource childScope childId childReasonAt) (fuel + 1) source scope id reasonAt) = .ok none at ordinary
    simp only [pure, Except.pure] at ordinary
    cases hook : policy.lowerSpecial? <;> simp only [hook] at ordinary accepted
    all_goals
      try rw [ordinary] at accepted
      by_cases owned : id.occurrence.owner = source.owner <;>
        simp [owned, found, form, read, bind, Except.bind, throw, pure, Except.pure] at accepted
  | ok pair =>
    obtain ⟨selected, type⟩ := pair
    have same := Option.some.inj ((readSound selected type read).symm.trans found)
    subst selected
    exact ⟨type, lambda_of_accepted ordinary ordinaryCells found read form extractBody accepted⟩

end Solcore.SourceSemantics.CoreLowering.DecoratedFunctionCode
