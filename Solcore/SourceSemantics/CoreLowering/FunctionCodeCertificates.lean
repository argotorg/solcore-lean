import Solcore.Frontend.SourceCoreFunctions

/-! Static certificates for the actual function-expression compiler.  A body
certificate is extracted from the supplied body compiler's accepted output;
it contains no execution premise here.  This layer exposes the exact emitted
parameter wrapper and lambda body, without asserting source frame validity,
stage-guard correctness, or call semantics. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FunctionCode

open Frontend Frontend.SourceInference

/-- Ordered results of the real parameter binder compiler. -/
inductive Parameters (policy : SourceCoreFunctions.Policy) (source : TypedSource) :
    SourceCoreLocalCell.Scope → List TypedBinder → List (TypedBinder × Core.Ty) →
      SourceCoreLocalCell.Scope → Prop where
  | nil {scope} : Parameters policy source scope [] [] scope
  | cons {scope finalScope parameter parameters type lowered}
      (head : policy.lowerBinder source scope parameter = .ok type)
      (tail : Parameters policy source ((parameter.id, type) :: scope) parameters lowered finalScope) :
      Parameters policy source scope (parameter :: parameters) ((parameter, type) :: lowered) finalScope

theorem Parameters.of_accepted {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Core.Ty)}
    (accepted : SourceCoreFunctions.lambdaParameters policy source scope parameters = .ok (lowered, finalScope)) :
    Parameters policy source scope parameters lowered finalScope := by
  induction parameters generalizing scope lowered with
  | nil =>
    simp only [SourceCoreFunctions.lambdaParameters, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact .nil
  | cons parameter parameters ih =>
    cases head : policy.lowerBinder source scope parameter with
    | error error => simp [SourceCoreFunctions.lambdaParameters, head, bind, Except.bind] at accepted
    | ok type =>
      cases tail : SourceCoreFunctions.lambdaParameters policy source ((parameter.id, type) :: scope) parameters with
      | error error => simp [SourceCoreFunctions.lambdaParameters, head, tail, bind, Except.bind] at accepted
      | ok pair =>
        obtain ⟨rest, bodyScope⟩ := pair
        simp only [SourceCoreFunctions.lambdaParameters, head, tail, bind, Except.bind,
          pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact .cons head (ih tail)

theorem Parameters.binders {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Core.Ty)}
    (certificate : Parameters policy source scope parameters lowered finalScope) :
    lowered.map Prod.fst = parameters := by
  induction certificate <;> simp_all

theorem Parameters.scope {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Core.Ty)}
    (certificate : Parameters policy source scope parameters lowered finalScope) :
    finalScope = (lowered.map fun entry => (entry.1.id, entry.2)).reverse ++ scope := by
  induction certificate with
  | nil => rfl
  | cons head tail ih => simpa [List.reverse_cons, List.append_assoc] using ih

abbrev BodyCertificate := TypedSource → SourceCoreLocalCell.Scope → List StatementId → Core.Ty → Core.Expr → Prop

/-- Exact recursive expression callback passed by the existing compiler. -/
def children (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) : SourceCoreFunctions.ExpressionLowerer :=
  fun budget source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context source scope id reasonAt

structure LambdaCertificate (bodyCertificate : BodyCertificate)
    (policy : SourceCoreFunctions.Policy) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (resultType : TypeSystem.Ty) (statements : List StatementId)
    (reportedType : Core.Ty) (lowered : SourceCoreBasic.LoweredExpr) where
  parameterType : TypeSystem.Ty
  parameterCore : Core.Ty
  resultCore : Core.Ty
  loweredParameters : List (TypedBinder × Core.Ty)
  bodyScope : SourceCoreLocalCell.Scope
  bodyCode : Core.Expr
  found : source.lookupExpression? id = some node
  read : policy.readExpression source id = .ok (node, reportedType)
  form : node.form = .lambda parameters resultType statements
  sourceType : node.type = .function parameterType resultType
  bundle : TypeSystem.Ty.productMany (parameters.map (·.scheme.body)) = parameterType
  parameterProjection : policy.projectType (.occurrence id.occurrence) parameterType = .ok parameterCore
  resultProjection : policy.projectType (.occurrence id.occurrence) resultType = .ok resultCore
  parametersTree : Parameters policy source scope parameters loweredParameters bodyScope
  bodyTree : bodyCertificate source bodyScope statements resultCore bodyCode
  emitted : lowered = ⟨reportedType, Core.LanguageResult.success (Core.TaggedFunction.anonymous
    (.lambda parameterCore (Core.LanguageResult.resultType resultCore)
      (SourceCoreFunctions.bindParameters loweredParameters resultCore (bodyCode.weakenAt loweredParameters.length))))⟩

/-- Static extraction is relative to the chosen metadata policy and body
compiler.  Their certificates are kept explicit, and no child evaluation is
assumed. This certificate uses the default tagged callable representation,
ordinary source-cell allocation and an absent special-expression hook. -/
theorem lambda_of_accepted
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : policy.lowerSpecial? = none)
    (ordinaryCells : policy.sourceCells = none)
    (defaultCallables : policy.callables = {})
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, reportedType))
    (form : node.form = .lambda parameters resultType statements)
    (extractBody : ∀ budget bodyScope type code,
      lowerBody (children policy lowerBody budget context) budget source bodyScope statements type
        reasonAt context.internalReason context.internalReason = .ok code →
      bodyCertificate source bodyScope statements type code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel context source scope id reasonAt = .ok lowered) :
    Nonempty (LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered) := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owned : id.occurrence.owner = source.owner
    · simp only [owned, ne_eq, not_true_eq_false, ↓reduceIte, found, ordinary, ordinaryCells, read, form,
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
                    simp only [compiledBody, pure, Except.pure, defaultCallables] at accepted
                    cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) reportedType
                        (Core.TaggedFunction.functionType parameterCore resultCore) with
                    | error error => simp [checked] at accepted
                    | ok doneUnit =>
                      cases doneUnit
                      simp only [checked] at accepted
                      cases accepted
                      exact ⟨⟨parameter, parameterCore, resultCore, loweredParameters, bodyScope, bodyCode,
                      found, read, form, type, bundle, parameterProjection, resultProjection,
                      Parameters.of_accepted compiledParameters, extractBody _ _ _ _ compiledBody, rfl⟩⟩
          · simp [bundle, resultSame, throw] at accepted
        · simp [bundle, throw] at accepted
      | «variable» | parameter | constructor | application | product | mapping | proxy | comptime | error =>
        simp [type] at accepted
    · simp [owned, bind, Except.bind, throw] at accepted

/-- The successful ordinary lambda branch itself supplies the metadata read.
The policy law only authenticates which source occurrence that read denotes. -/
theorem lambda_of_accepted_metadata
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : policy.lowerSpecial? = none)
    (ordinaryCells : policy.sourceCells = none)
    (defaultCallables : policy.callables = {})
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType statements)
    (readSound : ∀ selected type, policy.readExpression source id = .ok (selected, type) →
      source.lookupExpression? id = some selected)
    (extractBody : ∀ budget bodyScope type code,
      lowerBody (children policy lowerBody budget context) budget source bodyScope statements type
        reasonAt context.internalReason context.internalReason = .ok code →
      bodyCertificate source bodyScope statements type code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel context source scope id reasonAt = .ok lowered) :
    ∃ reportedType, Nonempty
      (LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered) := by
  cases read : policy.readExpression source id with
  | error error =>
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
      by_cases owned : id.occurrence.owner = source.owner <;>
        simp [owned, found, ordinary, form, read, bind, Except.bind, throw, pure, Except.pure] at accepted
  | ok pair =>
    obtain ⟨selected, type⟩ := pair
    have same := Option.some.inj ((readSound selected type read).symm.trans found)
    subst selected
    exact ⟨type, lambda_of_accepted ordinary ordinaryCells defaultCallables found read form extractBody accepted⟩

def LambdaCertificate.rawBody
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered) : Core.Expr :=
  SourceCoreFunctions.bindParameters certificate.loweredParameters certificate.resultCore
    (certificate.bodyCode.weakenAt certificate.loweredParameters.length)

/-- Whole-output Core checking supplies wrapper typing independently of the
body certificate's semantic interpretation. -/
theorem LambdaCertificate.rawBody_hasType
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered)
    {context : Core.Context} {definitions : Core.DataEnvironment}
    (typed : Core.HasType context lowered.expression
      (Core.LanguageResult.resultType (Core.TaggedFunction.functionType certificate.parameterCore certificate.resultCore)) definitions) :
    Core.HasType (certificate.parameterCore :: context) certificate.rawBody
      (Core.LanguageResult.resultType certificate.resultCore) definitions := by
  have emitted := congrArg SourceCoreBasic.LoweredExpr.expression certificate.emitted
  rw [emitted] at typed
  cases typed with
  | inRight _ function =>
    cases function with
    | pair _ closure =>
      cases closure with
      | lambda _ _ body => exact body

end Solcore.SourceSemantics.CoreLowering.FunctionCode
