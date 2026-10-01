import Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
import Solcore.SourceSemantics.CoreLowering.DecoratedFunctionCode
import Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy

/-! Static receipts from the actual lambda branch, including marked parameter
allocation and both production lambda hooks. Body compilation is retained as
an equation, with no premise about executing that body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCertificates
open Core Frontend SourceInference
open FunctionCode (children)

def parameterBody (policy : SourceCoreFunctions.Policy) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (parameters : List (TypedBinder × Core.Ty))
    (result : Core.Ty) (body : Core.Expr) : Except SourceCoreBasic.Error Core.Expr :=
  match policy.sourceCells with
  | none => pure (SourceCoreFunctions.bindParameters parameters result (body.weakenAt parameters.length))
  | some allocate => SourceCoreSourceCells.bindParameters allocate source scope parameters result
      SourceCoreFunctions.argumentProjection (body.weakenAt parameters.length)

structure Certificate (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId)
    (reported : Core.Ty) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  parameter : TypeSystem.Ty
  parameterCore : Core.Ty
  resultCore : Core.Ty
  sourceType : node.type = .function parameter result
  parameterTypes : TypeSystem.Ty.productMany (parameters.map (·.scheme.body)) = parameter
  parameterProjected : policy.projectType (.occurrence id.occurrence) parameter = .ok parameterCore
  resultProjected : policy.projectType (.occurrence id.occurrence) result = .ok resultCore
  loweredParameters : List (TypedBinder × Core.Ty)
  bodyScope : SourceCoreLocalCell.Scope
  parametersCompiled : SourceCoreFunctions.lambdaParameters policy source scope parameters = .ok (loweredParameters, bodyScope)
  body : Core.Expr
  bodyCompiled : lowerBody (children policy lowerBody fuel compilation) fuel source bodyScope statements resultCore
    reasonAt compilation.internalReason compilation.internalReason = .ok body
  allocatedBody : Core.Expr
  allocated : parameterBody policy source scope loweredParameters resultCore body = .ok allocatedBody
  rawBody : Core.Expr
  bodyHook : policy.rawLambdaBody compilation source scope node parameterCore resultCore allocatedBody = .ok rawBody
  checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) reported
    (policy.callables.functionType parameterCore resultCore) = .ok ()
  rawLambda : Core.Expr
  expressionHook : policy.rawLambdaExpression compilation source scope node parameterCore resultCore
    (.lambda parameterCore (LanguageResult.resultType resultCore) rawBody) = .ok rawLambda
  expression : Core.Expr
  decoration : policy.callables.decorateCallable compilation source node (.lambda id) parameterCore resultCore
    (LanguageResult.success (TaggedFunction.anonymous rawLambda)) = .ok expression
  emitted : lowered = ⟨reported, expression⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Core.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : DecoratedFunctionCode.SpecialPasses policy lowerBody fuel compilation source scope id reasonAt)
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, reported))
    (form : node.form = .lambda parameters result statements)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Certificate policy lowerBody fuel compilation source scope id node parameters result statements reported reasonAt lowered) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  change (match policy.lowerSpecial? with
    | none => pure none
    | some lower => lower compilation (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) compilation
          childSource childScope childId childReasonAt) (fuel + 1) source scope id reasonAt) = .ok none at ordinary
  simp only [pure, Except.pure] at ordinary
  cases hook : policy.lowerSpecial? <;> simp only [hook] at ordinary accepted
  all_goals
    try rw [ordinary] at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, read, form,
      bind, Except.bind, pure, Except.pure] at accepted
    cases sourceType : node.type with
    | function parameter sourceResult =>
      simp only [sourceType] at accepted
      by_cases bundle : TypeSystem.Ty.productMany (parameters.map (·.scheme.body)) = parameter
      · by_cases resultSame : result = sourceResult
        · subst sourceResult
          simp only [bundle, not_true_eq_false, ↓reduceIte] at accepted
          obtain ⟨parameterCore, parameterProjected, accepted⟩ := bind_ok accepted
          obtain ⟨resultCore, resultProjected, accepted⟩ := bind_ok accepted
          obtain ⟨⟨loweredParameters, bodyScope⟩, parametersCompiled, accepted⟩ := bind_ok accepted
          obtain ⟨body, bodyCompiled, accepted⟩ := bind_ok accepted
          have combined : (do
              let allocatedBody ← parameterBody policy source scope loweredParameters resultCore body
              let rawBody ← policy.rawLambdaBody compilation source scope node parameterCore resultCore allocatedBody
              SourceCoreBasic.ensureType (.occurrence id.occurrence) reported (policy.callables.functionType parameterCore resultCore)
              let rawLambda ← policy.rawLambdaExpression compilation source scope node parameterCore resultCore
                (.lambda parameterCore (LanguageResult.resultType resultCore) rawBody)
              let expression ← policy.callables.decorateCallable compilation source node (.lambda id) parameterCore resultCore
                (LanguageResult.success (TaggedFunction.anonymous rawLambda))
              pure (⟨reported, expression⟩ : SourceCoreBasic.LoweredExpr)) = .ok lowered := by
            cases cells : policy.sourceCells <;>
              simpa only [parameterBody, cells, bind, Except.bind, pure, Except.pure] using accepted
          obtain ⟨allocatedBody, allocated, accepted⟩ := bind_ok combined
          obtain ⟨rawBody, bodyHook, accepted⟩ := bind_ok accepted
          obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
          cases checked
          obtain ⟨rawLambda, expressionHook, accepted⟩ := bind_ok accepted
          obtain ⟨expression, decoration, accepted⟩ := bind_ok accepted
          cases accepted
          exact ⟨⟨parameter, parameterCore, resultCore, sourceType, bundle, parameterProjected, resultProjected,
            loweredParameters, bodyScope, parametersCompiled, body, bodyCompiled, allocatedBody, allocated,
            rawBody, bodyHook, checkedType, rawLambda, expressionHook, expression, decoration, rfl⟩⟩
        · simp [bundle, resultSame, throw] at accepted
      · simp [bundle, throw] at accepted
    | «variable» | parameter | constructor | application | product | mapping | proxy | comptime | error =>
      simp [sourceType] at accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCertificates
