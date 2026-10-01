import Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectedPrefix

/-! Finite evaluation inversion for the actual compatible hidden-cell wrapper.
Any completed whole match exposes the actual scrutinee completion. Failure
retains its effects and reaches neither allocation nor any candidate arm. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchScrutineeReflection
open Core Frontend SourceInference CoreProof ReadOnly
open CompatibleMatchCertificates
open CompatibleEncoding (bind_ok)

theorem initial_evaluation {allocator : Option SourceCoreSourceCells.Allocator}
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {references : Renaming} {binder : TypedBinder}
    {outputType payloadType : Ty} {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitialized allocator source scope references binder
      outputType payloadType initializer body = .ok code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {result : Value}
    (completed : Evaluates environment before (code.rename ξ) result after) :
    ∃ value middle, Evaluates environment before (initializer.rename ξ) value middle := by
  cases allocator with
  | none =>
    cases accepted
    rw [LoopRenaming.letInitialized] at completed
    cases completed with
    | caseLeft evaluated _ => exact ⟨_, _, evaluated⟩
    | caseRight evaluated _ => exact ⟨_, _, evaluated⟩
  | some allocate =>
    unfold SourceCoreSourceCells.letInitialized at accepted
    obtain ⟨allocation, generated, same⟩ := bind_ok accepted
    cases same
    cases completed with
    | caseLeft evaluated _ => exact ⟨_, _, evaluated⟩
    | caseRight evaluated _ => exact ⟨_, _, evaluated⟩

theorem failure_evaluation {allocator : Option SourceCoreSourceCells.Allocator}
    {source : TypedSource} {scope : SourceCoreSourceCells.Scope} {references : Renaming} {binder : TypedBinder}
    {outputType payloadType : Ty} {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitialized allocator source scope references binder
      outputType payloadType initializer body = .ok code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {inputType : Ty} {reason : Word}
    (failed : Evaluates environment before (initializer.rename ξ) (.inLeft inputType (.word reason)) after) :
    Evaluates environment before (code.rename ξ) (.inLeft outputType (.word reason)) after := by
  cases allocator with
  | none =>
    cases accepted
    rw [LoopRenaming.letInitialized]
    exact .caseLeft failed (.inLeft (.var rfl))
  | some allocate =>
    unfold SourceCoreSourceCells.letInitialized at accepted
    obtain ⟨allocation, generated, same⟩ := bind_ok accepted
    cases same
    exact .caseLeft failed (.inLeft (.var rfl))

/-- Reflection starts from whole Core completion and extracts the exact static
child certificate together with the child's finite completion; source child
execution remains the enclosing concrete expression Tree's conclusion. -/
theorem Certificate.initial_evaluation
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : SourceCoreSourceCells.Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    {environment : Environment} {before after : Store} {ξ : Renaming} {result : Value}
    (completed : Evaluates environment before (code.rename ξ) result after) :
    ∃ node lowered value middle, source.lookupExpression? resolution.scrutinee = some node ∧
      expressionCertificate scope resolution.scrutinee lowered ∧
      Evaluates environment before (lowered.expression.rename ξ) value middle := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    obtain ⟨value, middle, evaluated⟩ := CompatibleMatchScrutineeReflection.initial_evaluation hiddenCompiled completed
    exact ⟨_, _, value, middle, found, expression, evaluated⟩

/-- An independently established child failure has the actual whole match
failure envelope, with exactly the child's completed store. -/
theorem Certificate.failure_preserves
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : SourceCoreSourceCells.Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {environment : Environment} {before after : Store} {ξ : Renaming} {inputType : Ty} {reason : Word}
    (failed : Evaluates environment before (lowered.expression.rename ξ) (.inLeft inputType (.word reason)) after) :
    Evaluates environment before (code.rename ξ) (.inLeft (LocalLoop.controlType resultType) (.word reason)) after := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    have same := uniqueExpression _ expression
    subst lowered
    exact failure_evaluation hiddenCompiled failed

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchScrutineeReflection
