import Solcore.SourceSemantics.CoreLowering.AcceptedContextualSpecialActions
import Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCachedInputs

/-! Every successful contextual action of a real cached row supplies the same
root policy, selected special action and any reached ordinary lambda body.
There is no independent metadata scan, initializer selection or body profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedActionTrace
open Core Frontend SourceInference
open CallableIndexedNamedGeneration

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

structure Receipt (compilation : Compilation compiled.indexed named diagnostics code)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  predecessor : Nat
  budget : fuel = predecessor + 1
  root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := compiled) named diagnostics code compilation predecessor source scope id reasonAt lowered
  head : AcceptedNamedExpressionFlow.Head root.selected.policy root.selected.lowerBody predecessor
    (context compiled.indexed named) source scope id reasonAt lowered
  action : AcceptedContextualSpecialActions.Receipt compilation predecessor
    (context compiled.indexed named)
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child root.selected.policy
      root.selected.lowerBody predecessor (context compiled.indexed named))
    (predecessor + 1) source scope id reasonAt head.special
  lambdaBody : ∀ parameters result statements,
    head.special = none → head.node.form = .lambda parameters result statements →
    Nonempty (AcceptedContextualLambdaBody.Receipt root head parameters result statements)

/-- The literal accepted call, with its actual specialization record, constructs
the complete action receipt. All branch selection facts are derived inside. -/
theorem of_contextual (compilation : Compilation compiled.indexed named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      named.signature.key = .ok named.specialized)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key [])
      compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals compilation.parents
      compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none fuel source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt compilation fuel source scope id reasonAt lowered) := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ predecessor =>
    obtain ⟨root⟩ := CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      compilation record accepted
    obtain ⟨head⟩ := AcceptedNamedExpressionFlow.Head.of_accepted root.selected.accepted
    exact ⟨⟨predecessor, rfl, root, head, AcceptedContextualSpecialActions.of_head root head,
      fun _ _ _ plain form => AcceptedContextualLambdaBody.of_head root head plain form⟩⟩

/-- All final cache rows, including methods and rows added by preparation, retain
their real named compilation and the action receipts for every accepted call. -/
theorem at_cache {index : Nat}
    (position : compiled.indexed.base.functions[index]? = some named) :
    ∃ diagnostics code, compiled.indexed.secondPass.closures[index]? = some code ∧
      ∃ compilation : Compilation compiled.indexed named diagnostics code,
        ∀ (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
          (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr),
          SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
            ((representation compiled.indexed).atContext named.signature.key [])
            compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals compilation.parents
            compilation.own.assignments diagnostics (context compiled.indexed named)
            compiled.indexed.base.callableContext none none fuel source scope id reasonAt = .ok lowered →
          Nonempty (Receipt compilation fuel source scope id reasonAt lowered) := by
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ := compiled_at compiled.indexed position
  refine ⟨diagnostics, code, cached, compilation, ?_⟩
  intro fuel source scope id reasonAt lowered accepted
  exact of_contextual compilation
    (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled position) accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedActionTrace
