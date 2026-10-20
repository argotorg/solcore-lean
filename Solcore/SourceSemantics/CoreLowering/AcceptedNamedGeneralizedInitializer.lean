import Solcore.SourceSemantics.CoreLowering.AcceptedContextualGeneralizedInitializerReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCachedInputs

/-! Every actual cache position supplies its own accepted named compiler.
Each reached contextual expression then either retains the original generalized
initializer bundle or proves that the initializer override was absent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedGeneralizedInitializer
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open GeneralizedLocalInitializerCompilation (Receipt namedInputs)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

/-- Exact receipts of the original candidate list and root/child fuel values. -/
def Outcome (compilation : Compilation compiled.indexed named diagnostics code)
    (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  (∃ predecessor, fuel = predecessor + 1 ∧ ∃ initial binding,
    compiled.indexed.base.locals.bindings.find? (fun candidate =>
      decide (candidate.caller = named.signature.key ∧ candidate.initializer = id)) = some initial ∧
    compiled.indexed.base.locals.binding named.signature.key initial.binder.id = .ok binding ∧
    Nonempty (Receipt (namedInputs compilation predecessor fuel
      (context compiled.indexed named) scope id reasonAt) binding [] lowered)) ∨
  compiled.indexed.base.locals.bindings.find? (fun candidate =>
    decide (candidate.caller = named.signature.key ∧ candidate.initializer = id)) = none

/-- The successful original contextual call constructs the selected root policy.
Its initializer selection is a result of the proof, not an input law. -/
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
    Outcome compilation fuel scope id reasonAt lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ predecessor =>
    obtain ⟨root⟩ := CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      compilation record accepted
    obtain ⟨head⟩ := AcceptedNamedExpressionFlow.Head.of_accepted root.selected.accepted
    rcases AcceptedContextualGeneralizedInitializerReceipt.of_head root head with present | absent
    · obtain ⟨initial, binding, selected, located, _, receipt⟩ := present
      exact .inl ⟨predecessor, rfl, initial, binding, selected, located, receipt⟩
    · exact .inr absent

/-- Real final cache membership supplies the complete compilation witness and
exact specialization internally, including ordinary and method rows added later. -/
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
          Outcome compilation fuel scope id reasonAt lowered := by
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ := compiled_at compiled.indexed position
  refine ⟨diagnostics, code, cached, compilation, ?_⟩
  intro fuel source scope id reasonAt lowered accepted
  exact of_contextual compilation
    (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled position) accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedGeneralizedInitializer
