import Solcore.SourceSemantics.SourceInferenceActualInitializerReceipt
import Solcore.SourceSemantics.SourceCompiledGeneralizationLifetimeAllocation
import Solcore.SourceSemantics.SourceCompiledActualBinderRetention
import Solcore.SourceSemantics.SourceCompiledActualCallContinuation

/-! Actual initialized declaration edges retain the exact child receipt and
carry its lifetime through the compiled outer generalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open ProtectedVariables SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {checkingFuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    {selected : BodySelection compiled named.specialized checkingFuel}
    {binder : TypedBinder} {initializerId : ExpressionId}
    {event : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution binder initializerId}

theorem ChildStep.lifetime_statement_initializer
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {result : StatementResult} {name : Syntax.Identifier}
    {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expected : Option Ty} {value : InferredExpression} {ready : State}
    (here : selected.InferenceCall (.statement (fuel + 1) context source expectedReturn initial result))
    (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
    (form : source.value = .letDecl name sourceType (some initializer))
    (allocation : initial.allocateStatementId = (id, allocated))
    (annotated : AnnotationExpected context sourceType expected)
    (child : (CallIndex.expression fuel context initializer expected allocated value ready).Accepted)
    (life : GeneralizationLifetime event allocated.inference.next ready [value.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  cases allocatedEq
  let receipt := ActualInitializerReceipt.statement accepted form annotated child
  have childHere : selected.InferenceCall
      (.expression fuel context initializer expected initial.allocateStatementId.2 value ready) :=
    .child here (.statement_initializer accepted form allocation annotated child)
  have readyState := ((selected.actualCall_inputs checked childHere).progress child).2.1
  have retained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders := by
    apply (selected.actualCall_binders_retained here).nodes
    exact List.mem_flatMap.mpr ⟨_, receipt.recorded, by
      simp [Node.initializedLetBinders, StatementForm.initializedLetBinders]⟩
  have finished := GeneralizationLifetime.finishStatementReceipt artifact checked position receipt
    readyState (selected.actualCall_final_extension checked childHere) retained life (by exact List.mem_singleton.mpr rfl)
  exact finished.1.restrict_outputs (by simp)

theorem ChildStep.lifetime_header_initializer
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {result : ForItemForm} {name : Syntax.Identifier}
    {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expected : Option Ty} {value : InferredExpression} {ready : State}
    (here : selected.InferenceCall (.forItem (fuel + 1) context source initial result final))
    (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
    (form : source.value = .letDecl name sourceType (some initializer))
    (annotated : AnnotationExpected context sourceType expected)
    (child : (CallIndex.expression fuel context initializer expected initial value ready).Accepted)
    (life : GeneralizationLifetime event initial.inference.next ready [value.type]) :
    GeneralizationLifetime event initial.inference.next final [] := by
  let receipt := ActualInitializerReceipt.header accepted form annotated child
  have childHere : selected.InferenceCall (.expression fuel context initializer expected initial value ready) :=
    .child here (.forItem_initializer accepted form annotated child)
  have readyState := ((selected.actualCall_inputs checked childHere).progress child).2.1
  have retained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders := by
    apply (selected.actualCall_binders_retained here).returned ⟨receipt.binding.1, .expression receipt.value.id⟩
    change _ ∈ forItemInitializedLetBindings result
    have recorded : result = .letDecl receipt.binding.1 (some receipt.value.id) := receipt.recorded
    rw [congrArg forItemInitializedLetBindings recorded]
    exact List.mem_singleton_self _
  have finished := GeneralizationLifetime.finishHeader artifact checked position receipt readyState
    (selected.actualCall_final_extension checked childHere) retained life (by exact List.mem_singleton.mpr rfl)
  exact finished.1.restrict_outputs (by simp)

end Solcore.SourceSemantics.SourceInferenceExecution
