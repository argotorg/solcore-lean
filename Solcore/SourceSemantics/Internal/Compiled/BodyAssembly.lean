import Solcore.SourceSemantics.Internal.Compiled.ActualEntries
import Solcore.SourceSemantics.Internal.Execution.ExpressionProgress
import Solcore.SourceSemantics.Internal.Execution.CallGraph
import Solcore.SourceSemantics.Internal.Compiled.LifetimeSeeds
import Solcore.SourceSemantics.Internal.Execution.StatementProgress
import Solcore.SourceSemantics.Internal.Privacy.Lifetimes
import Solcore.SourceSemantics.Internal.Execution.TemplateBacking
import Solcore.SourceSemantics.Internal.Execution.CallInputs
import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.Expressions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodBodies
import Solcore.SourceSemantics.Internal.Compiled.MatchEntries
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.Internal.Selected.Matches
import Solcore.SourceSemantics.Internal.Compiled.Statements
import Solcore.SourceSemantics.Internal.Compiled.Loops

/-!
# Assembly of checked bodies

The recursive assembly closes original body typing. Actual call paths reach their parents,
generalized owners are compared and separated, match statements and the statement dispatch are
closed, and `SourceCompiledGeneralizedSoundness.checked_body_of_barriers` remains conditional on the
initializer barriers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualCallContinuation
/-! The selected checker receipt supplies the continuation of every reached
inference call through the final return check and source finalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution

namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem actualCall_continuation (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    call.final.InferenceProgress selected.body.body.state :=
  here.suffixProgress (selected.inferenceCall_inputs checked)

theorem actualCall_final_extension (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    selected.body.finalized.substitution.SemanticallyExtends call.final.inference.substitution :=
  (selected.inferenceProgress checked).final_substitution.trans
    (selected.actualCall_continuation checked here).substitution_extends

theorem actualCall_initial_extension (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    selected.body.finalized.substitution.SemanticallyExtends call.initial.inference.substitution :=
  (selected.actualCall_final_extension checked here).trans
    ((selected.actualCall_inputs checked here).progress here.accepted).1.substitution_extends

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualInitializerLifetime
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualLifetimeTraversal
/-! Every actual child lifetime reaches its actual parent. The two initialized
edges consume the same cached body and exact declaration receipts. -/
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
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
namespace ChildStep
theorem lifetime_statement
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement} {expected : Ty}
    {initial : State} {result : StatementResult} {child : CallIndex}
    (inputs : (CallIndex.statement fuel context source expected initial result).Inputs)
    (step : ChildStep (.statement fuel context source expected initial result) child)
    (here : selected.InferenceCall (.statement fuel context source expected initial result))
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  cases step
  all_goals first
  | solve | apply ChildStep.lifetime_statement_initializer artifact checked position <;> assumption
  | solve | apply ActualStatementLifetime.statement_return <;> assumption
  | solve | apply ActualStatementLifetime.statement_expression <;> assumption
  | solve | apply ActualStatementLifetime.statement_block <;> assumption
  | solve | apply ActualStatementLifetime.statement_assignment <;> assumption
  | solve | apply ActualStatementLifetime.statement_bitnot <;> assumption
  | solve | apply ActualStatementLifetime.statement_if_condition <;> assumption
  | solve | apply ActualStatementLifetime.statement_if_then <;> assumption
  | solve | apply ActualStatementLifetime.statement_if_else <;> assumption
  | solve | apply ActualStatementLifetime.statement_while_condition <;> assumption
  | solve | apply ActualStatementLifetime.statement_while_body <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_initializer <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_condition <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_body <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_post <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_single <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_many <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_cases <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_default <;> assumption

theorem lifetime_forItem
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {value : ForItemForm} {child : CallIndex}
    (inputs : (CallIndex.forItem fuel context source initial value final).Inputs)
    (step : ChildStep (.forItem fuel context source initial value final) child)
    (here : selected.InferenceCall (.forItem fuel context source initial value final))
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [] := by
  cases step
  all_goals first
  | solve | apply ChildStep.lifetime_header_initializer artifact checked position <;> assumption
  | solve | apply ActualStatementLifetime.forItem_expression <;> assumption
  | solve | apply ActualStatementLifetime.forItem_assignment <;> assumption
  | solve | apply ActualStatementLifetime.forItem_bitnot <;> assumption

theorem lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {parent child : CallIndex}
    (here : selected.InferenceCall parent) (step : ChildStep parent child)
    (life : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event parent.initial.inference.next parent.final parent.outputTypes := by
  have inputs := selected.actualCall_inputs checked here
  cases parent with
  | expression => exact step.lifetime_expression inputs life
  | constructorApplication => exact step.lifetime_constructorApplication inputs life
  | constructorArguments => exact step.lifetime_constructorArguments inputs life
  | statements => exact step.lifetime_statements inputs life
  | statement => exact step.lifetime_statement artifact checked position inputs here life
  | forItems => exact step.lifetime_forItems inputs life
  | forItem => exact step.lifetime_forItem artifact checked position inputs here life
  | place => exact step.lifetime_place inputs life
  | assignedValue => exact step.lifetime_assignedValue inputs life
  | expressions => exact step.lifetime_expressions inputs life
  | matchCases => exact step.lifetime_matchCases inputs life

end ChildStep

theorem CallOccurrence.lifetime_at
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {earlier call : CallIndex} (reached : selected.InferenceCall earlier)
    (path : CallOccurrence earlier call)
    (life : GeneralizationLifetime event call.initial.inference.next call.final call.outputTypes) :
    GeneralizationLifetime event earlier.initial.inference.next earlier.final earlier.outputTypes := by
  induction path with
  | root accepted => exact life
  | child prior step ih =>
      exact ih (step.lifetime artifact checked position (reached.trans prior) life)

theorem CallOccurrence.lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {call : CallIndex} (here : selected.InferenceCall call)
    (life : GeneralizationLifetime event call.initial.inference.next call.final call.outputTypes) :
    GeneralizationLifetime event selected.inferenceCall.initial.inference.next
      selected.inferenceCall.final selected.inferenceCall.outputTypes := by
  induction here with
  | root accepted => exact life
  | child prior step ih =>
      exact ih (step.lifetime artifact checked position prior life)

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualGeneralizationLifetime
/-! Every reached initialized declaration starts a lifetime from the real
entry invariants, then carries it through all actual enclosing calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open ProtectedVariables SourceCompiledGeneralizedSoundness SourceInferenceExecution
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {checkingFuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized checkingFuel)

theorem statementReceipt_retained
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (here : selected.InferenceCall (.statement (fuel + 1) context source expectedReturn initial result))
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result) :
    receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders := by
  apply (selected.actualCall_binders_retained here).nodes
  exact List.mem_flatMap.mpr ⟨_, receipt.recorded, by
    simp [Node.initializedLetBinders, StatementForm.initializedLetBinders]⟩

theorem headerReceipt_retained
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (here : selected.InferenceCall (.forItem (fuel + 1) context source initial result.1 result.2))
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result) :
    receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders := by
  apply (selected.actualCall_binders_retained here).returned ⟨receipt.binding.1, .expression receipt.value.id⟩
  change _ ∈ forItemInitializedLetBindings result.1
  rw [congrArg forItemInitializedLetBindings receipt.recorded]
  exact List.mem_singleton_self _

theorem statement_lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (here : selected.InferenceCall (.statement (fuel + 1) context source expectedReturn initial result))
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected)) :
    ∃ ready extension,
      GeneralizationLifetime
        (RawStatementLifetime.event (finalized := selected.body.finalized)
          receipt ready extension retained (selected.statementReceipt_retained here receipt))
        selected.inferenceCall.initial.inference.next selected.body.body.state [] := by
  have inputs := selected.actualCall_inputs checked here
  obtain ⟨ready, extension, seed⟩ := RawStatementLifetime.lifetime selected.body.resources receipt
    inputs.ready inputs.wellFormed inputs.catalog.catalog inputs.catalog.formation inputs.catalog.canonical
    (selected.actualCall_liveTemplatesBacked checked here)
    (selected.actualCall_captureOrigins checked here) retained
    (selected.statementReceipt_retained here receipt) (selected.actualCall_final_extension checked here)
  exact ⟨ready, extension, (CallOccurrence.lifetime artifact checked position here seed).restrict_outputs (by simp)⟩

theorem header_lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (here : selected.InferenceCall (.forItem (fuel + 1) context source initial result.1 result.2))
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected)) :
    ∃ ready extension,
      GeneralizationLifetime
        (RawHeaderLifetime.event (finalized := selected.body.finalized)
          receipt ready extension retained (selected.headerReceipt_retained here receipt))
        selected.inferenceCall.initial.inference.next selected.body.body.state [] := by
  have inputs := selected.actualCall_inputs checked here
  obtain ⟨ready, extension, seed⟩ := RawHeaderLifetime.lifetime selected.body.resources receipt
    inputs.ready inputs.wellFormed inputs.catalog.catalog inputs.catalog.formation inputs.catalog.canonical
    (selected.actualCall_liveTemplatesBacked checked here)
    (selected.actualCall_captureOrigins checked here) retained
    (selected.headerReceipt_retained here receipt) (selected.actualCall_final_extension checked here)
  exact ⟨ready, extension, (CallOccurrence.lifetime artifact checked position here seed).restrict_outputs (by simp)⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualGeneralizationSeparation
/-! Exact sites, lifetime bounds and actual path divergence compare retained
owners. Ancestors use the real initializer output, siblings use allocator order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open ProtectedVariables SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {checkingFuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    {selected : BodySelection compiled named.specialized checkingFuel}

theorem Site.seed
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    {call : CallIndex} {binder : TypedBinder} {initializer : ExpressionId}
    (here : selected.InferenceCall call) (site : Site call binder initializer)
    (retained : ({binder, initializer := .expression initializer} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected)) :
    ∃ event : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution binder initializer,
      GeneralizationLifetime event call.initial.inference.next call.final call.outputTypes := by
  have inputs := selected.actualCall_inputs checked here
  cases site with
  | statement receipt =>
      obtain ⟨ready, extension, seed⟩ := RawStatementLifetime.lifetime selected.body.resources receipt
        inputs.ready inputs.wellFormed inputs.catalog.catalog inputs.catalog.formation inputs.catalog.canonical
        (selected.actualCall_liveTemplatesBacked checked here)
        (selected.actualCall_captureOrigins checked here) retained
        (selected.statementReceipt_retained here receipt) (selected.actualCall_final_extension checked here)
      exact ⟨_, seed⟩
  | header receipt =>
      obtain ⟨ready, extension, seed⟩ := RawHeaderLifetime.lifetime selected.body.resources receipt
        inputs.ready inputs.wellFormed inputs.catalog.catalog inputs.catalog.formation inputs.catalog.canonical
        (selected.actualCall_liveTemplatesBacked checked here)
        (selected.actualCall_captureOrigins checked here) retained
        (selected.headerReceipt_retained here receipt) (selected.actualCall_final_extension checked here)
      exact ⟨_, seed⟩

theorem Site.ancestor_excludes
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {outerCall innerCall : CallIndex} {outer inner : TypedBinder} {outerId innerId : ExpressionId}
    (here : selected.InferenceCall outerCall)
    (outerSite : Site outerCall outer outerId) (innerSite : Site innerCall inner innerId)
    (path : CallOccurrence outerCall innerCall) (different : outer ≠ inner)
    {event : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution inner innerId}
    (seed : GeneralizationLifetime event innerCall.initial.inference.next innerCall.final innerCall.outputTypes) :
    ∀ q ∈ outer.scheme.quantified, q ∉ inner.scheme.quantified := by
  rcases path.uncons with same | ⟨child, step, rest⟩
  · cases same
    exact False.elim (different (outerSite.unique innerSite).1)
  · obtain ⟨actualChild, actualStep, unique, quantifiedOutputs⟩ := outerSite.initializer_child here.accepted
    have same := unique child step
    cases same
    have life := CallOccurrence.lifetime_at artifact checked position (.child here actualStep) rest seed
    intro q outerQuantified innerQuantified
    obtain ⟨type, member, occurs⟩ := quantifiedOutputs q outerQuantified
    exact (life.values type member) q occurs innerQuantified

theorem Site.excludes_of_child_order
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    (ordered : ∀ {parent first second}, selected.InferenceCall parent →
      ChildStep parent first → ChildStep parent second → first.Ordered second)
    {leftCall rightCall : CallIndex} {left right : TypedBinder} {leftId rightId : ExpressionId}
    (leftHere : selected.InferenceCall leftCall) (rightHere : selected.InferenceCall rightCall)
    (leftSite : Site leftCall left leftId) (rightSite : Site rightCall right rightId)
    (different : left ≠ right)
    {leftEvent : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution left leftId}
    {rightEvent : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution right rightId}
    (leftSeed : GeneralizationLifetime leftEvent leftCall.initial.inference.next leftCall.final leftCall.outputTypes)
    (rightSeed : GeneralizationLifetime rightEvent rightCall.initial.inference.next rightCall.final rightCall.outputTypes) :
    ∀ q ∈ left.scheme.quantified, q ∉ right.scheme.quantified := by
  rcases leftHere.compare_paths rightHere with forward | backward |
    ⟨parent, first, second, reached, a, b, distinct, rest, other⟩
  · exact leftSite.ancestor_excludes artifact checked position leftHere rightSite forward different rightSeed
  · have reversed := rightSite.ancestor_excludes artifact checked position rightHere leftSite backward
      (fun same => different same.symm) leftSeed
    exact fun q leftQuantified rightQuantified => reversed q rightQuantified leftQuantified
  · have leftLife := CallOccurrence.lifetime_at artifact checked position (.child reached a) rest leftSeed
    have rightLife := CallOccurrence.lifetime_at artifact checked position (.child reached b) other rightSeed
    rcases ordered reached a b with same | earlier | later
    · exact False.elim (distinct same)
    · intro q leftQuantified rightQuantified
      have lower := Nat.le_trans rightLife.createdAfter (rightLife.allocated q rightQuantified)
      have upper := Nat.lt_of_lt_of_le (leftLife.bound q leftQuantified) earlier
      exact Nat.not_lt_of_ge lower upper
    · intro q leftQuantified rightQuantified
      have lower := Nat.le_trans leftLife.createdAfter (leftLife.allocated q leftQuantified)
      have upper := Nat.lt_of_lt_of_le (rightLife.bound q rightQuantified) later
      exact Nat.not_lt_of_ge lower upper

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualQuantifierSeparation
/-! Every retained initialized owner comes from its actual inference call.
Comparing those paths derives quantifier separation for the complete body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open ProtectedVariables SourceCompiledGeneralizedSoundness SourceInferenceExecution
open ActualGeneralization

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}

theorem BodySelection.initialized_quantifiers_disjoint
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {current : InitializedLetBinding}
    (member : current ∈ initializedLetBindings (evidenceSource selected)) :
    ∀ other ∈ initializedLetBindings (evidenceSource selected), other.binder ≠ current.binder →
      ∀ q ∈ current.binder.scheme.quantified, q ∉ other.binder.scheme.quantified := by
  obtain ⟨leftId, leftForm, leftOrigin⟩ := selected.actual_initialized_origin member
  obtain ⟨leftCall, leftHere, leftSite⟩ := leftOrigin.site
  have leftRetained : ({binder := current.binder, initializer := .expression leftId} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected) := by
    simpa only [← leftForm] using member
  obtain ⟨leftEvent, leftSeed⟩ := leftSite.seed checked leftHere leftRetained
  intro other otherMember different
  obtain ⟨rightId, rightForm, rightOrigin⟩ := selected.actual_initialized_origin otherMember
  obtain ⟨rightCall, rightHere, rightSite⟩ := rightOrigin.site
  have rightRetained : ({binder := other.binder, initializer := .expression rightId} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected) := by
    simpa only [← rightForm] using otherMember
  obtain ⟨rightEvent, rightSeed⟩ := rightSite.seed checked rightHere rightRetained
  exact Site.excludes_of_child_order artifact checked position
    (fun reached first second => ChildStep.ordered (selected.actualCall_inputs checked reached) first second)
    leftHere rightHere leftSite rightSite (fun same => different same.symm) leftSeed rightSeed

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedBodyEntry
/-! The original selected checker call supplies the complete recursive body
entry. Only the declared input parameters are monomorphic; no condition is
placed on local schemes introduced by the body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem selected_original_interfaces (selected : BodySelection compiled row fuel)
    (member : row ∈ compiled.plan.specializations) :
    ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource := by
  have validated := compiled.plan_validated
  unfold SourceCompilationPlan.validateExecutablePlanEvidence at validated
  cases prepared : SourceCompilationPlan.prepareExecutablePlanEvidence compiled.program compiled.plan with
  | error error => rw [prepared] at validated; cases validated
  | ok plan =>
      have covered := CoreLowering.CallableCoercionPreparation.of_accepted_with prepared
      have actual := CoreLowering.SelectedCompilationCoercionInterfaces.of_covered
        (covered.2 row (covered.1.entries.subset member))
      rw [selected.specialized] at actual
      have original := CoreLowering.SelectedCompilationCoercionInterfaces.of_applied actual
      simpa only [checkingContext, context, ExecutableCoercionInterfaces.BodyInterfaces, selected.body.source,
        selected.body.solved] using original

theorem selected_body_header {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    CheckedBodyHeaderWellFormed compiled.program.signatures selected.signature selected.original := by
  exact selected.header checked

private theorem input_context_fields {owner : Resolved.DeclarationId}
    {base target : SourceSemantics.Context} {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types target) :
    target.signatures = base.signatures ∧
    target.typeParameters = base.typeParameters ∧
    target.currentDeclaration = base.currentDeclaration ∧
    target.residualTypeVariables = base.residualTypeVariables ∧
    target.solvedRequirements = base.solvedRequirements := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons _ head _ ih =>
      exact ⟨ih.1.trans head.context_fields.1,
        ih.2.1.trans head.context_fields.2.2.1,
        ih.2.2.1.trans head.context_fields.2.1,
        ih.2.2.2.1.trans head.residualTypeVariables_eq,
        ih.2.2.2.2.trans head.context_fields.2.2.2.2⟩

private theorem input_type_formed {owner : Resolved.DeclarationId}
    {base target : SourceSemantics.Context} {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types target) {type : Ty}
    (formed : TypeWellFormed base type) : TypeWellFormed target type := by
  induction extension with
  | nil => exact formed
  | cons _ head _ ih =>
      cases head
      exact ih (formed.withLocal _ _ _)

private theorem returned_source (selected : BodySelection compiled row fuel) :
    evidenceSource selected = selected.body.body.state.toTypedSource (bodyRoots selected) := by
  have header := Detail.unify_state_header selected.body.unified
  have owner := congrArg State.Header.owner header
  have inputs := congrArg State.Header.inputs header
  change selected.body.returned.owner = selected.body.body.state.owner at owner
  change selected.body.returned.inputs = selected.body.body.state.inputs at inputs
  simp only [evidenceSource, State.toTypedSource, owner, inputs, selected.body.returned_nodes]

structure BodyEntry (selected : BodySelection compiled row fuel)
    (target : SourceSemantics.Context) : Prop where
  inputs : MonoBindersExtend selected.signature.id
    (checkedBodyContext compiled.program.signatures selected.signature selected.original)
    selected.original.typedBody.inputs selected.signature.parameterTypes target
  returnSafe : ∀ binder ∈ (initial selected.signature selected.body.declaration).localBinders,
    ProtectedVariables.Safe binder.scheme.quantified
      (initial selected.signature selected.body.declaration)
      (Ty.productMany selected.signature.returnTypes)
  returnAdmissible : TypeAdmissible target
    (selected.body.finalized.substitution.apply (Ty.productMany selected.signature.returnTypes))
  boundary : StatementsBoundary selected fuel (checkingContext selected)
    selected.signature.source.value.body.value (Ty.productMany selected.signature.returnTypes)
    (initial selected.signature selected.body.declaration) selected.body.body [] target

/-- All entry conditions belong to the same original successful body check.
Actual executable preparation supplies the complete source interfaces. -/
theorem body_entry_of_interfaces {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource) :
    ∃ target, BodyEntry selected target := by
  have header := selected_body_header selected checked
  obtain ⟨target, inputs⟩ := header.inputs_extend
  have progress := selected.inferenceProgress checked
  have owner : selected.body.declaration.id = selected.signature.id :=
    (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have inputExtension : MonoBindersExtend selected.body.declaration.id
      (checkedBodyContext compiled.program.signatures selected.signature selected.original)
      ((initial selected.signature selected.body.declaration).localBinders.map
        (TypedBinder.applySubstitution selected.body.finalized.substitution))
      selected.signature.parameterTypes target := by
    have actualInputs := checkFunctionBody_success_typedBody_inputs selected.body.accepted
    rw [actualInputs, selected.body.substitution, ← owner] at inputs
    simpa only [initial, State.initial_inputs_eq_localBinders] using inputs
  have active : ActiveLocalContextInvariant (initial selected.signature selected.body.declaration)
      selected.body.finalized.substitution target := by
    constructor
    · exact LocalEnvironmentAligned.ofInitialMonoBindersExtend _ _ _ _
        (context := checkedBodyContext compiled.program.signatures selected.signature selected.original)
        (final := target) (types := selected.signature.parameterTypes) rfl rfl inputExtension
    · exact ActiveLocalFormation.ofMonoBindersExtend inputExtension
  have predicatesFixed : selected.signature.scheme.predicates.map
      (TypedTraitResolution.applySubstitution selected.body.finalized.substitution) =
        selected.signature.scheme.predicates :=
    selected.predicates_fixed checked _
  have emptyActual : ActualContext (checkingContext selected) selected.body.finalized []
      (checkedBodyContext compiled.program.signatures selected.signature selected.original) := by
    apply ActualContext.empty
    · rfl
    · simp only [checkingContext, context, checkedBodyContext, declarationContext,
        finalizedRequirementContext, Context.withResidualTypeVariables,
        Context.withSolvedRequirements, Context.withAssumptions, Context.forDeclaration,
        predicatesFixed]
    · rw [← selected.body.source]
      simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, owner] using
        checkFunctionBody_success_typedBody_owner selected.body.accepted
  have actual := emptyActual.monoBinders inputs
  have fields := input_context_fields inputs
  have invariant : RecursiveStatementInvariant (checkingContext selected)
      (Ty.productMany selected.signature.returnTypes) selected.body.finalized
      (initial selected.signature selected.body.declaration) target := by
    refine {
      active
      ready := progress.initialReady
      returnBelow := progress.returnBelow
      bindersBelow := State.initial_localBindersBelowNextLocal _ _ _
      nodesBelow := State.initial_nodesBelowNextOccurrence _ _ _
      schemeIsolation := ?_
      substitutionExtension := progress.initial_substitution
      signaturesEq := fields.1
      typeParametersEq := fields.2.1
      declarationEq := ?_
      residual := fields.2.2.2.1
      solvedRequirementsEq := ?_
      assumptionsMono := ?_ }
    · apply activeSchemeQuantifierIsolation_initial_mono
      intro entry present
      obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp present
      rfl
    · simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, owner,
        checkedBodyContext, declarationContext, Context.withResidualTypeVariables,
        Context.withSolvedRequirements, Context.withAssumptions, Context.forDeclaration] using fields.2.2.1
    · simpa only [checkedBodyContext, declarationContext, finalizedRequirementContext,
        Context.withResidualTypeVariables, Context.withSolvedRequirements,
        Context.withAssumptions, Context.forDeclaration, selected.body.solved] using fields.2.2.2.2
    · intro predicate present
      rw [actual.assumptions_eq]
      exact List.mem_append_left _ present
  have returnFixed : selected.body.finalized.substitution.apply
      (Ty.productMany selected.signature.returnTypes) = Ty.productMany selected.signature.returnTypes := by
    have resultType : selected.body.finalized.type = Ty.productMany selected.signature.returnTypes := by
      simpa only [selected.body.checkedResult] using header.result_type
    exact (Detail.finalize_type selected.body.finalization).symm.trans resultType
  refine ⟨target, inputs, ?_, ?_, ?_⟩
  · intro binder present
    exact ProtectedVariables.safe_closed _ _
      (selected.returns_closed checked)
  · rw [returnFixed]
    exact TypeAdmissible.ofWellFormed (input_type_formed inputs
      ⟨header.parameter_binders, StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped header.return_types)⟩)
  · refine {
      accepted := selected.body.inferred
      interfaces := interfaces
      extension := progress.final_substitution
      scope := .refl selected
      invariant
      actual
      operational := ?_
      rawSubtrees := ?_
      integerPatterns := ?_
      integerLiterals := ?_
      requirements := ?_
      covered := ?_
      actualCovered := ?_ }
    · apply GeneralizedActualStateInvariant.initial
      intro entry present
      obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp present
      rfl
    · intro child _
      rw [returned_source selected]
      exact RawSubtreePreserved.ofTypingSourceExtends (.refl _)
    · rw [Detail.unify_integerPatterns selected.body.unified]
      exact List.Subset.refl _
    · rw [Detail.unify_integerLiterals selected.body.unified]
      exact List.Subset.refl _
    · rw [selected.body.returned_requirements]
      exact List.Subset.refl _
    · intro child present
      apply TemplateScopeCovered.root selected.body.resources.graph_closed.rootsHaveNoParent
      rw [finalize_statementRoots selected.body.finalization]
      exact List.mem_map_of_mem present
    · intro child _
      exact ActualContext.covers_empty (.statement child)

theorem body_entry {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations) :
    ∃ target, BodyEntry selected target :=
  body_entry_of_interfaces selected checked (selected_original_interfaces selected member)

/-- The recursive assembly is applied at the real whole-body entry, with its
safe return type and state/context invariants discharged by accepted checking. -/
theorem body_of_recursive_of_interfaces_for {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    {callProvenance : CallIndex → Prop}
    (rootHere : callProvenance selected.inferenceCall)
    (sound : StatementsRootedSoundnessFor callProvenance selected fuel) :
    ∃ target, BodyEntry selected target ∧
      StatementsConclusion selected (checkingContext selected)
        (Ty.productMany selected.signature.returnTypes) selected.body.body [] target := by
  obtain ⟨target, entry⟩ := body_entry_of_interfaces selected checked interfaces
  exact ⟨target, entry, sound rootHere entry.returnSafe entry.returnAdmissible entry.boundary⟩

theorem body_of_recursive_of_interfaces {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (sound : StatementsRootedSoundness selected fuel) :
    ∃ target, BodyEntry selected target ∧
      StatementsConclusion selected (checkingContext selected)
        (Ty.productMany selected.signature.returnTypes) selected.body.body [] target := by
  exact body_of_recursive_of_interfaces_for (callProvenance := fun _ => True) selected checked interfaces True.intro
    (statementsRootedSoundnessFor_true sound)

theorem body_of_recursive {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (sound : StatementsRootedSoundness selected fuel) :
    ∃ target, BodyEntry selected target ∧
      StatementsConclusion selected (checkingContext selected)
        (Ty.productMany selected.signature.returnTypes) selected.body.body [] target :=
  body_of_recursive_of_interfaces selected checked
    (selected_original_interfaces selected member) sound

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedCheckedBody
/-! The actual recursive result supplies one body-facts witness for every
compatible input context of the same checked declaration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

private theorem input_context_unique {owner : Resolved.DeclarationId}
    {base left right : SourceSemantics.Context} {binders : List TypedBinder} {types : List Ty}
    (first : MonoBindersExtend owner base binders types left)
    (second : MonoBindersExtend owner base binders types right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons _ head _ ih =>
      cases second with
      | cons _ otherHead otherTail =>
          cases head
          cases otherHead
          exact ih otherTail

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head tail ih =>
      cases right with
      | nil => simp at same
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at same
          have equal := NodeId.statement.inj same.1
          subst other
          exact congrArg (List.cons head) (ih same.2)

theorem checked_statements_of_recursive_of_interfaces_for {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    {callProvenance : CallIndex → Prop}
    (rootHere : callProvenance selected.inferenceCall)
    (sound : StatementsRootedSoundnessFor callProvenance selected fuel) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original := by
  obtain ⟨target, entry, finalContext, facts, _, _, _, typed, matching⟩ :=
    body_of_recursive_of_interfaces_for selected checked interfaces rootHere sound
  have header := selected_body_header selected checked
  have returnFixed : selected.body.finalized.substitution.apply
      (Ty.productMany selected.signature.returnTypes) = Ty.productMany selected.signature.returnTypes := by
    have typeEq : selected.body.finalized.type = Ty.productMany selected.signature.returnTypes := by
      simpa only [selected.body.checkedResult] using header.result_type
    exact (Detail.finalize_type selected.body.finalization).symm.trans typeEq
  have factsType : facts.type = Ty.productMany selected.signature.returnTypes := by
    calc
      facts.type = selected.body.finalized.substitution.apply selected.body.body.type := matching.type_eq
      _ = selected.body.finalized.substitution.apply (Ty.productMany selected.signature.returnTypes) :=
        Detail.unify_then_finalize_eq selected.body.unified selected.body.finalization
      _ = _ := returnFixed
  have actualRoots : selected.original.typedBody.roots =
      selected.body.body.statements.map NodeId.statement := by
    rw [selected.body.source]
    exact finalize_statementRoots selected.body.finalization
  intro statements roots
  have same := roots_injective (roots.symm.trans actualRoots)
  subst statements
  refine ⟨facts, factsType, ?_⟩
  intro lexicalContext extension
  have contextEq := input_context_unique extension entry.inputs
  subst lexicalContext
  refine ⟨finalContext, ?_⟩
  simpa only [selected.body.source, returnFixed, checkingContext, context] using typed


theorem checked_statements_of_recursive_of_interfaces {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (sound : StatementsRootedSoundness selected fuel) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original := by
  exact checked_statements_of_recursive_of_interfaces_for (callProvenance := fun _ => True) selected checked interfaces True.intro
    (statementsRootedSoundnessFor_true sound)

/-- This is the original checked body's complete declarative judgment.
The caller supplies the recursive assembly at the same selected receipt. -/
theorem checked_body_of_recursive_of_interfaces {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (sound : StatementsRootedSoundness selected fuel) :
    CheckedBodyHasType compiled.program.signatures selected.signature selected.original :=
  checkedBodyHasType_ofStatements selected.body.accepted
    (checked_statements_of_recursive_of_interfaces selected checked interfaces sound)

theorem checked_statements_of_recursive {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (sound : StatementsRootedSoundness selected fuel) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original :=
  checked_statements_of_recursive_of_interfaces selected checked
    (selected_original_interfaces selected member) sound

theorem checked_body_of_recursive {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (sound : StatementsRootedSoundness selected fuel) :
    CheckedBodyHasType compiled.program.signatures selected.signature selected.original :=
  checked_body_of_recursive_of_interfaces selected checked
    (selected_original_interfaces selected member) sound

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedMatchCases
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables SourceInferenceExecution

private theorem binder_assumptions {owner : Resolved.DeclarationId}
    {before after : SourceSemantics.Context} {binders : List TypedBinder}
    (extension : BindersExtend owner before binders after) : after.assumptions = before.assumptions := by
  induction extension with
  | nil => rfl
  | cons head tail ih => cases head; exact ih

private theorem admissible_local {context : SourceSemantics.Context} {type : Ty}
    (typed : TypeAdmissible context type) (binder : TypedBinder) :
    TypeAdmissible (context.withLocal binder.id binder.scheme binder.schemeRequirements) type :=
  StructuralSubstitution.TypeAdmissible.transportContext (source := context)
    (target := context.withLocal binder.id binder.scheme binder.schemeRequirements) rfl rfl rfl rfl rfl typed

private theorem admissible_binders {owner : Resolved.DeclarationId}
    {before after : SourceSemantics.Context} {binders : List TypedBinder} {type : Ty}
    (extension : BindersExtend owner before binders after)
    (typed : TypeAdmissible before type) : TypeAdmissible after type := by
  induction extension with
  | nil => exact typed
  | cons head tail ih =>
    apply ih
    cases head
    exact admissible_local typed _

theorem matchCases_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}
    (descend : ChildClosed callProvenance)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {cases : List Syntax.MatchCase}
    {scrutinee expectedReturn : Ty} {initial : State} {outerScope : LexicalScope}
    {result : Detail.MatchCasesResult} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context} {occurrence : NodeId}
    (here : callProvenance (.matchCases childFuel inferenceContext scrutinee expectedReturn outerScope cases initial result))
    (boundary : MatchCasesBoundary selected childFuel inferenceContext cases scrutinee expectedReturn
      initial outerScope result frames target occurrence)
    (returnSafe : Safe (activeSchemeQuantifiers initial) initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        callProvenance (.statements small inferenceContext bodySource expectedReturn bodyInitial bodyResult) →
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    MatchCasesConclusion selected inferenceContext scrutinee expectedReturn result frames target := by
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  refine ⟨boundary.resultInvariant checked, boundary.actual,
    boundary.operational.ofMatchCases boundary.invariant.ready catalog formation canonical boundary.scrutineeBelow
      boundary.scrutineeSafe boundary.invariant.returnBelow returnSafe boundary.lexicalScope boundary.accepted, ?_⟩
  induction childFuel generalizing cases initial outerScope result with
  | zero =>
    have accepted := boundary.accepted
    simp only [Detail.inferMatchCasesFuel] at accepted
    cases accepted
  | succ childFuel ih =>
    cases cases with
    | nil =>
      have accepted := boundary.accepted
      simp only [Detail.inferMatchCasesFuel, Except.ok.injEq] at accepted
      subst result
      exact ⟨[], .nil _ _ _, rfl⟩
    | cons arm rest =>
      have accepted := boundary.accepted
      unfold Detail.inferMatchCasesFuel at accepted
      cases patternAccepted : Detail.inferMatchPatternFuel childFuel inferenceContext arm.value.pattern scrutinee initial with
      | error error => simp [patternAccepted, bind, Except.bind] at accepted
      | ok pair =>
        obtain ⟨pattern, patternState⟩ := pair
        cases bodyAccepted : Detail.inferStatementsFuel childFuel inferenceContext arm.value.body.value expectedReturn patternState with
        | error error => simp [patternAccepted, bodyAccepted, bind, Except.bind] at accepted
        | ok bodyResult =>
          let tailInput := bodyResult.state.restoreLexicalScope outerScope
          cases tailAccepted : Detail.inferMatchCasesFuel childFuel inferenceContext scrutinee expectedReturn outerScope rest tailInput with
          | error error => simp [patternAccepted, bodyAccepted, tailInput, tailAccepted, bind, Except.bind] at accepted
          | ok tail =>
            simp only [patternAccepted, bodyAccepted, tailInput, tailAccepted, bind, Except.bind,
              pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            subst result
            have patternProperties := Detail.inferMatchPatternFuel_inferenceProperties boundary.invariant.ready
              boundary.scrutineeBelow formation patternAccepted
            have patternNodes := (Detail.inferMatchPatternFuel_occurrenceBoundExtends patternAccepted).nodesBelowNextOccurrence
              boundary.invariant.nodesBelow
            have bodyNodes := (Detail.inferStatementsFuel_occurrenceBoundExtends bodyAccepted).nodesBelowNextOccurrence patternNodes
            have bodyProperties := Detail.inferStatementsFuel_inferenceProperties patternProperties.2.1 formation canonical
              (boundary.invariant.returnBelow.weaken patternProperties.1.next_le) bodyAccepted
            have throughBody := patternProperties.1.trans bodyProperties.1
            have restored : initial.InferenceProgress tailInput ∧ tailInput.InferenceReady := by
              dsimp [tailInput]
              rw [← boundary.lexicalScope]
              exact State.restoreLexicalScope_inferenceProperties boundary.invariant.ready throughBody
            have tailScope : tailInput.lexicalScope = outerScope := by simp [tailInput]
            have tailProperties := Detail.inferMatchCasesFuel_inferenceProperties restored.2 formation canonical
              (boundary.scrutineeBelow.weaken restored.1.next_le)
              (boundary.invariant.returnBelow.weaken restored.1.next_le) tailScope tailAccepted
            have tailExtension := boundary.extension.trans tailProperties.1.substitution_extends
            have bodyExtension : selected.body.finalized.substitution.SemanticallyExtends
                bodyResult.state.inference.substitution := tailExtension
            have patternExtension := bodyExtension.trans bodyProperties.1.substitution_extends
            have tailNodes := State.restoreLexicalScope_preserves_nodesBelowNextOccurrence bodyResult.state outerScope bodyNodes
            have bodySource : TypingSourceExtends (bodyResult.state.toTypedSource (bodyRoots selected))
                (tail.state.toTypedSource (bodyRoots selected)) := by
              constructor
              · have preserved := Detail.inferMatchCasesFuel_preserves_owner tailAccepted
                exact preserved
              · exact Detail.inferMatchCasesFuel_preserves_nodesPrefix tailAccepted List.prefix_rfl tailNodes (Nat.le_refl _)
            have bodyPatterns : bodyResult.state.integerPatterns ⊆ selected.body.returned.integerPatterns := by
              have subset := Detail.inferMatchCasesFuel_integerPatterns_subset tailAccepted
              exact subset.trans boundary.integerPatterns
            have bodyLiterals : bodyResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
              have subset := Detail.inferMatchCasesFuel_integerLiterals_subset tailAccepted
              exact subset.trans boundary.integerLiterals
            have bodyRequirements : bodyResult.state.requirements ⊆ selected.body.returned.requirements := by
              have subset := Detail.inferMatchCasesFuel_requirements_subset tailAccepted
              exact subset.trans boundary.requirements
            have patternMetadata := Detail.inferMatchCasesFuel_headPatternState_metadata_subset
              patternAccepted bodyAccepted boundary.accepted
            let recordedHead : TypedMatchCase := {span := arm.span, pattern, body := bodyResult.statements}
            obtain ⟨certificate, patternInvariant, patternActual, patternOperational⟩ :=
              patternEntered (inferred := pattern) checked boundary.scope (RecursiveExpressionInvariant.ofStatement boundary.invariant)
                boundary.actual boundary.operational boundary.owner boundary.scrutineeBelow boundary.scrutineeAdmissible
                boundary.scrutineeSafe patternExtension (patternMetadata.1.trans boundary.integerPatterns)
                (patternMetadata.2.trans boundary.requirements)
                (fun requirement member => boundary.patternOccurs recordedHead (by exact List.mem_cons_self) requirement member)
                boundary.patternCovered patternAccepted
            have armInvariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized
                patternState certificate.armContext := {
              active := patternInvariant.active
              ready := patternInvariant.ready
              returnBelow := boundary.invariant.returnBelow.weaken patternProperties.1.next_le
              bindersBelow := patternInvariant.bindersBelow
              nodesBelow := patternInvariant.nodesBelow
              schemeIsolation := patternInvariant.schemeIsolation
              substitutionExtension := patternInvariant.substitutionExtension
              signaturesEq := patternInvariant.signaturesEq
              typeParametersEq := patternInvariant.typeParametersEq
              declarationEq := patternInvariant.declarationEq
              residual := patternInvariant.residual
              solvedRequirementsEq := patternInvariant.solvedRequirementsEq
              assumptionsMono := patternInvariant.assumptionsMono }
            have armReturnSafe := boundary.operational.pattern_safe_transport boundary.invariant.ready formation
              boundary.scrutineeBelow boundary.scrutineeSafe returnSafe patternAccepted
            have assumptions := binder_assumptions certificate.binders_extend
            obtain ⟨bodyContext, bodyFacts, bodyInvariant, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
              recursiveBody childFuel (Nat.lt_succ_self _)
                (descend here (ChildStep.matchCases_body boundary.accepted patternAccepted bodyAccepted))
                (safe_active_iff.mp armReturnSafe)
                (admissible_binders certificate.binders_extend returnAdmissible) ({
                  accepted := bodyAccepted
                  interfaces := boundary.interfaces
                  extension := bodyExtension
                  scope := boundary.scope
                  invariant := armInvariant
                  actual := patternActual
                  operational := patternOperational
                  rawSubtrees := fun child member => (boundary.rawSubtrees recordedHead (by exact List.mem_cons_self) child member).monoBefore bodySource
                  integerPatterns := bodyPatterns
                  integerLiterals := bodyLiterals
                  requirements := bodyRequirements
                  covered := by
                    intro child member owner scopes
                    change owner.requirement.predicate ∈ certificate.armContext.assumptions
                    rw [assumptions]
                    exact boundary.covered recordedHead (by exact List.mem_cons_self) child member owner scopes
                  actualCovered := fun child member => boundary.actualCovered recordedHead (by exact List.mem_cons_self) child member } :
                  StatementsBoundary selected childFuel inferenceContext arm.value.body.value expectedReturn
                    patternState bodyResult frames certificate.armContext)
            let headCertificate : MatchCaseInferenceCertificate selected.body.finalized.typedSource
                {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
                target selected.body.finalized.substitution scrutinee pattern patternState bodyResult := {
              binders := certificate.binders
              rootArity := certificate.rootArity
              armContext := certificate.armContext
              finalContext := bodyContext
              facts := bodyFacts
              pattern_type := certificate.pattern_type
              binders_extend := certificate.binders_extend
              pattern_invariant := certificate.pattern_invariant
              body_type := bodyTyping
              body_matches := bodyAgreement }
            obtain ⟨headFacts, headTyping, headAgreement⟩ := headCertificate.toMatchCaseHasType (arm := arm)
            have tailInvariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized
                tailInput target := by
              dsimp [tailInput]
              rw [← boundary.lexicalScope]
              exact boundary.invariant.restoreLexicalScope throughBody bodyInvariant.nodesBelow
                (Nat.le_trans (Detail.inferMatchPatternFuel_nextLocal_le patternAccepted)
                  (Detail.inferStatementsFuel_nextLocal_le bodyAccepted)) bodyExtension
            have patternScope := ProtectedVariables.inferMatchPatternFuel_scope patternAccepted
            have saved : initial.localBinders ⊆ bodyResult.state.localBinders :=
              patternScope.retained.trans (ProtectedVariables.inferStatementsFuel_binders_subset bodyAccepted)
            have tailOperational : GeneralizedActualStateInvariant tailInput (evidenceSource selected) := by
              dsimp [tailInput]
              rw [← boundary.lexicalScope]
              exact bodyOperational.restoreSaved boundary.operational.origins saved
            have patternPrivacy := ProtectedVariables.inferMatchPatternFuel_private boundary.invariant.ready
              boundary.scrutineeBelow formation (activeSchemeQuantifiers_below_next boundary.operational.quantifiersBelow)
              boundary.scrutineeSafe boundary.operational.privacy.all_live patternAccepted
            have bodyPrivacy := ProtectedVariables.inferStatementsFuel_private (activeSchemeQuantifiers initial)
              childFuel inferenceContext arm.value.body.value expectedReturn patternState patternInvariant.ready
              patternOperational.requirements
              (fun v member => Nat.lt_of_lt_of_le
                (activeSchemeQuantifiers_below_next boundary.operational.quantifiersBelow v member) patternProperties.1.next_le)
              patternPrivacy.2.1 catalog formation canonical armInvariant.returnBelow
              (patternPrivacy.1 expectedReturn returnSafe) _ bodyAccepted
            have tailBinders : tailInput.localBinders = initial.localBinders := by
              change outerScope.binders = initial.localBinders
              exact congrArg LexicalScope.binders boundary.lexicalScope.symm
            have tailReturnSafe : Safe (activeSchemeQuantifiers tailInput) tailInput expectedReturn := by
              change Safe (activeSchemeQuantifiers tailInput) bodyResult.state expectedReturn
              rw [activeSchemeQuantifiers, tailBinders]
              exact bodyPrivacy.1 expectedReturn (patternPrivacy.1 expectedReturn returnSafe)
            have tailScrutineeSafe : Safe (activeSchemeQuantifiers tailInput) tailInput scrutinee := by
              change Safe (activeSchemeQuantifiers tailInput) bodyResult.state scrutinee
              rw [activeSchemeQuantifiers, tailBinders]
              exact bodyPrivacy.1 scrutinee (patternPrivacy.1 scrutinee boundary.scrutineeSafe)
            have tailOwner : tailInput.owner = (checkingContext selected).scope.genericOwner :=
              (Detail.inferStatementsFuel_preserves_owner bodyAccepted).trans
                ((Detail.inferMatchPatternFuel_preserves_owner patternAccepted).trans boundary.owner)
            obtain ⟨tailFacts, tailTyping, tailAgreement⟩ := ih
              (descend here (ChildStep.matchCases_tail boundary.accepted patternAccepted bodyAccepted tailAccepted)) ({
              accepted := tailAccepted
              interfaces := boundary.interfaces
              extension := boundary.extension
              scope := boundary.scope
              invariant := tailInvariant
              actual := boundary.actual
              operational := tailOperational
              owner := tailOwner
              lexicalScope := tailScope
              scrutineeBelow := boundary.scrutineeBelow.weaken restored.1.next_le
              scrutineeAdmissible := boundary.scrutineeAdmissible
              scrutineeSafe := tailScrutineeSafe
              integerPatterns := boundary.integerPatterns
              integerLiterals := boundary.integerLiterals
              requirements := boundary.requirements
              patternCovered := boundary.patternCovered
              patternOccurs := fun arm member => boundary.patternOccurs arm (by simp [member])
              rawSubtrees := fun arm member => boundary.rawSubtrees arm (by simp [member])
              covered := fun arm member => boundary.covered arm (by simp [member])
              actualCovered := fun arm member => boundary.actualCovered arm (by simp [member]) } :
              MatchCasesBoundary selected childFuel inferenceContext rest scrutinee expectedReturn
                tailInput outerScope tail frames target occurrence) tailReturnSafe
              (fun small bound => recursiveBody small (Nat.lt_trans bound (Nat.lt_succ_self _)))
            refine ⟨headFacts :: tailFacts, ?_, ?_⟩
            · simpa only [List.map_cons] using MatchCasesHaveType.cons headTyping tailTyping
            · change (headFacts.sawReturn && allBodiesSawReturn tailFacts) = (bodyResult.sawReturn && tail.allReturn)
              rw [headAgreement.sawReturn_eq, tailAgreement]

theorem matchCases
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {cases : List Syntax.MatchCase}
    {scrutinee expectedReturn : Ty} {initial : State} {outerScope : LexicalScope}
    {result : Detail.MatchCasesResult} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context} {occurrence : NodeId}
    (boundary : MatchCasesBoundary selected childFuel inferenceContext cases scrutinee expectedReturn
      initial outerScope result frames target occurrence)
    (returnSafe : Safe (activeSchemeQuantifiers initial) initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    MatchCasesConclusion selected inferenceContext scrutinee expectedReturn result frames target := by
  exact matchCases_for (callProvenance := fun _ => True) true_childClosed checked True.intro
    boundary returnSafe returnAdmissible (fun small less => by
      intro bodySource bodyInitial bodyResult bodyTarget _
      exact recursiveBody small less)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedMatchEntry
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables SourceInferenceExecution

theorem matchEntry_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}
    (descend : ChildClosed callProvenance)
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    {scrutinee : InferredExpression} {scrutineeState hiddenState : State}
    {hiddenScrutinee : Resolved.LocalId} {checked : Detail.MatchCasesResult}
    {defaultBody : Option (List StatementId)}
    (singleHere : ∀ expression, scrutinees.elements.toList = [expression] →
      callProvenance (.expression childFuel inferenceContext expression none
        initial.allocateStatementId.2 scrutinee scrutineeState))
    (manyHere : ∀ elements elementsState, (∀ expression, scrutinees.elements.toList ≠ [expression]) →
      Detail.inferExprsFuel childFuel inferenceContext scrutinees.elements.toList initial.allocateStatementId.2 =
        .ok (elements, elementsState) →
      callProvenance (.expressions childFuel inferenceContext scrutinees.elements.toList
        initial.allocateStatementId.2 elements elementsState))
    (scrutineeAccepted : inferMatchScrutineesFuel childFuel inferenceContext statement.span
      scrutinees.elements.toList initial.allocateStatementId.2 = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hiddenScrutinee, hiddenState))
    (casesAccepted : Detail.inferMatchCasesFuel childFuel inferenceContext scrutinee.type expectedReturn
      hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
    (casesExtension : selected.body.finalized.substitution.SemanticallyExtends checked.state.inference.substitution)
    (casesSource : TypingSourceExtends (checked.state.toTypedSource (bodyRoots selected))
      (result.state.toTypedSource (bodyRoots selected)))
    (patterns : checked.state.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (literals : checked.state.integerLiterals ⊆ selected.body.returned.integerLiterals)
    (requirements : checked.state.requirements ⊆ selected.body.returned.requirements)
    (contains : ContainsStatement (result.state.toTypedSource (bodyRoots selected)) result.id {
      id := result.id, span := statement.span, type := result.type, form := .matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases, defaultBody,
        requirements := checked.cases.flatMap (·.pattern.requirements) } }) :
    MatchCasesBoundary selected childFuel inferenceContext arms.value.cases scrutinee.type expectedReturn
      hiddenState hiddenState.lexicalScope checked frames target (.statement result.id) ∧
    ExpressionHasType selected.body.finalized.typedSource target scrutinee.id
      (selected.body.finalized.substitution.apply scrutinee.type) ∧
    Safe (activeSchemeQuantifiers hiddenState) hiddenState expectedReturn := by
  have resources := selected.body.resources
  have formation := boundary.scope.formation checkedProgram
  have canonical := boundary.scope.functionsCanonical checkedProgram
  have catalog := boundary.scope.catalog checkedProgram
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have allocatedOperational := boundary.operational.allocateStatementId
  have properties := inferMatchScrutineesFuel_inferenceProperties allocatedInvariant.ready
    formation canonical scrutineeAccepted
  have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
  have hiddenReady : hiddenState.InferenceReady := by
    rw [← hiddenEq]
    exact properties.2.1.allocateHiddenLocal
  have scrutineeBelow : scrutinee.type.VariablesBelow hiddenState.inference.next := by
    rw [← hiddenEq]
    exact properties.2.2
  have returnBelow : expectedReturn.VariablesBelow hiddenState.inference.next := by
    rw [← hiddenEq]
    exact allocatedInvariant.returnBelow.weaken properties.1.next_le
  have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties hiddenReady formation canonical
    scrutineeBelow returnBelow rfl casesAccepted
  have hiddenExtension := casesExtension.trans casesProperties.1.substitution_extends
  have scrutineeExtension : selected.body.finalized.substitution.SemanticallyExtends
      scrutineeState.inference.substitution := by
    rw [← hiddenEq] at hiddenExtension
    exact hiddenExtension
  have scrutineeNodes := inferMatchScrutineesFuel_success_nodesBelow scrutineeAccepted allocatedInvariant.nodesBelow
  have hiddenNodes : hiddenState.NodesBelowNextOccurrence := by
    rw [← hiddenEq]
    exact State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence _ scrutineeNodes
  have hiddenBinders : hiddenState.localBinders = initial.localBinders := by
    rw [← hiddenEq]
    exact congrArg LexicalScope.binders (inferMatchScrutineesFuel_success_lexicalScope_eq scrutineeAccepted)
  have hiddenInvariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized hiddenState target := {
    boundary.invariant with
    active := allocatedInvariant.active.inferMatchScrutineesFuel scrutineeAccepted |>.allocateHiddenLocal hiddenAllocation
    ready := hiddenReady
    returnBelow := returnBelow
    bindersBelow := by
      rw [← hiddenEq]
      exact State.allocateHiddenLocal_preserves_localBindersBelowNextLocal _
        (inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal allocatedInvariant.bindersBelow scrutineeAccepted)
    nodesBelow := hiddenNodes
    schemeIsolation := activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation hiddenBinders
    substitutionExtension := hiddenExtension }
  have scrutineeOperational := allocatedOperational.ofMatchScrutinees allocatedInvariant.ready catalog formation canonical
    scrutineeAccepted
  have hiddenOperational : GeneralizedActualStateInvariant hiddenState (evidenceSource selected) := by
    rw [← hiddenEq]
    exact scrutineeOperational.1.allocateHiddenLocal
  have scrutineeSafe : Safe (activeSchemeQuantifiers hiddenState) hiddenState scrutinee.type := by
    rw [← hiddenEq]
    exact scrutineeOperational.2
  have hiddenReturnSafe : Safe (activeSchemeQuantifiers hiddenState) hiddenState expectedReturn := by
    have privacy := allocatedOperational.scrutinees_safe_transport allocatedInvariant.ready catalog formation canonical
      scrutineeAccepted
    have beforeSafe : Safe (activeSchemeQuantifiers initial.allocateStatementId.2)
        initial.allocateStatementId.2 expectedReturn := safe_active_iff.mpr returnSafe
    have afterSafe := privacy expectedReturn beforeSafe
    change Safe (activeSchemeQuantifiers hiddenState) hiddenState expectedReturn
    simp only [activeSchemeQuantifiers, hiddenBinders]
    rw [← hiddenEq]
    exact afterSafe
  have scrutineeToHidden : TypingSourceExtends (scrutineeState.toTypedSource (bodyRoots selected))
      (hiddenState.toTypedSource (bodyRoots selected)) := by
    rw [← hiddenEq]
    exact ⟨rfl, List.prefix_rfl⟩
  have scrutineeSource := scrutineeToHidden.trans
    ((inferMatchCasesFuel_success_typingSourceExtends casesAccepted hiddenNodes (bodyRoots selected)).trans casesSource)
  have scrutineeReference : (.expression scrutinee.id : NodeId) ∈ (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases, defaultBody,
        requirements := checked.cases.flatMap (·.pattern.requirements) }).references := by
    simp [StatementForm.references, MatchResolution.references]
  have scrutineePatterns : scrutineeState.integerPatterns ⊆ checked.state.integerPatterns := by
    have rows := Detail.inferMatchCasesFuel_integerPatterns_subset casesAccepted
    simpa [← hiddenEq] using rows
  have scrutineeLiterals : scrutineeState.integerLiterals ⊆ checked.state.integerLiterals := by
    have rows := Detail.inferMatchCasesFuel_integerLiterals_subset casesAccepted
    simpa [← hiddenEq] using rows
  have scrutineeRequirements : scrutineeState.requirements ⊆ checked.state.requirements := by
    have rows := Detail.inferMatchCasesFuel_requirements_subset casesAccepted
    simpa [← hiddenEq] using rows
  have finalContains := (boundary.rawSubtree.finalized resources).containsStatement contains
  have typed := scrutineeRooted_for descend checkedProgram recursive singleHere manyHere ({
    accepted := scrutineeAccepted
    interfaces := boundary.interfaces, extension := scrutineeExtension, scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement allocatedInvariant
    actual := boundary.actual, operational := allocatedOperational
    rawSubtree := (boundary.rawSubtree.child (directChild_statement_reference contains scrutineeReference)).monoBefore scrutineeSource
    integerPatterns := scrutineePatterns.trans patterns, integerLiterals := scrutineeLiterals.trans literals
    requirements := scrutineeRequirements.trans requirements
    covered := by
      apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference boundary.covered resources.graph_closed finalContains
      · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
      · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, MatchResolution.applySubstitution,
          StatementForm.references, MatchResolution.references]
    actualCovered := boundary.actualCovered.preserved_statement_reference contains
      (boundary.rawSubtree.finalized resources) scrutineeReference } : ScrutineeBoundary selected childFuel
        inferenceContext statement.span scrutinees.elements.toList initial.allocateStatementId.2 scrutinee scrutineeState frames target)
  have reference : ∀ arm ∈ checked.cases, ∀ child ∈ arm.body,
      (.statement child : NodeId) ∈ (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases, defaultBody,
        requirements := checked.cases.flatMap (·.pattern.requirements) }).references := by
    intro arm present child member
    simp only [StatementForm.references, MatchResolution.references]
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨arm, present, by simpa [TypedMatchCase.references] using
      (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.statement child ∈ arm.body.map NodeId.statement)⟩
  have owner : hiddenState.owner = (checkingContext selected).scope.genericOwner := by
    have evidenceOwner : (evidenceSource selected).owner = (checkingContext selected).scope.genericOwner := by
      exact (congrArg State.Header.owner (Detail.unify_state_header selected.body.unified)).trans
        (Detail.inferStatementsFuel_preserves_owner selected.body.inferred)
    exact (Detail.inferMatchCasesFuel_preserves_owner casesAccepted).symm.trans
      (casesSource.owner_eq.symm.trans (boundary.rawSubtree.owner_eq.symm.trans evidenceOwner))
  refine ⟨{
    accepted := casesAccepted, interfaces := boundary.interfaces, extension := casesExtension
    scope := boundary.scope, invariant := hiddenInvariant, actual := boundary.actual, operational := hiddenOperational
    owner := owner, lexicalScope := rfl, scrutineeBelow := scrutineeBelow
    scrutineeAdmissible := typed.type_admissible, scrutineeSafe := scrutineeSafe
    integerPatterns := patterns, integerLiterals := literals, requirements := requirements
    patternCovered := boundary.covered
    patternOccurs := ?_
    rawSubtrees := fun arm present child member =>
      (boundary.rawSubtree.child (directChild_statement_reference contains (reference arm present child member))).monoBefore casesSource
    covered := ?_
    actualCovered := fun arm present child member => boundary.actualCovered.preserved_statement_reference contains
      (boundary.rawSubtree.finalized resources) (reference arm present child member) }, typed, hiddenReturnSafe⟩
  · intro arm present requirement member
    exact finalContains.matchCasePatternRequirementOccursAt rfl
      (List.mem_map.mpr ⟨arm, present, rfl⟩) (by
        simpa [TypedMatchCase.applySubstitution, TypedMatchPattern.applySubstitution] using member)
  · intro arm present child member
    exact TemplateScopeCovered.statementChild boundary.covered resources.graph_closed
      ((boundary.rawSubtree.finalized resources).directChild
        (directChild_statement_reference contains (reference arm present child member))) (fun _ member => member)

theorem matchEntry
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    {scrutinee : InferredExpression} {scrutineeState hiddenState : State}
    {hiddenScrutinee : Resolved.LocalId} {checked : Detail.MatchCasesResult}
    {defaultBody : Option (List StatementId)}
    (scrutineeAccepted : inferMatchScrutineesFuel childFuel inferenceContext statement.span
      scrutinees.elements.toList initial.allocateStatementId.2 = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hiddenScrutinee, hiddenState))
    (casesAccepted : Detail.inferMatchCasesFuel childFuel inferenceContext scrutinee.type expectedReturn
      hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
    (casesExtension : selected.body.finalized.substitution.SemanticallyExtends checked.state.inference.substitution)
    (casesSource : TypingSourceExtends (checked.state.toTypedSource (bodyRoots selected))
      (result.state.toTypedSource (bodyRoots selected)))
    (patterns : checked.state.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (literals : checked.state.integerLiterals ⊆ selected.body.returned.integerLiterals)
    (requirements : checked.state.requirements ⊆ selected.body.returned.requirements)
    (contains : ContainsStatement (result.state.toTypedSource (bodyRoots selected)) result.id {
      id := result.id, span := statement.span, type := result.type, form := .matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases, defaultBody,
        requirements := checked.cases.flatMap (·.pattern.requirements) } }) :
    MatchCasesBoundary selected childFuel inferenceContext arms.value.cases scrutinee.type expectedReturn
      hiddenState hiddenState.lexicalScope checked frames target (.statement result.id) ∧
    ExpressionHasType selected.body.finalized.typedSource target scrutinee.id
      (selected.body.finalized.substitution.apply scrutinee.type) ∧
    Safe (activeSchemeQuantifiers hiddenState) hiddenState expectedReturn := by
  exact matchEntry_for (callProvenance := fun _ => True) true_childClosed checkedProgram
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary)
    boundary returnSafe (fun _ _ => True.intro) (fun _ _ _ _ => True.intro)
    scrutineeAccepted hiddenAllocation casesAccepted casesExtension casesSource patterns literals requirements contains

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedMatchStatement
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables SourceInferenceExecution

theorem statement_match_without_default_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}
    (descend : ChildClosed callProvenance)
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel + 1 →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        callProvenance (.statements small inferenceContext bodySource expectedReturn bodyInitial bodyResult) →
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn
          bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      scrutineeAccepted, hiddenAllocation, casesAccepted, guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts form defaultEq rfl boundary.accepted (bodyRoots selected)
  have casesExtension : selected.body.finalized.substitution.SemanticallyExtends checked.state.inference.substitution := by
    simpa [resultEq, State.recordNode] using boundary.extension
  have casesSource : TypingSourceExtends (checked.state.toTypedSource (bodyRoots selected))
      (result.state.toTypedSource (bodyRoots selected)) := by
    rw [resultEq]
    exact ⟨rfl, List.prefix_append _ _⟩
  have patterns : checked.state.integerPatterns ⊆ selected.body.returned.integerPatterns := by
    simpa [resultEq, State.recordNode] using boundary.integerPatterns
  have literals : checked.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.recordNode] using boundary.integerLiterals
  have requirements : checked.state.requirements ⊆ selected.body.returned.requirements := by
    simpa [resultEq, State.recordNode] using boundary.requirements
  obtain ⟨casesBoundary, scrutineeTyping, hiddenSafe⟩ :=
    matchEntry_for descend checkedProgram recursiveExpression boundary returnSafe
      (fun expression single => descend here (ChildStep.statement_match_single boundary.accepted form rfl
        single (by
          have child := scrutineeAccepted
          rw [single] at child
          exact child)))
      (fun _ _ multiple child => descend here (ChildStep.statement_match_many boundary.accepted form rfl
        multiple child)) scrutineeAccepted hiddenAllocation
      casesAccepted casesExtension casesSource patterns literals requirements contains
  obtain ⟨casesInvariant, casesActual, casesOperational, caseFacts, casesTyping, allReturnEq⟩ :=
    matchCases_for descend checkedProgram
      (descend here (ChildStep.statement_match_cases boundary.accepted form rfl scrutineeAccepted
        hiddenAllocation casesAccepted)) casesBoundary hiddenSafe returnAdmissible
      (fun small less => recursiveBody small (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
  have casesNonempty : checked.cases ≠ [] := by
    intro empty
    have wildcardFalse : checked.hasWildcard = false := by
      cases wildcard : checked.hasWildcard with
      | false => rfl
      | true =>
        obtain ⟨arm, member, _⟩ := Detail.inferMatchCasesFuel_success_hasWildcard_member casesAccepted wildcard
        simp [empty] at member
    have nominalFalse : Detail.exhaustsNominalConstructors inferenceContext checked.state
        scrutinee.type checked.cases = false := by simp [empty, Detail.exhaustsNominalConstructors]
    simp [wildcardFalse, nominalFalse] at guardPassed
  have factsNonempty := matchCasesHaveType_facts_ne_nil_of_cases_ne_nil casesTyping (by simpa using casesNonempty)
  obtain ⟨summary, merged⟩ := mergeBodyControls_withoutDefault_eq_some_of_ne_nil caseFacts factsNonempty
  have signatures : target.signatures = inferenceContext.signatures :=
    boundary.invariant.signaturesEq.trans boundary.scope.signatures.symm
  have catalog : SignatureCatalogWellFormed target.signatures := signatures ▸ boundary.scope.catalog checkedProgram
  have exhaustive := matchExhaustiveWithoutDefault_of_guard catalog signatures casesAccepted casesTyping
    scrutineeTyping.type_admissible casesExtension guardPassed
  let facts : StatementFacts := {
    type := if allBodiesSawReturn caseFacts then selected.body.finalized.substitution.apply expectedReturn else .unit
    hasValue := allBodiesSawReturn caseFacts
    sawReturn := allBodiesSawReturn caseFacts
    control := summary.eraseValue }
  have finalContains := (boundary.rawSubtree.finalized selected.body.resources).containsStatement contains
  have resolvedFinal : selected.body.finalized.substitution.apply (checked.state.resolve expectedReturn) =
      selected.body.finalized.substitution.apply expectedReturn := by
    simpa [State.resolve, InferState.resolve] using casesExtension expectedReturn
  have typeEq : selected.body.finalized.substitution.apply result.type = facts.type := by
    simp only [resultEq]
    change selected.body.finalized.substitution.apply
      (if checked.allReturn then checked.state.resolve expectedReturn else .unit) = _
    dsimp [facts]
    rw [allReturnEq]
    cases checked.allReturn <;> simp [resolvedFinal]
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
      target result.id target facts := by
    exact .matchWithoutDefault finalContains rfl rfl scrutineeTyping casesTyping
      (by simp [MatchResolution.applySubstitution]) exhaustive merged typeEq
  have agreement : StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.matchWithoutDefault allReturnEq casesExtension _ _
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact casesInvariant.active.recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact casesOperational.recordStatement _ rfl
  have isolation : ActiveSchemeQuantifierIsolation result.state := by
    rw [resultEq]
    exact casesInvariant.schemeIsolation
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checkedProgram) (boundary.scope.functionsCanonical checkedProgram) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension isolation typing
  exact ⟨target, facts, invariant, casesActual, operational, typing, agreement⟩

theorem statement_match_without_default
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel + 1 →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn
          bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_match_without_default_for (callProvenance := fun _ => True) true_childClosed checkedProgram
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursiveExpression smaller less boundary)
    True.intro form defaultEq boundary returnSafe returnAdmissible
    (fun small less => by
      intro bodySource bodyInitial bodyResult bodyTarget _
      exact recursiveBody small less)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedDefaultMatchStatement
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables SourceInferenceExecution

theorem statement_match_with_default_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}
    (descend : ChildClosed callProvenance)
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {defaultBody : Syntax.Block} {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel + 1 →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        callProvenance (.statements small inferenceContext bodySource expectedReturn bodyInitial bodyResult) →
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn
          bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked, defaultResult,
      scrutineeAccepted, hiddenAllocation, casesAccepted, defaultAccepted, _guard, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithDefault_facts form defaultEq rfl boundary.accepted (bodyRoots selected)
  have formation := boundary.scope.formation checkedProgram
  have canonical := boundary.scope.functionsCanonical checkedProgram
  have catalog := boundary.scope.catalog checkedProgram
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have scrutineeProperties := inferMatchScrutineesFuel_inferenceProperties allocatedInvariant.ready formation canonical scrutineeAccepted
  have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
  have hiddenReady : hiddenState.InferenceReady := by
    rw [← hiddenEq]
    exact scrutineeProperties.2.1.allocateHiddenLocal
  have scrutineeBelow : scrutinee.type.VariablesBelow hiddenState.inference.next := by
    rw [← hiddenEq]
    exact scrutineeProperties.2.2
  have returnBelow : expectedReturn.VariablesBelow hiddenState.inference.next := by
    rw [← hiddenEq]
    exact allocatedInvariant.returnBelow.weaken scrutineeProperties.1.next_le
  have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties hiddenReady formation canonical
    scrutineeBelow returnBelow rfl casesAccepted
  have defaultProperties := Detail.inferStatementsFuel_inferenceProperties casesProperties.2.1 formation canonical
    (returnBelow.weaken casesProperties.1.next_le) defaultAccepted
  have defaultExtension : selected.body.finalized.substitution.SemanticallyExtends defaultResult.state.inference.substitution := by
    simpa [resultEq, State.recordNode, State.restoreLexicalScope] using boundary.extension
  have casesExtension := defaultExtension.trans defaultProperties.1.substitution_extends
  have hiddenNodes : hiddenState.NodesBelowNextOccurrence := by
    rw [← hiddenEq]
    exact State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence _
      (inferMatchScrutineesFuel_success_nodesBelow scrutineeAccepted allocatedInvariant.nodesBelow)
  have casesNodes := (Detail.inferMatchCasesFuel_occurrenceBoundExtends casesAccepted).nodesBelowNextOccurrence hiddenNodes
  have defaultSource : TypingSourceExtends (defaultResult.state.toTypedSource (bodyRoots selected))
      (result.state.toTypedSource (bodyRoots selected)) := by
    rw [resultEq]
    exact ⟨rfl, List.prefix_append _ _⟩
  have casesSource := (inferStatementsFuel_success_typingSourceExtends defaultAccepted casesNodes (bodyRoots selected)).trans defaultSource
  have defaultPatterns : defaultResult.state.integerPatterns ⊆ selected.body.returned.integerPatterns := by
    simpa [resultEq, State.recordNode, State.restoreLexicalScope] using boundary.integerPatterns
  have defaultLiterals : defaultResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.recordNode, State.restoreLexicalScope] using boundary.integerLiterals
  have defaultRequirements : defaultResult.state.requirements ⊆ selected.body.returned.requirements := by
    simpa [resultEq, State.recordNode, State.restoreLexicalScope] using boundary.requirements
  obtain ⟨casesBoundary, scrutineeTyping, hiddenSafe⟩ :=
    matchEntry_for descend checkedProgram recursiveExpression boundary returnSafe
      (fun expression single => descend here (ChildStep.statement_match_single boundary.accepted form rfl
        single (by
          have child := scrutineeAccepted
          rw [single] at child
          exact child)))
      (fun _ _ multiple child => descend here (ChildStep.statement_match_many boundary.accepted form rfl
        multiple child)) scrutineeAccepted hiddenAllocation
      casesAccepted casesExtension casesSource
      ((Detail.inferStatementsFuel_integerPatterns_subset defaultAccepted).trans defaultPatterns)
      ((Detail.inferStatementsFuel_integerLiterals_subset defaultAccepted).trans defaultLiterals)
      ((Detail.inferStatementsFuel_requirements_subset defaultAccepted).trans defaultRequirements) contains
  obtain ⟨casesInvariant, casesActual, casesOperational, caseFacts, casesTyping, allReturnEq⟩ :=
    matchCases_for descend checkedProgram
      (descend here (ChildStep.statement_match_cases boundary.accepted form rfl scrutineeAccepted
        hiddenAllocation casesAccepted)) casesBoundary hiddenSafe returnAdmissible
      (fun small less => recursiveBody small (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
  have casesScope : checked.state.lexicalScope = hiddenState.lexicalScope :=
    Detail.inferMatchCasesFuel_success_lexicalScope_eq rfl casesAccepted
  have defaultSafe : ∀ binder ∈ checked.state.localBinders,
      Safe binder.scheme.quantified checked.state expectedReturn := by
    apply safe_active_iff.mp
    have privacy := inferMatchCasesFuel_private (activeSchemeQuantifiers hiddenState) childFuel
      inferenceContext scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState
      casesBoundary.invariant.ready casesBoundary.operational.requirements
      (activeSchemeQuantifiers_below_next casesBoundary.operational.quantifiersBelow)
      casesBoundary.operational.privacy.all_live catalog formation canonical scrutineeBelow
      casesBoundary.scrutineeSafe returnBelow hiddenSafe rfl _ casesAccepted
    have binders : checked.state.localBinders = hiddenState.localBinders := congrArg LexicalScope.binders casesScope
    simpa only [activeSchemeQuantifiers, binders] using privacy.1 expectedReturn hiddenSafe
  have finalContains := (boundary.rawSubtree.finalized selected.body.resources).containsStatement contains
  have reference : ∀ child ∈ defaultResult.statements,
      (.statement child : NodeId) ∈ (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases,
        defaultBody := some defaultResult.statements,
        requirements := checked.cases.flatMap (·.pattern.requirements) }).references := by
    intro child member
    simp only [StatementForm.references, MatchResolution.references]
    apply List.mem_append_right
    simpa using (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.statement child ∈ defaultResult.statements.map NodeId.statement)
  obtain ⟨defaultContext, defaultFacts, _, _, defaultOperational, defaultTyping, defaultAgreement⟩ :=
    recursiveBody childFuel (Nat.lt_succ_self _)
      (descend here (ChildStep.statement_match_default boundary.accepted form rfl scrutineeAccepted
        hiddenAllocation casesAccepted defaultEq defaultAccepted)) defaultSafe returnAdmissible ({
      accepted := defaultAccepted, interfaces := boundary.interfaces, extension := defaultExtension
      scope := boundary.scope, invariant := casesInvariant, actual := casesActual, operational := casesOperational
      rawSubtrees := fun child member =>
        (boundary.rawSubtree.child (directChild_statement_reference contains (reference child member))).monoBefore defaultSource
      integerPatterns := defaultPatterns, integerLiterals := defaultLiterals, requirements := defaultRequirements
      covered := fun child member => TemplateScopeCovered.statementChild boundary.covered selected.body.resources.graph_closed
        ((boundary.rawSubtree.finalized selected.body.resources).directChild
          (directChild_statement_reference contains (reference child member))) (fun _ member => member)
      actualCovered := fun child member => boundary.actualCovered.preserved_statement_reference contains
        (boundary.rawSubtree.finalized selected.body.resources) (reference child member) } :
      StatementsBoundary selected childFuel inferenceContext defaultBody.value expectedReturn
        checked.state defaultResult frames target)
  obtain ⟨summary, merged⟩ := mergeBodyControls_withDefault_eq_some caseFacts defaultFacts
  let facts : StatementFacts := {
    type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then selected.body.finalized.substitution.apply expectedReturn else .unit
    hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
    sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
    control := summary.eraseValue }
  have resolvedFinal : selected.body.finalized.substitution.apply (defaultResult.state.resolve expectedReturn) =
      selected.body.finalized.substitution.apply expectedReturn := by
    simpa [State.resolve, InferState.resolve] using defaultExtension expectedReturn
  have typeEq : selected.body.finalized.substitution.apply result.type = facts.type := by
    simp only [resultEq]
    change selected.body.finalized.substitution.apply
      (if checked.allReturn && defaultResult.sawReturn then defaultResult.state.resolve expectedReturn else .unit) = _
    dsimp [facts]
    rw [allReturnEq, defaultAgreement.sawReturn_eq]
    cases checked.allReturn <;> cases defaultResult.sawReturn <;> simp [resolvedFinal]
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
      target result.id target facts := by
    exact .matchWithDefault finalContains rfl rfl scrutineeTyping casesTyping defaultTyping
      (by simp [MatchResolution.applySubstitution]) merged typeEq
  have agreement : StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.matchWithDefault allReturnEq defaultAgreement defaultExtension _ _
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq, ← casesScope]
    exact casesInvariant.active.restoreLexicalScope_recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq, ← casesScope]
    exact (defaultOperational.restoreSaved casesOperational.origins
      (ProtectedVariables.inferStatementsFuel_binders_subset defaultAccepted)).recordStatement _ rfl
  have isolation : ActiveSchemeQuantifierIsolation result.state := by
    rw [resultEq, ← casesScope]
    exact casesInvariant.schemeIsolation
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted formation canonical active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension isolation typing
  exact ⟨target, facts, invariant, casesActual, operational, typing, agreement⟩

theorem statement_match_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}
    (descend : ChildClosed callProvenance)
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .matchWith scrutinees arms)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel + 1 →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        callProvenance (.statements small inferenceContext bodySource expectedReturn bodyInitial bodyResult) →
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn
          bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  cases defaultEq : arms.value.defaultBody with
  | none =>
    exact statement_match_without_default_for descend checkedProgram recursiveExpression here form defaultEq boundary
      returnSafe returnAdmissible recursiveBody
  | some defaultBody =>
    exact statement_match_with_default_for descend checkedProgram recursiveExpression here form defaultEq boundary
      returnSafe returnAdmissible recursiveBody

theorem statement_match_with_default
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {defaultBody : Syntax.Block} {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel + 1 →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn
          bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_match_with_default_for (callProvenance := fun _ => True) true_childClosed checkedProgram
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursiveExpression smaller less boundary)
    True.intro form defaultEq boundary returnSafe returnAdmissible
    (fun small less => by
      intro bodySource bodyInitial bodyResult bodyTarget _
      exact recursiveBody small less)

theorem statement_match
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .matchWith scrutinees arms)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel + 1 →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn
          bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_match_for (callProvenance := fun _ => True) true_childClosed checkedProgram
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursiveExpression smaller less boundary)
    True.intro form boundary returnSafe returnAdmissible
    (fun small less => by
      intro bodySource bodyInitial bodyResult bodyTarget _
      exact recursiveBody small less)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedStatementDispatch
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}

theorem statementRooted_zero_for : StatementRootedSoundnessFor callProvenance selected 0 := by
  intro inferenceContext statement expectedReturn initial result frames target here returnSafe returnAdmissible boundary
  have success := boundary.accepted
  simp only [Detail.inferStatementFuel] at success
  cases success

theorem statementRooted_step_of_for_for
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (barriers : BodyInitializerBarriersFor callProvenance selected)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    (recursiveBody : ∀ smaller, smaller < childFuel + 1 → StatementsRootedSoundnessFor callProvenance selected smaller)
    (placeSound : PlaceRootedSoundnessFor callProvenance selected childFuel)
    (forSound : ∀ {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
      {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
      {initial : State} {result : Detail.StatementResult}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
      callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result) →
      statement.value = .forLoop headerSpan initializer condition post body →
      StatementBoundary selected (childFuel + 1) inferenceContext statement expectedReturn initial result frames target →
      (∀ binder ∈ initial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementConclusion selected inferenceContext expectedReturn result frames target) :
    StatementRootedSoundnessFor callProvenance selected (childFuel + 1) := by
  intro inferenceContext statement expectedReturn initial result frames target here returnSafe returnAdmissible boundary
  have expressionSound : ExpressionRootedSoundnessFor callProvenance selected childFuel :=
    expressionRooted_of_retained_for checked (recursiveExpression childFuel (Nat.lt_succ_self childFuel))
  have bodySound : StatementsRootedSoundnessFor callProvenance selected childFuel :=
    recursiveBody childFuel (Nat.lt_succ_self childFuel)
  cases form : statement.value with
  | letDecl name annotation initializer =>
    cases initializer with
    | none =>
      cases annotation with
      | none =>
        have success := boundary.accepted
        simp [Detail.inferStatementFuel, form, bind, Except.bind, throw] at success
      | some sourceType => exact statement_annotatedUninitialized checked form boundary
    | some source =>
      obtain ⟨occurrence, childEq, contextEq, initialEq, resultEq⟩ :=
        boundary.initializerOccurrence checked form
      have actualBoundary : StatementBoundary selected (occurrence.childFuel + 1)
          occurrence.inferenceContext statement expectedReturn occurrence.entry occurrence.result frames target := by
        simpa only [childEq, contextEq, initialEq, resultEq] using boundary
      have actualHere : callProvenance (.statement (occurrence.childFuel + 1)
          occurrence.inferenceContext statement expectedReturn occurrence.entry occurrence.result) := by
        simpa only [childEq, contextEq, initialEq, resultEq] using here
      have childSound : ExpressionRootedSoundnessFor callProvenance selected occurrence.childFuel := by
        rw [childEq]
        exact expressionSound
      simpa only [contextEq, resultEq] using
        statement_initialized_for occurrence checked descend childSound actualHere actualBoundary
          (barriers.statement occurrence actualHere actualBoundary)
  | returnStmt value =>
    cases value with
    | none => exact statement_returnUnit checked form boundary
    | some value => exact statement_returnValue_for checked descend expressionSound here form boundary returnSafe returnAdmissible
  | expression expression trailingSemicolon =>
    exact statement_expression_for checked descend expressionSound here form boundary
  | ifThen condition body elseBody =>
    cases elseBody with
    | none =>
      exact statement_if_without_else_for checked descend expressionSound here form boundary returnSafe returnAdmissible
        (fun bodyHere safe admissible bodyBoundary => bodySound bodyHere safe admissible bodyBoundary)
    | some elseBody =>
      exact statement_if_with_else_for checked descend expressionSound here form boundary returnSafe returnAdmissible
        (fun bodyHere safe admissible bodyBoundary => bodySound bodyHere safe admissible bodyBoundary)
  | block body =>
    exact statement_block_for checked descend bodySound here form returnSafe returnAdmissible boundary
  | assignValue target operator value =>
    exact statement_assignValue_for checked descend placeSound expressionSound here form boundary
  | assignBitNot target span => exact statement_assignBitNot_for checked descend placeSound here form boundary
  | matchWith scrutinees arms =>
    exact statement_match_for descend checked recursiveExpression here form boundary returnSafe returnAdmissible
      (fun smaller below {bodySource bodyInitial bodyResult bodyTarget} bodyHere safe admissible bodyBoundary =>
        recursiveBody smaller below bodyHere safe admissible bodyBoundary)
  | forLoop headerSpan initializer condition post body =>
    exact forSound here form boundary returnSafe returnAdmissible
  | whileLoop condition body =>
    exact statement_while_for checked descend expressionSound here form boundary returnSafe returnAdmissible
      (fun bodyHere safe admissible bodyBoundary => bodySound bodyHere safe admissible bodyBoundary)
  | assembly block =>
    have success := boundary.accepted
    simp only [Detail.inferStatementFuel, form] at success
    cases success
  | breakStmt => exact statement_break checked form boundary
  | continueStmt => exact statement_continue checked form boundary
  | error =>
    have success := boundary.accepted
    simp only [Detail.inferStatementFuel, form] at success
    cases success

theorem statementRooted_zero : StatementRootedSoundness selected 0 :=
  statementRootedSoundness_of_true (statementRooted_zero_for (selected := selected) (callProvenance := fun _ => True))

theorem statementRooted_step_of_for
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : BodyInitializerBarriers selected)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    (recursiveBody : ∀ smaller, smaller < childFuel + 1 → StatementsRootedSoundness selected smaller)
    (placeSound : PlaceRootedSoundness selected childFuel)
    (forSound : ∀ {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
      {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
      {initial : State} {result : Detail.StatementResult}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
      statement.value = .forLoop headerSpan initializer condition post body →
      StatementBoundary selected (childFuel + 1) inferenceContext statement expectedReturn initial result frames target →
      (∀ binder ∈ initial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementConclusion selected inferenceContext expectedReturn result frames target) :
    StatementRootedSoundness selected (childFuel + 1) := by
  apply statementRootedSoundness_of_true
  apply statementRooted_step_of_for_for checked true_childClosed barriers.with_true
    (fun smaller less => expressionRetainedSoundnessFor_true (recursiveExpression smaller less))
    (fun smaller less => statementsRootedSoundnessFor_true (recursiveBody smaller less))
    (placeRootedSoundnessFor_true placeSound)
  intro inferenceContext statement headerSpan initializer post condition body expectedReturn initial result frames target
    _ form boundary returnSafe returnAdmissible
  exact forSound form boundary returnSafe returnAdmissible

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedRecursiveAssembly
/-! Actual expressions, statements and header items are assembled together by
fuel. Generalization barriers remain indexed by the concrete selected
initializer boundaries, ready for the compiler-scope producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel}

theorem recursiveSoundness_of_barriers_for
    {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (barriers : BodyInitializerBarriersFor callProvenance selected) :
    ∀ childFuel,
      ExpressionRetainedSoundnessFor callProvenance selected childFuel ∧
      StatementRootedSoundnessFor callProvenance selected childFuel ∧
      StatementsRootedSoundnessFor callProvenance selected childFuel ∧
      ForItemRootedSoundnessFor callProvenance selected childFuel ∧
      ForItemsRootedSoundnessFor callProvenance selected childFuel := by
  intro childFuel
  induction childFuel using Nat.strongRecOn with
  | ind childFuel induction =>
    cases childFuel with
    | zero =>
      exact ⟨expressionRetained_zero_for, statementRooted_zero_for,
        (fun _ safe admissible boundary => statementsRooted_zero safe admissible boundary), forItemRooted_zero_for,
        forItemsRooted_of_item_for checked descend forItemRooted_zero_for⟩
    | succ childFuel =>
      have expressions : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller :=
        fun smaller below => (induction smaller below).1
      have rooted : ∀ smaller, smaller < childFuel + 1 → ExpressionRootedSoundnessFor callProvenance selected smaller :=
        fun smaller below => expressionRooted_of_retained_for checked (expressions smaller below)
      have bodies : ∀ smaller, smaller < childFuel + 1 → StatementsRootedSoundnessFor callProvenance selected smaller :=
        fun smaller below => (induction smaller below).2.2.1
      have previous := induction childFuel (Nat.lt_succ_self childFuel)
      have expressionSound : ExpressionRootedSoundnessFor callProvenance selected childFuel :=
        rooted childFuel (Nat.lt_succ_self childFuel)
      have placeSound : PlaceRootedSoundnessFor callProvenance selected childFuel :=
        placeRootedSoundness_for checked descend childFuel
          (fun smaller below => rooted smaller (Nat.lt_trans below (Nat.lt_succ_self childFuel)))
      have items : ForItemRootedSoundnessFor callProvenance selected (childFuel + 1) :=
        forItemRooted_step_for checked descend barriers expressionSound placeSound
      have statementSound : StatementRootedSoundnessFor callProvenance selected (childFuel + 1) := by
        apply statementRooted_step_of_for_for checked descend barriers expressions bodies placeSound
        intro inferenceContext statement headerSpan initializer post condition body expectedReturn initial result frames target
          here form boundary returnSafe returnAdmissible
        exact statement_for_for checked descend previous.2.2.2.2 expressionSound here form boundary returnSafe returnAdmissible
          (fun bodyHere safe admissible bodyBoundary => previous.2.2.1 bodyHere safe admissible bodyBoundary)
      exact ⟨expressionRetained_step_for checked descend expressions previous.2.2.1,
        statementSound, statementsRooted_step_for checked descend previous.2.1 previous.2.2.1,
        items, forItemsRooted_of_item_for checked descend items⟩

theorem recursiveSoundness_of_barriers
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : BodyInitializerBarriers selected) :
    ∀ childFuel,
      ExpressionRetainedSoundness selected childFuel ∧
      StatementRootedSoundness selected childFuel ∧
      StatementsRootedSoundness selected childFuel ∧
      ForItemRootedSoundness selected childFuel ∧
      ForItemsRootedSoundness selected childFuel := by
  intro childFuel
  have result := recursiveSoundness_of_barriers_for checked true_childClosed barriers.with_true childFuel
  exact ⟨expressionRetainedSoundness_of_true result.1,
    statementRootedSoundness_of_true result.2.1,
    statementsRootedSoundness_of_true result.2.2.1,
    forItemRootedSoundness_of_true result.2.2.2.1,
    forItemsRootedSoundness_of_true result.2.2.2.2⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedBodyAssembly
/-! The actual recursive assembly closes original body typing. Its remaining
inputs are the concrete initialized-occurrence generalization barriers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference
open SourceCompiledLocalFinalization

theorem checked_statements_of_barriers {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (barriers : BodyInitializerBarriers selected) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original :=
  checked_statements_of_recursive selected checked member
    (recursiveSoundness_of_barriers checked barriers fuel).2.2.1

/-- Initial invariants, executable interfaces and recursive child typing are
all supplied internally for the same selected original body and finalizer. -/
theorem checked_body_of_barriers {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (barriers : BodyInitializerBarriers selected) :
    CheckedBodyHasType compiled.program.signatures selected.signature selected.original :=
  checkedBodyHasType_ofStatements selected.body.accepted
    (checked_statements_of_barriers selected checked member barriers)

/-- Executable interfaces may come from any actual cached ordinary row,
including one discovered after the initial specialization frontier. -/
theorem checked_statements_of_barriers_of_interfaces {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (barriers : BodyInitializerBarriers selected) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original :=
  checked_statements_of_recursive_of_interfaces selected checked interfaces
    (recursiveSoundness_of_barriers checked barriers fuel).2.2.1

theorem checked_body_of_barriers_of_interfaces {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (barriers : BodyInitializerBarriers selected) :
    CheckedBodyHasType compiled.program.signatures selected.signature selected.original :=
  checkedBodyHasType_ofStatements selected.body.accepted
    (checked_statements_of_barriers_of_interfaces selected checked interfaces barriers)


/-- The remaining barriers are requested only at calls actually reached from
this original selected ordinary or method body check. -/
theorem checked_statements_of_actual_barriers_of_interfaces {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (barriers : BodyInitializerBarriersFor selected.InferenceCall selected) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original :=
  checked_statements_of_recursive_of_interfaces_for selected checked interfaces selected.inferenceCall_root
    (recursiveSoundness_of_barriers_for checked selected.inferenceCall_closed barriers fuel).2.2.1

theorem checked_body_of_actual_barriers_of_interfaces {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (barriers : BodyInitializerBarriersFor selected.InferenceCall selected) :
    CheckedBodyHasType compiled.program.signatures selected.signature selected.original :=
  checkedBodyHasType_ofStatements selected.body.accepted
    (checked_statements_of_actual_barriers_of_interfaces selected checked interfaces barriers)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedFunctionValidity
/-! The actual selected ordinary function receives semantic validity from its
original checker receipt and the generalized recursive body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

/-- Complete validity for the original ordinary definition selected by this
compiler row. The barrier producer is tied to the same selected body. -/
theorem function_valid_of_barriers_of_interfaces
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected.toBodySelection).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (barriers : SelectedInitializerBarriers selected) :
    FunctionDefinition.Valid compiled.program.signatures
      (FunctionDefinition.ofChecked selected.original) := by
  apply functionDefinitionValid_ofCheckProgram checked selected.originalMember
  intro signature signatureMember bodySuccess
  have same : signature = selected.signature :=
    eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids
      signatureMember selected.signatureMember
      ((checkFunctionBody_success_declaration bodySuccess).symm.trans
        (checkFunctionBody_success_declaration selected.body.accepted))
  subst signature
  exact checked_body_of_barriers_of_interfaces selected.toBodySelection checked interfaces barriers

theorem function_valid_of_barriers {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (barriers : SelectedInitializerBarriers selected) :
    FunctionDefinition.Valid compiled.program.signatures
      (FunctionDefinition.ofChecked selected.original) :=
  function_valid_of_barriers_of_interfaces selected checked
    (selected_original_interfaces selected.toBodySelection member) barriers

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end
