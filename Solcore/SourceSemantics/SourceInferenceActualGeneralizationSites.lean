import Solcore.SourceSemantics.SourceInferenceActualCallProperties
import Solcore.SourceSemantics.SourceInferenceActualGeneralizationOrigins
import Solcore.SourceSemantics.SourceInferenceGeneralizationReceiptCalls
import Solcore.SourceSemantics.SourceInferenceGeneralizationReceiptUniqueness

/-! A site identifies an actual initialized declaration call. Its only child
is the exact initializer whose result supplied the generalized quantifiers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail

inductive Site : CallIndex → TypedBinder → ExpressionId → Prop where
  | statement {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expected : Ty} {initial : State} {result : StatementResult}
      (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result) :
      Site (.statement (fuel + 1) context source expected initial result)
        receipt.binding.1 receipt.value.id
  | header {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial (result, final)) :
      Site (.forItem (fuel + 1) context source initial result final)
        receipt.binding.1 receipt.value.id

theorem Origin.site {root : CallIndex} {binder : TypedBinder} {initializer : ExpressionId}
    (origin : Origin root binder initializer) :
    ∃ call, CallOccurrence root call ∧ Site call binder initializer := by
  cases origin with
  | statement receipt here => exact ⟨_, here, .statement receipt⟩
  | @header fuel context source initial result receipt here =>
      rcases result with ⟨inferred, final⟩
      exact ⟨_, here, .header receipt⟩

theorem Site.unique {call : CallIndex} {left right : TypedBinder}
    {leftId rightId : ExpressionId} (first : Site call left leftId) (second : Site call right rightId) :
    left = right ∧ leftId = rightId := by
  cases first with
  | statement receipt =>
      cases second with
      | statement other =>
          have same := LocalLetRequirementTiming.Receipt.unique receipt other
          cases same
          exact ⟨rfl, rfl⟩
  | header receipt =>
      cases second with
      | header other =>
          have same := LocalHeaderRequirementTiming.Receipt.unique receipt other
          cases same
          exact ⟨rfl, rfl⟩

private theorem annotation_unique {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {left right : Option Ty}
    (first : AnnotationExpected context source left)
    (second : AnnotationExpected context source right) : left = right := by
  cases first <;> cases second <;> simp_all

private theorem statement_child_unique
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    {child : CallIndex}
    (step : ChildStep (.statement (fuel + 1) context source expected initial result) child) :
    child = .expression fuel context receipt.initializer receipt.expected
      initial.allocateStatementId.2 receipt.value receipt.ready := by
  cases step
  all_goals have syntaxForm := receipt.form
  all_goals try solve | simp_all
  rename_i allocated id name sourceType initializer childExpected value final annotated child form allocation accepted
  have parts : receipt.name = name ∧ receipt.annotation = sourceType ∧ receipt.initializer = initializer := by
    simpa only [receipt.form, Syntax.StatementValue.letDecl.injEq, Option.some.injEq] using form
  have actualAnnotation := annotationExpected_of_receipt receipt.annotationAccepted
  rw [← parts.2.1] at annotated
  have expectedEq := annotation_unique actualAnnotation annotated
  have actualChild := receipt.child
  rw [allocation, expectedEq, parts.2.2] at actualChild
  cases Except.ok.inj (actualChild.symm.trans child)
  simp only [allocation, expectedEq, parts.2.2]

private theorem header_child_unique
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    {child : CallIndex}
    (step : ChildStep (.forItem (fuel + 1) context source initial result.1 result.2) child) :
    child = .expression fuel context receipt.initializer receipt.expected initial receipt.value receipt.ready := by
  cases step
  all_goals have syntaxForm := receipt.form
  all_goals try solve | simp_all
  rename_i name sourceType initializer childExpected value childFinal annotated form child accepted
  have parts : receipt.name = name ∧ receipt.annotation = sourceType ∧ receipt.initializer = initializer := by
    simpa only [receipt.form, Syntax.ForItemValue.letDecl.injEq, Option.some.injEq] using form
  have actualAnnotation := annotationExpected_of_receipt receipt.annotationAccepted
  rw [← parts.2.1] at annotated
  have expectedEq := annotation_unique actualAnnotation annotated
  have actualChild := receipt.child
  rw [expectedEq, parts.2.2] at actualChild
  cases Except.ok.inj (actualChild.symm.trans child)
  simp only [expectedEq, parts.2.2]

theorem Site.initializer_child {call : CallIndex} {binder : TypedBinder} {initializer : ExpressionId}
    (site : Site call binder initializer) (accepted : call.Accepted) :
    ∃ child, ChildStep call child ∧
      (∀ other, ChildStep call other → other = child) ∧
      ∀ q ∈ binder.scheme.quantified,
        ∃ type ∈ child.outputTypes, q ∈ (child.final.resolve type).freeVariables := by
  cases site with
  | statement receipt =>
      refine ⟨_, statement_initializer_child receipt accepted, ?_, ?_⟩
      · intro other step
        exact statement_child_unique receipt step
      · intro q member
        exact ⟨receipt.value.type, List.mem_singleton_self _, (List.mem_filter.mp member).1⟩
  | header receipt =>
      refine ⟨_, header_initializer_child receipt accepted, ?_, ?_⟩
      · intro other step
        exact header_child_unique receipt step
      · intro q member
        exact ⟨receipt.value.type, List.mem_singleton_self _, (List.mem_filter.mp member).1⟩

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
