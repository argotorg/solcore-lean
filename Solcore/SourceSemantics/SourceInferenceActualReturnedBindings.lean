import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.SourceSemantics.SourceInferenceSoundness
import Solcore.SourceSemantics.Ownership

/-! Header declarations are returned before their enclosing loop records them.
This inventory follows those actual returned forms into the parent's source. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

/-- Initialized header declarations pending insertion into a statement node. -/
def CallIndex.returnedBindings : CallIndex → List InitializedLetBinding
  | .forItem _ _ _ _ item _ => forItemInitializedLetBindings item
  | .forItems _ _ _ _ result => result.items.flatMap forItemInitializedLetBindings
  | _ => []

private theorem forItems_result
    {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.ForItem} {sources : List Syntax.ForItem}
    {initial middle : State} {result : InferredForItems} {head : ForItemForm}
    (accepted : inferForItemsFuel fuel context (source :: sources) initial = .ok result)
    (first : inferForItemFuel fuel context source initial = .ok (head, middle)) :
    ∃ tail, inferForItemsFuel fuel context sources middle = .ok tail ∧
      result.items = head :: tail.items := by
  unfold inferForItemsFuel at accepted
  simp only [first, bind, Except.bind] at accepted
  cases rest : inferForItemsFuel fuel context sources middle with
  | error e => simp [rest, bind, Except.bind] at accepted
  | ok tail =>
    simp only [rest, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact ⟨tail, rfl, rfl⟩

/-- A child header's returned declaration is either still returned by its
parent header sequence, or has been recorded by its actual enclosing loop. -/
theorem ChildStep.returned_bindings {parent child : CallIndex}
    (step : ChildStep parent child) :
    child.returnedBindings ⊆
      initializedLetBindings (parent.final.toTypedSource []) ++ parent.returnedBindings := by
  cases step with
  | forItems_head accepted first =>
    obtain ⟨tail, _, items⟩ := forItems_result accepted first
    intro binding member
    apply List.mem_append_right
    simpa only [CallIndex.returnedBindings, items, List.flatMap_cons] using
      (List.mem_append_left (tail.items.flatMap forItemInitializedLetBindings) member)
  | forItems_tail accepted first rest =>
    obtain ⟨tail, tailAccepted, items⟩ := forItems_result accepted first
    have same := Except.ok.inj (tailAccepted.symm.trans rest)
    subst tail
    intro binding member
    apply List.mem_append_right
    simp only [CallIndex.returnedBindings, items, List.flatMap_cons]
    exact List.mem_append_right _ member
  | statement_for_initializer accepted form allocation initAccepted =>
    obtain ⟨init, test, testState, body, post, initRun, _, _, _, resultEq, _⟩ :=
      SourceInferenceSoundness.inferStatementFuel_success_forLoop_facts form allocation accepted
    have same := Except.ok.inj (initRun.symm.trans initAccepted)
    subst init
    intro binding member
    apply List.mem_append_left
    simp only [CallIndex.final, resultEq, initializedLetBindings, State.toTypedSource,
      State.recordNode, State.restoreLexicalScope, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, statementInitializedLetBindings]
    exact List.mem_append_right _ (List.mem_append_left _ member)
  | statement_for_post accepted form allocation initAccepted testAccepted bodyAccepted postAccepted =>
    obtain ⟨init, test, testState, body, post, initRun, testRun, bodyRun, postRun, resultEq, _⟩ :=
      SourceInferenceSoundness.inferStatementFuel_success_forLoop_facts form allocation accepted
    have same := Except.ok.inj (initRun.symm.trans initAccepted)
    subst init
    have same := Except.ok.inj (testRun.symm.trans testAccepted)
    cases same
    have same := Except.ok.inj (bodyRun.symm.trans bodyAccepted)
    subst body
    have same := Except.ok.inj (postRun.symm.trans postAccepted)
    subst post
    intro binding member
    apply List.mem_append_left
    simp only [CallIndex.final, resultEq, initializedLetBindings, State.toTypedSource,
      State.recordNode, State.restoreLexicalScope, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, statementInitializedLetBindings]
    exact List.mem_append_right _ (List.mem_append_right _ member)
  | _ => exact List.nil_subset _

end Solcore.SourceSemantics.SourceInferenceExecution
