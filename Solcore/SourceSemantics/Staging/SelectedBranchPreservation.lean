import Solcore.SourceSemantics.Staging.SelectedStatementPreservationSupport
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem if_branch
    {size testSize branchSize : Nat}
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (testSmaller : testSize < size) (branchSmaller : branchSize < size)
    {scope : Scope} {context innerContext : Context} {environment : Dynamic.Environment}
    {before middle after : Heap} {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {truth : Bool} {outcome : BodyOutcome}
    {control : ControlContext} {facts : StatementFacts}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : StatementControlFormTyping scope.source control context (.ifThen condition thenBody elseBody) facts)
    (test : Size.Expression program registry testSize scope context environment before condition (.value (.bool truth)) middle)
    (branch : Size.StatementsIn program registry false branchSize scope context environment middle
      (if truth then thenBody else elseBody.getD []) innerContext outcome after) :
    ControlPreserved context before after control.returnType outcome ∧
      (∀ env, outcome = .fallthrough env → facts.control.canFallthrough = true) := by
  cases typed with
  | ifWithoutElse conditionTyped yes =>
      have first := expressionIH testSize testSmaller runtime covers locals heap conditionTyped test
      cases truth with
      | true =>
          have post := statementsIH branchSize branchSmaller runtime covers (locals.mono first.heap_extends)
            first.heap_typed yes branch
          exact ⟨⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩,
            fun env equal => ControlSummary.branches_canFallthrough_left (post.fallthrough env equal).2.2⟩
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Option.getD_none] at branch
          cases branch
          exact ⟨⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩,
            fun _ _ => ControlSummary.branches_canFallthrough_right rfl⟩
  | ifWithElse conditionTyped yes no =>
      have first := expressionIH testSize testSmaller runtime covers locals heap conditionTyped test
      cases truth with
      | true =>
          have post := statementsIH branchSize branchSmaller runtime covers (locals.mono first.heap_extends)
            first.heap_typed yes branch
          exact ⟨⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩,
            fun env equal => ControlSummary.branches_canFallthrough_left (post.fallthrough env equal).2.2⟩
      | false =>
          have post := statementsIH branchSize branchSmaller runtime covers (locals.mono first.heap_extends)
            first.heap_typed no branch
          exact ⟨⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩,
            fun env equal => ControlSummary.branches_canFallthrough_right (post.fallthrough env equal).2.2⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
