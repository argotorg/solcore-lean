import Solcore.Frontend.SourceInference.LocalGeneralizationHeaderBoundaries

/-! A real for-statement carries header generalization boundaries through its
condition, body, post items, and both actual lexical scope restorations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

/-- Every initialized header binder of the actual returned for node has its
initializer-local reads contained in the real initializer return state. -/
theorem inferStatementFuel_for_boundary {fuel : Nat} {context : Context}
    {statement : Syntax.Statement} {expected : Ty} {initial : State} {result : StatementResult}
    {headerSpan : Syntax.SourceSpan} {initializers post : List Syntax.ForItem}
    {condition : Syntax.Expr} {body : Syntax.Located (List Syntax.Statement)}
    (form : statement.value = .forLoop headerSpan initializers condition post body)
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
    ∃ node : StatementNode, .statement node ∈ result.state.nodes ∧ node.id = result.id ∧
      StatementSince initial.nextLocal result.state node := by
  unfold inferStatementFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  let allocated := initial.allocateStatementId.2
  cases initRun : inferForItemsFuel fuel context initializers allocated with
  | error error => simp [allocated, initRun] at accepted
  | ok initResult =>
    cases condRun : inferExprFuel fuel context condition (some .bool) initResult.state with
    | error error => simp [allocated, initRun, condRun] at accepted
    | ok pair =>
      rcases pair with ⟨test, testState⟩
      let loopContext := { context with loopDepth := context.loopDepth + 1 }
      cases bodyRun : inferStatementsFuel fuel loopContext body.value expected testState with
      | error error => simp [allocated, initRun, condRun, loopContext, bodyRun] at accepted
      | ok bodyResult =>
        let afterBody := bodyResult.state.restoreLexicalScope initResult.state.lexicalScope
        cases postRun : inferForItemsFuel fuel loopContext post afterBody with
        | error error => simp [allocated, initRun, condRun, loopContext, bodyRun, afterBody, postRun] at accepted
        | ok postResult =>
          simp only [allocated, initRun, condRun, loopContext, bodyRun, afterBody, postRun,
            pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
          cases accepted
          have readyAllocated : Ready allocated := ⟨ready.wellFormed, ready.allocated, ready.origins⟩
          have belowAllocated : allocated.LocalBindersBelowNextLocal := below
          have readyInit := readyAllocated.progress (LocalReadEvents.inferForItemsFuel_origins_progress initRun)
          have belowInit := inferForItemsFuel_preserves_localBindersBelowNextLocal belowAllocated initRun
          have condScope := LocalReadScopeProgress.inferExprFuel_scope_progress condRun
          have bodyScope := LocalReadScopeProgress.inferStatementsFuel_scope_progress bodyRun
          have loopScope : LocalReadScopeProgress.Progress initResult.state afterBody :=
            (condScope.trans bodyScope).restore (fun _ member => member)
          have readyBody : Ready afterBody :=
            (readyInit.progress (LocalReadEvents.inferExprFuel_origins_progress condRun)).progress
              (LocalReadEvents.inferStatementsFuel_origins_progress bodyRun)
          have belowBody : afterBody.LocalBindersBelowNextLocal := by
            intro binder member
            exact Nat.lt_of_lt_of_le (belowInit binder member) loopScope.next
          have initBounds := (inferForItemsFuel_boundaries initRun readyAllocated belowAllocated).progress loopScope
          have postBounds := inferForItemsFuel_boundaries postRun readyBody belowBody
          have initNext := inferForItemsFuel_nextLocal_le initRun
          have postEntry : initial.nextLocal ≤ afterBody.nextLocal := Nat.le_trans initNext loopScope.next
          have postScope := LocalReadScopeProgress.inferForItemsFuel_scope_progress postRun
          have initialAtPost := initBounds.progress postScope
          have initialRestored := initialAtPost.restore_saved allocated.lexicalScope
            (initial := initial) (fun _ member => member) below (Nat.le_refl _)
          have postRestored := (postBounds.weaken postEntry).restore_saved allocated.lexicalScope
            (initial := initial) (fun _ member => member) below (Nat.le_refl _)
          refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, ?_⟩
          exact ⟨initialRestored.progress (LocalReadScopeProgress.Progress.recordStatement _ _),
            postRestored.progress (LocalReadScopeProgress.Progress.recordStatement _ _)⟩

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
