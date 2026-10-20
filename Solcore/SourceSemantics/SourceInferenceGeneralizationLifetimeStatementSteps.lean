import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeExpressionSteps
import Solcore.SourceSemantics.SourceInferencePrivacyScopeRetention

/-! Actual statement completion, saved-scope restoration and ordered block
suffixes preserve the lifetime of an event produced by a nested child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem recordNode {entryNext : Nat} {state : State} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext state outputs) (node : Node) :
    GeneralizationLifetime event entryNext (state.recordNode node) outputs :=
  { lifetime with live := lifetime.live.transport rfl (.of_substitution_eq rfl) }

theorem restoreScope {entryNext : Nat} {state : State} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext state outputs) (saved : LexicalScope)
    (subset : saved.binders ⊆ state.localBinders) :
    GeneralizationLifetime event entryNext (state.restoreLexicalScope saved) outputs := by
  refine { lifetime with live := ?_ }
  intro liveBinder member
  exact (lifetime.live liveBinder (subset member)).transport (.of_substitution_eq rfl)

theorem statement_expression
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expression : Syntax.Expr} {semicolon : Bool} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {child : InferredExpression × State} {result : StatementResult}
    (form : source.value = .expression expression semicolon)
    (allocation : initial.allocateStatementId = (id, allocated))
    (childAccepted : inferExprFuel fuel context expression none allocated = .ok child)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have sameNext : allocated.inference.next = initial.inference.next := by
    have pair := congrArg Prod.snd allocation
    change initial.allocateStatementId.2 = allocated at pair
    rw [← pair]; rfl
  unfold inferStatementFuel at accepted
  simp only [allocation, form, childAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  have recorded := lifetime.recordNode (.statement {
    id, span := source.span, type := if semicolon then .unit else child.1.type,
    form := .expression child.1.id semicolon })
  rw [sameNext] at recorded
  refine { recorded with values := ?_ }
  intro type member
  cases List.mem_singleton.mp member
  split
  · exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
  · exact recorded.values _ (List.mem_singleton_self _)

theorem statement_return
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expression : Syntax.Expr} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {child : InferredExpression × State} {result : StatementResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .returnStmt (some expression))
    (allocation : initial.allocateStatementId = (id, allocated))
    (childAccepted : inferExprFuel fuel context expression (some expectedReturn) allocated = .ok child)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedEq : allocated = initial.allocateStatementId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have properties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateStatementId) catalog.formation catalog.canonical
    (by intro type member; cases member; exact sameNext ▸ returnBelow) childAccepted
  have returnSafe := safe_resolved properties.2.1
    (lifetime.older expectedReturn (sameNext ▸ returnBelow))
  unfold inferStatementFuel at accepted
  simp only [allocation, form, childAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  have recorded := lifetime.recordNode (.statement {
    id, span := source.span, type := child.2.resolve expectedReturn,
    form := .returnStmt (some child.1.id) })
  rw [sameNext] at recorded
  exact { recorded with values := fun type member => (List.mem_singleton.mp member) ▸ returnSafe }

theorem statement_block
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {body : List Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {child : BlockResult} {result : StatementResult}
    (form : source.value = .block body)
    (allocation : initial.allocateStatementId = (id, allocated))
    (childAccepted : inferStatementsFuel fuel context body expectedReturn allocated = .ok child)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.state [child.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have sameNext : allocated.inference.next = initial.inference.next := by
    have pair := congrArg Prod.snd allocation
    change initial.allocateStatementId.2 = allocated at pair
    rw [← pair]; rfl
  have restored := lifetime.restoreScope allocated.lexicalScope
    (inferStatementsFuel_binders_subset childAccepted)
  unfold inferStatementFuel at accepted
  simp only [allocation, form, childAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  have recorded := restored.recordNode (.statement {
    id, span := source.span, type := child.type, form := .block child.statements })
  simpa only [sameNext] using recorded

theorem statements_single
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {head : StatementResult} {result : BlockResult}
    (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
    (accepted : inferStatementsFuel (fuel + 1) context [source] expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.state [head.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  unfold inferStatementsFuel at accepted
  simp only [headAccepted, bind, Except.bind, pure, Pure.pure, Except.pure,
    Except.ok.injEq] at accepted
  cases accepted
  refine { lifetime with values := ?_ }
  intro type member
  cases List.mem_singleton.mp member
  split
  · exact lifetime.values _ (List.mem_singleton_self _)
  · exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)

theorem statements_head
    {fuel : Nat} {context : SourceInference.Context} {source next : Syntax.Statement}
    {sources : List Syntax.Statement} {expectedReturn : Ty} {initial : State}
    {head : StatementResult} {tail result : BlockResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
    (tailAccepted : inferStatementsFuel fuel context (next :: sources) expectedReturn head.state = .ok tail)
    (accepted : inferStatementsFuel (fuel + 1) context (source :: next :: sources)
      expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.state [head.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have properties := inferStatementFuel_inferenceProperties ready catalog.formation
    catalog.canonical returnBelow headAccepted
  have after := lifetime.inferStatements properties.2.1
    ((inferStatementFuel_direct_progress headAccepted).wellFormed wellFormed) catalog
    (returnBelow.weaken properties.1.next_le) (lifetime.older _ returnBelow) tailAccepted
  unfold inferStatementsFuel at accepted
  simp only [headAccepted, tailAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  refine { after with values := ?_ }
  intro type member
  cases List.mem_singleton.mp member
  split
  · exact after.values _ (by simp)
  · split
    · exact after.values _ (by simp)
    · exact after.values _ (by simp)

theorem statements_tail
    {fuel : Nat} {context : SourceInference.Context} {source next : Syntax.Statement}
    {sources : List Syntax.Statement} {expectedReturn : Ty} {initial : State}
    {head : StatementResult} {tail result : BlockResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
    (tailAccepted : inferStatementsFuel fuel context (next :: sources) expectedReturn head.state = .ok tail)
    (accepted : inferStatementsFuel (fuel + 1) context (source :: next :: sources)
      expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event head.state.inference.next tail.state [tail.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have properties := inferStatementFuel_inferenceProperties ready catalog.formation
    catalog.canonical returnBelow headAccepted
  have headSafe := lifetime.older head.type properties.2.2
  have atEntry := lifetime.weaken_entry properties.1.next_le
  unfold inferStatementsFuel at accepted
  simp only [headAccepted, tailAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  refine { atEntry with values := ?_ }
  intro type member
  cases List.mem_singleton.mp member
  split
  · exact atEntry.values _ (List.mem_singleton_self _)
  · split
    · exact headSafe
    · exact atEntry.values _ (List.mem_singleton_self _)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
