import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyCompletion

/-! Original completion receipts select the reachable suffix of the actual
compiler tree. All nested bodies keep their existing scoped evaluation mode. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference AcceptedCompilerBodyCompletion

private theorem original_read {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

private def FinishAt (source : TypedSource) (expected : TypeSystem.Ty)
    (mode : Bool) (node : StatementNode) (rest : List StatementId) : Prop :=
  match node.form with
  | .returnStmt _ | .breakStmt | .continueStmt => True
  | .expression _ false => mode = false ∨ (rest = [] ∧ node.type = expected)
  | .block body => Finish source expected mode rest ∨ Stops source body
  | .ifThen _ left right => Finish source expected mode rest ∨
      (Stops source left ∧ Stops source (right.getD []))
  | .matchWith resolution => Finish source expected mode rest ∨ matchStops source resolution = true
  | _ => Finish source expected mode rest

private theorem finish_at {source expected mode id node rest}
    (finish : Finish source expected mode (id :: rest))
    (found : source.lookupStatement? id = some node) : FinishAt source expected mode node rest := by
  cases finish with
  | nested =>
    cases form : node.form <;> simp only [FinishAt, form]
    all_goals first | exact True.intro | exact Finish.nested _ | exact Or.inl (Finish.nested _) | exact Or.inl rfl | skip
    rename_i expression semicolon
    cases semicolon with
    | false => exact Or.inl True.intro
    | true => exact Finish.nested _
  | returning actual form =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form]
  | tail actual form type =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form]
    exact .inr ⟨True.intro, type⟩
  | «prefix» actual continuing remaining =>
    cases Option.some.inj (actual.symm.trans found)
    cases form : node.form <;> simp only [FinishAt, form]
    all_goals first | exact True.intro | exact remaining | exact Or.inl remaining | skip
    rename_i expression semicolon
    cases semicolon with
    | true => exact remaining
    | false => simp [form, notTail] at continuing
  | block actual form stopped _ =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form]
    exact .inr stopped
  | conditional actual form first second _ =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form, Option.getD_some]
    exact .inr ⟨first, second⟩
  | matching actual form present arms default _ =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form]
    exact .inr (by simp [matchStops, present, arms, Stops] at default ⊢; exact default)

/-- A formed tree retains every emitted child. Original completion determines
which continuation can be reached, without supplying a Source execution law. -/
theorem Tree.complete_of_formed {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (formed : tree.formed = true) {expected : TypeSystem.Ty}
    (finish : Finish source expected mode statements) : tree.complete expected = true := by
  induction tree generalizing expected with
  | nil => cases finish <;> simp_all [Tree.complete]
  | returning | returnUnit | breaking | continuing => rfl
  | assigning | boundary | forBoundary | matching => cases formed
  | tailValue read form _ _ _ _ =>
    have atHead := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form, Bool.true_eq_false, false_or] at atHead
    simp only [Tree.complete, atHead.2, decide_true]
  | initialized read form _ _ _ _ _ _ _ ih =>
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    exact ih formed next
  | absent read form _ _ _ _ ih =>
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    exact ih formed next
  | assigned read form _ _ _ _ ih =>
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    exact ih formed next
  | discard read form _ _ _ _ ih =>
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    exact ih formed next
  | @valueDiscard mode escaped fuel scope id rest node stored expression tail read form notTail child generated statementType remaining ih =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have nested : mode = false := by simpa using formed.1
    cases nested
    simpa only [Tree.complete, Bool.not_false, Bool.true_and] using ih (expected := expected) formed.2 (.nested _)
  | block read form inner remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have child := innerIH (expected := expected) formed.1 (.nested _)
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    rcases next with next | stopped
    · simp only [Tree.complete, child, formed.2, tailIH formed.2 next, Bool.true_and, Bool.true_or]
    · simp only [Stops] at stopped
      simp only [Tree.complete, child, formed.2, stopped, Bool.true_and, Bool.or_true]
  | conditional read form _ _ _ left right remaining leftIH rightIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have first := leftIH (expected := expected) formed.1.1 (.nested _)
    have second := rightIH (expected := expected) formed.1.2 (.nested _)
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    rcases next with next | stopped
    · simp only [Tree.complete, first, second, formed.2, tailIH formed.2 next, Bool.true_and, Bool.true_or]
    · simp only [Stops] at stopped
      simp only [Tree.complete, first, second, formed.2, stopped.1, stopped.2, Bool.true_and, Bool.or_true]
  | whileLoop read form _ _ _ _ inner remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    simp only [Tree.complete, innerIH (expected := expected) formed.1 (.nested _), tailIH formed.2 next, Bool.true_and]
  | matched read form receipt branches remaining branchIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have children : receipt.requests.attach.all (fun request =>
        (branches request.val request.property).complete expected) = true := by
      apply List.all_eq_true.mpr
      intro request member
      exact branchIH request.val request.property
        (List.all_eq_true.mp formed.1 request member) (.nested _)
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    rcases next with next | stopped
    · simp only [Tree.complete, children, formed.2, tailIH formed.2 next, Bool.true_and, Bool.true_or]
    · simp only [Tree.complete, children, formed.2, stopped, Bool.true_and, Bool.or_true]
  | forLoop read form _ _ _ _ initial inner after remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    simp only [Tree.complete, formed.1.1.1, innerIH (expected := expected) formed.1.1.2 (.nested _),
      formed.1.2, tailIH formed.2 next, Bool.true_and]

theorem Tree.complete_of_formed_nested {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt false escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (formed : tree.formed = true) (expected : TypeSystem.Ty) : tree.complete expected = true :=
  tree.complete_of_formed readPolicy formed (.nested statements)

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
