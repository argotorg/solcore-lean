import Solcore.SourceSemantics.CoreLowering.CallablePreparedViewSelection
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition
import Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceForm

/-! The static view and actual generalized local read use the same input node
and closed scheme matcher. Candidate identity follows from their real receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableViewReadSelection
open Frontend SourceInference TypeSystem SourceCoreCallableViews

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Actual view lowering checks one of the three authenticated forms of the
same expression. No completeness property of a source collector is used. -/
theorem lowered_node {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {table : Table program plan} {owner : Key} {active : Substitution} {source : TypedSource}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {receipt : SourceCoreCallableViewLowering.Viewed table owner active id lowered}
    (accepted : SourceCoreCallableViewLowering.lowerWithReceipt table owner active source id lowered = .ok receipt) :
    ∃ node, source.lookupExpression? id = some node ∧
      (node = receipt.entry.view.reference.original ∨
       node = receipt.entry.view.reference.normalized ∨ node = receipt.entry.view.rawRead) := by
  unfold SourceCoreCallableViewLowering.lowerWithReceipt at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · next selected selectedAt =>
    try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
    split at accepted
    · split at accepted
      · cases accepted
      · next node actualFound =>
        try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
        split at accepted
        · next equal =>
          have forms : node = selected.view.reference.original ∨
              node = selected.view.reference.normalized ∨ node = selected.view.rawRead := by
            simpa [Bool.or_eq_true, or_assoc] using equal
          split at accepted
          · cases accepted
            exact ⟨node, actualFound, forms⟩
          · split at accepted
            · cases accepted
              exact ⟨node, actualFound, forms⟩
            · cases accepted
        · cases accepted
    · cases accepted

/-- All three accepted forms preserve the local resolution and uncoerced type. -/
theorem lowered_fields {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {table : Table program plan} {owner : Key} {active : Substitution} {source : TypedSource}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    {receipt : SourceCoreCallableViewLowering.Viewed table owner active id lowered}
    (accepted : SourceCoreCallableViewLowering.lowerWithReceipt table owner active source id lowered = .ok receipt)
    (found : source.lookupExpression? id = some node) :
    node.form = receipt.entry.view.reference.original.form ∧
      node.rawType = receipt.entry.view.rawRead.rawType := by
  obtain ⟨actual, lookup, forms⟩ := lowered_node accepted
  have equal := Option.some.inj (lookup.symm.trans found)
  subst actual
  rcases forms with rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem same_selection {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : Key} {active : Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    {receipt : SourceCoreCallableViewLowering.Viewed ancestry.views owner active id lowered}
    (accepted : SourceCoreCallableViewLowering.lowerWithReceipt ancestry.views owner active source id lowered = .ok receipt)
    (read : GeneralizedLocalReadReceipts.Certificate base.locals owner active source scope id reason lowered)
    (generalized : receipt.entry.view.wrapsPrincipal = true)
    (originalForm : ∃ name, receipt.entry.view.reference.original.form =
      .reference name (.local receipt.entry.view.binding.binder.id)) :
    receipt.entry.view.selectedInstance = some read.candidate ∧
      read.binding.source = receipt.entry.view.binding.source ∧
      read.binding.binder = receipt.entry.view.binding.binder ∧
      read.binding.initializer = receipt.entry.view.binding.initializer ∧
      read.child = receipt.entry.view.ownSubstitution := by
  obtain ⟨selection⟩ := CallablePreparedViewSelection.at_receipt ancestry receipt generalized
  have keys : receipt.entry.view.owner = owner ∧ receipt.entry.view.read = id ∧
      receipt.entry.view.parentActive = active := by
    simpa only [View.key, decide_eq_true_eq, Prod.mk.injEq] using List.find?_some receipt.found
  have fields := lowered_fields accepted read.nodeFound
  obtain ⟨name, form⟩ := originalForm
  obtain ⟨actualName, actualForm⟩ := read.nodeForm
  have binderId : read.binder = receipt.entry.view.binding.binder.id := by
    have eq := actualForm.symm.trans (fields.1.trans form)
    exact Option.some.inj (congrArg (fun form =>
      match form with | .reference _ (.local binder) => some binder | _ => none) eq)
  have located : base.locals.binding receipt.entry.view.owner receipt.entry.view.binding.binder.id =
      .ok read.binding := by simpa only [keys.1, ← binderId] using read.bindingFound
  have sameBinding : selection.binding = read.binding := Except.ok.inj (selection.located.symm.trans located)
  have binder : read.binding.binder = receipt.entry.view.binding.binder := by
    rw [← sameBinding]; exact selection.binder
  have staticMatch := CallableAncestryProfiles.SourceComposition.witnesses_matched receipt.entry.view.exactFactory
  simp only [TypedBinder.applySubstitution, Principal.binder, Scheme.apply, CallableAncestryProfiles.SourceComposition.mask_twice] at staticMatch
  change SourceSpecialization.matchClosedSchemeInstance?
    (Scheme.apply receipt.entry.view.parentActive receipt.entry.view.binding.binder.scheme)
    receipt.entry.view.rawRead.rawType = some receipt.entry.view.ownSubstitution at staticMatch
  have actualMatch := read.matched
  rw [read.rawType, fields.2, binder] at actualMatch
  simp only [keys.2.2] at staticMatch
  have child : read.child = receipt.entry.view.ownSubstitution := Option.some.inj (actualMatch.symm.trans staticMatch)
  have candidateMember : read.candidate ∈ selection.binding.instances := by
    rw [sameBinding]
    exact (List.mem_filter.mp (List.mem_of_getElem? read.candidate_at)).1
  have cumulative : read.candidate.origin.substitution = receipt.entry.view.cumulative := by
    have cumulativeExact := receipt.entry.view.cumulativeExact
    change receipt.entry.view.cumulative = receipt.entry.view.ownSubstitution.compose
      receipt.entry.view.parentActive at cumulativeExact
    simp only [keys.2.2] at cumulativeExact
    exact read.candidate_key.trans (by simpa only [child] using cumulativeExact.symm)
  have sameCandidate := selection.same_candidate candidateMember cumulative
  refine ⟨?_, ?_, binder, ?_, child⟩
  · exact selection.selected.trans (congrArg some sameCandidate.symm)
  · rw [← sameBinding]; exact selection.source
  · rw [← sameBinding]; exact selection.initializer

/-- The real lowerRead and lowerWithReceipt select the same complete candidate.
The original local resolution and both matcher keys come from successful
compiler checks, without a binding or substitution equality premise. -/
theorem same_read {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : Key} {active : Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    {receipt : SourceCoreCallableViewLowering.Viewed ancestry.views owner active id lowered}
    (accepted : SourceCoreCallableViewLowering.lowerWithReceipt ancestry.views owner active source id lowered = .ok receipt)
    (read : GeneralizedLocalReadReceipts.Certificate base.locals owner active source scope id reason lowered)
    (generalized : receipt.entry.view.wrapsPrincipal = true) :
    receipt.entry.view.selectedInstance = some read.candidate ∧
      read.binding.source = receipt.entry.view.binding.source ∧
      read.binding.binder = receipt.entry.view.binding.binder ∧
      read.binding.initializer = receipt.entry.view.binding.initializer ∧
      read.child = receipt.entry.view.ownSubstitution := by
  exact same_selection ancestry accepted read generalized
    (SourceAuthenticatedReferenceForm.original_form receipt.entry.view.authenticatedReference)

structure WrappedRead {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    (owner : Key) (active : Substitution) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (original lowered : SourceCoreBasic.LoweredExpr)
    (candidate : SourceCoreLocalPolymorphism.Instance) where
  receipt : SourceCoreCallableViewLowering.Viewed ancestry.views owner active id original
  accepted : SourceCoreCallableViewLowering.lowerWithReceipt ancestry.views owner active source id original = .ok receipt
  generalized : receipt.entry.view.wrapsPrincipal = true
  selected : receipt.entry.view.selectedInstance = some candidate
  target : Core.Word
  origin : SourceCoreCallableIndexedAncestry.originId ancestry
    (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution) = .ok target
  parameter : Core.Ty
  result : Core.Ty
  carrier : original.type = .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word
  emitted : lowered = { original with expression :=
    (SourceCoreCallableIndexedAncestry.viewLower ancestry.layout.frame parameter result
      receipt.entry.id target (scope.length + 1 + base.globals.length) original.expression) }

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {result : α}
    (accepted : action.mapError f = .ok result) : action = .ok result := by
  cases action <;> cases accepted <;> rfl

/-- Actual indexed lowering either keeps the raw read or emits a wrapper for
exactly the complete candidate chosen by the same lowerRead certificate. -/
theorem lowerView_cases {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : Key} {active : Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {original lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreCallableIndexedAncestry.lowerView ancestry owner active source scope id original = .ok lowered)
    (read : GeneralizedLocalReadReceipts.Certificate base.locals owner active source scope id reason original) :
    lowered = original ∨ Nonempty (WrappedRead ancestry owner active source scope id original lowered read.candidate) := by
  unfold SourceCoreCallableIndexedAncestry.lowerView at accepted
  obtain ⟨receipt, prepared, accepted⟩ := bind_ok accepted
  have actual := mapError_ok prepared
  split at accepted
  · cases accepted
    exact .inl rfl
  · next wrapped =>
    have generalized : receipt.entry.view.wrapsPrincipal = true := by simpa using wrapped
    have chosen := (same_read ancestry actual read generalized).1
    rw [chosen] at accepted
    dsimp only [bind, Except.bind, pure, Except.pure] at accepted
    obtain ⟨target, origin, accepted⟩ := bind_ok accepted
    split at accepted
    · next parameter result carrier =>
      cases accepted
      exact .inr ⟨⟨receipt, actual, generalized, chosen, target, origin, parameter, result, carrier, rfl⟩⟩
    · cases accepted

end Solcore.SourceSemantics.CoreLowering.CallableViewReadSelection
