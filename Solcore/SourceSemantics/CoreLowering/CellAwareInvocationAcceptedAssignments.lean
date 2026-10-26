import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAssignmentPolicy
import Solcore.SourceSemantics.CoreLowering.AcceptedBareAssignmentReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedProjectedBitNotReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTerminals
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts

/-! The accepted bare-assignment and bit-not receipts of an actual body supply
the flow heads used by the mixed-cell write theorems. A right-hand side
certificate is the compiler's own child lowering; checker typing supplies
writability, and diagnostic words come from the body's own fault tables. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedAssignments
open Core Frontend SourceInference
open CellAwareInvocationAcceptedTerminals (children)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}

/-- The head is stated over any Source equal to the compiler's view, so it
can be used directly at the invocation's own Source. -/
theorem bare_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target) (unique : NodeOccurrencesUnique target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr}
    (receipt : AcceptedBareAssignmentReceipt.Receipt index.policy fuel index.compilerSource scope site assignment
      operator rhs output next index.reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    {context : SourceSemantics.Context} (typed : SourceAssignmentHasType target context assignment operator rhs)
    (administrative : Core.Context) :
    ∃ head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) target context
        (children index fuel) scope administrative compiled.indexed.layouts.definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = index.invalidOperand site assignment.target.root operator := by
  subst target
  have lowered := index.assignment_lowered receipt.accepted
  obtain ⟨_, writable, rightTyped, profile⟩ :=
    ScopedSourceForItemsAdmission.assignment_facts receipt.declaration targetType receipt.bare typed
  obtain ⟨node, found, _, _⟩ := CellAwareInvocationAcceptedSourceFacts.expression_node unique rightTyped
  exact GenericAssignmentStatements.Head.of_lower_bare_with_token receipt.bare unique writable rightTyped profile
    (fun _ generated => ⟨node, found, generated⟩) lowered

/-- Checker validity of a bare bit-not target gives its writable declaration
and Word representation. -/
theorem bitNot_facts {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {binder : TypedBinder}
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (targetType : binder.scheme.body = assignment.target.type)
    (bare : assignment.target.projections = [])
    (typed : SourceBitNotAssignmentValid source context assignment) :
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      WritableLocal context assignment.target.root actual.scheme.body) ∧
    (SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer) := by
  cases typed with
  | intro place _ =>
  cases place with
  | intro writable projections target =>
    refine ⟨?_, .inl (by rw [target]; rfl)⟩
    intro actual actualFound
    cases Except.ok.inj (declaration.symm.trans actualFound)
    rw [bare] at projections
    cases projections
    exact targetType.symm ▸ target.symm ▸ writable

/-- The accepted bare bit-not receipt supplies the unary flow head and its
diagnostic word from this body's own fault table. -/
theorem bitNot_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {output : Ty} {next code : Expr}
    (receipt : AcceptedBareBitNotReceipt.Receipt index.policy fuel index.compilerSource scope site assignment
      output next index.reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    {context : SourceSemantics.Context} (typed : SourceBitNotAssignmentValid target context assignment) :
    ∃ head : CompatibleBitNotStatements.Head context scope assignment,
      code = head.emit next output ∧ head.invalid = index.invalidUnary site assignment.target.root := by
  subst target
  have lowered := index.bitNot_lowered receipt.selected receipt.accepted
  obtain ⟨writable, profile⟩ := bitNot_facts receipt.declaration targetType receipt.bare typed
  exact CompatibleBitNotStatements.Head.of_lower_with_token writable receipt.bare profile lowered

/-- A projected write's head retains the compiler's ordered key and right-hand
actions, its native typing and the prepared place used by reached diagnostics. -/
theorem projected_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target) (unique : NodeOccurrencesUnique target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr}
    (receipt : AcceptedProjectedAssignmentReceipt.Receipt index.policy fuel index.compilerSource scope site
      assignment operator rhs output next index.reasonAt code)
    (route : AcceptedProjectedAssignmentRoute.Route index.compilerSource receipt.binder.scheme.body
      assignment.target.projections assignment.target.type)
    {context : SourceSemantics.Context} (signatures : context.signatures = compiled.compatible.checked.signatures)
    (typed : SourceAssignmentHasType target context assignment operator rhs)
    (administrative : Core.Context) {result : Ty}
    (native : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result
      compiled.indexed.layouts.definitions) :
    ∃ head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) target context
        (children index fuel) scope administrative compiled.indexed.layouts.definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = index.invalidOperand site assignment.target.root operator ∧
      head.PreparedAt site fuel (index.invalidProjection site assignment.target.root)
        (index.missingDefault site assignment.target.root) := by
  subst target
  have lowered := index.assignment_lowered receipt.accepted
  obtain ⟨sourceTyped, writable, rightTyped, profile⟩ :=
    ScopedSourceForItemsAdmission.projected_assignment_facts unique receipt.description.binding route typed
  exact CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
    unique signatures sourceTyped writable rightTyped profile
    (fun id _ member generated _ => by
      rcases List.mem_cons.mp member with same | member
      · subst id
        obtain ⟨node, found, _, _⟩ := CellAwareInvocationAcceptedSourceFacts.expression_node unique rightTyped
        exact ⟨node, found, generated⟩
      · obtain ⟨node, found, _⟩ := route.key_typed unique (sourceTyped _ receipt.description.binding) member
        exact ⟨node, found, generated⟩) lowered native

theorem bitNot_word {source : TypedSource} {context : SourceSemantics.Context} {assignment : AssignmentResolution}
    (typed : SourceBitNotAssignmentValid source context assignment) :
    SourceCoreRawMetadata.runtimeType assignment.target.type = .word := by
  cases typed with
  | intro place _ =>
  cases place with
  | intro _ _ target =>
    rw [target]
    rfl

/-- The projected unary head keeps the absent operand literal; only ordered
keys are compiler children, each certified by its own accepted lowering. -/
theorem projected_bitNot_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target) (unique : NodeOccurrencesUnique target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {output : Ty} {next code : Expr}
    (receipt : AcceptedProjectedBitNotReceipt.Receipt index.policy fuel index.compilerSource scope site
      assignment output next index.reasonAt code)
    (route : AcceptedProjectedAssignmentRoute.Route index.compilerSource receipt.binder.scheme.body
      assignment.target.projections assignment.target.type)
    {context : SourceSemantics.Context} (signatures : context.signatures = compiled.compatible.checked.signatures)
    (typed : SourceBitNotAssignmentValid target context assignment)
    (administrative : Core.Context) {result : Ty}
    (native : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result
      compiled.indexed.layouts.definitions) :
    ∃ head : CompatibleProjectedBitNotStatements.Head (.initial compiled.compatible.checked) target context
        (children index fuel) scope administrative compiled.indexed.layouts.definitions assignment,
      code = head.emit next output ∧ head.invalid = index.invalidUnary site assignment.target.root ∧
      head.PreparedAt site fuel (index.invalidProjection site assignment.target.root)
        (index.missingDefault site assignment.target.root) := by
  subst target
  have lowered := index.bitNot_lowered receipt.callbackSelected receipt.accepted
  obtain ⟨sourceTyped, writable⟩ :=
    ScopedSourceForItemsAdmission.projected_bitNot_facts unique receipt.description.binding route typed
  exact CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors.Head.of_lower_with_raw_occurrences
    unique signatures sourceTyped writable receipt.projected (.inl (bitNot_word typed))
    (fun id _ member generated _ => by
      obtain ⟨node, found, _⟩ := route.key_typed unique (sourceTyped _ receipt.description.binding) member
      exact ⟨node, found, generated⟩) lowered native

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedAssignments
