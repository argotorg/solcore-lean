import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ElementReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementWrites
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementBitNot

/-!
# Accepted bodies: the heads of writes to an element of a local array

The accepted receipts of `a[i] = v`, `a[i] op= v` and `a[i] ~=;` at one element of a local array supply the
heads the element write theorems take (`CellAwareElementWriteHeads.Head` and `BitNotHead`). The compiler's
own lowering of the index and the right side is the heads' children, checker typing at an element place gives
the root's writability at the array of the target's type and the index's and the right side's nodes, and the
diagnostic words come from the body's own fault tables. The fault inventory's concrete gate
(`CompatiblePlaceMissingPreparationCoverage.concrete`) holds at the write, from the element write's receipt
at the initial context, whose catalog's sources are closed. Main declarations:
`CellAwareInvocationAcceptedElementWrites.element_head` and `element_bitNot_head`.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedElementWrites
open Core Frontend SourceInference

section Facts
variable {source : TypedSource} {context : SourceSemantics.Context}

/-- Checker typing of a place that writes one element: its root is a writable local at the array of the
place's type, and its index is typed. -/
theorem element_place {place : PlaceResolution} {type : TypeSystem.Ty} {key : ExpressionId}
    (single : place.projections = [.element key]) (typed : SourcePlaceHasType source context place type) :
    WritableLocal context place.root (TypeSystem.Ty.array place.type) ∧
      ∃ indexType, ExpressionHasType source context key indexType := by
  cases typed with
  | intro writable projections stored =>
    rw [single] at projections
    cases projections with
    | element indexTyped rest =>
      cases rest
      rw [stored]
      exact ⟨writable, _, indexTyped⟩

/-- Checker typing of `a[i] = v` or `a[i] op= v` at one element: the writable root at the array of the
target's type, the index's typing, the right side's at a type that stands for the target's, and the
assignment's wide profile, as `ScopedSourceForItemsAdmission.assignment_facts` gives them at a bare target. -/
theorem element_assignment_facts {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    {rhs key : ExpressionId} (single : assignment.target.projections = [.element key])
    (typed : SourceAssignmentHasType source context assignment operator rhs) :
    WritableLocal context assignment.target.root (TypeSystem.Ty.array assignment.target.type) ∧
      (∃ indexType, ExpressionHasType source context key indexType) ∧
      AssignedOperandTyped source context operator rhs assignment.target.type ∧
      WideAssignmentProfile operator assignment.target.type := by
  have original : ∃ type, SourcePlaceHasType source context assignment.target type ∧
      AssignedOperandTyped source context operator rhs type ∧
      ((operator = .equal ∨ type = .word) ∨ FixedCompoundAssignment operator type) := by
    cases typed with
    | equal place value _ => exact ⟨_, place, .of_type value, .inl (.inl rfl)⟩
    | wordCompound _ place value _ => exact ⟨_, place, .of_type value, .inl (.inr rfl)⟩
    | fixedCompound kind place value _ => exact ⟨_, place, .of_type value, .inr ⟨⟨_, rfl⟩, .inl kind⟩⟩
    | shiftCompound kind place targetKind value amount _ =>
      -- A shift's amount keeps its own type, at a Word target and at a fixed-width one.
      cases targetKind with
      | word => exact ⟨_, place, ⟨_, value, .shiftAmount kind rfl amount⟩, .inl (.inr rfl)⟩
      | fixed type =>
        exact ⟨_, place, ⟨_, value, .fixedShiftAmount kind rfl amount⟩, .inr ⟨⟨_, rfl⟩, .inr kind⟩⟩
  obtain ⟨type, place, value, profile⟩ := original
  have target := place.type_eq
  obtain ⟨writable, indexTyped⟩ := element_place single place
  refine ⟨writable, indexTyped, target.symm ▸ value, ?_⟩
  rcases profile with (equal | word) | fixed
  · exact .inl (.inl equal)
  · exact .inl (.inr (.inl (by rw [target, word]; rfl)))
  · exact .inr (by rw [target]; exact fixed)

/-- Checker validity of `a[i] ~=;` at one element: the writable root at the array of the target's type and
the index's typing. -/
theorem element_bitNot_facts {assignment : AssignmentResolution} {key : ExpressionId}
    (single : assignment.target.projections = [.element key])
    (typed : SourceBitNotAssignmentValid source context assignment) :
    WritableLocal context assignment.target.root (TypeSystem.Ty.array assignment.target.type) ∧
      ∃ indexType, ExpressionHasType source context key indexType := by
  cases typed with
  | intro place _ _ => exact element_place single place

/-- Expression typing locates the expression's node. -/
private theorem expression_found (unique : NodeOccurrencesUnique source) {id : ExpressionId}
    {type : TypeSystem.Ty} (typed : ExpressionHasType source context id type) :
    ∃ node, source.lookupExpression? id = some node := by
  obtain ⟨node, contains, _⟩ := typed.stored_type
  exact ⟨node, lookupExpression?_complete unique contains⟩

end Facts

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}

/-- The accepted receipt of a value assignment at one element supplies its head: the element write's receipt
at the body's own place lowering (`Index.assignment_lowered`) gives the root's slot, the comparison, the
leaf and the children, whose certificate is the compiler's own lowering; checker typing gives the root's
writability, the index's and the right side's nodes, the right side's view and the profile. The head's code
is the compiler's, its words are this body's, and the write meets the fault inventory's concrete gate, from
that receipt in the compiled catalog's closed sources. -/
theorem element_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target) (unique : NodeOccurrencesUnique target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr}
    (receipt : AcceptedElementAssignmentReceipt.Receipt index.policy fuel index.compilerSource scope site
      assignment operator rhs output next index.reasonAt code)
    {context : SourceSemantics.Context} (typed : SourceAssignmentHasType target context assignment operator rhs) :
    ∃ head : CellAwareElementWriteHeads.Head (.initial compiled.compatible.checked) target context
        (fun scope expression lowered => index.policy.lowerExpression fuel index.compilerSource scope expression
          index.reasonAt = .ok lowered) scope assignment operator rhs,
      code = head.emit next output ∧ head.invalidProjection = index.invalidProjection site assignment.target.root ∧
        head.invalid = index.invalidOperand site assignment.target.root operator ∧
        CompatiblePlaceMissingPreparationCoverage.concrete target assignment = true := by
  subst target
  obtain ⟨key, single⟩ : ∃ key, assignment.target.projections = [.element key] := ⟨_, receipt.single⟩
  have generated := CompatibleElementWrites.generated_of_place single (index.assignment_lowered receipt.accepted)
  have gate := CompatibleElementWrites.generated_concrete
    (CallableIndexedOwnedPublicCatalogClosedSources.compiled_closed compiled) generated
  obtain ⟨writable, ⟨_, keyTyped⟩, rightTyped, profile⟩ := element_assignment_facts single typed
  obtain ⟨keyNode, keyFound⟩ := expression_found unique keyTyped
  obtain ⟨_, rhsTyped, _⟩ := id rightTyped
  obtain ⟨node, found⟩ := expression_found unique rhsTyped
  cases generated with
  | intro _ slot comparison keyCode elementType identity _ _ _ _ lookup preparedBy keyGenerated keyType leaf _
      rhsGenerated =>
    cases rhsGenerated with
    | @present _ child childGenerated childType =>
      exact ⟨⟨key, single, slot, elementType, identity, lookup, writable, fuel, comparison, preparedBy, site, leaf,
        keyNode, keyFound, keyCode, keyGenerated, keyType, node, found, child, childGenerated, childType.symm,
        rightTyped.view unique found, profile, index.invalidProjection site assignment.target.root,
        index.invalidOperand site assignment.target.root operator⟩, rfl, rfl, rfl, gate⟩

/-- The accepted receipt of an in-place `~` at one element supplies its head: the element write's receipt at
the body's own absent-operand place lowering (`Index.bitNot_lowered`) gives the root's slot, the comparison,
the leaf and the index's code, checker validity gives the root's writability and the index's node, and the
receipt's Word or fixed-width target gives in-place `~`'s profile. The head's code is the compiler's, its
words are this body's, and the write meets the fault inventory's concrete gate, as `element_head`'s does. -/
theorem element_bitNot_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target) (unique : NodeOccurrencesUnique target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {output : Ty} {next code : Expr}
    (receipt : AcceptedElementBitNotReceipt.Receipt index.policy fuel index.compilerSource scope site assignment
      output next index.reasonAt code)
    {context : SourceSemantics.Context} (typed : SourceBitNotAssignmentValid target context assignment) :
    ∃ head : CellAwareElementWriteHeads.BitNotHead (.initial compiled.compatible.checked) target context
        (fun scope expression lowered => index.policy.lowerExpression fuel index.compilerSource scope expression
          index.reasonAt = .ok lowered) scope assignment,
      code = head.emit next output ∧ head.invalidProjection = index.invalidProjection site assignment.target.root ∧
        head.invalid = index.invalidUnary site assignment.target.root ∧
        CompatiblePlaceMissingPreparationCoverage.concrete target assignment = true := by
  subst target
  obtain ⟨key, single⟩ : ∃ key, assignment.target.projections = [.element key] := ⟨_, receipt.single⟩
  have generated := CompatibleElementWrites.generated_of_place single
    (index.bitNot_lowered receipt.callbackSelected receipt.accepted)
  have gate := CompatibleElementWrites.generated_concrete
    (CallableIndexedOwnedPublicCatalogClosedSources.compiled_closed compiled) generated
  have profile := WideBitNotProfile.of_word_or_fixed receipt.sourceProfile
  obtain ⟨writable, _, keyTyped⟩ := element_bitNot_facts single typed
  obtain ⟨keyNode, keyFound⟩ := expression_found unique keyTyped
  cases generated with
  | intro _ slot comparison keyCode elementType identity _ _ _ _ lookup preparedBy keyGenerated keyType leaf _
      rhsGenerated =>
    cases rhsGenerated with
    | absent =>
      exact ⟨⟨key, single, slot, elementType, identity, lookup, writable, fuel, comparison, preparedBy, site, leaf,
        keyNode, keyFound, keyCode, keyGenerated, keyType, profile, index.invalidProjection site assignment.target.root,
        index.invalidUnary site assignment.target.root⟩, rfl, rfl, rfl, gate⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedElementWrites
