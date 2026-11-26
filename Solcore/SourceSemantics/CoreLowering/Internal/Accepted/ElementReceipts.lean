import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ElementWrites
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements

/-!
# Accepted writes to an element of a local array

The receipts the compiler leaves when it accepts `a[i] = v`, `a[i] op= v` or `a[i] ~=;` at one element of a
local array `a`, beside the projected ones: the accepted callback, its place lowering, the element write's
receipt (`CompatibleElementWrites.Generated`), and the index's and the right side's code. A place lowering that
writes one element is `lowerElements`'s (`CompatibleElementWrites.generated_of_place`). The continuation's
native typing follows from the whole write's (`CompatibleElementWrites.code_continuation`), and the write meets
the place-fault inventory's concrete gate (`CompatibleElementWrites.generated_concrete`). Main declarations:
`AcceptedElementAssignmentReceipt.Receipt`, `AcceptedElementAssignmentReceipt.of_accepted`,
`AcceptedElementBitNotReceipt.Receipt`, `AcceptedElementBitNotReceipt.of_accepted`,
`CompatibleElementWrites.code_continuation` and `CompatibleElementWrites.generated_concrete`.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open TypedLexicalWhile.Native (remove_front)

section Lowering
variable {context : SourceCoreCompatibleDataPlaces.Context} {signatures : ProgramSignatures}
  {expression : SourceCoreCompatibleDataPlaces.ExpressionLowerer} {fuel : Nat} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
  {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId} {outputType : Ty} {next : Expr}
  {reasonAt : ExpressionId → Word} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
  {key : ExpressionId} {lowered : Expr}

/-- A place that writes one element is lowered by `lowerElements`. -/
theorem elements_of_lower (single : assignment.target.projections = [.element key])
    (accepted : lower context signatures expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand missing = .ok lowered) :
    lowerElements context expression fuel source scope site assignment operator rhs outputType next reasonAt
      invalidProjection invalidOperand = .ok lowered := by
  have takes : takesElement assignment.target.projections = true := by rw [single]; rfl
  simpa only [lower, takes] using accepted

/-- The receipt of a place lowering that writes one element. -/
theorem generated_of_place (single : assignment.target.projections = [.element key])
    (accepted : lower context signatures expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand missing = .ok lowered) :
    Generated context expression fuel source scope site assignment operator rhs outputType next reasonAt
      invalidProjection invalidOperand key lowered :=
  generated_of_lower single (elements_of_lower single accepted)

/-- The place-fault inventory's concrete gate at an element write (`SourceCoreCompatibleDataPlaceFaultSites`
takes the write's site only when it holds): in a catalog of closed Source types, the root's projection and
the leaf's close the target's type and the declared root binder's, as `describe_concrete` has them for a
route. -/
theorem generated_concrete (closed : CompatibleCatalogRegistrationPrefix.ClosedSources context.checked.catalog)
    (generated : Generated context expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand key lowered) :
    (SourceCoreDataCatalog.closed assignment.target.type &&
      ((SourceCoreDataPlaces.declaredBinders source).filter (fun binder =>
        decide (binder.id = assignment.target.root))).any
          (fun binder => SourceCoreDataCatalog.closed binder.scheme.body)) = true := by
  cases generated with
  | intro binder _ _ _ _ _ _ _ rooted projected _ _ _ _ leaf _ _ =>
    have binding : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder := rooted
    have filtered := CompatibleMatchArmScopes.rootBinder_filter binding
    have targetClosed := CompatibleCatalogClosedSources.project_closed closed
      (CompatibleExpressionReads.projectType_of_accepted leaf)
    have rootClosed := CompatibleCatalogClosedSources.project_closed closed
      (CompatibleExpressionReads.projectType_of_accepted projected)
    rw [targetClosed, filtered]
    simp only [List.any_cons, List.any_nil, rootClosed, Bool.true_or, Bool.true_and]

end Lowering

/-- The modifier's check has the type of its write. -/
private theorem guard_typed {context : Core.Context} {outputType result : Ty}
    {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {write : Expr} {definitions : DataEnvironment}
    (typed : HasType context (Frontend.SourceCoreDataPlaces.guard outputType operator write) result definitions) :
    HasType context write result definitions := by
  rcases operator with _ | ⟨operation, _ | _ | ⟨type, binary⟩⟩
  · exact typed
  · exact typed
  · cases typed with
    | ifE _ _ written => exact written
  · cases division : SourceCorePrimitive.checkedDivision binary
    · rw [SourceCoreDataPlaces.guard_range_plain division] at typed
      cases typed with
      | ifE _ _ written => exact written
    · rw [SourceCoreDataPlaces.guard_range_division division] at typed
      cases typed with
      | ifE _ _ rest =>
        cases rest with
        | ifE _ _ written => exact written

/-- The continuation of a write to one element is typed as the whole write is: `next` runs under the
write's binders, five for a plain write and eight for a compound one or an in-place `~`, which it does not
name. -/
theorem code_continuation {slot : Nat} {storedType outputType : Ty} {invalid : Word}
    {comparison value next : Expr} {modifier : Option ElementModifier} {layout : OrderedMapping.Layout}
    {index : Expr} {definitions : DataEnvironment} {context : Core.Context} {result : Ty}
    (typed : HasType context (code slot storedType outputType invalid comparison value next modifier layout index)
      result definitions) :
    HasType context next result definitions := by
  rcases modifier with _ | modifier
  · cases typed with
    | caseE _ _ indexed =>
      cases indexed with
      | caseE _ _ checked =>
        cases checked with
        | ifE _ stored _ =>
          cases stored with
          | caseE _ _ inserted =>
            cases inserted with
            | caseE _ _ written =>
              cases written with
              | letE _ body => exact remove_front (remove_front (remove_front (remove_front (remove_front body))))
  · cases typed with
    | caseE _ _ indexed =>
      cases indexed with
      | caseE _ _ checked =>
        cases checked with
        | ifE _ stored _ =>
          cases stored with
          | caseE _ _ snapshot =>
            cases snapshot with
            | caseE _ _ right =>
              cases right with
              | caseE _ _ changed =>
                cases changed with
                | caseE _ _ inserted =>
                  cases inserted with
                  | caseE _ _ guarded =>
                    cases guard_typed guarded with
                    | letE _ body =>
                      exact remove_front (remove_front (remove_front (remove_front
                        (remove_front (remove_front (remove_front (remove_front body)))))))

end Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites

namespace Solcore.SourceSemantics.CoreLowering.AcceptedElementAssignmentReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces
open CompatibleAssignmentStatements (AssignmentPolicy)

/-- An accepted value assignment to one element of a local array, `a[i] = v` or `a[i] op= v`: the
authenticated callback and its place lowering, as a projected write's, with the element write's receipt and
the compiler's own code of the index and the right side. -/
structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (output : Ty) (next : Expr) (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : AssignmentPolicy policy values invalidProjection invalidOperand missing
  sourceProfile : (operator = .equal ∨ assignment.target.type = .word) ∨
    FixedCompoundAssignment operator assignment.target.type
  accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
    output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment operator (some rhs) output next reasonAt
    (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
    (missing site assignment.target.root) = .ok code
  /-- The element's index. -/
  key : ExpressionId
  single : assignment.target.projections = [.element key]
  generated : CompatibleElementWrites.Generated values policy.lowerExpression fuel source scope site assignment
    operator (some rhs) output next reasonAt (invalidProjection site assignment.target.root)
    (invalidOperand site assignment.target.root operator) key code
  /-- The index's code, as the compiler lowered it. -/
  keyCode : SourceCoreBasic.LoweredExpr
  keyGenerated : policy.lowerExpression fuel source scope key reasonAt = .ok keyCode
  /-- The right side's code, as the compiler lowered it. -/
  child : SourceCoreBasic.LoweredExpr
  rhsGenerated : policy.lowerExpression fuel source scope rhs reasonAt = .ok child

/-- The accepted callback of a value assignment at one element supplies its place lowering, the element
write's receipt and the children's code. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {values : SourceCoreCompatibleValues.Context}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs key : ExpressionId}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    (matched : AssignmentPolicy policy values invalidProjection invalidOperand missing)
    (sourceProfile : (operator = .equal ∨ assignment.target.type = .word) ∨
      FixedCompoundAssignment operator assignment.target.type)
    (single : assignment.target.projections = [.element key])
    (accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
      output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment operator rhs output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment operator (some rhs) output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
      (missing site assignment.target.root) = .ok code := by
    cases operator <;> simpa only [SourceCoreLoops.assignValue, matched.equal, matched.value] using accepted
  have generated := CompatibleElementWrites.generated_of_place single lowered
  have pieces := generated
  cases pieces with
  | intro _ _ _ keyCode _ _ _ _ _ _ _ _ keyGenerated _ _ _ rhsGenerated =>
    cases rhsGenerated with
    | @present _ child childGenerated _ =>
      exact ⟨⟨values, invalidProjection, invalidOperand, missing, matched, sourceProfile, accepted, lowered,
        key, single, generated, keyCode, keyGenerated, child, childGenerated⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedElementAssignmentReceipt

namespace Solcore.SourceSemantics.CoreLowering.AcceptedElementBitNotReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces

/-- An accepted in-place `~` at one element of a local array, `a[i] ~=;`: the actual absent-operand
callback and its place lowering, as a projected update's, with the element write's receipt and the
compiler's own code of the index. -/
structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution)
    (output : Ty) (next : Expr) (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing
  sourceProfile : assignment.target.type = .word ∨ ∃ type, assignment.target.type = .fixed type
  callback : ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
    SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
    (ExpressionId → Word) → Except SourceCoreBasic.Error Expr
  callbackSelected : policy.assignBitNotWithExpression = some callback
  accepted : callback policy.lowerExpression fuel source scope site assignment output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment .equal none output next reasonAt
    (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
    (missing site assignment.target.root) = .ok code
  /-- The element's index. -/
  key : ExpressionId
  single : assignment.target.projections = [.element key]
  generated : CompatibleElementWrites.Generated values policy.lowerExpression fuel source scope site assignment
    .equal none output next reasonAt (invalidProjection site assignment.target.root)
    (invalidUnary site assignment.target.root) key code
  /-- The index's code, as the compiler lowered it. -/
  keyCode : SourceCoreBasic.LoweredExpr
  keyGenerated : policy.lowerExpression fuel source scope key reasonAt = .ok keyCode

/-- The accepted absent-operand callback at one element supplies its place lowering, the element write's
receipt and the index's code. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {values : SourceCoreCompatibleValues.Context}
    {invalidProjection invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {key : ExpressionId}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    {callback : ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
      SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
      (ExpressionId → Word) → Except SourceCoreBasic.Error Expr}
    (matched : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing)
    (sourceProfile : assignment.target.type = .word ∨ ∃ type, assignment.target.type = .fixed type)
    (single : assignment.target.projections = [.element key])
    (callbackSelected : policy.assignBitNotWithExpression = some callback)
    (accepted : callback policy.lowerExpression fuel source scope site assignment output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment .equal none output next reasonAt
      (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
      (missing site assignment.target.root) = .ok code := by
    have same := Option.some.inj (callbackSelected.symm.trans matched)
    simpa only [same] using accepted
  have generated := CompatibleElementWrites.generated_of_place single lowered
  have pieces := generated
  cases pieces with
  | intro _ _ _ keyCode _ _ _ _ _ _ _ _ keyGenerated _ _ _ _ =>
    exact ⟨⟨values, invalidProjection, invalidUnary, missing, matched, sourceProfile, callback, callbackSelected,
      accepted, lowered, key, single, generated, keyCode, keyGenerated⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedElementBitNotReceipt
