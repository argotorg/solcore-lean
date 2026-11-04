import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementCertificates
import Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentRoute
import Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchAmbientLowering
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler

/-!
# Accepted compiler trees

The receipts the compiler leaves when it accepts a named body. The accepted-body
theorems are stated over these trees: they induct on what the compiler did, not on a
Source recognizer.

Main declarations:
- `AcceptedNamedBodyFlow.Tree` and `AcceptedNamedBodyFlow.Items`, the statement trees;
- `AcceptedNamedBodyFlow.Body`, one accepted body, and `AcceptedNamedBodyFlow.Incomplete`;
- `AcceptedNamedMatchFlow.Receipt`, one accepted match;
- `AcceptedBareAssignmentReceipt.Receipt`, `AcceptedProjectedAssignmentReceipt.Receipt`,
  `AcceptedBareBitNotReceipt.Receipt` and `AcceptedProjectedBitNotReceipt.Receipt`,
  the write heads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedBareAssignmentReceipt
/-! A bare value assignment follows the authenticated compatible callback.
Its actual right-hand action, original binder and emitted place code remain
attached to the same accepted flow action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedBareAssignmentReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces
open CompatibleAssignmentStatements (AssignmentPolicy)

structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (output : Ty) (next : Expr)
    (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : AssignmentPolicy policy values invalidProjection invalidOperand missing
  sourceProfile : operator = .equal ∨ assignment.target.type = .word
  bare : assignment.target.projections = []
  accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
    output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment operator (some rhs) output next reasonAt
    (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
    (missing site assignment.target.root) = .ok code
  binder : TypedBinder
  declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder
  place : SourceCoreCompatibleDataPlaces.Prepared
  index : Nat
  child : SourceCoreBasic.LoweredExpr
  rootType : place.route.rootSourceType = binder.scheme.body
  rawType : SourceCoreRawMetadata.runtimeType place.route.rootSourceType =
    SourceCoreRawMetadata.runtimeType assignment.target.type
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, place.route.rootType)
  layout : CompatibleBareAssignment.Layout values place
  generated : policy.lowerExpression fuel source scope rhs reasonAt = .ok child
  childType : child.type = place.route.leafType
  operatorType : operator = .equal ∨ place.route.leafType = .word ∨ place.route.leafType = .integer ∧ operator.wordOnly = false
  emitted : code = execute place (.var index) (SourceCoreCalls.packArguments []) child.expression
    next output (binaryOperator (place.route.leafType = .integer) operator) false
    (invalidOperand site assignment.target.root operator)

/-- Callback equality comes from the compiler policy, before its accepted
action is inverted. No right-hand syntax or execution law is an input. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {values : SourceCoreCompatibleValues.Context}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    (matched : AssignmentPolicy policy values invalidProjection invalidOperand missing)
    (sourceProfile : operator = .equal ∨ assignment.target.type = .word)
    (bare : assignment.target.projections = [])
    (accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
      output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment operator rhs output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment operator (some rhs) output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
      (missing site assignment.target.root) = .ok code := by
    cases operator <;> simpa only [SourceCoreLoops.assignValue, matched.equal, matched.value] using accepted
  obtain ⟨binder, place, index, child, declaration, rootType, rawType, slot, layout,
      generated, childType, operatorType, emitted⟩ := CompatibleBareAssignment.of_lower bare lowered
  exact ⟨⟨values, invalidProjection, invalidOperand, missing, matched, sourceProfile, bare, accepted, lowered,
    binder, declaration, place, index, child, rootType, rawType, slot, layout, generated,
    childType, operatorType, emitted⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedBareAssignmentReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentReceipt
/-! A projected value assignment retains the actual place preparation and
ordered key actions. Its declared root and selected leaf remain distinct;
the receipt does not assume execution of a key, getter or right-hand action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces
open CompatibleAssignmentStatements (AssignmentPolicy)
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute

structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (output : Ty) (next : Expr) (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : AssignmentPolicy policy values invalidProjection invalidOperand missing
  sourceProfile : operator = .equal ∨ assignment.target.type = .word
  projected : assignment.target.projections ≠ []
  accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
    output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment operator (some rhs) output next reasonAt
    (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
    (missing site assignment.target.root) = .ok code
  route : Route
  binder : TypedBinder
  selected : TypeSystem.Ty
  description : CompatiblePlaceDescription.Description values source site assignment route binder selected
  place : Prepared
  prepared : prepare values fuel route (invalidProjection site assignment.target.root)
    (missing site assignment.target.root) = .ok place
  routeType : place.route = route
  path : PreparedPath values.checked source site binder.scheme.body assignment.target.projections
    0 place.steps place.keys selected
  index : Nat
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, route.rootType)
  keys : List SourceCoreBasic.LoweredExpr
  keysGenerated : ListRel (KeyGenerated policy.lowerExpression fuel source scope reasonAt) place.keys keys
  keyIds : place.keys.map Prod.fst = DataPlaceKeyOrder.sourceKeys assignment.target.projections
  child : SourceCoreBasic.LoweredExpr
  generated : policy.lowerExpression fuel source scope rhs reasonAt = .ok child
  childType : child.type = place.route.leafType
  operatorType : operator = .equal ∨ place.route.leafType = .word ∨ place.route.leafType = .integer ∧ operator.wordOnly = false
  emitted : code = execute place (.var index) (SourceCoreCalls.packArguments keys) child.expression
    next output (binaryOperator (place.route.leafType = .integer) operator) false
    (invalidOperand site assignment.target.root operator)

/-- The same successful compiler callback supplies its original route,
ordered keys and RHS. Repeated key occurrences remain repeated actions. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {values : SourceCoreCompatibleValues.Context}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    (matched : AssignmentPolicy policy values invalidProjection invalidOperand missing)
    (sourceProfile : operator = .equal ∨ assignment.target.type = .word)
    (projected : assignment.target.projections ≠ [])
    (accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
      output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment operator rhs output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment operator (some rhs) output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
      (missing site assignment.target.root) = .ok code := by
    cases operator <;> simpa only [SourceCoreLoops.assignValue, matched.equal, matched.value] using accepted
  cases CompatiblePlaceCompilerCertificates.generated_of_lower lowered with
  | intro route place index keys value described slot prepared keysGenerated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | @present id child generated childType =>
      obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeType, _, path⟩ := description.prepared prepared
      have operatorType : operator = .equal ∨ place.route.leafType = .word ∨ place.route.leafType = .integer ∧ operator.wordOnly = false := by
        rw [routeType]
        rcases operatorValid with equal | word | integer
        · exact .inl equal.1
        · exact .inr (.inl word)
        · exact .inr (.inr integer)
      refine ⟨⟨values, invalidProjection, invalidOperand, missing, matched, sourceProfile,
        projected, accepted, lowered, route, binder, selected, description, place, prepared,
        routeType, path, index, slot, keys, keysGenerated,
        CompatiblePlaceCompilerCertificates.PreparedPath.key_ids path,
        child, generated, ?_, operatorType, ?_⟩⟩
      · simpa only [routeType] using childType.symm
      · simp only [routeType, Option.isNone_some]

end Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
/-! The actual absent-RHS callback retains the original bare Word target and
complete emitted update. It contributes no expression child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces

structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (output : Ty) (next : Expr)
    (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing
  sourceProfile : assignment.target.type = .word
  bare : assignment.target.projections = []
  callback : ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
    SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
    (ExpressionId → Word) → Except SourceCoreBasic.Error Expr
  selected : policy.assignBitNotWithExpression = some callback
  accepted : callback policy.lowerExpression fuel source scope site assignment
    output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment .equal none output next reasonAt
    (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
    (missing site assignment.target.root) = .ok code
  binder : TypedBinder
  declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder
  place : SourceCoreCompatibleDataPlaces.Prepared
  index : Nat
  rootType : place.route.rootSourceType = binder.scheme.body
  rawType : SourceCoreRawMetadata.runtimeType place.route.rootSourceType =
    SourceCoreRawMetadata.runtimeType assignment.target.type
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, place.route.rootType)
  layout : CompatibleBareBitNotCertificates.Layout place
  emitted : code = execute place (.var index) (SourceCoreCalls.packArguments [])
    (LanguageResult.success .unit) next output
    (binaryOperator (place.route.leafType = .integer) .equal) true
    (invalidUnary site assignment.target.root)

/-- The callback and accepted action determine the original layout and token.
Raw Word eligibility is retained separately from the native numeric view. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {values : SourceCoreCompatibleValues.Context}
    {invalidProjection invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    {callback : ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
      SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
      (ExpressionId → Word) → Except SourceCoreBasic.Error Expr}
    (matched : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing)
    (sourceProfile : assignment.target.type = .word)
    (bare : assignment.target.projections = [])
    (selected : policy.assignBitNotWithExpression = some callback)
    (accepted : callback policy.lowerExpression fuel source scope site assignment
      output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment .equal none output next reasonAt
      (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
      (missing site assignment.target.root) = .ok code := by
    have same := Option.some.inj (selected.symm.trans matched)
    simpa only [same] using accepted
  have numeric : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer :=
    .inl (by rw [sourceProfile]; rfl)
  obtain ⟨binder, place, index, declaration, rootType, rawType, slot, layout, emitted⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare numeric lowered
  exact ⟨⟨values, invalidProjection, invalidUnary, missing, matched, sourceProfile, bare,
    callback, selected, accepted, lowered, binder, declaration, place, index, rootType, rawType,
    slot, layout, emitted⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedProjectedBitNotReceipt
/-! A projected unary update retains its actual absent-RHS callback and
ordered key actions. The administrative Unit is not a Source expression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProjectedBitNotReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute

structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution)
    (output : Ty) (next : Expr) (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing
  sourceProfile : assignment.target.type = .word
  projected : assignment.target.projections ≠ []
  callback : ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
    SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
    (ExpressionId → Word) → Except SourceCoreBasic.Error Expr
  callbackSelected : policy.assignBitNotWithExpression = some callback
  accepted : callback policy.lowerExpression fuel source scope site assignment output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment .equal none output next reasonAt
    (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
    (missing site assignment.target.root) = .ok code
  route : Route
  binder : TypedBinder
  selected : TypeSystem.Ty
  description : CompatiblePlaceDescription.Description values source site assignment route binder selected
  place : Prepared
  prepared : prepare values fuel route (invalidProjection site assignment.target.root)
    (missing site assignment.target.root) = .ok place
  routeType : place.route = route
  path : PreparedPath values.checked source site binder.scheme.body assignment.target.projections
    0 place.steps place.keys selected
  index : Nat
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, route.rootType)
  keys : List SourceCoreBasic.LoweredExpr
  keysGenerated : ListRel (KeyGenerated policy.lowerExpression fuel source scope reasonAt) place.keys keys
  keyIds : place.keys.map Prod.fst = DataPlaceKeyOrder.sourceKeys assignment.target.projections
  leafType : place.route.leafType = .word ∨ place.route.leafType = .integer
  emitted : code = execute place (.var index) (SourceCoreCalls.packArguments keys) (LanguageResult.success .unit)
    next output (binaryOperator (place.route.leafType = .integer) .equal) true
    (invalidUnary site assignment.target.root)

/-- The accepted callback supplies the actual keys, route and unary token. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {values : SourceCoreCompatibleValues.Context}
    {invalidProjection invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    {callback : ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
      SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
      (ExpressionId → Word) → Except SourceCoreBasic.Error Expr}
    (matched : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing)
    (sourceProfile : assignment.target.type = .word)
    (projected : assignment.target.projections ≠ [])
    (callbackSelected : policy.assignBitNotWithExpression = some callback)
    (accepted : callback policy.lowerExpression fuel source scope site assignment output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment .equal none output next reasonAt
      (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
      (missing site assignment.target.root) = .ok code := by
    have same := Option.some.inj (callbackSelected.symm.trans matched)
    simpa only [same] using accepted
  cases CompatiblePlaceCompilerCertificates.generated_of_lower lowered with
  | intro route place index keys value described slot prepared keysGenerated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | absent =>
      obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeType, _, path⟩ := description.prepared prepared
      have leafType : place.route.leafType = .word ∨ place.route.leafType = .integer := by
        simpa only [Option.isNone_none, Bool.true_eq_false, and_false, false_or, routeType] using
          operatorValid.imp_right (Or.imp_right And.left)
      refine ⟨⟨values, invalidProjection, invalidUnary, missing, matched, sourceProfile,
        projected, _, callbackSelected, accepted, lowered, route, binder, selected, description,
        place, prepared, routeType, path, index, slot, keys, keysGenerated,
        CompatiblePlaceCompilerCertificates.PreparedPath.key_ids path, leafType, ?_⟩⟩
      simp only [routeType, Option.isNone_none]

end Solcore.SourceSemantics.CoreLowering.AcceptedProjectedBitNotReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedForItemsFlow
/-! Actual compiler receipts for for-loop header items. Each header retains
its exact continuation action, final lexical scope and generated expression
children. Unsupported item forms remain an explicit original-source boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

/-- Ordered expanded expression actions, including repeated source occurrences. -/
structure Child (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (reasonAt : ExpressionId → Word) where
  fuel : Nat
  scope : SourceCoreLocalCell.Scope
  expression : ExpressionId
  lowered : SourceCoreBasic.LoweredExpr
  accepted : policy.lowerExpression fuel source scope expression reasonAt = .ok lowered

/-- Each retained key has its own compiler action, in original route order. -/
def keyChildren {policy : SourceCoreLoops.Policy} {source : TypedSource} {reasonAt : ExpressionId → Word}
    (fuel : Nat) (scope : SourceCoreLocalCell.Scope)
    (keys : List (ExpressionId × Ty)) (codes : List SourceCoreBasic.LoweredExpr)
    (generated : DataPatternValues.ListRel
      (DataPlaceCertificates.KeyGenerated policy.lowerExpression fuel source scope reasonAt) keys codes) :
    List (Child policy source reasonAt) :=
  match keys, codes with
  | [], [] => []
  | [], _ :: _ => False.elim (by cases generated)
  | _ :: _, [] => False.elim (by cases generated)
  | key :: rest, code :: more =>
      have head : DataPlaceCertificates.KeyGenerated policy.lowerExpression fuel source scope reasonAt key code := by
        cases generated with | cons first _ => exact first
      have tail : DataPatternValues.ListRel
          (DataPlaceCertificates.KeyGenerated policy.lowerExpression fuel source scope reasonAt) rest more := by
        cases generated with | cons _ remaining => exact remaining
      ⟨fuel, scope, key.1, code, head.1⟩ :: keyChildren fuel scope rest more tail

theorem keyChildren_ids {policy : SourceCoreLoops.Policy} {source : TypedSource} {reasonAt : ExpressionId → Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {keys : List (ExpressionId × Ty)} {codes : List SourceCoreBasic.LoweredExpr}
    (generated : DataPatternValues.ListRel
      (DataPlaceCertificates.KeyGenerated policy.lowerExpression fuel source scope reasonAt) keys codes) :
    (keyChildren fuel scope keys codes generated).map Child.expression = keys.map Prod.fst := by
  induction keys generalizing codes with
  | nil => cases generated; rfl
  | cons key rest ih =>
      cases generated with
      | cons first remaining =>
          simp only [keyChildren, List.map_cons]
          exact congrArg (List.cons key.1) (ih remaining)

structure Binding (policy : SourceCoreLoops.Policy) (source : TypedSource) where
  scope : SourceCoreLocalCell.Scope
  binder : TypedBinder
  payload : Ty
  projected : policy.lowerBinder source scope binder = .ok payload

/-- Bare value writes retain the original declaration type as well as native layout. -/
def Assignable (source : TypedSource) (assignment : AssignmentResolution)
    (operator : Solcore.Syntax.ValueAssignOp) : Prop :=
  (operator = .equal ∨ assignment.target.type = .word) ∧ assignment.target.projections = [] ∧
    ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      binder.scheme.body = assignment.target.type

/-- Projected writes keep their root declaration distinct from the selected leaf. -/
def ProjectedAssignable (source : TypedSource) (assignment : AssignmentResolution)
    (operator : Solcore.Syntax.ValueAssignOp) : Prop :=
  (operator = .equal ∨ assignment.target.type = .word) ∧ assignment.target.projections ≠ [] ∧
    ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type

def ValueAssignable (source : TypedSource) (assignment : AssignmentResolution)
    (operator : Solcore.Syntax.ValueAssignOp) : Prop :=
  Assignable source assignment operator ∨ ProjectedAssignable source assignment operator

/-- Unary writes have the same original declaration requirement, with no RHS. -/
def BitNotAssignable (source : TypedSource) (assignment : AssignmentResolution) : Prop :=
  assignment.target.type = .word ∧ assignment.target.projections = [] ∧
    ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      binder.scheme.body = assignment.target.type

/-- Mapping routes retain the declared root and the actual raw Word leaf. -/
def ProjectedBitNotAssignable (source : TypedSource) (assignment : AssignmentResolution) : Prop :=
  assignment.target.type = .word ∧ assignment.target.projections ≠ [] ∧
    ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type

def UnaryAssignable (source : TypedSource) (assignment : AssignmentResolution) : Prop :=
  BitNotAssignable source assignment ∨ ProjectedBitNotAssignable source assignment

/-- Every current header form has a raw compiler receipt. Target eligibility
is checked separately when that receipt is refined. -/
def HeaderForms (_items : List ForItemForm) : Prop := True

inductive Items (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (site : SourceCoreElaboration.ErrorSite) (result : Ty) (reasonAt : ExpressionId → Word)
    (next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr)
    (finalScope : SourceCoreLocalCell.Scope) (finish : Expr) :
    Nat → SourceCoreLocalCell.Scope → List ForItemForm → Expr → Type where
  | nil {fuel scope} (same : scope = finalScope) (accepted : next scope = .ok finish) :
      Items policy source site result reasonAt next finalScope finish fuel scope [] finish
  | absent {fuel scope binder payload rest tail code}
      (projected : policy.lowerBinder source scope binder = .ok payload)
      (remaining : Items policy source site result reasonAt next finalScope finish fuel ((binder.id, payload) :: scope) rest tail)
      (allocated : SourceCoreSourceCells.letUninitialized policy.sourceCells source scope Renaming.id binder payload tail = .ok code) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.letDecl binder none :: rest) code
  | initialized {fuel scope binder expression payload rest tail code}
      (projected : policy.lowerBinder source scope binder = .ok payload)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (childType : SourceCoreBasic.ensureType (.binder binder.id) payload child.type = .ok ())
      (remaining : Items policy source site result reasonAt next finalScope finish fuel ((binder.id, payload) :: scope) rest tail)
      (allocated : (if binder.scheme.quantified.isEmpty then
          SourceCoreSourceCells.letInitialized policy.sourceCells source scope Renaming.id binder
            (LocalLoop.controlType result) payload child.expression tail
        else
          SourceCoreSourceCells.letInitializedSnapshot policy.sourceCells source scope binder
            (LocalLoop.controlType result) payload child.expression tail) = .ok code) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.letDecl binder (some expression) :: rest) code
  | discard {fuel scope expression rest tail}
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.expression expression :: rest)
        (LocalSequence.discard (LocalLoop.controlType result) child.expression tail)
  | assigning {fuel scope assignment operator expression rest tail code}
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail)
      (accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator expression
        (LocalLoop.controlType result) tail reasonAt = .ok code) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.assignValue assignment operator expression :: rest) code
  | assigned {fuel scope assignment operator expression rest tail code}
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail)
      (receipt : AcceptedBareAssignmentReceipt.Receipt policy fuel source scope site assignment operator expression
        (LocalLoop.controlType result) tail reasonAt code)
      (targetType : receipt.binder.scheme.body = assignment.target.type) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.assignValue assignment operator expression :: rest) code
  | projectedAssigned {fuel scope assignment operator expression rest tail code}
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail)
      (receipt : AcceptedProjectedAssignmentReceipt.Receipt policy fuel source scope site assignment operator expression
        (LocalLoop.controlType result) tail reasonAt code)
      (route : AcceptedProjectedAssignmentRoute.Route source receipt.binder.scheme.body
        assignment.target.projections assignment.target.type) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.assignValue assignment operator expression :: rest) code
  | bitNotting {fuel scope assignment rest tail code}
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail)
      (accepted : SourceCoreLoops.lowerForItems policy site (fuel + 1) source scope
        (.assignBitNot assignment :: rest) result reasonAt next = .ok code) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.assignBitNot assignment :: rest) code
  | bitNotted {fuel scope assignment rest tail code}
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail)
      (receipt : AcceptedBareBitNotReceipt.Receipt policy fuel source scope site assignment
        (LocalLoop.controlType result) tail reasonAt code)
      (targetType : receipt.binder.scheme.body = assignment.target.type) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.assignBitNot assignment :: rest) code
  | projectedBitNotted {fuel scope assignment rest tail code}
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail)
      (receipt : AcceptedProjectedBitNotReceipt.Receipt policy fuel source scope site assignment
        (LocalLoop.controlType result) tail reasonAt code)
      (route : AcceptedProjectedAssignmentRoute.Route source receipt.binder.scheme.body
        assignment.target.projections assignment.target.type) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.assignBitNot assignment :: rest) code

namespace Items
variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
  {result : Ty} {reasonAt : ExpressionId → Word}
  {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
  {finalScope : SourceCoreLocalCell.Scope} {finish : Expr}
  {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm} {code : Expr}

theorem of_accepted (_forms : HeaderForms items)
    (accepted : SourceCoreLoops.lowerForItems policy site fuel source scope items result reasonAt next = .ok code) :
    ∃ finalScope finish, Nonempty (Items policy source site result reasonAt next finalScope finish fuel scope items code) := by
  induction fuel generalizing scope items code with
  | zero =>
    cases items with
    | nil => exact ⟨scope, code, ⟨.nil rfl accepted⟩⟩
    | cons item rest => cases accepted
  | succ fuel ih =>
    cases items with
    | nil => exact ⟨scope, code, ⟨.nil rfl accepted⟩⟩
    | cons item rest =>
      have tailForms : HeaderForms rest := True.intro
      cases item with
      | letDecl binder initializer =>
        simp only [SourceCoreLoops.lowerForItems] at accepted
        obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
        obtain ⟨tail, generatedTail, accepted⟩ := bind_ok accepted
        obtain ⟨finalScope, finish, ⟨remaining⟩⟩ := ih tailForms generatedTail
        cases initializer with
        | none => exact ⟨finalScope, finish, ⟨.absent projected remaining accepted⟩⟩
        | some expression =>
          obtain ⟨child, generated, accepted⟩ := bind_ok accepted
          obtain ⟨checked, childType, allocated⟩ := bind_ok accepted
          cases checked
          exact ⟨finalScope, finish, ⟨.initialized projected child generated childType remaining allocated⟩⟩
      | expression expression =>
        simp only [SourceCoreLoops.lowerForItems] at accepted
        obtain ⟨child, generated, accepted⟩ := bind_ok accepted
        obtain ⟨tail, generatedTail, emitted⟩ := bind_ok accepted
        cases emitted
        obtain ⟨finalScope, finish, ⟨remaining⟩⟩ := ih tailForms generatedTail
        exact ⟨finalScope, finish, ⟨.discard child generated remaining⟩⟩
      | assignValue assignment operator expression =>
        simp only [SourceCoreLoops.lowerForItems] at accepted
        obtain ⟨tail, generatedTail, assigned⟩ := bind_ok accepted
        obtain ⟨finalScope, finish, ⟨remaining⟩⟩ := ih tailForms generatedTail
        exact ⟨finalScope, finish, ⟨.assigning remaining assigned⟩⟩
      | assignBitNot assignment =>
        have whole := accepted
        simp only [SourceCoreLoops.lowerForItems] at accepted
        cases selected : policy.assignBitNotWithExpression with
        | some callback =>
          simp only [selected] at accepted
          obtain ⟨tail, generatedTail, _assigned⟩ := bind_ok accepted
          obtain ⟨finalScope, finish, ⟨remaining⟩⟩ := ih tailForms generatedTail
          exact ⟨finalScope, finish, ⟨.bitNotting remaining whole⟩⟩
        | none =>
          simp only [selected] at accepted
          cases legacy : policy.assignBitNot with
          | none => simp only [legacy] at accepted; cases accepted
          | some callback =>
            simp only [legacy] at accepted
            obtain ⟨tail, generatedTail, _assigned⟩ := bind_ok accepted
            obtain ⟨finalScope, finish, ⟨remaining⟩⟩ := ih tailForms generatedTail
            exact ⟨finalScope, finish, ⟨.bitNotting remaining whole⟩⟩

theorem accepted (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) :
    SourceCoreLoops.lowerForItems policy site fuel source scope items result reasonAt next = .ok code := by
  induction tree with
  | @nil fuel scope same accepted => cases fuel <;> exact accepted
  | absent projected remaining allocated ih =>
    simpa [SourceCoreLoops.lowerForItems, projected, ih, bind, Except.bind] using allocated
  | initialized projected child generated childType remaining allocated ih =>
    simpa [SourceCoreLoops.lowerForItems, projected, ih, generated, childType, bind, Except.bind] using allocated
  | discard child generated remaining ih =>
    simp [SourceCoreLoops.lowerForItems, generated, ih, bind, Except.bind, pure, Except.pure]
  | assigning remaining assigned ih =>
    simpa only [SourceCoreLoops.lowerForItems, ih, bind, Except.bind] using assigned
  | assigned remaining receipt targetType ih =>
    simpa only [SourceCoreLoops.lowerForItems, ih, bind, Except.bind] using receipt.accepted
  | projectedAssigned remaining receipt route ih =>
    simpa only [SourceCoreLoops.lowerForItems, ih, bind, Except.bind] using receipt.accepted
  | bitNotting _ accepted _ => exact accepted
  | bitNotted remaining receipt targetType ih =>
    simpa only [SourceCoreLoops.lowerForItems, receipt.selected, ih, bind, Except.bind] using receipt.accepted
  | projectedBitNotted remaining receipt route ih =>
    simpa only [SourceCoreLoops.lowerForItems, receipt.callbackSelected, ih, bind, Except.bind] using receipt.accepted

theorem finish_accepted (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) :
    next finalScope = .ok finish := by
  induction tree with
  | nil same accepted => exact same ▸ accepted
  | absent _ _ _ ih | initialized _ _ _ _ _ _ ih | discard _ _ _ ih
      | assigning _ _ ih | assigned _ _ _ ih | projectedAssigned _ _ _ ih | bitNotting _ _ ih | bitNotted _ _ _ ih | projectedBitNotted _ _ _ ih => exact ih

def closed {fuel scope items code} (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : Bool :=
  match tree with
  | .nil .. => true
  | .absent _ remaining _ | .initialized _ _ _ _ remaining _ | .discard _ _ remaining | .assigned remaining _ _ | .projectedAssigned remaining _ _ | .bitNotted remaining _ _ | .projectedBitNotted remaining _ _ => remaining.closed
  | .assigning .. | .bitNotting .. => false

def children {fuel scope items code} (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : List (Child policy source reasonAt) :=
  match tree with
  | .nil .. => []
  | .absent _ remaining _ | .assigning remaining _ | .bitNotting remaining _ | .bitNotted remaining _ _ => remaining.children
  | @Items.initialized _ _ _ _ _ _ _ _ fuel scope _ expression _ _ _ _ _ child generated _ remaining _ =>
      ⟨fuel, scope, expression, child, generated⟩ :: remaining.children
  | @Items.discard _ _ _ _ _ _ _ _ fuel scope expression _ _ child generated remaining =>
      ⟨fuel, scope, expression, child, generated⟩ :: remaining.children
  | @Items.assigned _ _ _ _ _ _ _ _ fuel scope _ _ expression _ _ _ remaining receipt _ =>
      ⟨fuel, scope, expression, receipt.child, receipt.generated⟩ :: remaining.children
  | @Items.projectedAssigned _ _ _ _ _ _ _ _ fuel scope _ _ expression _ _ _ remaining receipt _route =>
      keyChildren fuel scope receipt.place.keys receipt.keys receipt.keysGenerated ++
        (⟨fuel, scope, expression, receipt.child, receipt.generated⟩ :: remaining.children)
  | @Items.projectedBitNotted _ _ _ _ _ _ _ _ fuel scope _ _ _ _ remaining receipt _route =>
      keyChildren fuel scope receipt.place.keys receipt.keys receipt.keysGenerated ++ remaining.children

def bindings {fuel scope items code} (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : List (Binding policy source) :=
  match tree with
  | .nil .. => []
  | @Items.absent _ _ _ _ _ _ _ _ _ scope binder payload _ _ _ projected remaining _ =>
      ⟨scope, binder, payload, projected⟩ :: remaining.bindings
  | @Items.initialized _ _ _ _ _ _ _ _ _ scope binder _ payload _ _ _ projected _ _ _ remaining _ =>
      ⟨scope, binder, payload, projected⟩ :: remaining.bindings
  | .discard _ _ remaining | .assigning remaining _ | .assigned remaining _ _ | .projectedAssigned remaining _ _ | .bitNotting remaining _ | .bitNotted remaining _ _ | .projectedBitNotted remaining _ _ => remaining.bindings

def Ready {fuel scope items code} (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : Prop :=
  match tree with
  | .nil .. => True
  | .absent _ remaining _ | .initialized _ _ _ _ remaining _ | .discard _ _ remaining | .assigned remaining _ _ | .projectedAssigned remaining _ _ | .bitNotted remaining _ _ | .projectedBitNotted remaining _ _ => remaining.Ready
  | @Items.assigning _ _ _ _ _ _ _ _ _ _ assignment operator _ _ _ _ remaining _ =>
      ¬ ValueAssignable source assignment operator ∧ remaining.Ready
  | @Items.bitNotting _ _ _ _ _ _ _ _ _ _ assignment _ _ _ remaining _ =>
      ¬ UnaryAssignable source assignment ∧ remaining.Ready

theorem refine {values : SourceCoreCompatibleValues.Context}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missing)
    {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    (unary : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing)
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) :
    ∃ refined : Items policy source site result reasonAt next finalScope finish fuel scope items code, refined.Ready := by
  classical
  induction tree with
  | nil same accepted => exact ⟨.nil same accepted, True.intro⟩
  | absent projected remaining allocated ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.absent projected tail allocated, ready⟩
  | initialized projected child generated childType remaining allocated ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.initialized projected child generated childType tail allocated, ready⟩
  | discard child generated remaining ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.discard child generated tail, ready⟩
  | @assigning fuel scope assignment operator expression rest tail code remaining assigned ih =>
    obtain ⟨remaining, ready⟩ := ih
    by_cases supported : Assignable source assignment operator
    · obtain ⟨profile, bare, type⟩ := supported
      obtain ⟨receipt⟩ := AcceptedBareAssignmentReceipt.of_accepted matched profile bare assigned
      exact ⟨.assigned remaining receipt (type receipt.binder receipt.declaration), ready⟩
    · by_cases projected : ProjectedAssignable source assignment operator
      · obtain ⟨receipt⟩ := AcceptedProjectedAssignmentReceipt.of_accepted matched projected.1 projected.2.1 assigned
        exact ⟨.projectedAssigned remaining receipt (projected.2.2 receipt.binder receipt.description.binding), ready⟩
      · exact ⟨.assigning remaining assigned, (fun eligible => eligible.elim supported projected), ready⟩
  | assigned remaining receipt targetType ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.assigned tail receipt targetType, ready⟩
  | projectedAssigned remaining receipt route ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.projectedAssigned tail receipt route, ready⟩
  | @bitNotting fuel scope assignment rest tail code remaining assigned ih =>
    obtain ⟨refined, ready⟩ := ih
    by_cases supported : BitNotAssignable source assignment
    · obtain ⟨profile, bare, type⟩ := supported
      have lowered := assigned
      simp only [SourceCoreLoops.lowerForItems, unary, remaining.accepted, bind, Except.bind] at lowered
      obtain ⟨receipt⟩ := AcceptedBareBitNotReceipt.of_accepted unary profile bare unary lowered
      exact ⟨.bitNotted refined receipt (type receipt.binder receipt.declaration), ready⟩
    · by_cases projected : ProjectedBitNotAssignable source assignment
      · have lowered := assigned
        simp only [SourceCoreLoops.lowerForItems, unary, remaining.accepted, bind, Except.bind] at lowered
        obtain ⟨receipt⟩ := AcceptedProjectedBitNotReceipt.of_accepted unary projected.1 projected.2.1 unary lowered
        exact ⟨.projectedBitNotted refined receipt (projected.2.2 receipt.binder receipt.description.binding), ready⟩
      · exact ⟨.bitNotting refined assigned, (fun eligible => eligible.elim supported projected), ready⟩
  | bitNotted remaining receipt targetType ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.bitNotted tail receipt targetType, ready⟩
  | projectedBitNotted remaining receipt route ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.projectedBitNotted tail receipt route, ready⟩

end Items
end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedMatchFlow
/-! Match receipts retain the actual callback action, its scrutinee action and
all emitted arm/default requests in source order. The body callback fixes its
predecessor budget and false execution mode exactly as the compiler does. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedMatchFlow
open Core Frontend SourceInference
open CompatibleMatchCertificates GenericMatchChildren SourceCoreCompatibleDataMatches

abbrev Callback := SourceCoreLoops.ExpressionLowerer → SourceCoreLoops.FlowLowerer → Nat →
  TypedSource → SourceCoreLocalCell.Scope → StatementId → MatchResolution → Ty →
  (ExpressionId → Word) → Word → Except SourceCoreBasic.Error Expr

def bodyCallback (policy : SourceCoreLoops.Policy) (fuel : Nat) : SourceCoreLoops.FlowLowerer :=
  fun _ source scope statements result reasonAt escaped =>
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements result reasonAt false escaped

structure Receipt (policy : SourceCoreLoops.Policy)
    (compilation : SourceCoreCompatibleDataMatches.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : StatementId) (resolution : MatchResolution)
    (result : Ty) (reasonAt : ExpressionId → Word) (escaped : Word) (fuel : Nat) (code : Expr) where
  callback : Callback
  selected : policy.lowerMatch = some callback
  accepted : callback policy.lowerExpression (bodyCallback policy fuel) fuel source scope id resolution
    result reasonAt escaped = .ok code
  childFuel : Nat
  child : SourceCoreBasic.LoweredExpr
  generated : policy.lowerExpression childFuel source scope resolution.scrutinee reasonAt = .ok child
  requests : List Request
  certificate : Certificate compilation source scope id resolution result escaped
    (fun childScope expression lowered => childScope = scope ∧ expression = resolution.scrutinee ∧ lowered = child)
    (Occurs requests) code
  count : requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0)
  original : ∀ request ∈ requests,
    (∃ arm ∈ resolution.cases, request.statements = arm.body) ∨
      resolution.defaultBody = some request.statements
  bodies : ∀ request ∈ requests,
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source request.scope request.statements
      result reasonAt false escaped = .ok request.code

private theorem armRequests_original (scope : SourceCoreLocalCell.Scope)
    (cases : List TypedMatchCase) (arms : List (Pattern × Expr))
    (request : Request) (member : request ∈ armRequests scope cases arms) :
    ∃ arm ∈ cases, request.statements = arm.body := by
  induction cases generalizing arms with
  | nil => cases member
  | cons arm cases ih =>
    cases arms with
    | nil => cases member
    | cons head arms =>
      cases head with
      | mk pattern code =>
        cases member with
        | head => exact ⟨arm, List.mem_cons_self, rfl⟩
        | tail _ member =>
          obtain ⟨selected, included, same⟩ := ih arms member
          exact ⟨selected, List.mem_cons_of_mem _ included, same⟩

private theorem fallbackRequests_original (scope : SourceCoreLocalCell.Scope)
    (fallback : Option (List StatementId)) (code : Expr)
    (request : Request) (member : request ∈ fallbackRequests scope fallback code) :
    fallback = some request.statements := by
  cases fallback with
  | none => cases member
  | some statements =>
    cases member with
    | head => rfl
    | tail _ member => cases member

/-- The selected compiler callback supplies the complete finite receipt.
No source syntax or child execution premise is used. -/
theorem of_accepted {policy : SourceCoreLoops.Policy}
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reasonAt : ExpressionId → Word} {escaped : Word} {fuel : Nat} {code : Expr}
    {callback : Callback}
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy compilation)
    (selected : policy.lowerMatch = some callback)
    (accepted : callback policy.lowerExpression (bodyCallback policy fuel) fuel source scope id resolution
      result reasonAt escaped = .ok code) :
    Nonempty (Receipt policy compilation source scope id resolution result reasonAt escaped fuel code) := by
  have actual := matchPolicy selected accepted
  have raw := CompatibleMatchCertificates.certificate_of_lowerWithReasons
    (expressionCertificate := fun childScope expression lowered => ∃ childFuel,
      policy.lowerExpression childFuel source childScope expression reasonAt = .ok lowered)
    (bodyCertificate := fun childScope statements code =>
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source childScope statements
        result reasonAt false escaped = .ok code)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩)
    (fun _ _ _ _ generated => generated) actual
  cases raw with
  | @matchWith node statementType scrutineeNode type child arms fallback branches code
      read statementTypeValid form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled =>
    obtain ⟨childFuel, generated⟩ := expression
    obtain ⟨retainedArms, armMembers⟩ := Arms.requests armCertificates
    obtain ⟨retainedFallback, fallbackMembers⟩ := Fallback.requests fallbackCertificate
    refine ⟨⟨callback, selected, accepted, childFuel, child, generated,
      armRequests ((resolution.hiddenScrutinee, type) :: scope) resolution.cases arms ++
        fallbackRequests ((resolution.hiddenScrutinee, type) :: scope) resolution.defaultBody fallback,
      ?_, ?_, ?_, ?_⟩⟩
    · apply Certificate.matchWith read statementTypeValid form requirements hiddenOwned hiddenFresh
        scrutineeOwned scrutineeFound projection ⟨rfl, rfl, rfl⟩ sameType
      · apply Arms.mapBodies retainedArms
        intro scope statements code member
        exact List.mem_append_left _ member
      · apply Fallback.mapBodies retainedFallback
        intro scope statements code member
        exact List.mem_append_right _ member
      · exact branchesCertified
      · exact hiddenCompiled
    · rw [List.length_append, Arms.requests_length armCertificates]
      cases resolution.defaultBody <;> rfl
    · intro request member
      rcases List.mem_append.mp member with left | right
      · exact .inl (armRequests_original _ _ _ _ left)
      · exact .inr (fallbackRequests_original _ _ _ _ right)
    · intro request member
      rcases List.mem_append.mp member with left | right
      · exact armMembers _ left
      · exact fallbackMembers _ right

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedMatchFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
/-! Structural inversion of the actual accepted flow action. Each retained
child is the action run by the compiler at its original source and scope.
The boundary alternative records the actual first unexpanded compiler form. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

/-- These are compiler branches expanded by this receipt, not a source checker. -/
def expanded : StatementForm → Bool
  | .returnStmt _ | .letDecl _ _ | .assignValue _ _ _ | .assignBitNot _ | .whileLoop _ _
    | .expression _ _ | .matchWith _ | .block _ | .ifThen _ _ _ | .forLoop _ _ _ _ | .breakStmt | .continueStmt => true

/-- Exact compiler continuation after all initializer declarations are in scope. -/
def forNext (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (site : SourceCoreElaboration.ErrorSite) (result : Ty) (reasonAt : ExpressionId → Word)
    (escaped : Word) (fuel : Nat) (condition : ExpressionId) (body : List StatementId)
    (post : List ForItemForm) (scope : SourceCoreLocalCell.Scope) : Except SourceCoreBasic.Error Expr := do
  let child ← policy.lowerExpression fuel source scope condition reasonAt
  SourceCoreBasic.ensureType site .bool child.type
  let loopBody ← SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope body result reasonAt false escaped
  let postCode ← SourceCoreLoops.lowerForItems policy site fuel source scope post result reasonAt
    (fun _ => pure (LocalLoop.fallthrough result))
  pure (LocalLoop.iterate result child.expression loopBody postCode escaped)

inductive Tree (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (result : Ty) (reasonAt : ExpressionId → Word) :
    Bool → Word → Nat → SourceCoreLocalCell.Scope → List StatementId → Expr → Type where
  | nil {mode escaped fuel scope} : Tree policy source result reasonAt mode escaped fuel scope []
      (LocalLoop.fallthrough result)
  | returning {mode escaped fuel scope id rest node stored expression}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .returnStmt (some expression))
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result stored = .ok ())
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result child.type = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.returnValue result child.expression)
  | returnUnit {mode escaped fuel scope id rest node stored}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .returnStmt none)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result stored = .ok ())
      (unitType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.returned .unit)
  | initialized {mode escaped fuel scope id rest node stored binder expression payload tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .letDecl binder (some expression))
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (projected : policy.lowerBinder source scope binder = .ok payload)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (childType : SourceCoreBasic.ensureType (.binder binder.id) payload child.type = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel ((binder.id, payload) :: scope) rest tail)
      (allocated : (if binder.scheme.quantified.isEmpty then
          SourceCoreSourceCells.letInitialized policy.sourceCells source scope Renaming.id binder
            (LocalLoop.controlType result) payload child.expression tail
        else
          SourceCoreSourceCells.letInitializedSnapshot policy.sourceCells source scope binder
            (LocalLoop.controlType result) payload child.expression tail) = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | absent {mode escaped fuel scope id rest node stored binder payload tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .letDecl binder none)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (projected : policy.lowerBinder source scope binder = .ok payload)
      (remaining : Tree policy source result reasonAt mode escaped fuel ((binder.id, payload) :: scope) rest tail)
      (allocated : SourceCoreSourceCells.letUninitialized policy.sourceCells source scope Renaming.id binder
        payload tail = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | assigning {mode escaped fuel scope id rest node stored assignment operator expression tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignValue assignment operator expression)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (assigned : SourceCoreLoops.assignValue policy fuel source scope (.occurrence id.occurrence)
        assignment operator expression (LocalLoop.controlType result) tail reasonAt = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | assigned {mode escaped fuel scope id rest node stored assignment operator expression tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignValue assignment operator expression)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (receipt : AcceptedBareAssignmentReceipt.Receipt policy fuel source scope (.occurrence id.occurrence)
        assignment operator expression (LocalLoop.controlType result) tail reasonAt code)
      (targetType : receipt.binder.scheme.body = assignment.target.type) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | projectedAssigned {mode escaped fuel scope id rest node stored assignment operator expression tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignValue assignment operator expression)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (receipt : AcceptedProjectedAssignmentReceipt.Receipt policy fuel source scope (.occurrence id.occurrence)
        assignment operator expression (LocalLoop.controlType result) tail reasonAt code)
      (route : AcceptedProjectedAssignmentRoute.Route source receipt.binder.scheme.body
        assignment.target.projections assignment.target.type) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | bitNotting {mode escaped fuel scope id rest node stored assignment tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignBitNot assignment)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | bitNotted {mode escaped fuel scope id rest node stored assignment tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignBitNot assignment)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (receipt : AcceptedBareBitNotReceipt.Receipt policy fuel source scope (.occurrence id.occurrence)
        assignment (LocalLoop.controlType result) tail reasonAt code)
      (targetType : receipt.binder.scheme.body = assignment.target.type) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | projectedBitNotted {mode escaped fuel scope id rest node stored assignment tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignBitNot assignment)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (receipt : AcceptedProjectedBitNotReceipt.Receipt policy fuel source scope (.occurrence id.occurrence)
        assignment (LocalLoop.controlType result) tail reasonAt code)
      (route : AcceptedProjectedAssignmentRoute.Route source receipt.binder.scheme.body
        assignment.target.projections assignment.target.type) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | discard {mode escaped fuel scope id rest node stored expression tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .expression expression true)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalSequence.discard (LocalLoop.controlType result) child.expression tail)
  | tailValue {escaped fuel scope id node stored expression}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .expression expression false)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result stored = .ok ())
      (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result child.type = .ok ()) :
      Tree policy source result reasonAt true escaped (fuel + 1) scope [id]
        (LocalLoop.returnValue result child.expression)
  | valueDiscard {mode escaped fuel scope id rest node stored expression tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .expression expression false)
      (notTail : (mode && rest.isEmpty) = false)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) stored child.type = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalSequence.discard (LocalLoop.controlType result) child.expression tail)
  | block {mode escaped fuel scope id rest node stored statements innerCode tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .block statements)
      (inner : Tree policy source result reasonAt false escaped fuel scope statements innerCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result innerCode tail)
  | conditional {mode escaped fuel scope id rest node stored condition thenBody elseBody thenCode elseCode tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .ifThen condition thenBody elseBody)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope condition reasonAt = .ok child)
      (conditionType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool child.type = .ok ())
      (left : Tree policy source result reasonAt false escaped fuel scope thenBody thenCode)
      (right : Tree policy source result reasonAt false escaped fuel scope (elseBody.getD []) elseCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result (LocalLoop.conditional result child.expression thenCode elseCode) tail)
  | matching {mode escaped fuel scope id rest node stored resolution matchedCode tail callback}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .matchWith resolution)
      (selected : policy.lowerMatch = some callback)
      (accepted : callback policy.lowerExpression (AcceptedNamedMatchFlow.bodyCallback policy fuel)
        fuel source scope id resolution result reasonAt escaped = .ok matchedCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result matchedCode tail)
  | matched {mode escaped fuel scope id rest node stored resolution matchedCode tail compilation}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .matchWith resolution)
      (receipt : AcceptedNamedMatchFlow.Receipt policy compilation source scope id resolution
        result reasonAt escaped fuel matchedCode)
      (branches : ∀ request ∈ receipt.requests,
        Tree policy source result reasonAt false escaped fuel request.scope request.statements request.code)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result matchedCode tail)
  | whileLoop {mode escaped fuel scope id rest node stored condition body loopCode tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .whileLoop condition body)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope condition reasonAt = .ok child)
      (conditionType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool child.type = .ok ())
      (inner : Tree policy source result reasonAt false escaped fuel scope body loopCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result (LocalLoop.whileLoop result child.expression loopCode escaped) tail)
  | breaking {mode escaped fuel scope id rest node stored}
      (read : policy.readStatement source id = .ok (node, stored)) (form : node.form = .breakStmt)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) (LocalLoop.breaking result)
  | continuing {mode escaped fuel scope id rest node stored}
      (read : policy.readStatement source id = .ok (node, stored)) (form : node.form = .continueStmt)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) (LocalLoop.continuing result)
  | forLoop {mode escaped fuel scope id rest node stored initializer condition post body
      loopScope postScope loopCode postCode initialCode tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .forLoop initializer condition post body)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source loopScope condition reasonAt = .ok child)
      (conditionType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool child.type = .ok ())
      (initial : Items policy source (.occurrence id.occurrence) result reasonAt
        (forNext policy source (.occurrence id.occurrence) result reasonAt escaped fuel condition body post)
        loopScope (LocalLoop.iterate result child.expression loopCode postCode escaped) fuel scope initializer initialCode)
      (inner : Tree policy source result reasonAt false escaped fuel loopScope body loopCode)
      (after : Items policy source (.occurrence id.occurrence) result reasonAt
        (fun _ => pure (LocalLoop.fallthrough result)) postScope (LocalLoop.fallthrough result) fuel loopScope post postCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result initialCode tail)
  | forBoundary {mode escaped fuel scope id rest node stored initializer condition post body code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .forLoop initializer condition post body)
      (outside : ¬ (HeaderForms initializer ∧ HeaderForms post))
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | boundary {mode escaped fuel scope id rest node stored code}
      (read : policy.readStatement source id = .ok (node, stored))
      (outside : expanded node.form = false)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code

/-- Inversion follows the compiler branch and its actual decreasing fuel. It
requires no independently recognized statement shape. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      statements result reasonAt mode escaped = .ok code) :
    Nonempty (Tree policy source result reasonAt mode escaped fuel scope statements code) := by
  classical
  induction fuel generalizing mode scope statements code with
  | zero =>
      cases statements with
      | nil => cases accepted; exact ⟨.nil⟩
      | cons id rest => cases accepted
  | succ fuel ih =>
      cases statements with
      | nil => cases accepted; exact ⟨.nil⟩
      | cons id rest =>
        have whole := accepted
        simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
        obtain ⟨⟨node, stored⟩, read, accepted⟩ := bind_ok accepted
        cases form : node.form with
        | returnStmt value =>
            simp only [form] at accepted
            cases value with
            | none =>
                obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                cases checked
                obtain ⟨checked, unitType, accepted⟩ := bind_ok accepted
                cases checked
                cases accepted
                exact ⟨.returnUnit read form statementType unitType⟩
            | some expression =>
                obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                cases checked
                obtain ⟨child, generated, accepted⟩ := bind_ok accepted
                obtain ⟨checked, childType, accepted⟩ := bind_ok accepted
                cases checked
                cases accepted
                exact ⟨.returning read form statementType child generated childType⟩
        | letDecl binder initializer =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
            cases initializer with
            | none =>
                obtain ⟨tail, generated, allocated⟩ := bind_ok accepted
                obtain ⟨remaining⟩ := ih generated
                exact ⟨.absent read form statementType projected remaining allocated⟩
            | some expression =>
                obtain ⟨child, generated, accepted⟩ := bind_ok accepted
                obtain ⟨checked, childType, accepted⟩ := bind_ok accepted
                cases checked
                obtain ⟨tail, tailGenerated, allocated⟩ := bind_ok accepted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.initialized read form statementType projected child generated childType remaining allocated⟩
        | assignValue assignment operator expression =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨tail, tailGenerated, assigned⟩ := bind_ok accepted
            obtain ⟨remaining⟩ := ih tailGenerated
            exact ⟨.assigning read form statementType remaining assigned⟩
        | expression value semicolon =>
            cases semicolon with
            | false =>
                simp only [form] at accepted
                obtain ⟨child, generated, accepted⟩ := bind_ok accepted
                by_cases tail : (mode && rest.isEmpty) = true
                · have both : mode = true ∧ rest.isEmpty = true := by simpa only [Bool.and_eq_true] using tail
                  cases both.1
                  have empty : rest = [] := List.isEmpty_iff.mp both.2
                  subst rest
                  simp only [Bool.not_false, Bool.true_and, List.isEmpty_nil, ↓reduceIte] at accepted
                  obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                  cases checked
                  obtain ⟨checked, childType, accepted⟩ := bind_ok accepted
                  cases checked
                  cases accepted
                  exact ⟨.tailValue read form child generated statementType childType⟩
                · have notTail : (mode && rest.isEmpty) = false := Bool.eq_false_iff.mpr tail
                  simp only [Bool.not_false, Bool.true_and, notTail, Bool.false_eq_true, ↓reduceIte] at accepted
                  obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                  cases checked
                  obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨remaining⟩ := ih tailGenerated
                  exact ⟨.valueDiscard read form notTail child generated statementType remaining⟩
            | true =>
                simp only [form, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at accepted
                obtain ⟨child, generated, accepted⟩ := bind_ok accepted
                obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                cases checked
                obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
                cases accepted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.discard read form child generated statementType remaining⟩
        | block statements =>
            simp only [form] at accepted
            obtain ⟨innerCode, innerGenerated, accepted⟩ := bind_ok accepted
            obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
            cases accepted
            obtain ⟨inner⟩ := ih innerGenerated
            obtain ⟨remaining⟩ := ih tailGenerated
            exact ⟨.block read form inner remaining⟩
        | ifThen condition thenBody elseBody =>
            simp only [form] at accepted
            obtain ⟨child, generated, accepted⟩ := bind_ok accepted
            obtain ⟨checked, conditionType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨thenCode, thenGenerated, accepted⟩ := bind_ok accepted
            obtain ⟨left⟩ := ih thenGenerated
            cases elseBody with
            | none =>
                simp only [pure, Except.pure, bind, Except.bind] at accepted
                obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
                cases accepted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.conditional read form child generated conditionType left .nil remaining⟩
            | some statements =>
                obtain ⟨elseCode, elseGenerated, accepted⟩ := bind_ok accepted
                obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
                cases accepted
                obtain ⟨right⟩ := ih elseGenerated
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.conditional read form child generated conditionType left right remaining⟩
        | whileLoop condition body =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨child, generated, accepted⟩ := bind_ok accepted
            obtain ⟨checked, conditionType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨loopCode, loopGenerated, accepted⟩ := bind_ok accepted
            obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
            cases accepted
            obtain ⟨inner⟩ := ih loopGenerated
            obtain ⟨remaining⟩ := ih tailGenerated
            exact ⟨.whileLoop read form statementType child generated conditionType inner remaining⟩
        | forLoop initializer condition post body =>
            by_cases headers : HeaderForms initializer ∧ HeaderForms post
            · simp only [form] at accepted
              obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
              cases checked
              obtain ⟨initialCode, initialAccepted, accepted⟩ := bind_ok accepted
              obtain ⟨tail, tailGenerated, emitted⟩ := bind_ok accepted
              cases emitted
              change SourceCoreLoops.lowerForItems policy (.occurrence id.occurrence) fuel source scope initializer
                result reasonAt (forNext policy source (.occurrence id.occurrence) result reasonAt escaped fuel condition body post) = .ok initialCode at initialAccepted
              obtain ⟨loopScope, finish, ⟨initial⟩⟩ := Items.of_accepted headers.1 initialAccepted
              have continuation := initial.finish_accepted
              unfold forNext at continuation
              obtain ⟨child, generated, continuation⟩ := bind_ok continuation
              obtain ⟨checked, conditionType, continuation⟩ := bind_ok continuation
              cases checked
              obtain ⟨loopCode, loopGenerated, continuation⟩ := bind_ok continuation
              obtain ⟨postCode, postGenerated, emitted⟩ := bind_ok continuation
              cases emitted
              obtain ⟨postScope, finish, ⟨after⟩⟩ := Items.of_accepted headers.2 postGenerated
              have final := after.finish_accepted
              cases final
              obtain ⟨inner⟩ := ih loopGenerated
              obtain ⟨remaining⟩ := ih tailGenerated
              exact ⟨.forLoop read form statementType child generated conditionType initial inner after remaining⟩
            · exact ⟨.forBoundary read form headers whole⟩
        | breakStmt =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            cases accepted
            exact ⟨.breaking read form statementType⟩
        | continueStmt =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            cases accepted
            exact ⟨.continuing read form statementType⟩
        | matchWith resolution =>
            simp only [form] at accepted
            cases selected : policy.lowerMatch with
            | none => simp only [selected] at accepted; cases accepted
            | some callback =>
                simp only [selected] at accepted
                obtain ⟨matchedCode, matchedAccepted, accepted⟩ := bind_ok accepted
                obtain ⟨tail, tailGenerated, emitted⟩ := bind_ok accepted
                cases emitted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.matching read form selected matchedAccepted remaining⟩
        | assignBitNot assignment =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            cases selected : policy.assignBitNotWithExpression with
            | some callback =>
                simp only [selected] at accepted
                obtain ⟨tail, tailGenerated, _assigned⟩ := bind_ok accepted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.bitNotting read form statementType remaining whole⟩
            | none =>
                simp only [selected] at accepted
                cases legacy : policy.assignBitNot with
                | none => simp only [legacy] at accepted; cases accepted
                | some callback =>
                    simp only [legacy] at accepted
                    obtain ⟨tail, tailGenerated, _assigned⟩ := bind_ok accepted
                    obtain ⟨remaining⟩ := ih tailGenerated
                    exact ⟨.bitNotting read form statementType remaining whole⟩

/-- The footer is retained once, around the exact recursively issued flow. -/
structure Body (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId) (result : Ty)
    (reasonAt : ExpressionId → Word) (fellThrough escaped : Word) (code : Expr) where
  flow : Expr
  tree : Tree policy source result reasonAt true escaped fuel scope statements flow
  emitted : code = CompatibleStatements.finish result flow fellThrough escaped

theorem body_of_accepted {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
      result reasonAt fellThrough escaped = .ok code) :
    Nonempty (Body policy fuel source scope statements result reasonAt fellThrough escaped code) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  obtain ⟨tree⟩ := of_accepted generated
  exact ⟨⟨flow, tree, (Except.ok.inj returned).symm⟩⟩


variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {result : Ty}
  {reasonAt : ExpressionId → Word} {mode : Bool}

-- Empty fallthrough remains a separate boundary: accepted native code alone
-- does not prove the original source body's return obligation.
def Tree.closed {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Bool :=
  match tree with
  | .nil => !mode
  | .boundary .. | .assigning .. | .bitNotting .. | .forBoundary .. | .matching .. | .tailValue .. => false
  | .returning .. | .returnUnit .. | .breaking .. | .continuing .. => true
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ => tail.closed
  | .assigned _ _ _ tail _ _ | .projectedAssigned _ _ _ tail _ _ | .bitNotted _ _ _ tail _ _ | .projectedBitNotted _ _ _ tail _ _ | .discard _ _ _ _ _ tail => tail.closed
  | .valueDiscard _ _ _ _ _ _ tail => !mode && tail.closed
  | .block _ _ inner tail => inner.closed && tail.closed
  | .conditional _ _ _ _ _ left right tail =>
      left.closed && right.closed && tail.closed
  | .matched _ _ receipt branches tail =>
      receipt.requests.attach.all (fun request => (branches request.val request.property).closed) && tail.closed
  | .whileLoop _ _ _ _ _ _ inner tail => inner.closed && tail.closed
  | .forLoop _ _ _ _ _ _ initial inner after tail => initial.closed && inner.closed && after.closed && tail.closed

def Tree.children {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    List (Child policy source reasonAt) :=
  match tree with
  | .nil | .returnUnit .. | .boundary .. | .forBoundary .. | .breaking .. | .continuing .. => []
  | @Tree.returning _ _ _ _ _ _ fuel scope _ _ _ _ expression _ _ _ child generated _ =>
      [⟨fuel, scope, expression, child, generated⟩]
  | @Tree.tailValue _ _ _ _ _ fuel scope _ _ _ expression _ _ child generated _ _ =>
      [⟨fuel, scope, expression, child, generated⟩]
  | @Tree.valueDiscard _ _ _ _ _ _ fuel scope _ _ _ _ expression _ _ _ _ child generated _ tail =>
      ⟨fuel, scope, expression, child, generated⟩ :: tail.children
  | @Tree.initialized _ _ _ _ _ _ fuel scope _ _ _ _ _ expression _ _ _ _ _ _ _ child generated _ tail _ =>
      ⟨fuel, scope, expression, child, generated⟩ :: tail.children
  | .absent _ _ _ _ tail _ | .assigning _ _ _ tail _ | .bitNotting _ _ _ tail _ | .bitNotted _ _ _ tail _ _ | .matching _ _ _ _ tail => tail.children
  | @Tree.assigned _ _ _ _ _ _ fuel scope _ _ _ _ _ _ expression _ _ _ _ _ tail receipt _ =>
      ⟨fuel, scope, expression, receipt.child, receipt.generated⟩ :: tail.children
  | @Tree.projectedAssigned _ _ _ _ _ _ fuel scope _ _ _ _ _ _ expression _ _ _ _ _ tail receipt _route =>
      keyChildren fuel scope receipt.place.keys receipt.keys receipt.keysGenerated ++
        (⟨fuel, scope, expression, receipt.child, receipt.generated⟩ :: tail.children)
  | @Tree.discard _ _ _ _ _ _ fuel scope _ _ _ _ expression _ _ _ child generated _ tail =>
      ⟨fuel, scope, expression, child, generated⟩ :: tail.children
  | .block _ _ inner tail => inner.children ++ tail.children
  | @Tree.conditional _ _ _ _ _ _ fuel scope _ _ _ _ condition _ _ _ _ _ _ _ child generated _ left right tail =>
      ⟨fuel, scope, condition, child, generated⟩ :: (left.children ++ right.children ++ tail.children)
  | .matched _ _ receipt branches tail =>
      ⟨receipt.childFuel, _, _, receipt.child, receipt.generated⟩ ::
        (receipt.requests.attach.flatMap (fun request => (branches request.val request.property).children) ++ tail.children)
  | @Tree.whileLoop _ _ _ _ _ _ fuel scope _ _ _ _ condition _ _ _ _ _ _ child generated _ inner tail =>
      ⟨fuel, scope, condition, child, generated⟩ :: (inner.children ++ tail.children)

  | @Tree.forLoop _ _ _ _ _ _ fuel _ _ _ _ _ _ condition _ _ loopScope _ _ _ _ _ _ _ _ child generated _ initial inner after tail =>
      initial.children ++ (⟨fuel, loopScope, condition, child, generated⟩ :: (inner.children ++ after.children ++ tail.children))
  | @Tree.projectedBitNotted _ _ _ _ _ _ fuel scope _ _ _ _ _ _ _ _ _ _ tail receipt _route =>
      keyChildren fuel scope receipt.place.keys receipt.keys receipt.keysGenerated ++ tail.children

def Tree.bindings {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    List (Binding policy source) :=
  match tree with
  | .nil | .returning .. | .returnUnit .. | .boundary .. | .forBoundary .. | .breaking .. | .continuing .. | .tailValue .. => []
  | @Tree.initialized _ _ _ _ _ _ _ scope _ _ _ _ binder _ payload _ _ _ _ _ projected _ _ _ tail _ =>
      ⟨scope, binder, payload, projected⟩ :: tail.bindings
  | @Tree.absent _ _ _ _ _ _ _ scope _ _ _ _ binder payload _ _ _ _ _ projected tail _ =>
      ⟨scope, binder, payload, projected⟩ :: tail.bindings
  | .assigning _ _ _ tail _ | .assigned _ _ _ tail _ _ | .projectedAssigned _ _ _ tail _ _ | .bitNotting _ _ _ tail _ | .bitNotted _ _ _ tail _ _ | .projectedBitNotted _ _ _ tail _ _ | .discard _ _ _ _ _ tail | .valueDiscard _ _ _ _ _ _ tail | .matching _ _ _ _ tail => tail.bindings
  | .block _ _ inner tail => inner.bindings ++ tail.bindings
  | .conditional _ _ _ _ _ left right tail => left.bindings ++ right.bindings ++ tail.bindings
  | .matched _ _ receipt branches tail =>
      receipt.requests.attach.flatMap (fun request => (branches request.val request.property).bindings) ++ tail.bindings
  | .whileLoop _ _ _ _ _ _ inner tail => inner.bindings ++ tail.bindings
  | .forLoop _ _ _ _ _ _ initial inner after tail => initial.bindings ++ inner.bindings ++ after.bindings ++ tail.bindings

/-- A refined tree exposes every supported assignment RHS from its actual callback. -/
def Tree.Ready {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Prop :=
  match tree with
  | .nil | .returning .. | .returnUnit .. | .boundary .. | .forBoundary .. | .breaking .. | .continuing .. | .tailValue .. => True
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ | .assigned _ _ _ tail _ _ | .projectedAssigned _ _ _ tail _ _ | .bitNotted _ _ _ tail _ _ | .projectedBitNotted _ _ _ tail _ _ => tail.Ready
  | @Tree.assigning _ _ _ _ _ _ _ _ _ _ _ _ assignment operator _ _ _ _ _ _ tail _ =>
      ¬ ValueAssignable source assignment operator ∧ tail.Ready
  | @Tree.bitNotting _ _ _ _ _ _ _ _ _ _ _ _ assignment _ _ _ _ _ tail _ =>
      ¬ UnaryAssignable source assignment ∧ tail.Ready
  | .discard _ _ _ _ _ tail | .valueDiscard _ _ _ _ _ _ tail => tail.Ready
  | .block _ _ inner tail => inner.Ready ∧ tail.Ready
  | .conditional _ _ _ _ _ left right tail => left.Ready ∧ right.Ready ∧ tail.Ready
  | .matching .. => False
  | .matched _ _ receipt branches tail => (∀ request member, (branches request member).Ready) ∧ tail.Ready
  | .whileLoop _ _ _ _ _ _ inner tail => inner.Ready ∧ tail.Ready
  | .forLoop _ _ _ _ _ _ initial inner after tail => initial.Ready ∧ inner.Ready ∧ after.Ready ∧ tail.Ready

/-- The profile identifies the actual callback. Unsupported original writes
keep their complete action and suffix in the returned tree. -/
theorem Tree.accepted {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements
      result reasonAt mode escaped = .ok code := by
  induction tree with
  | nil => simp [SourceCoreLoops.lowerFlowStatementsWithPolicy]
  | breaking read form statementType | continuing read form statementType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        bind, Except.bind, pure, Except.pure]
  | returning read form statementType child generated childType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        generated, childType, bind, Except.bind, pure, Except.pure]
  | returnUnit read form statementType unitType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        unitType, bind, Except.bind, pure, Except.pure]
  | tailValue read form child generated statementType childType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        generated, childType, bind, Except.bind, pure, Except.pure]
  | valueDiscard read form notTail child generated statementType _ ih =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, notTail,
        generated, statementType, ih, bind, Except.bind, pure, Except.pure]
  | initialized read form statementType projected child generated childType _ allocated ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        projected, generated, childType, ih, bind, Except.bind, pure, Except.pure] using allocated
  | absent read form statementType projected _ allocated ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        projected, ih, bind, Except.bind, pure, Except.pure] using allocated
  | assigning read form statementType _ assigned ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        ih, bind, Except.bind, pure, Except.pure] using assigned
  | assigned read form statementType _ receipt _ ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        ih, bind, Except.bind, pure, Except.pure] using receipt.accepted
  | projectedAssigned read form statementType _ receipt route ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        ih, bind, Except.bind, pure, Except.pure] using receipt.accepted
  | bitNotting _ _ _ _ accepted _ => exact accepted
  | bitNotted read form statementType _ receipt _ ih =>
      simpa only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        receipt.selected, ih, bind, Except.bind] using receipt.accepted
  | projectedBitNotted read form statementType _ receipt _ ih =>
      simpa only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        receipt.callbackSelected, ih, bind, Except.bind] using receipt.accepted
  | discard read form child generated statementType _ ih =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, generated, statementType,
        ih, bind, Except.bind, pure, Except.pure]
  | block read form _ _ innerIH tailIH =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, innerIH, tailIH,
        bind, Except.bind, pure, Except.pure]
  | @conditional _ _ _ _ _ _ _ _ _ _ elseBody _ _ _ read form child generated conditionType _ _ _ leftIH rightIH tailIH =>
      cases elseBody with
      | none =>
          simp only [Option.getD_none, SourceCoreLoops.lowerFlowStatementsWithPolicy, Except.ok.injEq] at rightIH
          cases rightIH
          simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, generated, conditionType,
            leftIH, tailIH, bind, Except.bind, pure, Except.pure]
      | some statements =>
          simp only [Option.getD_some] at rightIH
          simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, generated, conditionType,
            leftIH, rightIH, tailIH, bind, Except.bind, pure, Except.pure]
  | matching read form selected accepted _ tailIH =>
      unfold AcceptedNamedMatchFlow.bodyCallback at accepted
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, selected,
        accepted, tailIH, bind, Except.bind, pure, Except.pure]
  | matched read form receipt branches remaining branchIH tailIH =>
      have accepted := receipt.accepted
      unfold AcceptedNamedMatchFlow.bodyCallback at accepted
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, receipt.selected,
        accepted, tailIH, bind, Except.bind, pure, Except.pure]
  | whileLoop read form statementType child generated conditionType _ _ innerIH tailIH =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        generated, conditionType, innerIH, tailIH, bind, Except.bind, pure, Except.pure]
  | @forLoop mode escaped fuel scope id rest node stored initializer condition post body loopScope postScope
      loopCode postCode initialCode tail read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType, bind, Except.bind]
      change (do
        let loop ← SourceCoreLoops.lowerForItems policy (.occurrence id.occurrence) fuel source scope initializer result reasonAt
          (forNext policy source (.occurrence id.occurrence) result reasonAt escaped fuel condition body post)
        let next ← SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope rest result reasonAt mode escaped
        pure (LocalLoop.sequence result loop next)) = .ok (LocalLoop.sequence result initialCode tail)
      rw [initial.accepted]
      simp only [bind, Except.bind]
      rw [tailIH]
      rfl
  | forBoundary _ _ _ accepted => exact accepted
  | boundary _ _ accepted => exact accepted

theorem Tree.refine {values : SourceCoreCompatibleValues.Context}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missing)
    {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    (unary : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing)
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy compilation)
    {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    ∃ refined : Tree policy source result reasonAt mode escaped fuel scope statements code, refined.Ready := by
  classical
  induction fuel using Nat.strongRecOn generalizing mode scope statements code with
  | ind fuel ih =>
    cases tree with
    | nil => exact ⟨.nil, True.intro⟩
    | breaking read form statementType => exact ⟨.breaking read form statementType, True.intro⟩
    | continuing read form statementType => exact ⟨.continuing read form statementType, True.intro⟩
    | returning read form statementType child generated childType =>
        exact ⟨.returning read form statementType child generated childType, True.intro⟩
    | returnUnit read form statementType unitType =>
        exact ⟨.returnUnit read form statementType unitType, True.intro⟩
    | tailValue read form child generated statementType childType =>
        exact ⟨.tailValue read form child generated statementType childType, True.intro⟩
    | valueDiscard read form notTail child generated statementType remaining =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.valueDiscard read form notTail child generated statementType tail, ready⟩
    | initialized read form statementType projected child generated childType remaining allocated =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.initialized read form statementType projected child generated childType tail allocated, ready⟩
    | absent read form statementType projected remaining allocated =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.absent read form statementType projected tail allocated, ready⟩
    | @assigning mode escaped fuel scope id rest node stored assignment operator expression tail code
        read form statementType remaining assigned =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        by_cases supported : Assignable source assignment operator
        · obtain ⟨profile, bare, target⟩ := supported
          obtain ⟨receipt⟩ := AcceptedBareAssignmentReceipt.of_accepted matched profile bare assigned
          exact ⟨.assigned read form statementType tail receipt (target receipt.binder receipt.declaration), ready⟩
        · by_cases projected : ProjectedAssignable source assignment operator
          · obtain ⟨receipt⟩ := AcceptedProjectedAssignmentReceipt.of_accepted matched projected.1 projected.2.1 assigned
            exact ⟨.projectedAssigned read form statementType tail receipt (projected.2.2 receipt.binder receipt.description.binding), ready⟩
          · exact ⟨.assigning read form statementType tail assigned,
              (fun eligible => eligible.elim supported projected), ready⟩
    | assigned read form statementType remaining receipt targetType =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.assigned read form statementType tail receipt targetType, ready⟩
    | projectedAssigned read form statementType remaining receipt route =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.projectedAssigned read form statementType tail receipt route, ready⟩
    | @bitNotting mode escaped fuel scope id rest node stored assignment body code
        read form statementType remaining assigned =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        by_cases supported : BitNotAssignable source assignment
        · obtain ⟨profile, bare, target⟩ := supported
          have lowered := assigned
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
            unary, remaining.accepted, bind, Except.bind] at lowered
          obtain ⟨receipt⟩ := AcceptedBareBitNotReceipt.of_accepted unary profile bare unary lowered
          exact ⟨.bitNotted read form statementType tail receipt (target receipt.binder receipt.declaration), ready⟩
        · by_cases projected : ProjectedBitNotAssignable source assignment
          · have lowered := assigned
            simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
              unary, remaining.accepted, bind, Except.bind] at lowered
            obtain ⟨receipt⟩ := AcceptedProjectedBitNotReceipt.of_accepted unary projected.1 projected.2.1 unary lowered
            exact ⟨.projectedBitNotted read form statementType tail receipt
              (projected.2.2 receipt.binder receipt.description.binding), ready⟩
          · exact ⟨.bitNotting read form statementType tail assigned,
              (fun eligible => eligible.elim supported projected), ready⟩
    | bitNotted read form statementType remaining receipt targetType =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.bitNotted read form statementType tail receipt targetType, ready⟩
    | projectedBitNotted read form statementType remaining receipt route =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.projectedBitNotted read form statementType tail receipt route, ready⟩
    | discard read form child generated statementType remaining =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.discard read form child generated statementType tail, ready⟩
    | block read form inner remaining =>
        obtain ⟨inner, innerReady⟩ := ih _ (Nat.lt_succ_self _) inner
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.block read form inner tail, innerReady, tailReady⟩
    | conditional read form child generated conditionType left right remaining =>
        obtain ⟨left, leftReady⟩ := ih _ (Nat.lt_succ_self _) left
        obtain ⟨right, rightReady⟩ := ih _ (Nat.lt_succ_self _) right
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.conditional read form child generated conditionType left right tail, leftReady, rightReady, tailReady⟩
    | @matching _ _ childFuel _ _ _ _ _ _ _ _ _ read form selected accepted remaining =>
        obtain ⟨receipt⟩ := AcceptedNamedMatchFlow.of_accepted matchPolicy selected accepted
        have each : ∀ request ∈ receipt.requests, ∃ refined :
            Tree policy source result reasonAt false escaped childFuel request.scope request.statements request.code,
            refined.Ready := by
          intro request member
          obtain ⟨raw⟩ := of_accepted (receipt.bodies request member)
          exact ih _ (Nat.lt_succ_self _) raw
        let branches := fun request member => Classical.choose (each request member)
        have branchesReady := fun request member => Classical.choose_spec (each request member)
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.matched read form receipt branches tail, branchesReady, tailReady⟩
    | matched read form receipt branches remaining =>
        have each := fun request member => ih _ (Nat.lt_succ_self _) (branches request member)
        let refined := fun request member => Classical.choose (each request member)
        have branchesReady := fun request member => Classical.choose_spec (each request member)
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.matched read form receipt refined tail, branchesReady, tailReady⟩
    | whileLoop read form statementType child generated conditionType inner remaining =>
        obtain ⟨inner, innerReady⟩ := ih _ (Nat.lt_succ_self _) inner
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.whileLoop read form statementType child generated conditionType inner tail, innerReady, tailReady⟩
    | forLoop read form statementType child generated conditionType initial inner after remaining =>
        obtain ⟨initial, initialReady⟩ := initial.refine matched unary
        obtain ⟨inner, innerReady⟩ := ih _ (Nat.lt_succ_self _) inner
        obtain ⟨after, afterReady⟩ := after.refine matched unary
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.forLoop read form statementType child generated conditionType initial inner after tail,
          initialReady, innerReady, afterReady, tailReady⟩
    | forBoundary read form outside accepted => exact ⟨.forBoundary read form outside accepted, True.intro⟩
    | boundary read outside accepted => exact ⟨.boundary read outside accepted, True.intro⟩

/-- A remaining compiler branch, retaining its exact action and local scope. -/
inductive Boundary (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (result : Ty) (reasonAt : ExpressionId → Word) : Bool → Word → Type where
  | fallthrough {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope []
        result reasonAt mode escaped = .ok (LocalLoop.fallthrough result)) :
      Boundary policy source result reasonAt mode escaped
  | statement {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (node : StatementNode) (stored : Ty) (code : Expr)
      (read : policy.readStatement source id = .ok (node, stored))
      (outside : expanded node.form = false)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped

  | tailExpression {escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (code : Expr)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        [id] result reasonAt true escaped = .ok code) :
      Boundary policy source result reasonAt true escaped

  | valueExpression {escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (code : Expr)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt true escaped = .ok code) :
      Boundary policy source result reasonAt true escaped
  | assignment {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (code : Expr)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped
  | conditionalType {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (node : StatementNode) (stored : Ty) (code : Expr)
      (read : policy.readStatement source id = .ok (node, stored))
      (notUnit : node.type ≠ .unit)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped
  | header {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (code : Expr)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped
  | matchCallback {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (code : Expr)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped
  | nested {mode escaped} (boundary : Boundary policy source result reasonAt false escaped) :
      Boundary policy source result reasonAt mode escaped

theorem Tree.frontier {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (openBranch : tree.closed = false) : Nonempty (Boundary policy source result reasonAt mode escaped) := by
  induction tree with
  | @nil _ _ actualFuel actualScope => exact ⟨.fallthrough actualFuel actualScope (by simp [SourceCoreLoops.lowerFlowStatementsWithPolicy])⟩
  | returning | returnUnit | breaking | continuing => cases openBranch
  | initialized _ _ _ _ _ _ _ _ _ ih | absent _ _ _ _ _ _ ih => exact ih openBranch
  | assigning read form statementType remaining assigned ih =>
      exact ⟨.assignment _ _ _ _ _ (Tree.assigning read form statementType remaining assigned).accepted⟩
  | assigned _ _ _ _ _ _ ih | projectedAssigned _ _ _ _ _ _ ih | bitNotted _ _ _ _ _ _ ih | projectedBitNotted _ _ _ _ _ _ ih => exact ih openBranch
  | bitNotting read form statementType remaining accepted ih =>
      exact ⟨.assignment _ _ _ _ _ accepted⟩
  | discard _ _ _ _ _ _ ih => exact ih openBranch
  | @valueDiscard actualMode _ _ _ _ _ _ _ _ _ read form notTail child generated statementType remaining ih =>
    cases actualMode with
    | false => exact ih openBranch
    | true => exact ⟨.valueExpression _ _ _ _ _
        (Tree.valueDiscard read form notTail child generated statementType remaining).accepted⟩
  | tailValue read form child generated statementType childType =>
      exact ⟨.tailExpression _ _ _ _ (Tree.tailValue read form child generated statementType childType).accepted⟩
  | block read form inner remaining innerIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with innerOpen | tailOpen
      · obtain ⟨boundary⟩ := innerIH innerOpen
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | conditional read form child generated conditionType left right remaining leftIH rightIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with (leftOpen | rightOpen) | tailOpen
      · obtain ⟨boundary⟩ := leftIH leftOpen
        exact ⟨.nested boundary⟩
      · obtain ⟨boundary⟩ := rightIH rightOpen
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | matching read form selected accepted remaining tailIH =>
      exact ⟨.matchCallback _ _ _ _ _ (Tree.matching read form selected accepted remaining).accepted⟩
  | matched read form receipt branches remaining branchIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with branchOpen | tailOpen
      · have existsOpen : ∃ request : { request // request ∈ receipt.requests },
            (branches request.val request.property).closed = false := by
          classical
          apply Classical.byContradiction
          intro missing
          have allClosed : ∀ request : { request // request ∈ receipt.requests },
              (branches request.val request.property).closed = true := by
            intro request
            cases same : (branches request.val request.property).closed with
            | false => exact False.elim (missing ⟨request, same⟩)
            | true => rfl
          have accepted : receipt.requests.attach.all (fun request => (branches request.val request.property).closed) = true :=
            List.all_eq_true.mpr (fun request _ => allClosed request)
          rw [accepted] at branchOpen
          cases branchOpen
        obtain ⟨request, failed⟩ := existsOpen
        obtain ⟨boundary⟩ := branchIH request.val request.property failed
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with innerOpen | tailOpen
      · obtain ⟨boundary⟩ := innerIH innerOpen
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with ((initialOpen | innerOpen) | afterOpen) | tailOpen
      · exact ⟨.header _ _ _ _ _ (Tree.forLoop read form statementType child generated conditionType initial inner after remaining).accepted⟩
      · obtain ⟨boundary⟩ := innerIH innerOpen
        exact ⟨.nested boundary⟩
      · exact ⟨.header _ _ _ _ _ (Tree.forLoop read form statementType child generated conditionType initial inner after remaining).accepted⟩
      · exact tailIH tailOpen
  | forBoundary read form outside accepted => exact ⟨.header _ _ _ _ _ accepted⟩
  | boundary read outside accepted => exact ⟨.statement _ _ _ _ _ _ _ read outside accepted⟩

theorem Body.accepted {escaped fellThrough : Word} {fuel scope statements code}
    (body : Body policy fuel source scope statements result reasonAt fellThrough escaped code) :
    SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements result
      reasonAt fellThrough escaped = .ok code := by
  rw [body.emitted]
  unfold SourceCoreLoops.lowerStatementsWithPolicy
  rw [body.tree.accepted]
  rfl

/-- The residual is indexed by the complete accepted body, so a frontier
from an unrelated source position cannot satisfy this alternative. -/
structure Incomplete (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId) (result : Ty)
    (reasonAt : ExpressionId → Word) (fellThrough escaped : Word) (code : Expr) where
  body : Body policy fuel source scope statements result reasonAt fellThrough escaped code
  openBranch : body.tree.closed = false

theorem Incomplete.frontier {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Incomplete policy fuel source scope statements result reasonAt fellThrough escaped code) :
    Nonempty (Boundary policy source result reasonAt true escaped) :=
  receipt.body.tree.frontier receipt.openBranch

/-- The exact named policy keeps the original full ledger, parents, local
specializations, diagnostics and callable context of the accepted action. -/
def namedPolicy {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : CallableIndexedNamedGeneration.Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (parents : List SourceCoreLocalEvidence.Prepared)
    (own : SourceCoreProgramFaultSites.Function) : SourceCoreLoops.Policy :=
  let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
  { actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
      own.assignments diagnostics named.signature.key
      (SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
        (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none) with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }

/-- This endpoint starts at the actual sealed named compilation receipt. -/
theorem of_compilation {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked}
    {named : CallableIndexedNamedGeneration.Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    Nonempty (Body (namedPolicy prepared named diagnostics compilation.parents compilation.own)
      prepared.fuel (CallableIndexedNamedGeneration.source named)
      (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) compilation.statements
      named.signature.resultType (diagnostics.reasonAt named.signature.key)
      compilation.own.fellThroughReason compilation.own.table.escapedReason compilation.body) :=
  body_of_accepted compilation.bodyCompiled

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
end
