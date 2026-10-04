import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCallRequirementLayouts
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRequirementSafety
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectionIdentity

/-! Original source children of prepared operators retain their own sizes,
ordered intermediate heaps and independently selected method dictionary.
The ordered view below stores each original child. It does not identify the
size of a synthetic argument-list derivation with the raw operator size. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds
open Core Frontend SourceInference

/-- The original raw form judgment, before the original output-coercion path. -/
def RawOutcomeAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (node : ExpressionNode) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value value => SourceExecutionSize.ExpressionFormEvaluates program size context evidence source environment before
      node.form node.requirements node.coercions value after
  | .fault reason => SourceExecutionSize.ExpressionFormFaults program size context evidence source environment before
      node.form node.requirements node.coercions reason after

def PathAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap) (steps : List CoercionStep)
    (value : Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value result => SourceExecutionSize.CoercionPathExecutes program size context evidence before steps value result after
  | .fault reason => SourceExecutionSize.CoercionPathFaults program size context evidence before steps value reason after

theorem RawOutcomeAt.sound {program size context evidence source environment before node outcome after}
    (raw : RawOutcomeAt program size context evidence source environment before node outcome after) :
    CallableCoercionExpressionMeaning.RawOutcome program context evidence source environment before node outcome after := by
  cases outcome with
  | value value => exact SourceExecutionSize.ExpressionFormEvaluates.sound raw
  | fault reason => exact SourceExecutionSize.ExpressionFormFaults.sound raw

theorem PathAt.sound {program size context evidence before steps value outcome after}
    (path : PathAt program size context evidence before steps value outcome after) :
    CallableCoercionExpressionMeaning.Path program context evidence before steps value outcome after := by
  cases outcome with
  | value result => exact SourceExecutionSize.CoercionPathExecutes.sound path
  | fault reason => exact SourceExecutionSize.CoercionPathFaults.sound path

/-- Each leaf is the original operand derivation, with its own strict bound. -/
inductive ArgumentsAt (program : Program) (budget : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment) :
    Dynamic.Heap → List ExpressionId → List Dynamic.Value → Dynamic.Heap → Prop where
  | nil {heap} : ArgumentsAt program budget context evidence source environment heap [] [] heap
  | cons {size before middle after id ids value values}
      (head : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id value middle)
      (strict : size < budget)
      (tail : ArgumentsAt program budget context evidence source environment middle ids values after) :
      ArgumentsAt program budget context evidence source environment before (id :: ids) (value :: values) after

inductive ArgumentsFaultAt (program : Program) (budget : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment) :
    Dynamic.Heap → List ExpressionId → Dynamic.SemanticFault → Dynamic.Heap → Prop where
  | head {size before after id ids reason}
      (failed : SourceExecutionSize.ExpressionFaults program size context evidence source environment before id reason after)
      (strict : size < budget) : ArgumentsFaultAt program budget context evidence source environment before (id :: ids) reason after
  | tail {size before middle after id ids value reason}
      (head : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id value middle)
      (strict : size < budget)
      (tail : ArgumentsFaultAt program budget context evidence source environment middle ids reason after) :
      ArgumentsFaultAt program budget context evidence source environment before (id :: ids) reason after

/-- The body uses the source-selected dictionary at the original body size. -/
inductive RawTraceAt (program : Program) (budget : Nat) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (ids : List ExpressionId) (body : Dynamic.BodyInstance) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentFault {reason after}
      (failed : ArgumentsFaultAt program budget context caller source environment before ids reason after) :
      RawTraceAt program budget context caller invocation source environment before ids body (.fault reason) after
  | apply {bodySize arguments middle outcome after}
      (argumentsEvaluated : ArgumentsAt program budget context caller source environment before ids arguments middle)
      (called : RecursiveNamedCallBounds.BodyOutcome program bodySize body invocation middle arguments outcome after)
      (bodyStrict : bodySize < budget) :
      RawTraceAt program budget context caller invocation source environment before ids body outcome after

theorem ArgumentsAt.sound {program budget context evidence source environment before ids values after}
    (trace : ArgumentsAt program budget context evidence source environment before ids values after) :
    Dynamic.ExpressionsEvaluate program context evidence source environment before ids values after := by
  induction trace with
  | nil => exact .nil
  | cons head _ _ ih => exact .cons head.sound ih

theorem ArgumentsFaultAt.sound {program budget context evidence source environment before ids reason after}
    (trace : ArgumentsFaultAt program budget context evidence source environment before ids reason after) :
    Dynamic.ExpressionsFault program context evidence source environment before ids reason after := by
  induction trace with
  | head failed _ => exact .head failed.sound
  | tail head _ _ ih => exact .tail head.sound ih

theorem RawTraceAt.sound {program budget context caller invocation source environment before ids body outcome after}
    (trace : RawTraceAt program budget context caller invocation source environment before ids body outcome after) :
    NamedCalls.Arguments.Trace program context caller invocation source environment before ids body outcome after := by
  cases trace with
  | argumentFault failed => exact .argumentFault failed.sound
  | apply arguments called _ =>
    cases called with
    | value invoked => exact .apply arguments.sound (.value invoked.sound)
    | fault failed => exact .apply arguments.sound (.fault failed.sound)

/-- Raw and suffix children are bounded by the same original whole judgment.
The intermediate value and heap remain distinct from the final result. -/
inductive TraceForAt (raw : Nat → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop)
    (path : Nat → Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop)
    (budget : Nat) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | rawFault {rawSize reason after} (trace : raw rawSize (.fault reason) after) (strict : rawSize < budget) :
      TraceForAt raw path budget (.fault reason) after
  | path {rawSize pathSize value middle outcome after}
      (rawTrace : raw rawSize (.value value) middle) (suffix : path pathSize middle value outcome after)
      (rawStrict : rawSize < budget) (pathStrict : pathSize < budget) : TraceForAt raw path budget outcome after

theorem TraceForAt.forget
    {raw : Nat → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
    {path : Nat → Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
    {plainRaw : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
    {plainPath : Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
    {budget outcome after}
    (rawSound : ∀ {size outcome after}, raw size outcome after → plainRaw outcome after)
    (pathSound : ∀ {size heap value outcome after}, path size heap value outcome after → plainPath heap value outcome after)
    (trace : TraceForAt raw path budget outcome after) :
    CallableCoercionExpressionMeaning.TraceFor plainRaw plainPath outcome after := by
  cases trace with
  | rawFault raw _ => exact .rawFault (rawSound raw)
  | path raw path _ _ => exact .path (rawSound raw) (pathSound path)

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

/-- Split the original whole witness without assigning new sizes to either
child. Missing and generalized-local cases are excluded by the actual node. -/
theorem raw_source_inv_sized {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (found : source.lookupExpression? id = some node) (unique : NodeOccurrencesUnique source)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    TraceForAt (fun child => RawOutcomeAt program child context evidence source environment before node)
      (fun child heap value => PathAt program child context evidence heap node.coercions value) size outcome after := by
  have contains := lookupExpression?_sound found
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro other raw path =>
      have same := contains_unique unique other contains
      subst same
      exact .path raw path (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))
    | generalizedLocal other form _ _ _ _ _ _ _ =>
      have same := contains_unique unique other contains
      subst same
      exact False.elim (notLocal _ _ form)
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form other raw =>
      exact .rawFault (contains_unique unique other contains ▸ raw) (SourceExecutionSize.child_lt_stepSize (by simp))
    | coercion other raw failed =>
      have same := contains_unique unique other contains
      subst same
      exact .path raw failed (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))
    | generalizedLocalRequirement other form _ _ _ _ _ _ _ | generalizedLocalCoercion other form _ _ _ _ _ _ _ =>
      have same := contains_unique unique other contains
      subst same
      exact False.elim (notLocal _ _ form)

section SourceInversion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableCoercionExpressionCertificates (Projector Specialized Lowered)

theorem unary_dispatch_unique {operator : Syntax.UnaryOp}
    {leftTrait leftMethod rightTrait rightMethod : String}
    (left : UnaryTraitDispatch operator leftTrait leftMethod)
    (right : UnaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod := by
  cases left <;> cases right
  exact ⟨rfl, rfl⟩

theorem binary_dispatch_valid_left {operator : Syntax.BinaryOp}
    {traitName methodName : String} {value : Dynamic.Value}
    (dispatch : BinaryTraitDispatch operator traitName methodName)
    (invalid : Dynamic.BinaryLeftOperandInvalid operator value) : False := by
  cases dispatch <;> cases invalid

theorem binary_dispatch_unique {operator : Syntax.BinaryOp}
    {leftTrait leftMethod rightTrait rightMethod : String}
    (left : BinaryTraitDispatch operator leftTrait leftMethod)
    (right : BinaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod := by
  cases left <;> cases right <;> exact ⟨rfl, rfl⟩

variable {checkedProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  {receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output}
  (selected : OperatorSource receipt)
  {program : Program} {context : SourceSemantics.Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
  {sourceBody : Dynamic.BodyInstance}
  (catalog : CallableCoercionSelectionIdentity.Catalog program)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  (selection : Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)

theorem owned_eq {owned : List RequirementId}
    (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned) :
    owned = receipt.requirements := by
  have original := CallableCallRequirementLayouts.ordinary_owned receipt.ordinary
  exact List.append_cancel_right (layout.symm.trans original)

include selected catalog ledger selection in
theorem same_body {otherBody : Dynamic.BodyInstance} {otherDictionary : Dynamic.EvidenceEnvironment}
    (actual : Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
      receipt.requirements otherBody otherDictionary) : otherBody = sourceBody := by
  have unique := CallableCoercionSelectionIdentity.primary_unique ledger selected.certificate.roots.primarySelected
  apply CallableCoercionSelectionIdentity.body_eq catalog unique
  · simpa only [selected.requirements] using actual
  · simpa only [selected.requirements] using selection

include selected ledger selection in
theorem requirement_safe {failed : RequirementId}
    (fault : Dynamic.RequirementListFaults context evidence receipt.requirements failed) : False := by
  apply CallableCoercionRequirementSafety.selected_safe_for ledger selected.certificate.roots
  · simpa only [selected.requirements] using selection
  · simpa only [selected.requirements] using fault

include selected catalog ledger selection in
/-- Reverse the original raw source outcome, preserving each actual source
dictionary. An argument fault retains the anchor selection without invoking it. -/
theorem OperatorSource.raw_inv_sized {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (raw : RawOutcomeAt program size context evidence source environment before node outcome after) :
    ∃ actualDictionary,
      Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
        receipt.requirements sourceBody actualDictionary ∧
      RawTraceAt program size context evidence actualDictionary source environment before
        receipt.arguments sourceBody outcome after := by
  have dispatch := selected.dispatch
  rcases receipt.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · simp only [form] at dispatch
    rw [arguments]
    cases outcome with
    | value value =>
      change SourceExecutionSize.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _ _ at raw
      rw [form] at raw
      cases raw with
      | unary layout operandEvaluated applied =>
        rw [owned_eq (receipt := receipt) layout] at applied
        rw [selected.requirements] at applied
        cases applied with
        | method actualDispatch actual invoked =>
          rw [← selected.requirements] at actual
          obtain ⟨sameTrait, sameMethod⟩ := unary_dispatch_unique dispatch actualDispatch
          cases sameTrait
          cases sameMethod
          cases same_body selected catalog ledger selection actual
          refine ⟨_, actual, .apply (.cons operandEvaluated ?_ .nil) (.value invoked) ?_⟩
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
    | fault reason =>
      change SourceExecutionSize.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _ _ at raw
      rw [form] at raw
      cases raw with
      | unaryOperand _ failed =>
        refine ⟨_, selection, .argumentFault (.head failed ?_)⟩
        all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
      | unaryApply layout operandEvaluated failed =>
        rw [owned_eq (receipt := receipt) layout] at failed
        rw [selected.requirements] at failed
        cases failed with
        | requirement fault => exact False.elim (requirement_safe selected ledger selection (by simpa only [selected.requirements] using fault))
        | method actualDispatch actual failed =>
          rw [← selected.requirements] at actual
          obtain ⟨sameTrait, sameMethod⟩ := unary_dispatch_unique dispatch actualDispatch
          cases sameTrait
          cases sameMethod
          cases same_body selected catalog ledger selection actual
          refine ⟨_, actual, .apply (.cons operandEvaluated ?_ .nil) (.fault failed) ?_⟩
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
  · simp only [form] at dispatch
    rw [arguments]
    cases outcome with
    | value value =>
      change SourceExecutionSize.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _ _ at raw
      rw [form] at raw
      cases raw with
      | binaryShortCircuit layout _ _ empty =>
        exact False.elim (receipt.nonempty ((owned_eq (receipt := receipt) layout).symm.trans empty))
      | binaryEvaluateRight layout leftEvaluated _ rightEvaluated applied =>
        rw [owned_eq (receipt := receipt) layout] at applied
        rw [selected.requirements] at applied
        cases applied with
        | method actualDispatch actual invoked =>
          rw [← selected.requirements] at actual
          obtain ⟨sameTrait, sameMethod⟩ := binary_dispatch_unique dispatch actualDispatch
          cases sameTrait
          cases sameMethod
          cases same_body selected catalog ledger selection actual
          refine ⟨_, actual, .apply (.cons leftEvaluated ?_ (.cons rightEvaluated ?_ .nil)) (.value invoked) ?_⟩
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
    | fault reason =>
      change SourceExecutionSize.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _ _ at raw
      rw [form] at raw
      cases raw with
      | binaryLeft _ failed =>
        refine ⟨_, selection, .argumentFault (.head failed ?_)⟩
        all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
      | binaryLeftOperand _ _ invalid => exact False.elim (binary_dispatch_valid_left dispatch invalid)
      | binaryRight _ leftEvaluated _ failed =>
        refine ⟨_, selection, .argumentFault (.tail leftEvaluated ?_ (.head failed ?_))⟩
        all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
      | binaryApply layout leftEvaluated _ rightEvaluated failed =>
        rw [owned_eq (receipt := receipt) layout] at failed
        rw [selected.requirements] at failed
        cases failed with
        | requirement fault => exact False.elim (requirement_safe selected ledger selection (by simpa only [selected.requirements] using fault))
        | method actualDispatch actual failed =>
          rw [← selected.requirements] at actual
          obtain ⟨sameTrait, sameMethod⟩ := binary_dispatch_unique dispatch actualDispatch
          cases sameTrait
          cases sameMethod
          cases same_body selected catalog ledger selection actual
          refine ⟨_, actual, .apply (.cons leftEvaluated ?_ (.cons rightEvaluated ?_ .nil)) (.fault failed) ?_⟩
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)


end SourceInversion

section SelectedWhole
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableCoercionExpressionCertificates (Projector Specialized Lowered)
variable {checkedProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  {receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output}
  (selected : OperatorSource receipt)
  {program : Program} {context : SourceSemantics.Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
  {sourceBody : Dynamic.BodyInstance}
  (catalog : CallableCoercionSelectionIdentity.Catalog program)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  (selection : Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)

include selected catalog ledger selection in
/-- The same selected body retains the source's actual dictionary, each original
operand/body child, and the original output-coercion path with its own size. -/
theorem OperatorSource.source_inv_sized {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (unique : NodeOccurrencesUnique source)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    TraceForAt
      (fun rawSize rawOutcome rawHeap => ∃ actualDictionary,
        Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
          receipt.requirements sourceBody actualDictionary ∧
        RawTraceAt program rawSize context evidence actualDictionary source environment before
          receipt.arguments sourceBody rawOutcome rawHeap)
      (fun pathSize heap value => PathAt program pathSize context evidence heap node.coercions value)
      size outcome after := by
  have notLocal : ∀ name binder, node.form ≠ .reference name (.local binder) := by
    intro name binder impossible
    rcases receipt.form with ⟨_, _, form, _⟩ | ⟨_, _, _, form, _⟩ <;> rw [form] at impossible <;> cases impossible
  cases raw_source_inv_sized receipt.found unique notLocal trace with
  | rawFault raw strict => exact .rawFault (OperatorSource.raw_inv_sized selected catalog ledger selection raw) strict
  | path raw path rawStrict pathStrict =>
    exact .path (OperatorSource.raw_inv_sized selected catalog ledger selection raw) path rawStrict pathStrict

end SelectedWhole

end Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds
