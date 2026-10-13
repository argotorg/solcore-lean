import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds

/-! Original staged operator children retain independent grades, both fault
kinds, and the exact heap reached before a second operand or chosen branch. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorSourceBounds
open Core Frontend SourceInference GeneralHeap CompatiblePayload CoreProof
open CompatibleExpressionPrimitives
inductive UnaryTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (operand : ExpressionId) (operator : Syntax.UnaryOp) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | value {childSize input output after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before operand (.value input) after)
      (applies : Dynamic.UnaryPrimitiveApplies operator input output)
      (childSizeSmaller : childSize < size) : UnaryTrace program size context registry invocation environment before operand operator (.value output) after
  | fault {childSize reason after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before operand (.fault reason) after)
      (childSizeSmaller : childSize < size) :
      UnaryTrace program size context registry invocation environment before operand operator (.fault reason) after
  | invalid {childSize input after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before operand (.value input) after)
      (invalid : Dynamic.UnaryPrimitiveOperandInvalid operator input)
      (childSizeSmaller : childSize < size) :
      UnaryTrace program size context registry invocation environment before operand operator
        (.fault (.semantic (.invalidUnaryOperand operator))) after


inductive BinaryTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) (operator : Syntax.BinaryOp) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | leftFault {childSize reason after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before left (.fault reason) after)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.fault reason) after
  | leftInvalid {childSize input after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before left (.value input) after)
      (invalid : Dynamic.BinaryLeftOperandInvalid operator input)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.fault (.semantic (.invalidBinaryOperands operator))) after
  | short {childSize input output after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before left (.value input) after)
      (circuit : Dynamic.ShortCircuits operator input output)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.value output) after
  | rightFault {firstSize secondSize input reason middle after}
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context environment before left (.value input) middle)
      (continues : Dynamic.EvaluatesRightOperand operator input)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context environment middle right (.fault reason) after)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.fault reason) after
  | value {firstSize secondSize a b output middle after}
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context environment before left (.value a) middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context environment middle right (.value b) after)
      (applies : Dynamic.BinaryPrimitiveApplies operator a b output)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.value output) after
  | invalid {firstSize secondSize a b middle after}
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context environment before left (.value a) middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context environment middle right (.value b) after)
      (invalid : Dynamic.BinaryPrimitiveOperandsInvalid operator a b)
      (firstSizeSmaller : firstSize < size) (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator
        (.fault (.semantic (.invalidBinaryOperands operator))) after


inductive ConditionalTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition thenId elseId : ExpressionId) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | fault {childSize reason after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before condition (.fault reason) after)
      (childSizeSmaller : childSize < size) :
      ConditionalTrace program size context registry invocation environment before condition thenId elseId (.fault reason) after
  | branch {childSize branchSize flag middle outcome after}
      (conditionTrace : Staging.Recursive.Size.Expression program registry childSize invocation context environment before condition (.value (.bool flag)) middle)
      (branchTrace : Staging.Recursive.Size.Expression program registry branchSize invocation context environment middle
        (if flag then thenId else elseId) outcome after)
      (childSizeSmaller : childSize < size)
      (branchSizeSmaller : branchSize < size) :
      ConditionalTrace program size context registry invocation environment before condition thenId elseId outcome after

variable {checked : SourceCoreCompatibleCatalog.Checked} {program : Program}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {id : ExpressionId} {node : ExpressionNode}
  {type : Ty} {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Staging.Recursive.Outcome}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Staging.Recursive.Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

private theorem occurrence_requirements {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Staging.Recursive.Occurrence invocation id actualForm requirements) : node.requirements = requirements := by
  obtain ⟨actualNode, contains, _, actualRequirements, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact (congrArg ExpressionNode.requirements same).symm.trans actualRequirements

theorem unary_inv {operator : Syntax.UnaryOp} {operand : ExpressionId}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .unary operator operand) (unique : NodeOccurrencesUnique invocation.source)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after) :
    UnaryTrace program size context registry invocation environment before operand operator outcome after := by
  have actual : ∀ {actualForm requirements}, Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .unary operator operand :=
    fun occurrence => (occurrence_form unique metadata.found occurrence).trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      rw [same, form] at atomic
      cases atomic
  | unaryMethod occurrence _ selected _ _ _ _ _ _ _ =>
      have empty := (occurrence_requirements unique metadata.found occurrence).symm.trans metadata.requirements
      rw [empty] at selected
      cases selected
  | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _ => cases actual occurrence
  | unary occurrence child applied =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      refine .value child applied ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | unaryOperandFault occurrence child =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      refine .fault child ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | unaryInvalid occurrence child invalid =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      refine .invalid child invalid ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

theorem binary_inv {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .binary left operator right) (unique : NodeOccurrencesUnique invocation.source)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after) :
    BinaryTrace program size context registry invocation environment before left right operator outcome after := by
  have actual : ∀ {actualForm requirements}, Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .binary left operator right :=
    fun occurrence => (occurrence_form unique metadata.found occurrence).trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      rw [same, form] at atomic
      cases atomic
  | binaryMethod occurrence _ selected _ _ _ _ _ _ _ _ _ =>
      have empty := (occurrence_requirements unique metadata.found occurrence).symm.trans metadata.requirements
      rw [empty] at selected
      cases selected
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ => cases actual occurrence
  | binaryLeftFault occurrence child =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .leftFault child ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binaryLeftInvalid occurrence child invalid =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .leftInvalid child invalid ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binaryShortCircuit occurrence child circuit =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .short child circuit ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binaryRightFault occurrence first continues second =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .rightFault first continues second ?_ ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binary occurrence first continues second applied =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .value first continues second applied ?_ ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binaryInvalid occurrence first continues second invalid =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .invalid first continues second invalid ?_ ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _ | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _ | conditional occurrence _ _ | conditionalFault occurrence _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

theorem conditional_inv {condition thenId elseId : ExpressionId}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .conditional condition thenId elseId) (unique : NodeOccurrencesUnique invocation.source)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after) :
    ConditionalTrace program size context registry invocation environment before condition thenId elseId outcome after := by
  have actual : ∀ {actualForm requirements}, Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .conditional condition thenId elseId :=
    fun occurrence => (occurrence_form unique metadata.found occurrence).trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      rw [same, form] at atomic
      cases atomic
  | conditional occurrence first second =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (actual occurrence)
      refine .branch first second ?_ ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | conditionalFault occurrence child =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (actual occurrence)
      refine .fault child ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _ | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorSourceBounds
