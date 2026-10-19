import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed

/-! A genuine nonempty method requirement list excludes primitive operation
rules. The remaining traces retain the actual selected dictionary and body,
including operand faults, parameter allocation and exact strict child grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceInversion
open Frontend SourceInference Staging.Recursive
open Solcore.SourceSemantics.Dynamic

inductive UnaryTrace (program : Program) (registry : Registry) (scope : Scope)
    (context : Context) (environment : Dynamic.Environment) (before : Heap)
    (operator : Syntax.UnaryOp) (operand : ExpressionId) (requirements : List RequirementId) :
    Nat → Outcome → Heap → Prop where
  | operandFault {operandSize after failure}
      (operandTrace : Size.Expression program registry operandSize scope context environment before operand (.fault failure) after) :
      UnaryTrace program registry scope context environment before operator operand requirements
        (Size.stepSize [operandSize]) (.fault failure) after
  | method {operandSize bodySize argumentsHeap bound after input traitName methodName bodyInstance dictionary
      roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
      (dispatch : UnaryTraitDispatch operator traitName methodName)
      (selection : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
      (operandTrace : Size.Expression program registry operandSize scope context environment before operand (.value input) argumentsHeap)
      (rootsEq : StatementRoots bodyInstance.source.roots roots)
      (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
      (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
      (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [input] bodyEnvironment bound)
      (body : Size.StatementsIn program registry true bodySize child bodyContext bodyEnvironment bound roots finalContext outcome after)
      (resultRule : BodyResult bodyInstance.resultType outcome result) :
      UnaryTrace program registry scope context environment before operator operand requirements
        (Size.stepSize [operandSize, bodySize]) result after

inductive BinaryTrace (program : Program) (registry : Registry) (scope : Scope)
    (context : Context) (environment : Dynamic.Environment) (before : Heap)
    (left : ExpressionId) (operator : Syntax.BinaryOp) (right : ExpressionId) (requirements : List RequirementId) :
    Nat → Outcome → Heap → Prop where
  | leftFault {leftSize after failure}
      (first : Size.Expression program registry leftSize scope context environment before left (.fault failure) after) :
      BinaryTrace program registry scope context environment before left operator right requirements
        (Size.stepSize [leftSize]) (.fault failure) after
  | rightFault {leftSize rightSize middle after input failure}
      (first : Size.Expression program registry leftSize scope context environment before left (.value input) middle)
      (continues : EvaluatesRightOperand operator input)
      (second : Size.Expression program registry rightSize scope context environment middle right (.fault failure) after) :
      BinaryTrace program registry scope context environment before left operator right requirements
        (Size.stepSize [leftSize, rightSize]) (.fault failure) after
  | method {leftSize rightSize bodySize middle argumentsHeap bound after a b traitName methodName bodyInstance dictionary
      roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
      (dispatch : BinaryTraitDispatch operator traitName methodName)
      (selection : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
      (first : Size.Expression program registry leftSize scope context environment before left (.value a) middle)
      (continues : EvaluatesRightOperand operator a)
      (second : Size.Expression program registry rightSize scope context environment middle right (.value b) argumentsHeap)
      (rootsEq : StatementRoots bodyInstance.source.roots roots)
      (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
      (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
      (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [a, b] bodyEnvironment bound)
      (body : Size.StatementsIn program registry true bodySize child bodyContext bodyEnvironment bound roots finalContext outcome after)
      (resultRule : BodyResult bodyInstance.resultType outcome result) :
      BinaryTrace program registry scope context environment before left operator right requirements
        (Size.stepSize [leftSize, rightSize, bodySize]) result after

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Heap}
  {id : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

private theorem occurrence_requirements {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : node.requirements = requirements := by
  obtain ⟨actualNode, contains, _, actualRequirements, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact (congrArg ExpressionNode.requirements same).symm.trans actualRequirements

theorem requirements_nonempty {caller : EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : BodyInstance} {dictionary : EvidenceEnvironment}
    (selected : OperatorMethodSelected program context caller traitName methodName requirements body dictionary) :
    requirements ≠ [] := by
  cases selected
  simp

theorem unary {operator : Syntax.UnaryOp} {operand : ExpressionId}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .unary operator operand) (nonempty : node.requirements ≠ [])
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    UnaryTrace program registry invocation context environment before operator operand node.requirements size outcome after := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .unary operator operand :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | unaryOperandFault occurrence operandTrace =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      exact .operandFault operandTrace
  | unaryMethod occurrence dispatch selection operandTrace rootsEq selected parameters allocate body resultRule =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      rw [← occurrence_requirements unique found occurrence] at selection
      exact .method dispatch selection operandTrace rootsEq selected parameters allocate body resultRule
  | unary occurrence _ _ | unaryInvalid occurrence _ _ =>
      exact False.elim (nonempty (occurrence_requirements unique found occurrence))
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | tupleValue occurrence _ _ | tupleFault occurrence _ | constructorValue occurrence _ _ | constructorFault occurrence _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

theorem binary {left right : ExpressionId} {operator : Syntax.BinaryOp}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .binary left operator right) (nonempty : node.requirements ≠ [])
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    BinaryTrace program registry invocation context environment before left operator right node.requirements size outcome after := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .binary left operator right :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | binaryLeftFault occurrence first =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      exact .leftFault first
  | binaryRightFault occurrence first continues second =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      exact .rightFault first continues second
  | binaryMethod occurrence dispatch selection first continues second rootsEq selected parameters allocate body resultRule =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      rw [← occurrence_requirements unique found occurrence] at selection
      exact .method dispatch selection first continues second rootsEq selected parameters allocate body resultRule
  | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _ | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ =>
      exact False.elim (nonempty (occurrence_requirements unique found occurrence))
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | tupleValue occurrence _ _ | tupleFault occurrence _ | constructorValue occurrence _ _ | constructorFault occurrence _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceInversion
