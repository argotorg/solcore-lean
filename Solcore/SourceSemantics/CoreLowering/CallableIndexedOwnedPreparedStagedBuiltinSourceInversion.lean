import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed

/-! Direct builtin calls execute their ordered argument vector and primitive.
Staging failures are inherited from those actual arguments. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinSourceInversion
open Frontend SourceInference Staging.Recursive

theorem source_types {source : TypedSource} {context : Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.builtinFunction function))
    (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ExpressionsHaveTypes source context ids function.parameterTypes ∧ node.type = function.returnType := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize rawEq : node.type = actualType at raw
    cases raw with
    | builtinCall _calleeValid argumentsTyped => exact ⟨argumentsTyped, rfl⟩

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id callee : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}
  {function : BuiltinFunctionId} {arguments : List ExpressionId}

private theorem occurrence_form {actualForm : ExpressionForm}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

theorem children
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.builtinFunction function))
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    (∃ sequenceSize invocationSize argumentsHeap values,
      size = Size.stepSize [sequenceSize, invocationSize] ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.values values) argumentsHeap ∧
      Size.Applies program registry invocationSize invocation context argumentsHeap
        (.builtin ⟨function⟩) values outcome after) ∨
    (∃ sequenceSize failure, size = Size.stepSize [sequenceSize] ∧
      outcome = .fault failure ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.fault failure) after) := by
  have actual : ∀ {actualForm}, Occurrence invocation id actualForm → actualForm = .call callee arguments (.builtinFunction function) :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | builtinApplied occurrence children applied =>
      obtain ⟨rfl, rfl, same⟩ := ExpressionForm.call.inj (actual occurrence)
      cases same
      exact .inl ⟨_, _, _, _, rfl, children, applied⟩
  | builtinArgumentsFault occurrence children =>
      obtain ⟨rfl, rfl, same⟩ := ExpressionForm.call.inj (actual occurrence)
      cases same
      exact .inr ⟨_, _, rfl, rfl, children⟩
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleValue occurrence _ _ | tupleFault occurrence _ | constructorValue occurrence _ _ | constructorFault occurrence _
  | unary occurrence _ _ | unaryOperandFault occurrence _
  | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _
  | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _
  | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinSourceInversion
