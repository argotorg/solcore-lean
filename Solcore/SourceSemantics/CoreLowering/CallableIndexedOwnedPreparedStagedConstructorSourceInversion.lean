import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed

/-! Original constructor traces retain the ordered argument sequence, its exact
heap, and the wrapper grade. Staging and semantic faults stay distinct. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorSourceInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}
  {instantiation : DataConstructorInstantiation} {arguments : List ExpressionId}

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
    (form : node.form = .constructor instantiation arguments)
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    (∃ sequenceSize values, size = Size.stepSize [sequenceSize] ∧
      outcome = .value (.constructed instantiation values) ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.values values) after) ∨
    (∃ sequenceSize failure, size = Size.stepSize [sequenceSize] ∧
      outcome = .fault failure ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.fault failure) after) := by
  have actual : ∀ {actualForm}, Occurrence invocation id actualForm → actualForm = .constructor instantiation arguments :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | constructorValue occurrence _valid children =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.constructor.inj (actual occurrence)
      exact .inl ⟨_, _, rfl, rfl, children⟩
  | constructorFault occurrence children =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.constructor.inj (actual occurrence)
      exact .inr ⟨_, _, rfl, rfl, children⟩
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleValue occurrence _ _ | tupleFault occurrence _ | unary occurrence _ _ | unaryOperandFault occurrence _
  | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _
  | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorSourceInversion
