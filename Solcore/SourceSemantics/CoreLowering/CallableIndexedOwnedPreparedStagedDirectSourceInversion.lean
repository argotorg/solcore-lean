import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed

/-! Direct calls evaluate their argument vector before entering the selected
named body. No runtime callee evaluation or indirect call guard is inserted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectSourceInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id callee : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}
  {instantiation : DeclarationInstantiation} {arguments : List ExpressionId}

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

theorem children
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (coercions : node.coercions = [])
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    (∃ sequenceSize invocationSize argumentsHeap values name evidence,
      size = Size.stepSize [sequenceSize, invocationSize] ∧
      Occurrence invocation callee (.reference name (.declaration instantiation)) ∧
      SourceSemantics.DeclarationInstantiation.Valid context instantiation ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.values values) argumentsHeap ∧
      Dynamic.DirectCallProducesEvidence context invocation.evidence node.requirements [] instantiation.predicates evidence ∧
      Size.Applies program registry invocationSize invocation context argumentsHeap
        (.global ⟨instantiation, evidence⟩) values outcome after) ∨
    (∃ sequenceSize failure, size = Size.stepSize [sequenceSize] ∧
      outcome = .fault failure ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.fault failure) after) := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .call callee arguments (.declaration instantiation) :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | directApplied occurrence calleeOccurrence valid children callEvidence applied =>
      obtain ⟨rfl, rfl, same⟩ := ExpressionForm.call.inj (actual occurrence)
      cases same
      rw [← occurrence_requirements unique found occurrence] at callEvidence
      exact .inl ⟨_, _, _, _, _, _, rfl, calleeOccurrence, valid, children, callEvidence, applied⟩
  | directArgumentsFault occurrence _calleeOccurrence children =>
      obtain ⟨rfl, rfl, same⟩ := ExpressionForm.call.inj (actual occurrence)
      cases same
      exact .inr ⟨_, _, rfl, rfl, children⟩
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleValue occurrence _ _ | tupleFault occurrence _ | constructorValue occurrence _ _ | constructorFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _
  | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _
  | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectSourceInversion
