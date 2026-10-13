import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed

/-! Original index traces retain base-before-key execution, each strict child
grade, and the exact heap before the lookup decision. Staging and semantic faults stay distinct. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexSourceInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}
  {base key : ExpressionId}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

inductive Children (program : Program) (registry : Registry) (size : Nat) (invocation : Scope)
    (context : Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (base key : ExpressionId) : Outcome → Dynamic.Heap → Prop where
  | baseFault {firstSize failure after}
      (first : Size.Expression program registry firstSize invocation context environment before base (.fault failure) after)
      (smaller : firstSize < size) : Children program registry size invocation context environment before base key (.fault failure) after
  | keyFault {firstSize secondSize value failure middle after}
      (first : Size.Expression program registry firstSize invocation context environment before base (.value value) middle)
      (second : Size.Expression program registry secondSize invocation context environment middle key (.fault failure) after)
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size) :
      Children program registry size invocation context environment before base key (.fault failure) after
  | result {firstSize secondSize baseValue keyValue outcome middle after}
      (first : Size.Expression program registry firstSize invocation context environment before base (.value baseValue) middle)
      (second : Size.Expression program registry secondSize invocation context environment middle key (.value keyValue) after)
      (result : IndexOutcome baseValue keyValue outcome)
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size) :
      Children program registry size invocation context environment before base key outcome after

theorem children
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .index base key)
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    Children program registry size invocation context environment before base key outcome after := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .index base key :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | indexBaseFault occurrence first =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.index.inj (actual occurrence)
      exact .baseFault first (Size.child_lt_stepSize (by simp))
  | indexKeyFault occurrence first second =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.index.inj (actual occurrence)
      exact .keyFault first second (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp))
  | indexResult occurrence first second result =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.index.inj (actual occurrence)
      exact .result first second result (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp))
  | constructorValue occurrence _ _ | constructorFault occurrence _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleValue occurrence _ _ | tupleFault occurrence _ | unary occurrence _ _ | unaryOperandFault occurrence _
  | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _
  | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexSourceInversion
