import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyProfile

/-! Original return annotations identify a scoped body's result independently
of its native representation. Approval transport preserves every source node. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
open Core Frontend SourceInference
open AcceptedCompilerBodyProfile (HasReturn returns)

theorem Scan.map {source : TypedSource} {approved other : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {mode : Bool} {statements : List StatementId}
    (scan : Scan source approved expected mode statements)
    (mapped : ∀ id, approved id → other id) : Scan source other expected mode statements := by
  induction scan with
  | nil allowed => exact .nil allowed
  | returnUnit rest found form sourceType result => exact .returnUnit rest found form sourceType result
  | returning rest found form sourceType expressionFound valueType value =>
    exact .returning rest found form sourceType expressionFound valueType (mapped _ value)
  | tail found form sourceType expressionFound valueType value =>
    exact .tail found form sourceType expressionFound valueType (mapped _ value)
  | absent found form declaration monomorphic ordinary _ ih => exact .absent found form declaration monomorphic ordinary ih
  | initialized found form declaration monomorphic ordinary expressionFound valueType value _ ih =>
    exact .initialized found form declaration monomorphic ordinary expressionFound valueType (mapped _ value) ih
  | discard found form continuing sourceType expressionFound value _ ih =>
    exact .discard found form continuing sourceType expressionFound (mapped _ value) ih
  | block found form _ _ inner remaining => exact .block found form inner remaining
  | conditional found form sourceType conditionFound conditionType value _ _ _ left right remaining =>
    exact .conditional found form sourceType conditionFound conditionType (mapped _ value) left right remaining
  | whileLoop found form conditionFound conditionType value _ _ inner remaining =>
    exact .whileLoop found form conditionFound conditionType (mapped _ value) inner remaining
  | assign found form declaration targetType bare rhsFound rhsType value _ ih =>
    exact .assign found form declaration targetType bare rhsFound rhsType (mapped _ value) ih

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem returned_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : Option ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt expression)
    (typed : StatementHasType source control context id final facts) : node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem return_in_tail {source : TypedSource} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} (found : source.lookupStatement? id = some node)
    (ordinary : returns node.form = false) (present : HasReturn source (id :: rest)) :
    HasReturn source rest := by
  obtain ⟨actual, member, value, selected, returned⟩ := present
  rcases List.mem_cons.mp member with same | member
  · subst actual
    cases Option.some.inj (found.symm.trans selected)
    simp [ordinary] at returned
  · exact ⟨actual, member, value, selected, returned⟩

/-- A real return in the original statement list fixes the raw result type.
Nested blocks and loops retain the same return context; no native equality is used. -/
theorem Scan.result_eq_of_return {source : TypedSource} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {mode : Bool} {statements : List StatementId}
    (scan : Scan source approved expected mode statements) (unique : NodeOccurrencesUnique source)
    (present : HasReturn source statements)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    control.returnType = expected := by
  induction scan generalizing control context final facts with
  | nil => obtain ⟨_, member, _⟩ := present; cases member
  | returnUnit rest found form sourceType result =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    exact (returned_annotation unique found form head).symm.trans (sourceType.trans result.symm)
  | returning rest found form sourceType =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    exact (returned_annotation unique found form head).symm.trans sourceType
  | tail found form =>
    have absent := return_in_tail found (by simp [form, returns]) present
    obtain ⟨_, member, _⟩ := absent
    cases member
  | absent found form _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail
  | initialized found form _ _ _ _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail
  | discard found form _ _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail
  | block found form _ _ _ remaining =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact remaining (return_in_tail found (by simp [form, returns]) present) tail
  | conditional found form _ _ _ _ _ _ _ _ _ remaining =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact remaining (return_in_tail found (by simp [form, returns]) present) tail
  | whileLoop found form _ _ _ _ _ _ remaining =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact remaining (return_in_tail found (by simp [form, returns]) present) tail
  | assign found form _ _ _ _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail

end Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
