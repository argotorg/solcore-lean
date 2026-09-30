import Solcore.SourceSemantics.CoreLowering.ControlStatementTree

/-! Extract scoped control statement trees from the actual successful compiler.
The ambient context/scope alignment and unique source occurrences are static
premises. Neither child trees nor source/Core evaluations are assumed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok
    {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Function and nested-list tail conventions are both recovered from
successful lowering. Branch/block binders remain local to their child tree. -/
theorem tree_of_lowerFlowStatements
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerFlowStatementsWithReasons fuel source scope statements
      resultType reasonAt tailReturns = .ok code) :
    Tree source reasonAt scope context tailReturns statements resultType code := by
  induction fuel generalizing scope context statements code tailReturns with
  | zero =>
      cases statements with
      | nil => cases accepted; exact .nil
      | cons => cases accepted
  | succ fuel ih =>
      cases statements with
      | nil => cases accepted; exact .nil
      | cons id rest =>
          simp only [SourceCoreControl.lowerFlowStatementsWithReasons,
            SourceCoreControl.lowerFlowStatementsWithExpression] at accepted
          obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
          have metadata := (readStatement_certificate read).2
          cases form : node.form with
          | letDecl binder initializer =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
              have certificate := lowerBinder_certificate binding
              have extension := certificate.extends aligned
              cases initializer with
              | none =>
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .letUninitialized metadata form certificate extension
                    (ih (aligned.bind binder payload) compiledBody)
              | some initializer =>
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨_, _, valueTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .letInitialized metadata form certificate extension valueTree
                    (ih (aligned.bind binder payload) compiledBody)
          | assignValue assignment operator rhs =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              have targetCertificate := lowerAssignment_certificate target
              have equal := targetCertificate.equal
              subst operator
              obtain ⟨_, _, valueTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledValue
              rw [← ensureType_ok checked] at valueTree
              exact .assign metadata form targetCertificate valueTree (ih aligned compiledBody)
          | returnStmt value =>
              cases value with
              | none =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultUnit : resultType = .unit :=
                    (ensureType_ok resultChecked).trans (ensureType_ok unitChecked).symm
                  rw [← ensureType_ok unitChecked] at metadata
                  cases accepted
                  rw [resultUnit]
                  exact .returnUnit rest metadata form
              | some value =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  rw [← ensureType_ok resultChecked] at metadata
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  cases accepted
                  obtain ⟨_, _, valueTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .returnValue rest metadata form valueTree
          | expression value semicolon =>
              simp only [form] at accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨_, _, valueTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledValue
              split at accepted
              · rename_i isTail
                have shape : semicolon = false ∧ tailReturns = true ∧ rest = [] := by
                  cases semicolon <;> cases tailReturns <;> cases rest <;> simp_all
                obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                cases checkedUnit
                rw [← ensureType_ok resultChecked] at metadata
                obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                cases checkedUnit
                cases accepted
                rw [← ensureType_ok checked] at valueTree
                rcases shape with ⟨rfl, rfl, rfl⟩
                exact .tailExpression metadata form valueTree
              · rename_i notTail
                have notTail : (!semicolon && tailReturns && rest.isEmpty) = false := by simpa using notTail
                cases semicolon with
                | true =>
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                    cases accepted
                    exact .discard metadata form notTail (ensureType_ok checked).symm
                      valueTree (ih aligned compiledBody)
                | false =>
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                    cases accepted
                    exact .discard metadata form notTail (ensureType_ok checked)
                      valueTree (ih aligned compiledBody)
          | block statements =>
              simp only [form] at accepted
              obtain ⟨block, compiledBlock, accepted⟩ := bind_ok accepted
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              exact .block metadata form (ih aligned compiledBlock) (ih aligned compiledBody)
          | ifThen condition thenBody elseBody =>
              simp only [form] at accepted
              obtain ⟨condition, compiledCondition, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨thenBranch, compiledThen, accepted⟩ := bind_ok accepted
              obtain ⟨_, _, conditionTree⟩ := ControlExpressions.tree_of_lowerExpression unique compiledCondition
              rw [← ensureType_ok checked] at conditionTree
              cases elseBody with
              | none =>
                  obtain ⟨elseBranch, compiledElse, accepted⟩ := bind_ok accepted
                  cases compiledElse
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .ifThen metadata form conditionTree (ih aligned compiledThen) .nil (ih aligned compiledBody)
              | some statements =>
                  obtain ⟨elseBranch, compiledElse, accepted⟩ := bind_ok accepted
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact .ifThen metadata form conditionTree (ih aligned compiledThen)
                    (ih aligned compiledElse) (ih aligned compiledBody)
          | assignBitNot | matchWith | forLoop | whileLoop | breakStmt | continueStmt =>
              simp [form] at accepted

/-- The actual function compiler supplies its complete flow tree and the
precise finish expression, including Unit/non-Unit fallthrough handling. -/
theorem tree_of_lowerStatements
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerStatementsWithReasons fuel source scope statements
      resultType reasonAt fellThroughReason = .ok code) :
    ∃ flow, code = Core.LocalControl.finish resultType flow
        (if resultType = .unit then Core.LanguageResult.success .unit
         else Core.LanguageResult.failure resultType (.word fellThroughReason)) ∧
      Tree source reasonAt scope context true statements resultType flow := by
  unfold SourceCoreControl.lowerStatementsWithReasons at accepted
  obtain ⟨flow, compiledFlow, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨flow, rfl, tree_of_lowerFlowStatements aligned unique compiledFlow⟩

end Solcore.SourceSemantics.CoreLowering.ControlStatements
