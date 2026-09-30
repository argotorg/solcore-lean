import Solcore.SourceSemantics.CoreLowering.LoopStatementTree

/-! Extract scoped default while-loop statement trees from the actual successful compiler.
The ambient context/scope alignment and unique source occurrences are static
premises. For-header traversal is explicitly excluded by syntax. Neither child
trees nor source/Core evaluations are assumed; no termination is concluded. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- This certificate grammar covers while loops. Exclusion of for headers is
a static source-table condition, including nested statement occurrences. -/
def NoForLoops (source : TypedSource) : Prop :=
  ∀ {id : StatementId} {node : StatementNode}, source.lookupStatement? id = some node →
    ∀ initializer condition post body, node.form ≠ .forLoop initializer condition post body

/-- The default compiler policy authenticated by this certificate. -/
def defaultPolicy (compilation : SourceCorePrimitive.Context) : SourceCoreLoops.Policy :=
  { lowerExpression := fun fuel source scope id reasonAt =>
      SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt }

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
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (defaultPolicy compilation)
      fuel source scope statements resultType reasonAt tailReturns selfReason = .ok code) :
    Tree compilation source reasonAt selfReason scope context tailReturns statements resultType code := by
  induction fuel generalizing scope context statements code tailReturns with
  | zero =>
      cases statements with
      | nil =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
          cases accepted; exact .nil
      | cons =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
          cases accepted
  | succ fuel ih =>
      cases statements with
      | nil =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
          cases accepted; exact .nil
      | cons id rest =>
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, defaultPolicy] at accepted
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
                  obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .letInitialized metadata form certificate extension valueTree
                    (ih (aligned.bind binder payload) compiledBody)
          | assignValue assignment operator rhs =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              let assignmentStep := fun operator => do
                let (index, payload) ← SourceCoreBasic.lowerAssignment source scope assignment operator
                let value ← SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope rhs reasonAt
                SourceCoreBasic.ensureType (.binder assignment.target.root) payload value.type
                pure (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType)
                  (.var index) value.expression body)
              change (match operator, (defaultPolicy compilation).assignValue with
                | .equal, _ | _, none => assignmentStep operator
                | _, some callback => callback (defaultPolicy compilation).lowerExpression fuel source scope
                    (.occurrence id.occurrence) assignment operator rhs (Core.LocalLoop.controlType resultType)
                    body reasonAt) = .ok code at accepted
              cases operator <;> dsimp only [defaultPolicy, assignmentStep] at accepted
              all_goals
                obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
                have targetCertificate := lowerAssignment_certificate target
                have equal := targetCertificate.equal
                cases equal
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              cases accepted
              obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
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
                  obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
                  rw [← ensureType_ok checked] at valueTree
                  exact .returnValue rest metadata form valueTree
          | expression value semicolon =>
              simp only [form] at accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
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
              obtain ⟨_, _, conditionTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledCondition
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
          | whileLoop condition statements =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok unitChecked] at metadata
              obtain ⟨condition, compiledCondition, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨loopBody, compiledLoopBody, accepted⟩ := bind_ok accepted
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              obtain ⟨_, _, conditionTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledCondition
              rw [← ensureType_ok checked] at conditionTree
              exact .whileLoop metadata form conditionTree (ih aligned compiledLoopBody) (ih aligned compiledBody)
          | breakStmt =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              cases accepted
              exact .breaking rest metadata form
          | continueStmt =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              rw [← ensureType_ok checked] at metadata
              cases accepted
              exact .continuing rest metadata form
          | forLoop initializer condition post statements =>
              exact False.elim (noFor (readStatement_certificate read).1 initializer condition post statements form)
          | assignBitNot =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases accepted
          | matchWith => simp [form] at accepted

/-- Recover the default flow tree through the expression-policy compatibility
wrapper used by the public default statement compiler. -/
theorem tree_of_lowerFlowStatementsWithExpression
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {statements : List StatementId}
    {resultType : Core.Ty} {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word}
    {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasonAt => SourceCorePrimitive.lowerExpressionWithReasons
        fuel compilation source scope id reasonAt)
      fuel source scope statements resultType reasonAt tailReturns selfReason = .ok code) :
    Tree compilation source reasonAt selfReason scope context tailReturns statements resultType code :=
  tree_of_lowerFlowStatements aligned unique noFor accepted

/-- The actual function compiler supplies its complete flow tree and precise
finish expression. Escaped loop control and non-Unit fallthrough keep their
separate supplied language failure tokens. -/
theorem tree_of_lowerStatements
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {statements : List StatementId}
    {resultType : Core.Ty} {reasonAt : ExpressionId → Core.Word}
    {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements
      resultType reasonAt fellThroughReason escapedReason = .ok code) :
    ∃ flow, code = Core.LocalControl.finish resultType
        (Core.LocalLoop.toControl resultType flow escapedReason)
        (if resultType = .unit then Core.LanguageResult.success .unit
         else Core.LanguageResult.failure resultType (.word fellThroughReason)) ∧
      Tree compilation source reasonAt escapedReason scope context true statements resultType flow := by
  unfold SourceCoreLoops.lowerStatementsWithReasons SourceCoreLoops.lowerStatementsWithExpression
    SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, compiledFlow, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨flow, rfl, tree_of_lowerFlowStatements aligned unique noFor compiledFlow⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
