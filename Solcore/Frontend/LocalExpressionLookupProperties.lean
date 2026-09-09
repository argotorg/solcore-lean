import Solcore.Frontend.LocalExpressionEvaluator

/-! Direct expressions observe only the composed first-match actual-value
lookup. Intermediate identities, row layouts and the reason for absence are
not observable; neither typing nor whole checking is assumed. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Equal optional actual values for every spelling preserve the complete
result, including raw absence, selected opaque values and exact cost. -/
theorem evaluateLocalExpressionWithCost?_congr_lookup
    (leftTable rightTable : LocalNameTable)
    (leftEnvironment rightEnvironment : Resolved.Environment)
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?) (source : Syntax.Expr) :
    evaluateLocalExpressionWithCost? leftTable leftEnvironment source =
      evaluateLocalExpressionWithCost? rightTable rightEnvironment source := by
  cases source with
  | mk span payload =>
      cases payload <;> try simp only [evaluateLocalExpressionWithCost?]
      case identifier name =>
        simp only [bind, ← Option.bind_assoc, sameLookup]
      case group inner =>
        exact evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
          leftEnvironment rightEnvironment sameLookup inner
      case tuple elements =>
        cases elements with
        | mk tupleSpan children =>
          cases children with
          | nil => simp only [evaluateLocalExpressionWithCost?]
          | cons left remaining =>
            cases remaining with
            | nil => simp only [evaluateLocalExpressionWithCost?]
            | cons right tail =>
              have first := evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
                leftEnvironment rightEnvironment sameLookup left
              cases tail with
              | nil =>
                have second := evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
                  leftEnvironment rightEnvironment sameLookup right
                simp only [evaluateLocalExpressionWithCost?, first, second]
              | cons third rest =>
                have remaining := evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
                  leftEnvironment rightEnvironment sameLookup ⟨span,.tuple ⟨tupleSpan,right :: third :: rest⟩⟩
                conv => lhs; rw [evaluateLocalExpressionWithCost?]
                conv => rhs; rw [evaluateLocalExpressionWithCost?]
                rw [first, remaining]
      case unary operator operand =>
        have child := evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
          leftEnvironment rightEnvironment sameLookup operand
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;> simp only [evaluateLocalExpressionWithCost?, child]
      case binary left operator right =>
        have first := evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
          leftEnvironment rightEnvironment sameLookup left
        have second := evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
          leftEnvironment rightEnvironment sameLookup right
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;> simp only [evaluateLocalExpressionWithCost?, first, second]
      case conditional condition question thenBranch colon elseBranch =>
        have guard := evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
          leftEnvironment rightEnvironment sameLookup condition
        have yes := evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
          leftEnvironment rightEnvironment sameLookup thenBranch
        have no := evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
          leftEnvironment rightEnvironment sameLookup elseBranch
        simp only [guard, yes, no]
termination_by sizeOf source

end Solcore.Frontend
