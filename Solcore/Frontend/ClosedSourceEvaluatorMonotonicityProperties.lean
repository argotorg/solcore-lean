import Solcore.Frontend.ClosedSourceEvaluator

/- Successful depth growth keeps every actual mixed value and store literal.
One private simultaneous induction covers all caller and saved lexical inputs. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem simultaneous_step (budget : Nat) :
    (∀ owner names captured store source value finalStore,
      evaluateClosedSourceExpression? budget owner names captured store source = some (value, finalStore) →
      evaluateClosedSourceExpression? (budget + 1) owner names captured store source = some (value, finalStore)) ∧
    (∀ owner names captured store source value finalStore,
      evaluateClosedSourceBody? budget owner names captured store source = some (value, finalStore) →
      evaluateClosedSourceBody? (budget + 1) owner names captured store source = some (value, finalStore)) := by
  induction budget with
  | zero =>
      constructor <;> intro owner names captured store source value finalStore accepted
      · simp only [evaluateClosedSourceExpression?, reduceCtorEq] at accepted
      · simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
  | succ n ih =>
      constructor
      · intro owner names captured store source value finalStore accepted
        rcases source with ⟨span, payload⟩
        cases payload <;> try (solve | simpa only [evaluateClosedSourceExpression?] using accepted)
        case group inner =>
          rw [evaluateClosedSourceExpression?] at accepted ⊢
          exact ih.1 _ _ _ _ _ _ _ accepted
        case tuple elements =>
          rcases elements with ⟨tupleSpan, children⟩
          cases children with
          | nil => simpa only [evaluateClosedSourceExpression?] using accepted
          | cons left remaining =>
              cases remaining with
              | nil => simpa only [evaluateClosedSourceExpression?] using accepted
              | cons right tail =>
                  cases tail with
                  | nil =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨lv, middleStore⟩, leftResult, ⟨rv, finalStore⟩, rightResult, rfl, rfl⟩ := accepted
                      rw [evaluateClosedSourceExpression?]
                      simp only [ih.1 _ _ _ _ _ _ _ leftResult, ih.1 _ _ _ _ _ _ _ rightResult,
                        bind, Option.bind_some, pure]
                  | cons third rest =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨head, middleStore⟩, headResult, ⟨tail, finalStore⟩, tailResult, rfl, rfl⟩ := accepted
                      rw [evaluateClosedSourceExpression?]
                      simp only [ih.1 _ _ _ _ _ _ _ headResult, ih.1 _ _ _ _ _ _ _ tailResult,
                        bind, Option.bind_some, pure]
        case conditional condition question thenBranch colon elseBranch =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, middleStore⟩, conditionResult, selectedResult⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at selectedResult
          rename_i choice
          rw [evaluateClosedSourceExpression?]
          simp only [ih.1 _ _ _ _ _ _ _ conditionResult, bind, Option.bind_some]
          exact ih.1 _ _ _ _ _ _ _ selectedResult
        case unary operator operand =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator with
          | logicalNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rw [evaluateClosedSourceExpression?]
              simp only [ih.1 _ _ _ _ _ _ _ child, bind, Option.bind_some, pure]
          | bitNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rw [evaluateClosedSourceExpression?]
              simp only [ih.1 _ _ _ _ _ _ _ child, bind, Option.bind_some, pure]
        case call callee arguments =>
          rcases arguments with ⟨argumentsSpan, arguments⟩
          cases arguments with
          | nil => simpa only [evaluateClosedSourceExpression?] using accepted
          | cons argument rest =>
              cases rest with
              | cons _ _ => simpa only [evaluateClosedSourceExpression?] using accepted
              | nil =>
                  simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
                  obtain ⟨⟨function, calleeStore⟩, calleeResult,
                    ⟨argumentValue, argumentStore⟩, argumentResult, result⟩ := accepted
                  cases function <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
                  obtain ⟨⟨name, body⟩, shape, bodyResult⟩ := result
                  rw [evaluateClosedSourceExpression?]
                  simp only [ih.1 _ _ _ _ _ _ _ calleeResult, ih.1 _ _ _ _ _ _ _ argumentResult,
                    shape, bind, Option.bind_some]
                  exact ih.2 _ _ _ _ _ _ _ bodyResult
      · intro owner names captured store source value finalStore accepted
        rcases source with ⟨blockSpan, statements⟩
        cases statements with
        | nil => simpa only [evaluateClosedSourceBody?] using accepted
        | cons statement rest =>
            rcases statement with ⟨statementSpan, payload⟩
            cases payload <;> try (solve | simpa only [evaluateClosedSourceBody?] using accepted)
            case returnStmt returned =>
                cases rest with
                | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                | nil =>
                    cases returned with
                    | none => simpa only [evaluateClosedSourceBody?] using accepted
                    | some child =>
                        rw [evaluateClosedSourceBody?] at accepted ⊢
                        exact ih.1 _ _ _ _ _ _ _ accepted
            case block inner =>
                cases rest with
                | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                | nil =>
                    rw [evaluateClosedSourceBody?] at accepted ⊢
                    exact ih.2 _ _ _ _ _ _ _ accepted
            case letDecl name annotation initializer =>
                cases initializer with
                | none => simpa only [evaluateClosedSourceBody?] using accepted
                | some initializer =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨boundValue, middleStore⟩, head, tail⟩ := accepted
                    rw [evaluateClosedSourceBody?]
                    simp only [ih.1 _ _ _ _ _ _ _ head, bind, Option.bind_some]
                    exact ih.2 _ _ _ _ _ _ _ tail
            case expression child terminated =>
                cases terminated with
                | false => simpa only [evaluateClosedSourceBody?] using accepted
                | true =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨discarded, middleStore⟩, head, tail⟩ := accepted
                    rw [evaluateClosedSourceBody?]
                    simp only [ih.1 _ _ _ _ _ _ _ head, bind, Option.bind_some]
                    exact ih.2 _ _ _ _ _ _ _ tail
            case ifThen condition thenBody elseBody =>
                cases rest with
                | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                | nil =>
                    cases elseBody with
                    | none => simpa only [evaluateClosedSourceBody?] using accepted
                    | some elseBody =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, conditionResult, selectedResult⟩ := accepted
                        cases actual <;> simp only [reduceCtorEq] at selectedResult
                        rename_i choice
                        rw [evaluateClosedSourceBody?]
                        simp only [ih.1 _ _ _ _ _ _ _ conditionResult, bind, Option.bind_some]
                        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at selectedResult ⊢
                        · exact ih.2 _ _ _ _ _ _ _ selectedResult
                        · exact ih.2 _ _ _ _ _ _ _ selectedResult
            case matchWith scrutinees arms =>
                cases rest with
                | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                | nil =>
                    rcases scrutinees with ⟨scrutineeSpan, ⟨scrutinee, additional⟩⟩
                    rcases arms with ⟨armsSpan, ⟨cases, defaultBody⟩⟩
                    cases additional with
                    | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                    | nil =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, scrutineeResult,
                          ⟨selected, tests⟩, choice, selectedResult⟩ := accepted
                        rw [evaluateClosedSourceBody?]
                        simp only [ih.1 _ _ _ _ _ _ _ scrutineeResult, choice, bind, Option.bind_some]
                        exact ih.2 _ _ _ _ _ _ _ selectedResult

/-- Increasing depth retains the entire actual successful expression endpoint. -/
theorem evaluateClosedSourceExpression?_monotone
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Expr} {value : RuntimeValue} {finalStore : List RuntimeValue}
    (order : small ≤ large)
    (accepted : evaluateClosedSourceExpression? small owner names captured initialStore source =
      some (value, finalStore)) :
    evaluateClosedSourceExpression? large owner names captured initialStore source = some (value, finalStore) := by
  induction order with
  | refl => exact accepted
  | @step large _ ih => exact (simultaneous_step large).1 _ _ _ _ _ _ _ ih

/-- A larger-depth None excludes successes at every smaller depth. -/
theorem evaluateClosedSourceExpression?_none_of_le
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Expr}
    (order : small ≤ large)
    (rejected : evaluateClosedSourceExpression? large owner names captured initialStore source = none) :
    evaluateClosedSourceExpression? small owner names captured initialStore source = none := by
  cases result : evaluateClosedSourceExpression? small owner names captured initialStore source with
  | none => rfl
  | some endpoint =>
      have retained := evaluateClosedSourceExpression?_monotone order result
      rw [rejected] at retained
      cases retained

/-- Increasing depth retains the entire actual successful original-body endpoint. -/
theorem evaluateClosedSourceBody?_monotone
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Block} {value : RuntimeValue} {finalStore : List RuntimeValue}
    (order : small ≤ large)
    (accepted : evaluateClosedSourceBody? small owner names captured initialStore source =
      some (value, finalStore)) :
    evaluateClosedSourceBody? large owner names captured initialStore source = some (value, finalStore) := by
  induction order with
  | refl => exact accepted
  | @step large _ ih => exact (simultaneous_step large).2 _ _ _ _ _ _ _ ih

/-- Original bodies satisfy the same None-downward direction. -/
theorem evaluateClosedSourceBody?_none_of_le
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Block}
    (order : small ≤ large)
    (rejected : evaluateClosedSourceBody? large owner names captured initialStore source = none) :
    evaluateClosedSourceBody? small owner names captured initialStore source = none := by
  cases result : evaluateClosedSourceBody? small owner names captured initialStore source with
  | none => rfl
  | some endpoint =>
      have retained := evaluateClosedSourceBody?_monotone order result
      rw [rejected] at retained
      cases retained

end Solcore.Frontend
