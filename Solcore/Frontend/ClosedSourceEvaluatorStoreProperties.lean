import Solcore.Frontend.ClosedSourceEvaluator

/- Exact store replay at the same finite budget. The private proof transports
success directly through the joint evaluator recursion; reversing that transport
retains None. Captures, saved lexical fields and opaque values are unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem simultaneous_replay (budget : Nat) :
    (∀ owner names captured store source value finalStore replacement,
      evaluateClosedSourceExpression? budget owner names captured store source = some (value, finalStore) →
      evaluateClosedSourceExpression? budget owner names captured replacement source = some (value, replacement)) ∧
    (∀ owner names captured store source value finalStore replacement,
      evaluateClosedSourceBody? budget owner names captured store source = some (value, finalStore) →
      evaluateClosedSourceBody? budget owner names captured replacement source = some (value, replacement)) := by
  induction budget with
  | zero =>
      constructor <;> intro owner names captured store source value finalStore replacement accepted
      · simp only [evaluateClosedSourceExpression?, reduceCtorEq] at accepted
      · simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
  | succ n ih =>
      constructor
      · intro owner names captured store source value finalStore replacement accepted
        rcases source with ⟨span, payload⟩
        cases payload <;> try (solve |
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted ⊢
          obtain ⟨actual, computed, rfl, rfl⟩ := accepted
          exact ⟨actual, computed, rfl, True.intro⟩)
        case identifier name =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted ⊢
          obtain ⟨id, named, actual, found, rfl, rfl⟩ := accepted
          exact ⟨id, named, actual, found, rfl, True.intro⟩
        case group inner =>
          rw [evaluateClosedSourceExpression?] at accepted ⊢
          exact ih.1 _ _ _ _ _ _ _ replacement accepted
        case tuple elements =>
          rcases elements with ⟨tupleSpan, children⟩
          cases children with
          | nil =>
              simp only [evaluateClosedSourceExpression?, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              simp only [evaluateClosedSourceExpression?]
          | cons left remaining =>
              cases remaining with
              | nil => simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?, bind, Option.bind_none, reduceCtorEq] at accepted
              | cons right tail =>
                  cases tail with
                  | nil =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨lv, middleStore⟩, leftResult, ⟨rv, finalStore⟩, rightResult, rfl, rfl⟩ := accepted
                      rw [evaluateClosedSourceExpression?]
                      simp only [ih.1 _ _ _ _ _ _ _ replacement leftResult, ih.1 _ _ _ _ _ _ _ replacement rightResult,
                        bind, Option.bind_some, pure]
                  | cons third rest =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨head, middleStore⟩, headResult, ⟨tail, finalStore⟩, tailResult, rfl, rfl⟩ := accepted
                      rw [evaluateClosedSourceExpression?]
                      simp only [ih.1 _ _ _ _ _ _ _ replacement headResult, ih.1 _ _ _ _ _ _ _ replacement tailResult,
                        bind, Option.bind_some, pure]
        case conditional condition question thenBranch colon elseBranch =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, middleStore⟩, conditionResult, selectedResult⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at selectedResult
          rename_i choice
          rw [evaluateClosedSourceExpression?]
          simp only [ih.1 _ _ _ _ _ _ _ replacement conditionResult, bind, Option.bind_some]
          exact ih.1 _ _ _ _ _ _ _ replacement selectedResult
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
              simp only [ih.1 _ _ _ _ _ _ _ replacement child, bind, Option.bind_some, pure]
          | bitNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rw [evaluateClosedSourceExpression?]
              simp only [ih.1 _ _ _ _ _ _ _ replacement child, bind, Option.bind_some, pure]
        case binary left operator right =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator
          case logicalAnd =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            rw [evaluateClosedSourceExpression?]
            simp only [ih.1 _ _ _ _ _ _ _ replacement leftResult, bind, Option.bind_some]
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result ⊢
            · simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rfl
            · exact ih.1 _ _ _ _ _ _ _ replacement result
          case logicalOr =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            rw [evaluateClosedSourceExpression?]
            simp only [ih.1 _ _ _ _ _ _ _ replacement leftResult, bind, Option.bind_some]
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result ⊢
            · exact ih.1 _ _ _ _ _ _ _ replacement result
            · simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rfl
          all_goals
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨leftActual, middleStore⟩, leftResult, result⟩ := accepted
            cases leftActual <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
            obtain ⟨⟨rightActual, finalStore⟩, rightResult, result⟩ := result
            cases rightActual <;>
              simp only [reduceCtorEq, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨coreValue, meaning, rfl, rfl⟩ := result
            simp only [evaluateClosedSourceExpression?,
              ih.1 _ _ _ _ _ _ _ replacement leftResult, ih.1 _ _ _ _ _ _ _ replacement rightResult,
              meaning, bind, Option.bind_some, pure]
        case call callee arguments =>
          rcases arguments with ⟨argumentsSpan, arguments⟩
          cases arguments with
          | nil => simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?, bind, Option.bind_none, reduceCtorEq] at accepted
          | cons argument rest =>
              cases rest with
              | cons _ _ => simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?, bind, Option.bind_none, reduceCtorEq] at accepted
              | nil =>
                  simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
                  obtain ⟨⟨function, calleeStore⟩, calleeResult,
                    ⟨argumentValue, argumentStore⟩, argumentResult, result⟩ := accepted
                  cases function <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
                  obtain ⟨⟨name, body⟩, shape, bodyResult⟩ := result
                  rw [evaluateClosedSourceExpression?]
                  simp only [ih.1 _ _ _ _ _ _ _ replacement calleeResult, ih.1 _ _ _ _ _ _ _ replacement argumentResult,
                    shape, bind, Option.bind_some]
                  exact ih.2 _ _ _ _ _ _ _ replacement bodyResult
      · intro owner names captured store source value finalStore replacement accepted
        rcases source with ⟨blockSpan, statements⟩
        cases statements with
        | nil => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
        | cons statement rest =>
            rcases statement with ⟨statementSpan, payload⟩
            cases payload <;> try (solve | simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted)
            case returnStmt returned =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    cases returned with
                    | none =>
                        simp only [evaluateClosedSourceBody?, Option.some.injEq, Prod.mk.injEq] at accepted
                        obtain ⟨rfl, rfl⟩ := accepted
                        simp only [evaluateClosedSourceBody?]
                    | some child =>
                        rw [evaluateClosedSourceBody?] at accepted ⊢
                        exact ih.1 _ _ _ _ _ _ _ replacement accepted
            case block inner =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    rw [evaluateClosedSourceBody?] at accepted ⊢
                    exact ih.2 _ _ _ _ _ _ _ replacement accepted
            case letDecl name annotation initializer =>
                cases initializer with
                | none => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | some initializer =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨boundValue, middleStore⟩, head, tail⟩ := accepted
                    rw [evaluateClosedSourceBody?]
                    simp only [ih.1 _ _ _ _ _ _ _ replacement head, bind, Option.bind_some]
                    exact ih.2 _ _ _ _ _ _ _ replacement tail
            case expression child terminated =>
                cases terminated with
                | false => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | true =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨discarded, middleStore⟩, head, tail⟩ := accepted
                    rw [evaluateClosedSourceBody?]
                    simp only [ih.1 _ _ _ _ _ _ _ replacement head, bind, Option.bind_some]
                    exact ih.2 _ _ _ _ _ _ _ replacement tail
            case ifThen condition thenBody elseBody =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    cases elseBody with
                    | none => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                    | some elseBody =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, conditionResult, selectedResult⟩ := accepted
                        cases actual <;> simp only [reduceCtorEq] at selectedResult
                        rename_i choice
                        rw [evaluateClosedSourceBody?]
                        simp only [ih.1 _ _ _ _ _ _ _ replacement conditionResult, bind, Option.bind_some]
                        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at selectedResult ⊢
                        · exact ih.2 _ _ _ _ _ _ _ replacement selectedResult
                        · exact ih.2 _ _ _ _ _ _ _ replacement selectedResult
            case matchWith scrutinees arms =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    rcases scrutinees with ⟨scrutineeSpan, ⟨scrutinee, additional⟩⟩
                    rcases arms with ⟨armsSpan, ⟨cases, defaultBody⟩⟩
                    cases additional with
                    | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                    | nil =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, scrutineeResult,
                          ⟨selected, tests⟩, choice, selectedResult⟩ := accepted
                        rw [evaluateClosedSourceBody?]
                        simp only [ih.1 _ _ _ _ _ _ _ replacement scrutineeResult, choice, bind, Option.bind_some]
                        exact ih.2 _ _ _ _ _ _ _ replacement selectedResult

/-- Replacing only the store preserves the complete finite expression outcome. -/
theorem evaluateClosedSourceExpression?_replay_store
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue)
    (initialStore replacement : List RuntimeValue) (source : Syntax.Expr) :
    evaluateClosedSourceExpression? budget owner names captured replacement source =
      (evaluateClosedSourceExpression? budget owner names captured initialStore source).map
        (fun endpoint => (endpoint.1, replacement)) := by
  cases original : evaluateClosedSourceExpression? budget owner names captured initialStore source with
  | some endpoint =>
      exact (simultaneous_replay budget).1 _ _ _ _ _ _ _ replacement original
  | none =>
      cases replayed : evaluateClosedSourceExpression? budget owner names captured replacement source with
      | none => rfl
      | some endpoint =>
          have back := (simultaneous_replay budget).1 _ _ _ _ _ _ _ initialStore replayed
          rw [original] at back
          cases back

/-- Body replay also retains None, with exactly the original finite budget. -/
theorem evaluateClosedSourceBody?_replay_store
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue)
    (initialStore replacement : List RuntimeValue) (source : Syntax.Block) :
    evaluateClosedSourceBody? budget owner names captured replacement source =
      (evaluateClosedSourceBody? budget owner names captured initialStore source).map
        (fun endpoint => (endpoint.1, replacement)) := by
  cases original : evaluateClosedSourceBody? budget owner names captured initialStore source with
  | some endpoint =>
      exact (simultaneous_replay budget).2 _ _ _ _ _ _ _ replacement original
  | none =>
      cases replayed : evaluateClosedSourceBody? budget owner names captured replacement source with
      | none => rfl
      | some endpoint =>
          have back := (simultaneous_replay budget).2 _ _ _ _ _ _ _ initialStore replayed
          rw [original] at back
          cases back

end Solcore.Frontend
