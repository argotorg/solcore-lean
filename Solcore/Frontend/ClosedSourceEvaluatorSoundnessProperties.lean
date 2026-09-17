import Solcore.Frontend.ClosedSourceEvaluator
import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.StrictWordBinaryProperties
import Solcore.Frontend.SourceLambdaEvaluationProperties
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.WordLiteralProperties
import Solcore.Resolved.LocalScopeProperties

/- One private simultaneous budget induction constructs the independent source
judgments at exact actual endpoints, without callback or checking premises. -/

set_option autoImplicit false
namespace Solcore.Frontend

private theorem simultaneous_sound (budget : Nat) :
    (∀ owner names captured store source value finalStore,
      evaluateClosedSourceExpression? budget owner names captured store source = some (value, finalStore) →
      ClosedSourceExpressionEvaluates owner names captured store source value finalStore) ∧
    (∀ owner names captured store source value finalStore,
      evaluateClosedSourceBody? budget owner names captured store source = some (value, finalStore) →
      ClosedSourceBodyEvaluates owner names captured store source value finalStore) := by
  induction budget with
  | zero =>
      constructor <;> intro owner names captured store source value finalStore accepted
      · simp only [evaluateClosedSourceExpression?, reduceCtorEq] at accepted
      · simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
  | succ n ih =>
      constructor
      · intro owner names captured store source value finalStore accepted
        rcases source with ⟨span, payload⟩
        cases payload <;> try (solve |
          simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
            bind, Option.bind_none, reduceCtorEq] at accepted)
        case identifier name =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨id, named, actual, found, rfl, rfl⟩ := accepted
          exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)
        case literal literal =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨word, meaning, rfl, rfl⟩ := accepted
          exact .wordLiteral (interpretWordLiteral?_sound meaning)
        case group inner =>
          rw [evaluateClosedSourceExpression?] at accepted
          exact .group (ih.1 _ _ _ _ _ _ _ accepted)
        case tuple elements =>
          rcases elements with ⟨tupleSpan, children⟩
          cases children with
          | nil =>
              simp only [evaluateClosedSourceExpression?, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact .unit
          | cons left remaining =>
              cases remaining with
              | nil =>
                  simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
                    bind, Option.bind_none, reduceCtorEq] at accepted
              | cons right tail =>
                  cases tail with
                  | nil =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨leftValue, middleStore⟩, leftResult,
                        ⟨rightValue, finalStore⟩, rightResult, rfl, rfl⟩ := accepted
                      exact .pair (ih.1 _ _ _ _ _ _ _ leftResult) (ih.1 _ _ _ _ _ _ _ rightResult)
                  | cons third rest =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨headValue, middleStore⟩, headResult,
                        ⟨tailValue, finalStore⟩, tailResult, rfl, rfl⟩ := accepted
                      exact .many (ih.1 _ _ _ _ _ _ _ headResult) (ih.1 _ _ _ _ _ _ _ tailResult)
        case call callee arguments =>
          rcases arguments with ⟨argumentsSpan, arguments⟩
          cases arguments with
          | nil =>
              simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
                bind, Option.bind_none, reduceCtorEq] at accepted
          | cons argument rest =>
              cases rest with
              | cons _ _ =>
                  simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
                    bind, Option.bind_none, reduceCtorEq] at accepted
              | nil =>
                  simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
                  obtain ⟨⟨function, calleeStore⟩, calleeResult,
                    ⟨argumentValue, argumentStore⟩, argumentResult, result⟩ := accepted
                  cases function <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
                  obtain ⟨⟨name, body⟩, shape, bodyResult⟩ := result
                  exact .call (sourceUnaryLambdaShape?_iff.mp shape)
                    (ih.1 _ _ _ _ _ _ _ calleeResult) (ih.1 _ _ _ _ _ _ _ argumentResult)
                    (ih.2 _ _ _ _ _ _ _ bodyResult)
        case conditional condition question thenBranch colon elseBranch =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, middleStore⟩, conditionResult, result⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at result
          rename_i choice
          cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result
          · exact .conditionalFalse (ih.1 _ _ _ _ _ _ _ conditionResult) (ih.1 _ _ _ _ _ _ _ result)
          · exact .conditionalTrue (ih.1 _ _ _ _ _ _ _ conditionResult) (ih.1 _ _ _ _ _ _ _ result)
        case unary operator operand =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator with
          | logicalNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              exact .logicalNot (ih.1 _ _ _ _ _ _ _ child)
          | bitNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              exact .bitNot (ih.1 _ _ _ _ _ _ _ child)
        case binary left operator right =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator
          case logicalAnd =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result
            · simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              exact .andFalse (ih.1 _ _ _ _ _ _ _ leftResult)
            · exact .andTrue (ih.1 _ _ _ _ _ _ _ leftResult) (ih.1 _ _ _ _ _ _ _ result)
          case logicalOr =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result
            · exact .orFalse (ih.1 _ _ _ _ _ _ _ leftResult) (ih.1 _ _ _ _ _ _ _ result)
            · simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              exact .orTrue (ih.1 _ _ _ _ _ _ _ leftResult)
          all_goals
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨leftActual, middleStore⟩, leftResult, result⟩ := accepted
            cases leftActual <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
            obtain ⟨⟨rightActual, finalStore⟩, rightResult, result⟩ := result
            cases rightActual <;>
              simp only [reduceCtorEq, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨coreValue, meaning, rfl, rfl⟩ := result
            exact .strictWordBinary (ih.1 _ _ _ _ _ _ _ leftResult)
              (ih.1 _ _ _ _ _ _ _ rightResult) (evaluateStrictWordBinary?_iff.mp meaning)
        case lambda keyword parameters returns body =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨⟨name, body⟩, shape, rfl, rfl⟩ := accepted
          exact .creation (sourceUnaryLambdaShape?_iff.mp shape)
      · intro owner names captured store source value finalStore accepted
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
                        exact .bare
                    | some child =>
                        rw [evaluateClosedSourceBody?] at accepted
                        exact .expression (ih.1 _ _ _ _ _ _ _ accepted)
            case block inner =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    rw [evaluateClosedSourceBody?] at accepted
                    exact .block (ih.2 _ _ _ _ _ _ _ accepted)
            case letDecl name annotation initializer =>
                cases initializer with
                | none => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | some initializer =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨boundValue, middleStore⟩, head, tail⟩ := accepted
                    cases annotation with
                    | none => exact .inferred (ih.1 _ _ _ _ _ _ _ head) (ih.2 _ _ _ _ _ _ _ tail)
                    | some annotation => exact .binding (ih.1 _ _ _ _ _ _ _ head) (ih.2 _ _ _ _ _ _ _ tail)
            case expression child terminated =>
                cases terminated with
                | false => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | true =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨discarded, middleStore⟩, head, tail⟩ := accepted
                    exact .discard (ih.1 _ _ _ _ _ _ _ head) (ih.2 _ _ _ _ _ _ _ tail)
            case ifThen condition thenBody elseBody =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    cases elseBody with
                    | none => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                    | some elseBody =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, conditionResult, result⟩ := accepted
                        cases actual <;> simp only [reduceCtorEq] at result
                        rename_i choice
                        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result
                        · exact .ifFalse (ih.1 _ _ _ _ _ _ _ conditionResult) (ih.2 _ _ _ _ _ _ _ result)
                        · exact .ifTrue (ih.1 _ _ _ _ _ _ _ conditionResult) (ih.2 _ _ _ _ _ _ _ result)
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
                          ⟨selected, tests⟩, choice, branch⟩ := accepted
                        exact .wordMatch (ih.1 _ _ _ _ _ _ _ scrutineeResult)
                          (chooseRuntimeWordMatch?_iff.mp choice) (ih.2 _ _ _ _ _ _ _ branch)

set_option doc.verso true in
/-- Successful bounded evaluation gives an independent
{lean}`ClosedSourceExpressionEvaluates` derivation with the same owner, names,
captured values, initial store, result, and final store. The corresponding body
theorem provides this direction for source bodies.

This is conditional on a successful result. It does not classify every failed
optional result as a typing error or establish termination of arbitrary source.
-/
theorem evaluateClosedSourceExpression?_sound
    {budget owner names captured initialStore source value finalStore}
    (accepted : evaluateClosedSourceExpression? budget owner names captured initialStore source =
      some (value, finalStore)) :
    ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore :=
  (simultaneous_sound budget).1 _ _ _ _ _ _ _ accepted

/-- Every computed body endpoint has an independent closed derivation. -/
theorem evaluateClosedSourceBody?_sound
    {budget owner names captured initialStore source value finalStore}
    (accepted : evaluateClosedSourceBody? budget owner names captured initialStore source =
      some (value, finalStore)) :
    ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore :=
  (simultaneous_sound budget).2 _ _ _ _ _ _ _ accepted

end Solcore.Frontend
