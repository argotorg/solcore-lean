import Solcore.Frontend.TypedLetReturnTreeEvaluator
import Solcore.Frontend.TypedLetReturnTreeEvaluation
import Solcore.Frontend.LocalExpressionEvaluatorSoundnessProperties
import Solcore.Frontend.LocalExpressionEvaluatorCompletenessProperties

/-! Direct body results and independent raw cost evidence agree on the original
syntax and actual caller rows. No annotation meaning or name-freshness premise
is inserted; strict initializers extend the tail with their actual value. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateTypedLetReturnTreeWithCost?_sound
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (accepted : evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost))
    (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment store body value store cost := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
              case returnStmt returned =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                | nil =>
                    cases returned with
                    | none =>
                        simp only [evaluateTypedLetReturnTreeWithCost?, Option.some.injEq, Prod.mk.injEq] at accepted
                        obtain ⟨rfl, rfl⟩ := accepted
                        exact .single .bare
                    | some source =>
                        rw [evaluateTypedLetReturnTreeWithCost?] at accepted
                        exact .single (.expression (evaluateLocalExpressionWithCost?_sound accepted store))
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                | some annotation =>
                    cases optionalInitializer with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                    | some initializer =>
                        simp only [evaluateTypedLetReturnTreeWithCost?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨boundValue, initializerCost⟩, initializerAccepted,
                          ⟨actual, tailCost⟩, tailAccepted, result⟩ := accepted
                        simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
                        obtain ⟨rfl, rfl⟩ := result
                        exact .binding (evaluateLocalExpressionWithCost?_sound initializerAccepted store)
                          (evaluateTypedLetReturnTreeWithCost?_sound tailAccepted store)
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                | nil =>
                    cases optionalElse with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                    | some elseBody =>
                        simp only [evaluateTypedLetReturnTreeWithCost?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, conditionCost⟩, conditionAccepted, result⟩ := accepted
                        cases actual <;> simp only [reduceCtorEq] at result
                        rename_i choice
                        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at result
                        all_goals
                          obtain ⟨⟨actual, branchCost⟩, branchAccepted, result⟩ := result
                          simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
                          obtain ⟨rfl, rfl⟩ := result
                          first
                          | exact .ifTrue (evaluateLocalExpressionWithCost?_sound conditionAccepted store)
                              (evaluateTypedLetReturnTreeWithCost?_sound branchAccepted store)
                          | exact .ifFalse (evaluateLocalExpressionWithCost?_sound conditionAccepted store)
                              (evaluateTypedLetReturnTreeWithCost?_sound branchAccepted store)
termination_by sizeOf body

theorem evaluateTypedLetReturnTreeWithCost?_complete
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment
      initialStore body value finalStore cost) :
    evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost) := by
  induction evaluation with
  | single child =>
      cases child with
      | bare => simp only [evaluateTypedLetReturnTreeWithCost?]
      | expression evaluated =>
          simpa only [evaluateTypedLetReturnTreeWithCost?] using evaluateLocalExpressionWithCost?_complete evaluated
  | binding initializer _ ih | ifTrue initializer _ ih | ifFalse initializer _ ih =>
      simp [evaluateTypedLetReturnTreeWithCost?, evaluateLocalExpressionWithCost?_complete initializer, ih]

end Solcore.Frontend
