import Solcore.Core.LocalFragment.RuntimeSafety
import Solcore.Core.Correspondence

/-! Local termination does not require a typed store or terminating closures
in the environment. Returning those values does not execute or dereference them. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentTermination

open Solcore.Core

private def returnedPair : Expr :=
  .letE (.var 0) (.ifE (.bool true) (.pair (.var 0) (.var 2)) (.pair (.var 1) (.var 2)))

private theorem returnedPair_fragment : returnedPair.LocalFragment :=
  .letE .var (.ifE .bool (.pair .var .var) (.pair .var .var))

private theorem returnedPair_typed (parameterType resultType : Ty) :
    HasType [.cell .word, .function parameterType resultType] returnedPair
      (.product (.cell .word) (.function parameterType resultType)) :=
  .letE (.var rfl) (.ifE .bool (.pair (.var rfl) (.var rfl)) (.pair (.var rfl) (.var rfl)))

/-- The same arbitrary store is retained while local binding and branching
return an untouched reference and closure supplied by the caller. -/
theorem returning_a_closure_and_reference_needs_no_store_or_termination_premise
    {parameterType resultType : Ty} {body : Expr} {captured : Environment}
    (closureTyped : RuntimeValueHasType [.word]
      (.closure parameterType resultType body captured) (.function parameterType resultType))
    (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel
        (.initial returnedPair
          [.cellRef .word 0, .closure parameterType resultType body captured] store) =
        .done (.pair (.cellRef .word 0) (.closure parameterType resultType body captured)) store := by
  have environmentTyped : RuntimeEnvironmentHasTypes [.word]
      [.cellRef .word 0, .closure parameterType resultType body captured]
      [.cell .word, .function parameterType resultType] :=
    .cons (.cellRef rfl) (.cons closureTyped .nil)
  obtain ⟨value, evaluation, _⟩ :=
    returnedPair_fragment.runtime_evaluates (returnedPair_typed parameterType resultType)
      environmentTyped store
  have originalValue : Evaluates
      [.cellRef .word 0, .closure parameterType resultType body captured]
      store returnedPair
      (.pair (.cellRef .word 0) (.closure parameterType resultType body captured)) store :=
    .letE (.var rfl) (.ifTrue .bool (.pair (.var rfl) (.var rfl)))
  obtain ⟨rfl, _⟩ := evaluation_deterministic evaluation originalValue
  exact evaluation_runStateful_complete_with_sufficient_fuel evaluation

/-- Even an absent referenced location is harmless when the expression only
returns the reference. It would not satisfy the full machine's store invariant. -/
theorem returning_reference_from_an_empty_store :
    (¬ StoreHasTypes [.word] []) ∧
      ∃ value, Evaluates [.cellRef .word 0] [] (.var 0) value [] ∧
        RuntimeValueHasType [.word] value (.cell .word) := by
  constructor
  · intro typed
    have sameLength := typed.length_eq
    simp at sameLength
  · exact Expr.LocalFragment.var.runtime_evaluates (.var rfl)
      (.cons (.cellRef rfl) .nil) []

end Tests.CoreLocalFragmentTermination
