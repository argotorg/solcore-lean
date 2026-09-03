import Solcore.Syntax.DeclarativeSelectedAliasOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact optional aliases of selected imports. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The committed alias marker fixes its complete optional identifier. -/
theorem SelectedAliasOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.Identifier}
    (leftParsed : SelectedAliasOrdinaryParses input left afterLeft)
    (rightParsed : SelectedAliasOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present _ rightMarker _ _ _ _ => exact False.elim (leftAbsent ⟨_, rightMarker⟩)
  | @present _ leftNameValue _ leftMarker leftName _ _ _ =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent ⟨_, leftMarker⟩)
      | @present _ rightNameValue _ _ rightName _ _ _ =>
          have nameEq := leftName.token_unique rightName
          congr 1
          cases leftNameValue
          cases rightNameValue
          simp_all

/-- Alias success fixes both the optional located identifier and remainder. -/
theorem SelectedAliasOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.Identifier}
    (leftParsed : SelectedAliasOrdinaryParses input left afterLeft)
    (rightParsed : SelectedAliasOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- A malformed alias has one endpoint immediately after its marker. -/
theorem SelectedAliasRejects.output_unique {input left right : Remainder}
    (leftRejected : SelectedAliasRejects input left)
    (rightRejected : SelectedAliasRejects input right) : left = right :=
  leftRejected.output_eq.trans rightRejected.output_eq.symm

/-- Optional selected aliases have exact values and rejecting endpoints. -/
theorem selectedAliasExactOutcomeSpec :
    ExactDeterministicOutcomeSpec SelectedAliasOrdinaryParses SelectedAliasRejects where
  toDeterministicOutcomeSpec := selectedAliasDeterministicOutcomeSpec
  successValueUnique := SelectedAliasOrdinaryParses.value_unique
  rejectOutputUnique := SelectedAliasRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
