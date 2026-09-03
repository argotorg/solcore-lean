import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeEnumBodyOutcomeProperties
import Solcore.Syntax.DeclarativeEnumConstructorExactnessProperties

/-! Exact values and rejection endpoints for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem enumBodyListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftBrace .rightBrace
        EnumConstructorOrdinaryParses)
      EnumBodyRejects :=
  trailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
    enumConstructorExactOutcomeSpec

/-- A successful enum body fixes its span, constructors, and remainder. -/
theorem EnumBodyOrdinaryParses.result_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftConstructors rightConstructors : List Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumBodyOrdinaryParses input leftSpan leftConstructors
      afterLeft)
    (rightParsed : EnumBodyOrdinaryParses input rightSpan rightConstructors
      afterRight) :
    leftSpan = rightSpan ∧ leftConstructors = rightConstructors ∧
      afterLeft = afterRight := by
  rcases enumBodyListExactOutcomeSpec.successResultUnique leftParsed
      rightParsed with ⟨bodyEq, outputEq⟩
  cases bodyEq
  exact ⟨rfl, rfl, outputEq⟩

/-- The single-value enum-body adapter fixes its span and constructor list. -/
theorem EnumBodyOrdinaryOutcomeParses.value_unique
    {input : Remainder}
    {left right : SourceSpan × List Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumBodyOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : EnumBodyOrdinaryOutcomeParses input right afterRight) :
    left = right := by
  rcases EnumBodyOrdinaryParses.result_unique leftParsed rightParsed with
    ⟨spanEq, constructorsEq, outputEq⟩
  exact Prod.ext spanEq constructorsEq

/-- Enum-body rejection fixes its first failing endpoint. -/
theorem EnumBodyRejects.output_unique
    {input left right : Remainder}
    (leftRejected : EnumBodyRejects input left)
    (rightRejected : EnumBodyRejects input right) : left = right :=
  enumBodyListExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- Canonical enum bodies have fully exact ordinary outcomes. -/
theorem enumBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec EnumBodyOrdinaryOutcomeParses
      EnumBodyRejects where
  toDeterministicOutcomeSpec := enumBodyDeterministicOutcomeSpec
  successValueUnique := EnumBodyOrdinaryOutcomeParses.value_unique
  rejectOutputUnique := EnumBodyRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
