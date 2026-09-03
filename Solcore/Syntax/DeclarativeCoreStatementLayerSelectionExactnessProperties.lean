import Solcore.Syntax.DeclarativeCoreStatementLayerSelectionOutcomeProperties
import Solcore.Syntax.DeclarativeTransactionalFallbackExactnessProperties

/-! Exact selected-stage outcomes without exact raw primary rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The selected stage and unique branch values determine the statement AST. -/
theorem StatementLayerSelectionOrdinaryParses.value_unique {alpha : Type}
    {primaryParses : StatementLayerStage → Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage → Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage) (primaryRejects stage))
    (primaryValues : ∀ stage, stage ≠ .fallback →
      ∀ {input left right afterLeft afterRight},
        primaryParses stage input left afterLeft →
        primaryParses stage input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftStage, leftParsed⟩
  rcases rightParsed with ⟨rightStage, rightParsed⟩
  have selected := statementLayer_selectedStage_unique leftParsed.priority
    leftParsed.guard rightParsed.priority rightParsed.guard
  subst rightStage
  cases leftParsed <;> cases rightParsed
  · exact TransactionalFallbackOrdinaryParses.value_unique_of_success
      (fallbackParses := fallbackParses)
      (primaryOutcomes _ (by assumption)) (primaryValues _ (by assumption))
      fallbackValues (by assumption) (by assumption)
  · contradiction
  · contradiction
  · exact fallbackValues (by assumption) (by assumption)

/-- Deterministic stages and unique successful values fix complete results. -/
theorem StatementLayerSelectionOrdinaryParses.result_unique {alpha : Type}
    {primaryParses : StatementLayerStage → Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage → Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage) (primaryRejects stage))
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses fallbackRejects)
    (primaryValues : ∀ stage, stage ≠ .fallback →
      ∀ {input left right afterLeft afterRight},
        primaryParses stage input left afterLeft →
        primaryParses stage input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique (fallbackParses := fallbackParses)
      primaryOutcomes primaryValues fallbackValues rightParsed,
    leftParsed.output_unique primaryOutcomes fallbackOutcomes rightParsed⟩

/-- Guarded rejection rewinds; only final-stage rejection needs an endpoint law. -/
theorem StatementLayerSelectionRejects.output_unique {alpha : Type}
    {primaryParses : StatementLayerStage → Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage → Remainder → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    (fallbackOutputs : ∀ {input left right},
      fallbackRejects input left → fallbackRejects input right → left = right)
    {input left right : Remainder}
    (leftRejects : StatementLayerSelectionRejects primaryParses
      primaryRejects fallbackRejects input left)
    (rightRejects : StatementLayerSelectionRejects primaryParses
      primaryRejects fallbackRejects input right) : left = right := by
  rcases leftRejects with ⟨leftStage, leftRejects⟩
  rcases rightRejects with ⟨rightStage, rightRejects⟩
  have selected := statementLayer_selectedStage_unique leftRejects.priority
    leftRejects.guard rightRejects.priority rightRejects.guard
  subst rightStage
  cases leftRejects <;> cases rightRejects
  · exact TransactionalFallbackRejects.output_unique
      (by assumption) (by assumption)
  · contradiction
  · contradiction
  · exact fallbackOutputs (by assumption) (by assumption)

/-- Priority, successful primary values, and an exact fallback determine every
ordinary result and rejecting endpoint of the complete selected-stage layer. -/
theorem statementLayerSelectionExactOutcomeSpecOfSuccess {alpha : Type}
    (primaryParses : StatementLayerStage → Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage → Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop)
    (fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage) (primaryRejects stage))
    (primaryValues : ∀ stage, stage ≠ .fallback →
      ∀ {input left right afterLeft afterRight},
        primaryParses stage input left afterLeft →
        primaryParses stage input right afterRight → left = right)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec fallbackParses fallbackRejects) :
    ExactDeterministicOutcomeSpec
      (StatementLayerSelectionOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (StatementLayerSelectionRejects primaryParses primaryRejects fallbackRejects) where
  toDeterministicOutcomeSpec :=
    statementLayerSelectionDeterministicOutcomeSpec primaryParses primaryRejects
      fallbackParses fallbackRejects primaryOutcomes
      fallbackOutcomes.toDeterministicOutcomeSpec
  successValueUnique := fun leftParsed rightParsed =>
    leftParsed.value_unique (fallbackParses := fallbackParses) primaryOutcomes
      primaryValues fallbackOutcomes.successValueUnique rightParsed
  rejectOutputUnique := fun leftRejects rightRejects =>
    leftRejects.output_unique (primaryParses := primaryParses)
      (primaryRejects := primaryRejects) (fallbackRejects := fallbackRejects)
      fallbackOutcomes.rejectOutputUnique rightRejects

end Solcore.Syntax.DeclarativeGrammar
