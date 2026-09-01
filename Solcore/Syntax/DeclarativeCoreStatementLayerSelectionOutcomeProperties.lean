import Solcore.Syntax.DeclarativeCoreStatementLayerPriorityProperties
import Solcore.Syntax.DeclarativeTransactionalFallbackOutcomeProperties

/-!
Generic deterministic outcomes for the selected stage of the ordered Core
statement dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success at one selected stage.  Every guarded primary is wrapped
in the executable transactional fallback; the final stage runs the fallback
directly. -/
inductive StatementLayerSelectionOrdinaryParsesAt {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop) :
    StatementLayerStage → Remainder → alpha → Remainder → Prop where
  | guarded {stage input value output}
      (notFallback : stage ≠ .fallback)
      (priority : StatementLayerPrefixAbsent input stage)
      (guard : StatementLayerGuardAt input stage)
      (parsed : TransactionalFallbackOrdinaryParses
        (primaryParses stage) (primaryRejects stage) fallbackParses input
          value output) :
      StatementLayerSelectionOrdinaryParsesAt primaryParses primaryRejects
        fallbackParses stage input value output
  | fallback {input value output}
      (priority : StatementLayerPrefixAbsent input .fallback)
      (parsed : fallbackParses input value output) :
      StatementLayerSelectionOrdinaryParsesAt primaryParses primaryRejects
        fallbackParses .fallback input value output

/-- Ordinary success at the uniquely selected dispatcher stage. -/
def StatementLayerSelectionOrdinaryParses {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop)
    (input : Remainder) (value : alpha) (output : Remainder) : Prop :=
  ∃ stage, StatementLayerSelectionOrdinaryParsesAt primaryParses
    primaryRejects fallbackParses stage input value output

/-- Exact rejection at one selected stage. -/
inductive StatementLayerSelectionRejectsAt {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackRejects : Remainder → Remainder → Prop) :
    StatementLayerStage → Remainder → Remainder → Prop where
  | guarded {stage input rejected}
      (notFallback : stage ≠ .fallback)
      (priority : StatementLayerPrefixAbsent input stage)
      (guard : StatementLayerGuardAt input stage)
      (rejection : TransactionalFallbackRejects (primaryRejects stage)
        fallbackRejects input rejected) :
      StatementLayerSelectionRejectsAt primaryParses primaryRejects
        fallbackRejects stage input rejected
  | fallback {input rejected}
      (priority : StatementLayerPrefixAbsent input .fallback)
      (rejection : fallbackRejects input rejected) :
      StatementLayerSelectionRejectsAt primaryParses primaryRejects
        fallbackRejects .fallback input rejected

/-- Exact rejection at the uniquely selected dispatcher stage. -/
def StatementLayerSelectionRejects {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackRejects : Remainder → Remainder → Prop)
    (input rejected : Remainder) : Prop :=
  ∃ stage, StatementLayerSelectionRejectsAt primaryParses primaryRejects
    fallbackRejects stage input rejected

theorem StatementLayerSelectionOrdinaryParsesAt.priority {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {stage input value output}
    (parsed : StatementLayerSelectionOrdinaryParsesAt primaryParses
      primaryRejects fallbackParses stage input value output) :
    StatementLayerPrefixAbsent input stage := by
  cases parsed <;> assumption

theorem StatementLayerSelectionOrdinaryParsesAt.guard {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {stage input value output}
    (parsed : StatementLayerSelectionOrdinaryParsesAt primaryParses
      primaryRejects fallbackParses stage input value output) :
    StatementLayerGuardAt input stage := by
  cases parsed <;> simp_all [StatementLayerGuardAt]

theorem StatementLayerSelectionRejectsAt.priority {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    {stage input rejected}
    (rejection : StatementLayerSelectionRejectsAt primaryParses
      primaryRejects fallbackRejects stage input rejected) :
    StatementLayerPrefixAbsent input stage := by
  cases rejection <;> assumption

theorem StatementLayerSelectionRejectsAt.guard {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    {stage input rejected}
    (rejection : StatementLayerSelectionRejectsAt primaryParses
      primaryRejects fallbackRejects stage input rejected) :
    StatementLayerGuardAt input stage := by
  cases rejection <;> simp_all [StatementLayerGuardAt]

/-- Selected-stage success has one output whenever every primary and the
shared fallback have deterministic outcomes. -/
theorem StatementLayerSelectionOrdinaryParses.output_unique {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage)
        (primaryRejects stage))
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses
      fallbackRejects)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : StatementLayerSelectionOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftStage, leftParsed⟩
  rcases rightParsed with ⟨rightStage, rightParsed⟩
  have selected := statementLayer_selectedStage_unique leftParsed.priority
    leftParsed.guard rightParsed.priority rightParsed.guard
  subst rightStage
  cases leftParsed <;> cases rightParsed
  · exact TransactionalFallbackOrdinaryParses.output_unique
      (primaryOutcomes _ (by assumption)) fallbackOutcomes
        (by assumption) (by assumption)
  · contradiction
  · contradiction
  · exact fallbackOutcomes.successOutputUnique (by assumption)
      (by assumption)

/-- Selected-stage rejection excludes every ordinary success. -/
theorem StatementLayerSelectionRejects.disjointOrdinary {alpha : Type}
    {primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop}
    {fallbackParses : Remainder → alpha → Remainder → Prop}
    {fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage)
        (primaryRejects stage))
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses
      fallbackRejects)
    {input rejected : Remainder}
    (rejection : StatementLayerSelectionRejects primaryParses primaryRejects
      fallbackRejects input rejected) :
    ¬ ∃ value output, StatementLayerSelectionOrdinaryParses
      primaryParses primaryRejects fallbackParses input value output := by
  rintro ⟨value, output, successful⟩
  rcases rejection with ⟨rejectedStage, rejection⟩
  rcases successful with ⟨successfulStage, successful⟩
  have selected := statementLayer_selectedStage_unique rejection.priority
    rejection.guard successful.priority successful.guard
  subst successfulStage
  cases rejection <;> cases successful
  · exact TransactionalFallbackRejects.disjointOrdinary
      (primaryOutcomes _ (by assumption)) fallbackOutcomes (by assumption)
        ⟨_, _, by assumption⟩
  · contradiction
  · contradiction
  · exact fallbackOutcomes.successRejectDisjoint (by assumption)
      ⟨_, _, by assumption⟩

/-- Package deterministic outcomes of the generic selected-stage layer. -/
theorem statementLayerSelectionDeterministicOutcomeSpec {alpha : Type}
    (primaryParses : StatementLayerStage →
      Remainder → alpha → Remainder → Prop)
    (primaryRejects : StatementLayerStage →
      Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop)
    (fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : ∀ stage, stage ≠ .fallback →
      DeterministicOutcomeSpec (primaryParses stage)
        (primaryRejects stage))
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses
      fallbackRejects) :
    DeterministicOutcomeSpec
      (StatementLayerSelectionOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (StatementLayerSelectionRejects primaryParses primaryRejects
        fallbackRejects) where
  successOutputUnique := StatementLayerSelectionOrdinaryParses.output_unique
    primaryOutcomes fallbackOutcomes
  successRejectDisjoint := StatementLayerSelectionRejects.disjointOrdinary
    primaryOutcomes fallbackOutcomes

end Solcore.Syntax.DeclarativeGrammar
