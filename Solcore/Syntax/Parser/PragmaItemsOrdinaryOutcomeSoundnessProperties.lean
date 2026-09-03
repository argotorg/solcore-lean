import Solcore.Syntax.DeclarativePragmaItemsExactnessProperties
import Solcore.Syntax.Parser.PragmaItemsOrdinaryRejectionSoundnessProperties

/-! Complete executable ordinary outcomes for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

/-- Package success and rejection reflection for the production tail fuel. -/
theorem pragmaItemsTail_production_ordinaryOutcome_sound
    (itemsRev : List Identifier) :
    (∀ {input output : State} {items : List Identifier},
      pragmaItemsTail (input.remainingCount + 1) itemsRev input =
          .ok items output →
        ∃ suffix,
          items = itemsRev.reverse ++ suffix ∧
          DeclarativeGrammar.PragmaItemsTailOrdinaryParses
            input.declarativeRemainder suffix output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      pragmaItemsTail (input.remainingCount + 1) itemsRev input =
          .reject failure rejected →
        DeclarativeGrammar.PragmaItemsTailRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev,
    pragmaItemsTail_production_reject_ordinaryOutcome_sound itemsRev⟩

/-- Package exact executable success and rejection for public pragma items. -/
theorem pragmaItems_ordinaryOutcome_sound :
    (∀ {input output : State} {items : List Identifier},
      pragmaItems input = .ok items output →
        DeclarativeGrammar.PragmaItemsOrdinaryParses
          input.declarativeRemainder items output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      pragmaItems input = .reject failure rejected →
        DeclarativeGrammar.PragmaItemsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨pragmaItems_success_ordinaryOutcome_sound,
    pragmaItems_reject_ordinaryOutcome_sound⟩

/-- Re-export the parser-independent deterministic pragma-tail contract. -/
theorem pragmaItemsTail_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PragmaItemsTailOrdinaryParses
      DeclarativeGrammar.PragmaItemsTailRejects :=
  DeclarativeGrammar.pragmaItemsTailDeterministicOutcomeSpec

/-- Re-export the parser-independent deterministic pragma-item contract. -/
theorem pragmaItems_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PragmaItemsOrdinaryParses
      DeclarativeGrammar.PragmaItemsRejects :=
  DeclarativeGrammar.pragmaItemsDeterministicOutcomeSpec

/-- Re-export unconditional exact outcomes of forward pragma-item suffixes. -/
theorem pragmaItemsTail_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PragmaItemsTailOrdinaryParses
      DeclarativeGrammar.PragmaItemsTailRejects :=
  DeclarativeGrammar.pragmaItemsTailExactOutcomeSpec

/-- With the same reverse prefix, two production-tail successes fix the
complete forward item list and declarative remainder. -/
theorem pragmaItemsTail_production_success_result_unique
    (itemsRev : List Identifier)
    {input leftOutput rightOutput : State} {left right : List Identifier}
    (leftResult : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok left leftOutput)
    (rightResult : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev
    leftResult with ⟨leftSuffix, leftEq, leftParsed⟩
  rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev
    rightResult with ⟨rightSuffix, rightEq, rightParsed⟩
  rcases pragmaItemsTail_exactOutcomeSpec.successResultUnique leftParsed
    rightParsed with ⟨suffixEq, afterEq⟩
  constructor
  · rw [leftEq, rightEq, suffixEq]
  · exact afterEq

/-- Production-tail rejection fixes its declarative endpoint; failure
diagnostic payloads are not compared. -/
theorem pragmaItemsTail_production_reject_output_unique
    (itemsRev : List Identifier)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .reject leftFailure leftOutput)
    (rightResult : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pragmaItemsTail_exactOutcomeSpec.rejectOutputUnique
    (pragmaItemsTail_production_reject_ordinaryOutcome_sound itemsRev leftResult)
    (pragmaItemsTail_production_reject_ordinaryOutcome_sound itemsRev rightResult)

/-- Re-export unconditional exact complete pragma-item outcomes. -/
theorem pragmaItems_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PragmaItemsOrdinaryParses
      DeclarativeGrammar.PragmaItemsRejects :=
  DeclarativeGrammar.pragmaItemsExactOutcomeSpec

/-- Two pragma-item successes fix their forward items and remainder. -/
theorem pragmaItems_success_result_unique
    {input leftOutput rightOutput : State} {left right : List Identifier}
    (leftResult : pragmaItems input = .ok left leftOutput)
    (rightResult : pragmaItems input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pragmaItems_exactOutcomeSpec.successResultUnique
    (pragmaItems_success_ordinaryOutcome_sound leftResult)
    (pragmaItems_success_ordinaryOutcome_sound rightResult)

/-- Two pragma-item rejections fix their declarative endpoints. -/
theorem pragmaItems_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : pragmaItems input = .reject leftFailure leftOutput)
    (rightResult : pragmaItems input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pragmaItems_exactOutcomeSpec.rejectOutputUnique
    (pragmaItems_reject_ordinaryOutcome_sound leftResult)
    (pragmaItems_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.PragmaInternals
