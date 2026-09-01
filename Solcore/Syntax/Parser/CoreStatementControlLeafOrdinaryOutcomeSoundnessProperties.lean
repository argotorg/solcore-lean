import Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeProperties
import Solcore.Syntax.Parser.CoreBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementControlSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-!
Executable ordinary outcomes for Core block and terminated-control statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ControlInternals

/-- A successful executable terminated-control statement retains both exact
tokens, its fixed statement value, span, and final remainder. -/
theorem terminatedControl_success_ordinary_sound
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input output : State} {statement : Statement}
    (result : terminatedControl keywordValue statementValue input =
      .ok statement output) :
    DeclarativeGrammar.TerminatedControlStatementOrdinaryParses keywordValue
      statementValue input.declarativeRemainder statement
        output.declarativeRemainder :=
  terminatedControl_success_sound keywordValue statementValue result

/-- A rejected executable terminated-control statement records the first
missing required token and the exact rejected remainder. -/
theorem terminatedControl_reject_ordinary_sound
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input rejected : State} {failure : Failure}
    (result : terminatedControl keywordValue statementValue input =
      .reject failure rejected) :
    DeclarativeGrammar.TerminatedControlStatementRejects keywordValue
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold terminatedControl at result
  cases markerResult : keyword keywordValue .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq keywordValue
        .statement markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt keywordValue .statement
          markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses keywordValue
        .statement markerResult
      cases semicolonResult : symbol .semicolon .statement afterMarker with
      | invariant error => simp [semicolonResult] at result
      | ok semicolon output => simp [semicolonResult, pure] at result
      | reject semicolonFailure semicolonRejected =>
          have semicolonRejectedEq := symbol_reject_state_eq .semicolon
            .statement semicolonResult
          subst semicolonRejected
          simp only [semicolonResult] at result
          cases result
          exact .semicolonMissing marker.span markerParsed
            (symbol_reject_tokenKindAbsentAt .semicolon .statement
              semicolonResult)

/-- Package both executable outcomes of a fixed terminated-control
statement. -/
theorem terminatedControl_ordinaryOutcome_sound
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    (forall {input output : State} {statement : Statement},
      terminatedControl keywordValue statementValue input =
        .ok statement output ->
          DeclarativeGrammar.TerminatedControlStatementOrdinaryParses
            keywordValue statementValue input.declarativeRemainder statement
              output.declarativeRemainder) ∧
    (forall {input rejected : State} {failure : Failure},
      terminatedControl keywordValue statementValue input =
        .reject failure rejected ->
          DeclarativeGrammar.TerminatedControlStatementRejects keywordValue
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨terminatedControl_success_ordinary_sound keywordValue statementValue,
    terminatedControl_reject_ordinary_sound keywordValue statementValue⟩

/-- Re-export deterministic terminated-control outcomes under the executable
bridge name. -/
theorem terminatedControl_ordinaryOutcomeSpec
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.TerminatedControlStatementOrdinaryParses
        keywordValue statementValue)
      (DeclarativeGrammar.TerminatedControlStatementRejects keywordValue) :=
  DeclarativeGrammar.terminatedControlStatementDeterministicOutcomeSpec
    keywordValue statementValue

end ControlInternals

/-- A successful executable block statement retains the diagnostic-inclusive
ordinary outcome of its raw required block. -/
theorem blockStatement_success_ordinary_sound
    (statementParser : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder -> Statement ->
      DeclarativeGrammar.Remainder -> Prop)
    (statementRejects : DeclarativeGrammar.Remainder ->
      DeclarativeGrammar.Remainder -> Prop)
    (statementSuccessSound : forall {input output : State}
      {statement : Statement}, statementParser input = .ok statement output ->
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (statementRejectSound : forall {input rejected : State}
      {failure : Failure}, statementParser input = .reject failure rejected ->
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input output : State} {statement : Statement}
    (result : blockStatement statementParser input = .ok statement output) :
    DeclarativeGrammar.BlockStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold blockStatement at result
  cases bodyResult : coreBlock statementParser .require input with
  | invariant error => simp [bind, bodyResult] at result
  | reject failure rejected => simp [bind, bodyResult] at result
  | ok body afterBody =>
      simp only [bind, bodyResult, pure] at result
      cases result
      exact .parsed ((coreBlock_ordinaryOutcome_sound statementParser .require
        statementOrdinary statementRejects statementSuccessSound
          statementRejectSound).1 bodyResult)

/-- A rejected executable block statement propagates the exact ordinary raw
block rejection. -/
theorem blockStatement_reject_ordinary_sound
    (statementParser : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder -> Statement ->
      DeclarativeGrammar.Remainder -> Prop)
    (statementRejects : DeclarativeGrammar.Remainder ->
      DeclarativeGrammar.Remainder -> Prop)
    (statementSuccessSound : forall {input output : State}
      {statement : Statement}, statementParser input = .ok statement output ->
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (statementRejectSound : forall {input rejected : State}
      {failure : Failure}, statementParser input = .reject failure rejected ->
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : blockStatement statementParser input = .reject failure rejected) :
    DeclarativeGrammar.BlockStatementRejects statementOrdinary statementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold blockStatement at result
  cases bodyResult : coreBlock statementParser .require input with
  | invariant error => simp [bind, bodyResult] at result
  | ok body output => simp [bind, bodyResult, pure] at result
  | reject bodyFailure bodyRejected =>
      simp only [bind, bodyResult] at result
      cases result
      exact (coreBlock_ordinaryOutcome_sound statementParser .require
        statementOrdinary statementRejects statementSuccessSound
          statementRejectSound).2 bodyResult

/-- Package both executable ordinary outcomes of `blockStatement`. -/
theorem blockStatement_ordinaryOutcome_sound
    (statementParser : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder -> Statement ->
      DeclarativeGrammar.Remainder -> Prop)
    (statementRejects : DeclarativeGrammar.Remainder ->
      DeclarativeGrammar.Remainder -> Prop)
    (statementSuccessSound : forall {input output : State}
      {statement : Statement}, statementParser input = .ok statement output ->
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (statementRejectSound : forall {input rejected : State}
      {failure : Failure}, statementParser input = .reject failure rejected ->
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (forall {input output : State} {statement : Statement},
      blockStatement statementParser input = .ok statement output ->
        DeclarativeGrammar.BlockStatementOrdinaryParses statementOrdinary
          input.declarativeRemainder statement output.declarativeRemainder) ∧
    (forall {input rejected : State} {failure : Failure},
      blockStatement statementParser input = .reject failure rejected ->
        DeclarativeGrammar.BlockStatementRejects statementOrdinary
          statementRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨blockStatement_success_ordinary_sound statementParser statementOrdinary
      statementRejects statementSuccessSound statementRejectSound,
    blockStatement_reject_ordinary_sound statementParser statementOrdinary
      statementRejects statementSuccessSound statementRejectSound⟩

/-- Re-export deterministic block-statement outcomes under the executable
bridge name. -/
theorem blockStatement_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder -> Statement ->
      DeclarativeGrammar.Remainder -> Prop}
    {statementRejects : DeclarativeGrammar.Remainder ->
      DeclarativeGrammar.Remainder -> Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.BlockStatementOrdinaryParses statementOrdinary)
      (DeclarativeGrammar.BlockStatementRejects statementOrdinary
        statementRejects) :=
  DeclarativeGrammar.blockStatementDeterministicOutcomeSpec statementOutcomes

end Solcore.Syntax.Parser
