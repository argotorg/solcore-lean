import Solcore.Syntax.Grammar.Declarations
import Solcore.Syntax.Parser.Internal.ContractProofs
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.DeriveSoundness
import Solcore.Syntax.Parser.Internal.ImportProofs
import Solcore.Syntax.Internal.DeriveOutcomes
import Solcore.Syntax.Parser.Internal.EnumProofs
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Internal.ContractBodyOutcomes
import Solcore.Syntax.Parser.Internal.ParameterSoundness

/-!
Soundness of the parsers of contract bodies: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveAttributeRecoveryBoundaryProperties
/-!
Executable-to-declarative boundary bridges for malformed derive-attribute
recovery.  Recursive tail reflection is intentionally kept separate.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem isSymbol_eq_true_of_tokenAt (value : Symbol)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value }) :
    isSymbol input value = true := by
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem tokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .topItem present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .topItem parsed).1⟩

private theorem atTopItemStart_eq_true_of_importTerminatorTopItemStartsAt
    {input : State}
    (starts : DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder) :
    atTopItemStart input = true := by
  rcases starts with ⟨kind, member, span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := kind } at token
  have peekKind : input.peekKind? = some kind := by
    unfold State.peekKind? State.peek?
    simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  unfold atTopItemStart
  rw [peekKind]
  exact (importTerminatorTopItemStartKind_iff kind).mpr member

namespace DeriveAttributeInternals

private theorem declarationBoundaryGuard_eq (input : State) :
    atDeriveDeclarationBoundary input =
      (atTopItemStart input || ContractInternals.startsContractField input ||
        isSymbol input .rightBrace) := by
  rfl

/-- A true executable declaration-boundary guard exposes the exact first
matching declarative boundary in dispatcher priority order. -/
theorem recoveryDeclarationStartsAt_of_atDeriveDeclarationBoundary_eq_true
    {input : State} (present : atDeriveDeclarationBoundary input = true) :
    DeclarativeGrammar.DeriveAttributeRecoveryDeclarationStartsAt
      input.declarativeRemainder := by
  rw [declarationBoundaryGuard_eq] at present
  by_cases topItem : atTopItemStart input = true
  · exact .topItem
      (importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true topItem)
  · have topItemFalse : atTopItemStart input = false :=
      Bool.eq_false_iff.mpr topItem
    by_cases field : ContractInternals.startsContractField input = true
    · exact .contractField
        (ContractInternals.contractFieldStartsAt_of_startsContractField_eq_true
          field)
    · have fieldFalse :
          ContractInternals.startsContractField input = false :=
        Bool.eq_false_iff.mpr field
      have rightBrace : isSymbol input .rightBrace = true := by
        simpa [topItemFalse, fieldFalse] using present
      rcases tokenAt_of_isSymbol_eq_true .rightBrace rightBrace with
        ⟨span, token⟩
      exact .rightBrace span token

/-- Every declarative recovery declaration boundary makes the executable
boundary guard true. -/
theorem atDeriveDeclarationBoundary_eq_true_of_recoveryDeclarationStartsAt
    {input : State}
    (starts : DeclarativeGrammar.DeriveAttributeRecoveryDeclarationStartsAt
      input.declarativeRemainder) :
    atDeriveDeclarationBoundary input = true := by
  rw [declarationBoundaryGuard_eq]
  cases starts with
  | topItem topItemStarts =>
      have topItem :=
        atTopItemStart_eq_true_of_importTerminatorTopItemStartsAt topItemStarts
      simp [topItem]
  | contractField fieldStarts =>
      have field :=
        ContractInternals.startsContractField_eq_true_of_contractFieldStartsAt
          fieldStarts
      simp [field]
  | rightBrace span token =>
      have rightBrace := isSymbol_eq_true_of_tokenAt .rightBrace token
      simp [rightBrace]

/-- The second executable tail guard gives an exact nonconsuming unclosed
recovery stop.  A preceding right-bracket guard is handled by the caller. -/
theorem recoveryStops_of_unclosedGuard_eq_true (input : State)
    (stops : (input.atEnd || atDeriveDeclarationBoundary input) = true) :
    DeclarativeGrammar.DeriveAttributeRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have boundary : atDeriveDeclarationBoundary input = true := by
      simpa [atEndFalse] using stops
    exact .declaration
      (recoveryDeclarationStartsAt_of_atDeriveDeclarationBoundary_eq_true
        boundary)

/-- With the second guard false, failure to advance is exactly a missing array
slot inside the active token window. -/
theorem recoveryStops_of_advance?_eq_none (input : State)
    (guard : (input.atEnd || atDeriveDeclarationBoundary input) = false)
    (advanced : input.advance? = none) :
    DeclarativeGrammar.DeriveAttributeRecoveryStops
      input.declarativeRemainder := by
  have notAtEnd : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    have atEndTrue : input.atEnd = true := by
      unfold State.atEnd
      exact decide_eq_true atEnd
    simp [atEndTrue] at guard
  have inside : input.cursor < input.window.endIndex := by omega
  apply DeclarativeGrammar.DeriveAttributeRecoveryStops.missingToken inside
  unfold State.advance? State.peek? at advanced
  simpa [State.declarativeRemainder, inside] using advanced

/-- A current token under a false second guard excludes every declarative
recovery stop, so the tail must advance after its separate `]` check. -/
theorem no_recoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (guard : (input.atEnd || atDeriveDeclarationBoundary input) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.DeriveAttributeRecoveryStops
      input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | declaration starts =>
      have boundary :=
        atDeriveDeclarationBoundary_eq_true_of_recoveryDeclarationStartsAt
          starts
      simp [boundary] at guard
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

end DeriveAttributeInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveAttributeRecoveredOrdinarySuccessSoundnessProperties
/-! Exact ordinary-success reflection for derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.DeriveAttributeInternals

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

/-- Every successful malformed-tail scan follows the exact priority-ordered
declarative recovery relation, at any fuel. -/
theorem recoverTail_success_ordinaryOutcome_sound (hash : SourceSpan) :
    ∀ fuel last input value output,
      recoverTail hash last fuel input = .ok value output →
      DeclarativeGrammar.DeriveAttributeRecoveryTailParses hash last
        input.declarativeRemainder value output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input value output result
      simp [recoverTail] at result
  | succ fuel inductionHypothesis =>
      intro last input value output result
      unfold recoverTail at result
      cases closingPresent : isSymbol input .rightBracket with
      | true =>
          simp only [closingPresent, if_true] at result
          cases closingResult : symbol .rightBracket .topItem input with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing afterClosing =>
              simp only [closingResult] at result
              unfold finishRecovered at result
              cases result
              simpa [State.emit, State.declarativeRemainder,
                DeclarativeGrammar.recoveredDeriveAttributeValue] using
                (DeclarativeGrammar.DeriveAttributeRecoveryTailParses.malformed
                  (hash := hash) (last := last) closing.span
                  (symbol_success_exactTokenParses .rightBracket .topItem
                    closingResult))
      | false =>
          have closingAbsent :=
            symbolAbsentAt_of_isSymbol_eq_false .rightBracket closingPresent
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases unclosedGuard :
              (input.atEnd || atDeriveDeclarationBoundary input) with
          | true =>
              simp only [unclosedGuard, if_true] at result
              unfold finishRecovered at result
              cases result
              simpa [State.emit, State.declarativeRemainder,
                DeclarativeGrammar.recoveredDeriveAttributeValue] using
                (DeclarativeGrammar.DeriveAttributeRecoveryTailParses.unclosed
                  (hash := hash) (last := last) closingAbsent
                  (recoveryStops_of_unclosedGuard_eq_true input
                    unclosedGuard))
          | false =>
              simp only [unclosedGuard, Bool.false_eq_true, if_false] at result
              cases advanced : input.advance? with
              | none =>
                  simp only [advanced] at result
                  unfold finishRecovered at result
                  cases result
                  simpa [State.emit, State.declarativeRemainder,
                    DeclarativeGrammar.recoveredDeriveAttributeValue] using
                    (DeclarativeGrammar.DeriveAttributeRecoveryTailParses.unclosed
                      (hash := hash) (last := last) closingAbsent
                      (recoveryStops_of_advance?_eq_none input unclosedGuard
                        advanced))
              | some pair =>
                  rcases pair with ⟨token, next⟩
                  simp only [advanced] at result
                  rcases advance?_state_shape advanced with ⟨found, nextEq⟩
                  have tail := inductionHypothesis token.span next value output
                    result
                  rw [nextEq] at tail
                  exact .next closingAbsent
                    (no_recoveryStops_of_nonBoundary_token unclosedGuard found)
                    (tokenAt_of_peek?_eq_some found) tail

/-- Production fuel specializes successful malformed-tail reflection. -/
theorem recoverTail_production_success_ordinaryOutcome_sound
    (hash last : SourceSpan) {input output : State}
    {value : DeriveAttribute}
    (result : recoverTail hash last (input.remainingCount + 1) input =
      .ok value output) :
    DeclarativeGrammar.DeriveAttributeRecoveryTailParses hash last
      input.declarativeRemainder value output.declarativeRemainder :=
  recoverTail_success_ordinaryOutcome_sound hash
    (input.remainingCount + 1) last input value output result

/-- Every successful recovered derive path consumes the exact `#[` prefix and
then follows the exact malformed-tail recovery relation. -/
theorem recovered_success_ordinaryOutcome_sound
    {input output : State} {value : DeriveAttribute}
    (result : recovered input = .ok value output) :
    DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold recovered at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp [hashResult] at result
  | reject failure rejected => simp [hashResult] at result
  | ok hash afterHash =>
      simp only [hashResult] at result
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp [openingResult] at result
      | reject failure rejected => simp [openingResult] at result
      | ok opening afterOpening =>
          simp only [openingResult] at result
          exact .recovered hash.span opening.span
            (symbol_success_exactTokenParses .hash .topItem hashResult)
            (symbol_success_exactTokenParses .leftBracket .topItem
              openingResult)
            (recoverTail_production_success_ordinaryOutcome_sound hash.span
              opening.span result)

end Solcore.Syntax.Parser.DeriveAttributeInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveAttributeRecoveredOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export recovered-path success reflection outside the internal
namespace. -/
theorem deriveAttributeRecovered_success_ordinaryOutcome_sound
    {input output : State} {value : DeriveAttribute}
    (result : DeriveAttributeInternals.recovered input = .ok value output) :
    DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value output.declarativeRemainder :=
  DeriveAttributeInternals.recovered_success_ordinaryOutcome_sound result

/-- Re-export recovered-path rejection reflection outside the internal
namespace. -/
theorem deriveAttributeRecovered_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : DeriveAttributeInternals.recovered input =
      .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeRecoveredRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  DeriveAttributeInternals.recovered_reject_ordinaryOutcome_sound result

/-- Package unconditional success and exact rejection reflection for the
recovered derive-attribute path. -/
theorem deriveAttributeRecovered_ordinaryOutcome_sound :
    (∀ {input output : State} {value : DeriveAttribute},
      DeriveAttributeInternals.recovered input = .ok value output →
        DeclarativeGrammar.DeriveAttributeRecoveredParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      DeriveAttributeInternals.recovered input = .reject failure rejected →
        DeclarativeGrammar.DeriveAttributeRecoveredRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨deriveAttributeRecovered_success_ordinaryOutcome_sound,
    deriveAttributeRecovered_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive recovered derive outcomes. -/
theorem deriveAttributeRecovered_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeRecoveredParses
      DeclarativeGrammar.DeriveAttributeRecoveredRejects :=
  DeclarativeGrammar.deriveAttributeRecoveredDeterministicOutcomeSpec

/-- Re-export exact recovered-path value and rejection-endpoint
functionality. -/
theorem deriveAttributeRecovered_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeRecoveredParses
      DeclarativeGrammar.DeriveAttributeRecoveredRejects :=
  DeclarativeGrammar.deriveAttributeRecoveredExactOutcomeSpec

/-- Two successful recovered-path reflections have the same derive attribute
and final declarative remainder. -/
theorem deriveAttributeRecovered_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : DeriveAttribute}
    (leftResult : DeriveAttributeInternals.recovered input =
      .ok left leftOutput)
    (rightResult : DeriveAttributeInternals.recovered input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeRecoveredParses.result_unique
    (deriveAttributeRecovered_success_ordinaryOutcome_sound leftResult)
    (deriveAttributeRecovered_success_ordinaryOutcome_sound rightResult)

/-- Two rejected recovered-path reflections have the same exact declarative
endpoint. -/
theorem deriveAttributeRecovered_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : DeriveAttributeInternals.recovered input =
      .reject leftFailure leftOutput)
    (rightResult : DeriveAttributeInternals.recovered input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeRecoveredRejects.output_unique
    (deriveAttributeRecovered_reject_ordinaryOutcome_sound leftResult)
    (deriveAttributeRecovered_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveAttributeOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for public derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every public derive-attribute success is the preferred normal success or
the exact recovered success selected after a normal-path rejection. -/
theorem deriveAttribute_success_ordinaryOutcome_sound
    {input output : State} {value : DeriveAttribute}
    (result : deriveAttribute input = .ok value output) :
    DeclarativeGrammar.DeriveAttributeOrdinaryParses
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold deriveAttribute orElse at result
  cases validResult : DeriveAttributeInternals.valid input with
  | invariant error => simp [validResult] at result
  | ok normal afterNormal =>
      simp only [validResult] at result
      cases result
      exact .normal
        (deriveAttributeValid_success_ordinaryOutcome_sound validResult)
  | reject validFailure validRejected =>
      simp only [validResult] at result
      exact .recovered
        (deriveAttributeValid_reject_ordinaryOutcome_sound validResult)
        (deriveAttributeRecovered_success_ordinaryOutcome_sound result)

/-- Every public derive-attribute rejection records rejection of both the
normal attempt and recovery retried at the original input. -/
theorem deriveAttribute_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : deriveAttribute input = .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold deriveAttribute orElse at result
  cases validResult : DeriveAttributeInternals.valid input with
  | invariant error => simp [validResult] at result
  | ok normal afterNormal => simp [validResult] at result
  | reject validFailure validRejected =>
      simp only [validResult] at result
      exact .both
        (deriveAttributeValid_reject_ordinaryOutcome_sound validResult)
        (deriveAttributeRecovered_reject_ordinaryOutcome_sound result)

/-- Package unconditional public success and exact double-rejection
reflection. -/
theorem deriveAttribute_ordinaryOutcome_sound :
    (∀ {input output : State} {value : DeriveAttribute},
      deriveAttribute input = .ok value output →
        DeclarativeGrammar.DeriveAttributeOrdinaryParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      deriveAttribute input = .reject failure rejected →
        DeclarativeGrammar.DeriveAttributeRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨deriveAttribute_success_ordinaryOutcome_sound,
    deriveAttribute_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive public derive-attribute outcomes. -/
theorem deriveAttribute_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeOrdinaryParses
      DeclarativeGrammar.DeriveAttributeRejects :=
  DeclarativeGrammar.deriveAttributeDeterministicOutcomeSpec

/-- Re-export full value and rejection-endpoint functionality for public
derive attributes at the executable reflection boundary. -/
theorem deriveAttribute_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeOrdinaryParses
      DeclarativeGrammar.DeriveAttributeRejects :=
  DeclarativeGrammar.deriveAttributeExactOutcomeSpec

/-- Two successful executable reflections have the same public derive
attribute and final declarative remainder. -/
theorem deriveAttribute_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : DeriveAttribute}
    (leftResult : deriveAttribute input = .ok left leftOutput)
    (rightResult : deriveAttribute input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeOrdinaryParses.result_unique
    (deriveAttribute_success_ordinaryOutcome_sound leftResult)
    (deriveAttribute_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same exact public
declarative endpoint. -/
theorem deriveAttribute_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : deriveAttribute input = .reject leftFailure leftOutput)
    (rightResult : deriveAttribute input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeRejects.output_unique
    (deriveAttribute_reject_ordinaryOutcome_sound leftResult)
    (deriveAttribute_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractDeriveAttachmentSoundnessProperties
/-! Declarative transformation performed when a contract enum gains `derive`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/--
Attaching an already parsed derive attribute changes only the enum's retained
attribute and outer start.  Its marker-to-body token derivation and final
remainder stay unchanged.
-/
theorem EnumDeclParses.withDerive
    {input output : Remainder} {declaration : Syntax.EnumDecl}
    (derive : Syntax.DeriveAttribute)
    (parsed : EnumDeclParses none input declaration output) :
    EnumDeclParses (some derive) input {
      declaration with
      span := SourceSpan.cover derive.span declaration.span
      value := {
        declaration.value with deriveAttribute := some derive
      }
    } output := by
  cases parsed with
  | parsed markerSpan markerToken nameParsed parametersParsed bodyParsed =>
      simpa [SourceSpan.cover] using
        (EnumDeclParses.parsed (deriveAttribute := some derive) markerSpan
          markerToken nameParsed parametersParsed bodyParsed)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractDeriveAttachmentOrdinarySoundnessProperties
/-! Exact executable reflection for contract-member derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Every successful derive attachment performs the exact pure AST
transformation and leaves the declarative parser remainder unchanged. -/
theorem attachContractDerive_success_ordinaryOutcome_sound
    {derive : DeriveAttribute} {member attached : ContractMember}
    {input output : State}
    (result : attachContractDerive derive member input = .ok attached output) :
    DeclarativeGrammar.ContractDeriveAttaches derive member attached ∧
      output.declarativeRemainder = input.declarativeRemainder := by
  rcases member with ⟨memberSpan, leadingComments, memberValue⟩
  cases memberValue with
  | field declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.field, rfl⟩
  | function declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.function, rfl⟩
  | constructor declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.constructor, rfl⟩
  | fallback declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.fallback, rfl⟩
  | typeAlias declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.typeAlias, rfl⟩
  | enum declaration =>
      simp only [attachContractDerive, pure] at result
      cases result
      exact ⟨.enum, rfl⟩
  | error =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.error, rfl⟩

/-- Derive attachment is an unconditional ordinary success for every member
variant and parser state. -/
theorem attachContractDerive_total_success
    (derive : DeriveAttribute) (member : ContractMember) (input : State) :
    ∃ attached output,
      attachContractDerive derive member input = .ok attached output := by
  rcases member with ⟨memberSpan, leadingComments, memberValue⟩
  cases memberValue <;>
    simp [attachContractDerive, emitDiagnostic, modifyState, bind, pure]

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinaryRejectionSoundnessProperties
/-! Broad ordinary-rejection reflection for derive-aware contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem hashPresentAt_of_isSymbol_eq_true {input : State}
    (present : isSymbol input .hash = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.symbol .hash) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .hash .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses .hash .topItem result).1⟩

/-- Every executable public contract-member rejection records the exact first
rejecting stage.  Pure derive attachment cannot reject. -/
theorem contractMemberWithAttribute_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : contractMemberWithAttribute input = .reject failure rejected) :
    DeclarativeGrammar.ContractMemberRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold contractMemberWithAttribute at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plainCoreRejected
        (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (contractMemberCore_reject_ordinaryOutcome_sound result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | invariant error => simp [deriveResult] at result
      | reject deriveFailure deriveRejected =>
          simp only [deriveResult] at result
          cases result
          exact .deriveRejected
            (hashPresentAt_of_isSymbol_eq_true hashPresent)
            (deriveAttribute_reject_ordinaryOutcome_sound deriveResult)
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases coreResult : contractMemberCore afterDerive with
          | invariant error => simp [coreResult] at result
          | reject coreFailure coreRejected =>
              simp only [coreResult] at result
              cases result
              exact .derivedCoreRejected
                (hashPresentAt_of_isSymbol_eq_true hashPresent)
                (deriveAttribute_success_ordinaryOutcome_sound deriveResult)
                (contractMemberCore_reject_ordinaryOutcome_sound coreResult)
          | ok coreMember afterCore =>
              simp only [coreResult] at result
              rcases attachContractDerive_total_success derive coreMember
                  afterCore with
                ⟨attached, output, attachedResult⟩
              rw [attachedResult] at result
              contradiction

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodyOutcomePrimitiveProperties
/-! Shared executable primitives for broad contract-body outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- A derive-aware member rejection and its canonical state contract supply the
declarative rewind witness used by the body loop. -/
theorem contractMemberRejectsWithPreservedWindow_of_result
    {input failed : State} {failure : Failure}
    (result : contractMemberWithAttribute input = .reject failure failed) :
    DeclarativeGrammar.ContractMemberRejectsWithPreservedWindow
      input.declarativeRemainder := by
  have resultShape :=
    contractMemberWithAttribute_canonical_contract.preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧
      failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    contractMemberWithAttribute_reject_ordinaryOutcome_sound result,
    shape.1, congrArg TokenWindow.endIndex shape.2⟩

/-- Preserved carrier and active window make the member-loop cursor rewind
declaratively invisible. -/
theorem rewoundContractMember_declarativeRemainder_eq
    (input failed : State)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    ({ failed with cursor := input.cursor } : State).declarativeRemainder =
      input.declarativeRemainder := by
  unfold State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

/-- A false executable end guard is exactly strict containment in the active
token window. -/
theorem cursor_lt_endIndex_of_atEnd_eq_false {input : State}
    (notAtEnd : input.atEnd = false) :
    input.cursor < input.window.endIndex := by
  unfold State.atEnd at notAtEnd
  have outside : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    rw [decide_eq_true atEnd] at notAtEnd
    contradiction
  omega

/-- A true executable recovery-boundary guard exposes the corresponding exact
declarative boundary. -/
theorem contractMemberRecoveryBoundaryStartsAt_of_guard_eq_true
    {input : State} (present : atContractRecoveryBoundary input = true) :
    DeclarativeGrammar.ContractMemberRecoveryBoundaryStartsAt
      input.declarativeRemainder :=
  recoveryBoundaryStartsAt_of_atContractRecoveryBoundary_eq_true present

/-- A false executable recovery-boundary guard excludes every exact
declarative boundary. -/
theorem no_contractMemberRecoveryBoundaryStartsAt_of_guard_eq_false
    {input : State} (absent : atContractRecoveryBoundary input = false) :
    ¬ DeclarativeGrammar.ContractMemberRecoveryBoundaryStartsAt
      input.declarativeRemainder := by
  intro starts
  have present :=
    atContractRecoveryBoundary_eq_true_of_recoveryBoundaryStartsAt starts
  rw [present] at absent
  contradiction

/-- A successful close exposes the exact closing brace and constructed body. -/
theorem closeContractBody_success_exact (opening : Token)
    (membersRev : List ContractMember) {input output : State}
    {body : ContractBody}
    (result : closeContractBody opening membersRev input = .ok body output) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        members := membersRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan output.declarativeRemainder := by
  unfold closeContractBody at result
  rcases bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult⟩

/-- A positive right-brace lookahead makes body closing total and successful. -/
theorem closeContractBody_success_of_rightBrace_guard (opening : Token)
    (membersRev : List ContractMember) {input : State}
    (present : isSymbol input .rightBrace = true) :
    ∃ body output, closeContractBody opening membersRev input =
      .ok body output := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .topItem present with
    ⟨closing, closingResult⟩
  exact ⟨{
      span := SourceSpan.cover opening.span closing.span
      members := membersRev.reverse
    }, { input with cursor := input.cursor + 1 }, by
      simp only [closeContractBody, bind, closingResult, pure]⟩

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for derive-aware contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Every successful public contract-member parse follows the exact plain or
derive-aware broad ordinary branch, without a diagnostic-free premise. -/
theorem contractMemberWithAttribute_success_ordinaryOutcome_sound
    {input output : State} {member : ContractMember}
    (result : contractMemberWithAttribute input = .ok member output) :
    DeclarativeGrammar.ContractMemberOrdinaryParses
      input.declarativeRemainder member output.declarativeRemainder := by
  unfold contractMemberWithAttribute at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plain
        (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (contractMemberCore_success_ordinaryOutcome_sound result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | invariant error => simp [deriveResult] at result
      | reject failure rejected => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases coreResult : contractMemberCore afterDerive with
          | invariant error => simp [coreResult] at result
          | reject failure rejected => simp [coreResult] at result
          | ok coreMember afterCore =>
              simp only [coreResult] at result
              have attachment :=
                attachContractDerive_success_ordinaryOutcome_sound result
              rw [attachment.2]
              exact .derived
                (hashPresentAt_of_isSymbol_eq_true hashPresent)
                (deriveAttribute_success_ordinaryOutcome_sound deriveResult)
                (contractMemberCore_success_ordinaryOutcome_sound coreResult)
                attachment.1

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for derive-aware contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Package unconditional executable success and exact selected-stage
rejection for derive-aware contract members. -/
theorem contractMemberWithAttribute_ordinaryOutcome_sound :
    (∀ {input output : State} {member : ContractMember},
      contractMemberWithAttribute input = .ok member output →
        DeclarativeGrammar.ContractMemberOrdinaryParses
          input.declarativeRemainder member output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractMemberWithAttribute input = .reject failure rejected →
        DeclarativeGrammar.ContractMemberRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨contractMemberWithAttribute_success_ordinaryOutcome_sound,
    contractMemberWithAttribute_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive derive-aware member outcomes. -/
theorem contractMemberWithAttribute_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects :=
  DeclarativeGrammar.contractMemberDeterministicOutcomeSpec

/-- Re-export exact derive-aware member outcomes conditional only on an exact
attribute-free core contract. -/
theorem contractMemberWithAttribute_exactOutcomeSpec_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects :=
  DeclarativeGrammar.contractMemberExactOutcomeSpecOfCore coreOutcomes

/-- Fixed-fuel Core expression and statement exactness alone supplies exact
derive-aware member outcomes. -/
theorem contractMemberWithAttribute_exactOutcomeSpec_of_coreTermFuel
    (expressionOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects :=
  DeclarativeGrammar.contractMemberExactOutcomeSpecOfCoreTermFuel
    expressionOutcomes statementOutcomes

/-- Under an exact core contract, two successful executable reflections have
the same member AST and final declarative remainder. -/
theorem contractMemberWithAttribute_success_result_unique_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects)
    {input leftOutput rightOutput : State}
    {left right : ContractMember}
    (leftResult : contractMemberWithAttribute input = .ok left leftOutput)
    (rightResult : contractMemberWithAttribute input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ContractMemberOrdinaryParses.result_unique_of_core
    coreOutcomes
    (contractMemberWithAttribute_success_ordinaryOutcome_sound leftResult)
    (contractMemberWithAttribute_success_ordinaryOutcome_sound rightResult)

/-- Under an exact core contract, two rejected executable reflections have
the same exact declarative endpoint. -/
theorem contractMemberWithAttribute_reject_output_unique_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractMemberWithAttribute input =
      .reject leftFailure leftOutput)
    (rightResult : contractMemberWithAttribute input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ContractMemberRejects.output_unique_of_core coreOutcomes
    (contractMemberWithAttribute_reject_ordinaryOutcome_sound leftResult)
    (contractMemberWithAttribute_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberSoundnessProperties
/-! Parametric diagnostic-free soundness for attribute-aware contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Derive attachment either stays pure for an enum or emits a diagnostic, so
it can never erase an incoming diagnostic. -/
theorem attachContractDerive_reflectsDiagnosticFreeOnSuccess
    (derive : DeriveAttribute) (member : ContractMember) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (attachContractDerive derive member) := by
  intro input value next result diagnosticFree
  rcases member with ⟨memberSpan, leadingComments, memberValue⟩
  cases memberValue <;>
    simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
      at result
  all_goals rcases result with ⟨rfl, rfl⟩
  case enum => exact diagnosticFree
  all_goals cases diagnosticFree

/-- A diagnostic-free attachment success is possible only for an enum member. -/
private theorem attachContractDerive_success_requiresEnum
    {derive : DeriveAttribute} {member value : ContractMember}
    {input next : State} (diagnosticFree : next.diagnosticsRev = [])
    (result : attachContractDerive derive member input = .ok value next) :
    ∃ declaration, member.value = .enum declaration := by
  rcases member with ⟨memberSpan, leadingComments, memberValue⟩
  cases memberValue <;>
    simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
      at result
  all_goals rcases result with ⟨rfl, rfl⟩
  case enum declaration => exact ⟨declaration, rfl⟩
  all_goals cases diagnosticFree

/-- Attribute-aware dispatch reflects diagnostic freedom through the derive
attribute, core member, and attachment stages. -/
theorem contractMemberWithAttribute_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess contractMemberWithAttribute := by
  intro input member next result diagnosticFree
  unfold contractMemberWithAttribute at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact contractMemberCore_reflectsDiagnosticFreeOnSuccess
        expressionReflects allowBodyReflects requiredBodyReflects input member
          next result diagnosticFree
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | reject failure rejected => simp [deriveResult] at result
      | invariant error => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases memberResult : contractMemberCore afterDerive with
          | reject failure rejected => simp [memberResult] at result
          | invariant error => simp [memberResult] at result
          | ok coreMember afterMember =>
              simp only [memberResult] at result
              have afterMemberFree :=
                attachContractDerive_reflectsDiagnosticFreeOnSuccess
                  derive coreMember afterMember member next result
                    diagnosticFree
              have afterDeriveFree :=
                contractMemberCore_reflectsDiagnosticFreeOnSuccess
                  expressionReflects allowBodyReflects requiredBodyReflects
                    afterDerive coreMember afterMember memberResult
                      afterMemberFree
              exact deriveAttribute_reflectsDiagnosticFreeOnSuccess input
                derive afterDerive deriveResult afterDeriveFree

/-!
Every diagnostic-free success follows exact hash priority.  A leading derive
attribute can survive attachment only when core dispatch selected its enum
branch; the enum's earlier field/function/constructor/fallback/type exclusions
are retained unchanged.
-/
theorem contractMemberWithAttribute_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {member : ContractMember}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractMemberWithAttribute input = .ok member next) :
    DeclarativeGrammar.ContractMemberParses expressionParses allowBodyParses
      requiredBodyParses input.declarativeRemainder member
        next.declarativeRemainder := by
  unfold contractMemberWithAttribute at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plain (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (contractMemberCore_success_sound expressionParses allowBodyParses
          requiredBodyParses expressionSound allowBodyReflects allowBodySound
          requiredBodyReflects requiredBodySound diagnosticFree result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | reject failure rejected => simp [deriveResult] at result
      | invariant error => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases memberResult : contractMemberCore afterDerive with
          | reject failure rejected => simp [memberResult] at result
          | invariant error => simp [memberResult] at result
          | ok coreMember afterMember =>
              simp only [memberResult] at result
              have afterMemberFree :=
                attachContractDerive_reflectsDiagnosticFreeOnSuccess
                  derive coreMember afterMember member next result
                    diagnosticFree
              have afterDeriveFree :=
                contractMemberCore_reflectsDiagnosticFreeOnSuccess
                  expressionReflects allowBodyReflects requiredBodyReflects
                    afterDerive coreMember afterMember memberResult
                      afterMemberFree
              have deriveParsed := deriveAttribute_success_sound
                afterDeriveFree deriveResult
              have attachedEnum :=
                attachContractDerive_success_requiresEnum diagnosticFree
                  result
              have coreParsed := contractMemberCore_success_sound
                expressionParses allowBodyParses requiredBodyParses
                expressionSound allowBodyReflects allowBodySound
                requiredBodyReflects requiredBodySound afterMemberFree
                memberResult
              cases coreParsed with
              | field startsField fieldParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | function fieldAbsent functionParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | constructor fieldAbsent functionAbsent constructorParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | fallback fieldAbsent functionAbsent constructorAbsent
                  fallbackParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | typeAlias fieldAbsent functionAbsent constructorAbsent
                  fallbackAbsent aliasParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | enum fieldAbsent functionAbsent constructorAbsent
                  fallbackAbsent typeAbsent enumParsed =>
                  simp only [attachContractDerive, pure] at result
                  cases result
                  exact .derivedEnum deriveParsed fieldAbsent functionAbsent
                    constructorAbsent fallbackAbsent typeAbsent
                    (enumParsed.withDerive derive)

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodyDiagnosticReflectionProperties
/-! Diagnostic-freedom reflection through fuel-bounded contract bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem closeContractBody_reflectsDiagnosticFreeOnSuccess
    (opening : Token) (membersRev : List ContractMember) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closeContractBody opening membersRev) := by
  unfold closeContractBody
  exact Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .topItem)
    (fun _ => Parser.pure_reflectsDiagnosticFreeOnSuccess _)

private theorem contractMembers_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) (opening : Token) :
    ∀ fuel membersRev input body next,
      contractMembers opening fuel membersRev input = .ok body next →
      next.diagnosticsRev = [] → input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input body next result diagnosticFree
      simp [contractMembers] at result
  | succ fuel inductionHypothesis =>
      intro membersRev input body next result diagnosticFree
      unfold contractMembers at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          exact closeContractBody_reflectsDiagnosticFreeOnSuccess opening
            membersRev input body next result diagnosticFree
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .topItem input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases memberResult : contractMemberWithAttribute input with
              | invariant error => simp [memberResult] at result
              | ok member afterMember =>
                  simp only [memberResult] at result
                  by_cases progress : afterMember.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    have afterMemberFree := inductionHypothesis
                      (member :: membersRev) afterMember body next result
                        diagnosticFree
                    exact contractMemberWithAttribute_reflectsDiagnosticFreeOnSuccess
                      expressionReflects allowBodyReflects requiredBodyReflects
                        input member afterMember memberResult afterMemberFree
                  · simp only [progress, if_false] at result
                    contradiction
              | reject failure failedState =>
                  simp only [memberResult] at result
                  let rewound : State := {
                    failedState with cursor := input.cursor
                  }
                  change (if atContractRecoveryBoundary input then
                      .reject failure rewound
                    else match recoverContractMember rewound with
                      | .ok member afterRecovery =>
                          contractMembers opening fuel
                            (member :: membersRev) afterRecovery
                      | .reject recoveryFailure rejected =>
                          .reject recoveryFailure rejected
                      | .invariant error => .invariant error) =
                    .ok body next at result
                  split at result
                  · contradiction
                  · cases recoveryResult : recoverContractMember rewound with
                    | invariant error => simp [recoveryResult] at result
                    | reject recoveryFailure rejected =>
                        simp [recoveryResult] at result
                    | ok member afterRecovery =>
                        simp only [recoveryResult] at result
                        have afterRecoveryFree := inductionHypothesis
                          (member :: membersRev) afterRecovery body next result
                            diagnosticFree
                        exact (recoverContractMember_success_hasDiagnostic
                          recoveryResult afterRecoveryFree).elim

/-- Contract-body parsing cannot erase an incoming diagnostic. -/
theorem contractBody_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess contractBody := by
  intro input body next result diagnosticFree
  unfold contractBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have afterOpeningFree := contractMembers_reflectsDiagnosticFreeOnSuccess
        expressionReflects allowBodyReflects requiredBodyReflects opening
          (afterOpening.remainingCount + 1) [] afterOpening body next result
            diagnosticFree
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .topItem input
        opening afterOpening openingResult afterOpeningFree

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodySoundnessProperties
/-! Parametric diagnostic-free soundness for fuel-bounded contract bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem bind_ok_components_variant {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem closeContractBody_success_sound_and_reflects
    (opening : Token) (membersRev : List ContractMember)
    {input next : State} {body : ContractBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : closeContractBody opening membersRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        members := membersRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder ∧
      input.diagnosticsRev = [] := by
  unfold closeContractBody at result
  rcases bind_ok_components_variant result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have afterClosingFree : afterClosing.diagnosticsRev = [] := by
    cases finished
    exact diagnosticFree
  have inputFree : input.diagnosticsRev = [] :=
    symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .topItem input closing
      afterClosing closingResult afterClosingFree
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult,
    inputFree⟩

private theorem contractMembers_success_sound_strong
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (opening : Token) :
    ∀ fuel membersRev input body next,
      next.diagnosticsRev = [] →
      contractMembers opening fuel membersRev input = .ok body next →
      ∃ members closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          members := membersRev.reverse ++ members
        } ∧
        DeclarativeGrammar.ContractMemberTailParses expressionParses
          allowBodyParses requiredBodyParses input.declarativeRemainder
            members closingSpan next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input body next diagnosticFree result
      simp [contractMembers] at result
  | succ fuel inductionHypothesis =>
      intro membersRev input body next diagnosticFree result
      unfold contractMembers at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeContractBody_success_sound_and_reflects opening membersRev
              diagnosticFree result with
            ⟨closingSpan, bodyEq, closingGrammar, inputFree⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingGrammar, inputFree⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .topItem input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases memberResult : contractMemberWithAttribute input with
              | invariant error => simp [memberResult] at result
              | ok member afterMember =>
                  simp only [memberResult] at result
                  by_cases progress : afterMember.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (member :: membersRev)
                        afterMember body next diagnosticFree result with
                      ⟨members, closingSpan, bodyEq, tailGrammar,
                        afterMemberFree⟩
                    have memberGrammar :=
                      contractMemberWithAttribute_success_sound expressionParses
                        allowBodyParses requiredBodyParses expressionReflects
                        expressionSound allowBodyReflects allowBodySound
                        requiredBodyReflects requiredBodySound afterMemberFree
                        memberResult
                    have inputFree :=
                      contractMemberWithAttribute_reflectsDiagnosticFreeOnSuccess
                        expressionReflects allowBodyReflects requiredBodyReflects
                          input member afterMember memberResult afterMemberFree
                    refine ⟨member :: members, closingSpan, ?_,
                      .next
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        memberGrammar progress tailGrammar,
                      inputFree⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction
              | reject failure failedState =>
                  simp only [memberResult] at result
                  let rewound : State := {
                    failedState with cursor := input.cursor
                  }
                  change (if atContractRecoveryBoundary input then
                      .reject failure rewound
                    else match recoverContractMember rewound with
                      | .ok member afterRecovery =>
                          contractMembers opening fuel
                            (member :: membersRev) afterRecovery
                      | .reject recoveryFailure rejected =>
                          .reject recoveryFailure rejected
                      | .invariant error => .invariant error) =
                    .ok body next at result
                  split at result
                  · contradiction
                  · cases recoveryResult : recoverContractMember rewound with
                    | invariant error => simp [recoveryResult] at result
                    | reject recoveryFailure rejected =>
                        simp [recoveryResult] at result
                    | ok member afterRecovery =>
                        simp only [recoveryResult] at result
                        rcases inductionHypothesis (member :: membersRev)
                            afterRecovery body next diagnosticFree result with
                          ⟨members, closingSpan, bodyEq, tailGrammar,
                            afterRecoveryFree⟩
                        exact (recoverContractMember_success_hasDiagnostic
                          recoveryResult afterRecoveryFree).elim

/-! Every diagnostic-free contract body has exact braces, member order,
branch priority, and strict member progress under the supplied leaf grammars. -/
theorem contractBody_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {body : ContractBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractBody input = .ok body next) :
    DeclarativeGrammar.ContractBodyParses expressionParses allowBodyParses
      requiredBodyParses input.declarativeRemainder body.span body.members
        next.declarativeRemainder := by
  unfold contractBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases contractMembers_success_sound_strong expressionParses
          allowBodyParses requiredBodyParses expressionReflects expressionSound
          allowBodyReflects allowBodySound requiredBodyReflects requiredBodySound
          opening (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨members, closingSpan, bodyEq, tailGrammar, afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.ContractBodyParses.parsed opening.span
        closingSpan
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        tailGrammar

/-- Contract-body grammar soundness composes with canonical source validity. -/
theorem contractBody_success_sound_and_validFor
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {body : ContractBody} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractBody input = .ok body next) :
    DeclarativeGrammar.ContractBodyParses expressionParses allowBodyParses
        requiredBodyParses input.declarativeRemainder body.span body.members
          next.declarativeRemainder ∧
      ContractBody.ValidFor input.file body := by
  refine ⟨contractBody_success_sound expressionParses allowBodyParses
    requiredBodyParses expressionReflects expressionSound allowBodyReflects
    allowBodySound requiredBodyReflects requiredBodySound diagnosticFree result,
    ?_⟩
  have valid := contractBody_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractDeclSoundnessProperties
/-! Parametric diagnostic-free soundness for complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Contract declaration parsing cannot erase an incoming diagnostic. -/
theorem contractDecl_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess contractDecl := by
  unfold contractDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .contractKw .topItem)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .topItem)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalGenericParameters_reflectsDiagnosticFreeOnSuccess
  intro genericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contractBody_reflectsDiagnosticFreeOnSuccess expressionReflects
      allowBodyReflects requiredBodyReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every diagnostic-free contract success follows its exact declaration grammar. -/
theorem contractDecl_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ContractDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractDecl input = .ok declaration next) :
    DeclarativeGrammar.ContractDeclParses expressionParses allowBodyParses
      requiredBodyParses input.declarativeRemainder declaration
        next.declarativeRemainder := by
  unfold contractDecl at result
  rcases bind_ok_components_variant result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components_variant rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components_variant rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components_variant rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .contractKw .topItem markerResult)
    (identifier_success_sound .topItem nameResult)
    (optionalGenericParameters_success_sound genericsResult)
    (contractBody_success_sound expressionParses allowBodyParses
      requiredBodyParses expressionReflects expressionSound allowBodyReflects
      allowBodySound requiredBodyReflects requiredBodySound diagnosticFree
      bodyResult)

/-- Contract grammar soundness composes with canonical source validity. -/
theorem contractDecl_success_sound_and_validFor
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ContractDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractDecl input = .ok declaration next) :
    DeclarativeGrammar.ContractDeclParses expressionParses allowBodyParses
        requiredBodyParses input.declarativeRemainder declaration
          next.declarativeRemainder ∧
      ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor input.file
        declaration := by
  refine ⟨contractDecl_success_sound expressionParses allowBodyParses
    requiredBodyParses expressionReflects expressionSound allowBodyReflects
    allowBodySound requiredBodyReflects requiredBodySound diagnosticFree result,
    ?_⟩
  have valid := contractDecl_canonical_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.ContractInternals
end
