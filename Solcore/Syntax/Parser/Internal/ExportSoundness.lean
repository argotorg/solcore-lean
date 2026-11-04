import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.ModuleTotality
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Internal.ExportOutcomes
import Solcore.Syntax.Parser.Internal.ExportProofs
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.ImportProofs
import Solcore.Syntax.Internal.ImportOutcomes
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Syntax.Validity

/-!
Soundness of the parsers of export declarations and pragmas: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ExportPathOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for maximal export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExportInternals

private theorem exportPathTail_ne_reject (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      exportPathTail first fuel last tailRev input ≠
        .reject failure rejected := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input failure rejected result
      simp [exportPathTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input failure rejected result
      unfold exportPathTail at result
      split at result
      next continues =>
        unfold continuesExportPath at continues
        have guards := Bool.and_eq_true_iff.mp continues
        rcases symbol_eq_ok_of_isSymbol_eq_true .dot .exportDecl guards.1 with
          ⟨dot, dotResult⟩
        simp only [dotResult] at result
        unfold State.peekOffsetKind? at guards
        cases followingFound : input.peekOffset? 1 with
        | none => simp [followingFound] at guards
        | some following =>
            rcases following with ⟨componentSpan, followingKind⟩
            cases followingKind <;>
              simp only [followingFound, Option.map_some] at guards
            all_goals try simp_all
            case identifier spelling =>
              let afterDot : State := {
                input with cursor := input.cursor + 1
              }
              have componentAt : DeclarativeGrammar.TokenAt
                  afterDot.tokens afterDot.window.endIndex afterDot.cursor {
                    span := componentSpan
                    value := .identifier spelling
                  } := by
                exact ⟨
                  State.cursor_add_lt_endIndex_of_peekOffset?_eq_some
                    followingFound,
                  State.getElem?_eq_some_of_peekOffset?_eq_some
                    followingFound⟩
              cases componentResult : identifier .exportDecl afterDot with
              | invariant error => simp [afterDot, componentResult] at result
              | reject componentFailure componentRejected =>
                  have absent := identifier_reject_identifierAbsentAt
                    .exportDecl componentResult
                  exact (absent ⟨componentSpan, spelling, componentAt⟩).elim
              | ok component next =>
                  simp only [afterDot, componentResult] at result
                  exact inductionHypothesis component
                    (component :: tailRev) next failure rejected result
      next stopped =>
        unfold finishExportPath at result
        contradiction

end ExportInternals

/-- Every executable export-path rejection is the exact nonconsuming
rejection of its required first checked identifier. -/
theorem exportPath_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.exportPath input = .reject failure rejected) :
    DeclarativeGrammar.ExportPathRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected (identifier_reject_sound .exportDecl firstResult)
  | ok first next =>
      simp only [firstResult] at result
      exact False.elim
        (ExportInternals.exportPathTail_ne_reject first
          (next.remainingCount + 1) first [] next failure rejected result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportPathOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for maximal export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export maximal export-path success as a broad ordinary outcome. -/
theorem exportPath_success_ordinaryOutcome_sound
    {input output : State} {path : QualifiedName}
    (result : ExportInternals.exportPath input = .ok path output) :
    DeclarativeGrammar.ExportPathOrdinaryParses input.declarativeRemainder
      path output.declarativeRemainder :=
  exportPath_success_sound result

/-- Package maximal export-path success and exact initial rejection. -/
theorem exportPath_ordinaryOutcome_sound :
    (∀ {input output : State} {path : QualifiedName},
      ExportInternals.exportPath input = .ok path output →
        DeclarativeGrammar.ExportPathOrdinaryParses
          input.declarativeRemainder path output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.exportPath input = .reject failure rejected →
        DeclarativeGrammar.ExportPathRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨exportPath_success_ordinaryOutcome_sound,
    exportPath_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive maximal export-path outcomes. -/
theorem exportPath_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExportPathOrdinaryParses
      DeclarativeGrammar.ExportPathRejects :=
  DeclarativeGrammar.exportPathDeterministicOutcomeSpec


/-- Exact values and endpoints for the independent exportPath grammar. -/
theorem exportPath_exactOutcomeSpec  :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ExportPathOrdinaryParses DeclarativeGrammar.ExportPathRejects :=
  DeclarativeGrammar.exportPathExactOutcomeSpec

/-- Executable successes agree on their complete value and remainder. -/
theorem exportPath_success_result_unique
    {input leftOutput rightOutput : State} {left right : QualifiedName}
    (leftResult : ExportInternals.exportPath input = .ok left leftOutput)
    (rightResult : ExportInternals.exportPath input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (exportPath_exactOutcomeSpec ).successResultUnique
    (exportPath_success_ordinaryOutcome_sound  leftResult)
    (exportPath_success_ordinaryOutcome_sound  rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem exportPath_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.exportPath input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.exportPath input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (exportPath_exactOutcomeSpec ).rejectOutputUnique
    (exportPath_reject_ordinaryOutcome_sound  leftResult)
    (exportPath_reject_ordinaryOutcome_sound  rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ConstructorSelectionOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem markerPresentAt_one_of_guard_eq_true {input : State}
    (present :
      (input.peekOffsetKind? 1 == some (.symbol .star)) = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      (input.cursor + 1) { span, value := .symbol .star } := by
  have advancedPresent :=
    isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true .star present
  rcases symbol_eq_ok_of_isSymbol_eq_true .star .exportDecl
      advancedPresent with ⟨marker, markerResult⟩
  have parsed := symbol_success_exactTokenParses .star .exportDecl markerResult
  exact ⟨marker.span, by
    simpa only [State.declarativeRemainder, State.tokens, State.window,
      State.cursor] using parsed.1⟩

private theorem markerAbsentAt_one_of_guard_eq_false {input : State}
    (absent :
      (input.peekOffsetKind? 1 == some (.symbol .star)) = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      (input.cursor + 1) (.symbol .star) := by
  rintro ⟨span, tokenAt⟩
  have found : input.peekOffsetKind? 1 = some (.symbol .star) := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [tokenAt.1, ↓reduceIte, tokenAt.2, Option.map_some]
  have present :
      (input.peekOffsetKind? 1 == some (.symbol .star)) = true := by
    rw [found]
    rfl
  rw [present] at absent
  contradiction

/-- Every executable constructor-selection rejection records the exact first
failed all-selection token or named-list stage selected by offset lookahead. -/
theorem constructorSelection_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.constructorSelection input =
      .reject failure rejected) :
    DeclarativeGrammar.ConstructorSelectionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold ExportInternals.constructorSelection getState at result
  simp only [bind] at result
  by_cases allPresent :
      (input.peekOffsetKind? 1 == some (.symbol .star)) = true
  · simp only [allPresent, if_true] at result
    rcases markerPresentAt_one_of_guard_eq_true allPresent with
      ⟨guardMarkerSpan, guardMarkerToken⟩
    cases openingResult : symbol .leftParen .exportDecl input with
    | invariant error => simp [openingResult] at result
    | reject openingFailure openingRejected =>
        have rejectedEq := symbol_reject_state_eq .leftParen .exportDecl
          openingResult
        simp only [openingResult] at result
        cases result
        rw [rejectedEq]
        exact .openingMissing guardMarkerSpan guardMarkerToken
          (symbol_reject_tokenKindAbsentAt .leftParen .exportDecl
            openingResult)
    | ok opening afterOpening =>
        have openingSound := symbol_ok_tokenAt .leftParen .exportDecl
          openingResult
        have openingParsed := symbol_success_exactTokenParses
          .leftParen .exportDecl openingResult
        have markerPresent : isSymbol afterOpening .star = true := by
          rw [openingSound.2]
          exact isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true
            .star allPresent
        rcases symbol_eq_ok_of_isSymbol_eq_true .star .exportDecl
            markerPresent with ⟨marker, markerResult⟩
        have markerParsed := symbol_success_exactTokenParses
          .star .exportDecl markerResult
        simp only [openingResult, markerResult] at result
        cases closingResult : symbol .rightParen .exportDecl
            { afterOpening with cursor := afterOpening.cursor + 1 } with
        | invariant error => simp [closingResult] at result
        | ok closing afterClosing =>
            simp [closingResult, pure] at result
        | reject closingFailure closingRejected =>
            have rejectedEq := symbol_reject_state_eq .rightParen .exportDecl
              closingResult
            simp only [closingResult] at result
            cases result
            rw [rejectedEq]
            exact .closingMissing opening.span marker.span openingParsed
              markerParsed
              (symbol_reject_tokenKindAbsentAt .rightParen .exportDecl
                closingResult)
  · have namedGuard :
        (input.peekOffsetKind? 1 == some (.symbol .star)) = false :=
      Bool.eq_false_iff.mpr allPresent
    simp only [namedGuard, Bool.false_eq_true, if_false] at result
    cases namesResult : delimitedNoTrailing .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel input with
    | invariant error => simp [namesResult] at result
    | reject namesFailure namesRejected =>
        simp only [namesResult] at result
        cases result
        exact .namedRejected
          (markerAbsentAt_one_of_guard_eq_false namedGuard)
          (delimitedNoTrailing_reject_sound .leftParen .rightParen false
            (identifier .exportDecl) DeclarativeGrammar.IdentifierParses
            DeclarativeGrammar.IdentifierRejects .exportDecl .topLevel
            (identifier_success_sound .exportDecl)
            (identifier_reject_sound .exportDecl) namesResult)
    | ok names afterNames =>
        simp only [namesResult] at result
        rcases
            ExportInternals.requireConstructorNames_ok_of_delimitedNoTrailing_false_ok
              namesResult with
          ⟨constructors, constructorsResult⟩
        simp [constructorsResult, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportNameOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem exportNameTokenPresentAt_of_isSymbol_eq_true
    (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.ExportNameTokenPresentAt input.declarativeRemainder
      (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .exportDecl present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .exportDecl result).1⟩

/-- Every executable export-name rejection records the exact first failing
operator, identifier, or constructor-selection stage under parser priority. -/
theorem exportName_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.exportName input = .reject failure rejected) :
    DeclarativeGrammar.ExportNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.exportName at result
  by_cases starPresent : isSymbol input .star = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .star .exportDecl starPresent with
      ⟨marker, markerResult⟩
    simp [starPresent, markerResult] at result
  · have starAbsent : isSymbol input .star = false :=
      Bool.eq_false_iff.mpr starPresent
    simp only [starAbsent, Bool.false_eq_true, if_false] at result
    have starMissing := symbolAbsentAt_of_isSymbol_eq_false .star starAbsent
    by_cases openingPresent : isSymbol input .leftParen = true
    · simp only [openingPresent, if_true] at result
      have openingToken := exportNameTokenPresentAt_of_isSymbol_eq_true
        .leftParen openingPresent
      cases selectorResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectorResult] at result
      | reject selectorFailure selectorRejected =>
          have selectorReply : selectorName .exportDecl input =
              .reject selectorFailure selectorRejected := by
            unfold selectorName
            simp only [openingPresent, if_true]
            exact selectorResult
          have selectorGrammar :=
            selectorName_reject_ordinaryOutcome_sound .exportDecl
              selectorReply
          simp only [selectorResult] at result
          cases result
          exact .operatorRejected starMissing openingToken selectorGrammar
      | ok selector afterSelector =>
          rcases selector with ⟨selectorSpan, selectorValue⟩
          cases selectorValue <;> simp [selectorResult] at result
    · have openingAbsent : isSymbol input .leftParen = false :=
        Bool.eq_false_iff.mpr openingPresent
      simp only [openingAbsent, Bool.false_eq_true, if_false] at result
      have openingMissing := symbolAbsentAt_of_isSymbol_eq_false
        .leftParen openingAbsent
      cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .identifierRejected starMissing openingMissing
            (identifier_reject_sound .exportDecl nameResult)
      | ok name afterName =>
          have nameParsed := identifier_success_sound .exportDecl nameResult
          simp only [nameResult] at result
          by_cases constructorsPresent :
              isSymbol afterName .leftParen = true
          · simp only [constructorsPresent, if_true] at result
            have constructorsToken :=
              exportNameTokenPresentAt_of_isSymbol_eq_true .leftParen
                constructorsPresent
            cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp [constructorsResult] at result
            | ok constructors afterConstructors =>
                simp [constructorsResult] at result
            | reject constructorsFailure constructorsRejected =>
                have constructorsGrammar :=
                  constructorSelection_reject_ordinaryOutcome_sound
                    constructorsResult
                simp only [constructorsResult] at result
                cases result
                exact .constructorsRejected starMissing openingMissing
                  nameParsed constructorsToken constructorsGrammar
          · have constructorsAbsent :
                isSymbol afterName .leftParen = false :=
              Bool.eq_false_iff.mpr constructorsPresent
            simp [constructorsAbsent] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportNameOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export export-name success as a broad ordinary outcome. -/
theorem exportName_success_ordinaryOutcome_sound
    {input output : State} {name : ExportName}
    (result : ExportInternals.exportName input = .ok name output) :
    DeclarativeGrammar.ExportNameOrdinaryParses
      input.declarativeRemainder name output.declarativeRemainder :=
  exportName_success_sound result

/-- Package export-name success and exact prioritized rejection. -/
theorem exportName_ordinaryOutcome_sound :
    (∀ {input output : State} {name : ExportName},
      ExportInternals.exportName input = .ok name output →
        DeclarativeGrammar.ExportNameOrdinaryParses
          input.declarativeRemainder name output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.exportName input = .reject failure rejected →
        DeclarativeGrammar.ExportNameRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨exportName_success_ordinaryOutcome_sound,
    exportName_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive export-name outcomes. -/
theorem exportName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExportNameOrdinaryParses
      DeclarativeGrammar.ExportNameRejects :=
  DeclarativeGrammar.exportNameDeterministicOutcomeSpec

/-- Re-export exact exportName outcomes with all supplied span data fixed. -/
theorem exportName_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ExportNameOrdinaryParses
      DeclarativeGrammar.ExportNameRejects :=
  DeclarativeGrammar.exportNameExactOutcomeSpec

/-- Two exportName successes fix the complete AST and declarative remainder. -/
theorem exportName_success_result_unique
    {input leftOutput rightOutput : State} {left right : ExportName}
    (leftResult : ExportInternals.exportName input = .ok left leftOutput)
    (rightResult : ExportInternals.exportName input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportName_exactOutcomeSpec.successResultUnique
    (exportName_success_ordinaryOutcome_sound leftResult)
    (exportName_success_ordinaryOutcome_sound rightResult)

/-- Two exportName rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem exportName_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.exportName input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.exportName input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportName_exactOutcomeSpec.rejectOutputUnique
    (exportName_reject_ordinaryOutcome_sound leftResult)
    (exportName_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportSelectionOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable export-selection rejection is the exact braced-list
failure reached after the prioritized wildcard guard is absent. -/
theorem exportSelection_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.exportSelection input =
      .reject failure rejected) :
    DeclarativeGrammar.ExportSelectionRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.exportSelection at result
  by_cases starPresent : isSymbol input .star = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .star .exportDecl starPresent with
      ⟨marker, markerResult⟩
    simp [starPresent, markerResult] at result
  · have starAbsent : isSymbol input .star = false :=
      Bool.eq_false_iff.mpr starPresent
    simp only [starAbsent, Bool.false_eq_true, if_false] at result
    have starMissing := symbolAbsentAt_of_isSymbol_eq_false .star starAbsent
    cases itemsResult : delimited .leftBrace .rightBrace true
        ExportInternals.exportName .exportDecl .topLevel input with
    | invariant error => simp [itemsResult] at result
    | ok items afterItems => simp [itemsResult] at result
    | reject itemsFailure itemsRejected =>
        simp only [itemsResult] at result
        cases result
        exact .selectedRejected starMissing
          (delimited_reject_sound .leftBrace .rightBrace true
            ExportInternals.exportName
            DeclarativeGrammar.ExportNameOrdinaryParses
            DeclarativeGrammar.ExportNameRejects .exportDecl .topLevel
            exportName_success_ordinaryOutcome_sound
            exportName_reject_ordinaryOutcome_sound itemsResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportSelectionOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export export-selection success as a broad ordinary outcome. -/
theorem exportSelection_success_ordinaryOutcome_sound
    {input output : State} {selection : ExportSelection}
    (result : ExportInternals.exportSelection input = .ok selection output) :
    DeclarativeGrammar.ExportSelectionOrdinaryParses
      input.declarativeRemainder selection output.declarativeRemainder :=
  exportSelection_success_sound result

/-- Package export-selection success and exact prioritized rejection. -/
theorem exportSelection_ordinaryOutcome_sound :
    (∀ {input output : State} {selection : ExportSelection},
      ExportInternals.exportSelection input = .ok selection output →
        DeclarativeGrammar.ExportSelectionOrdinaryParses
          input.declarativeRemainder selection output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.exportSelection input = .reject failure rejected →
        DeclarativeGrammar.ExportSelectionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨exportSelection_success_ordinaryOutcome_sound,
    exportSelection_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive export-selection outcomes. -/
theorem exportSelection_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExportSelectionOrdinaryParses
      DeclarativeGrammar.ExportSelectionRejects :=
  DeclarativeGrammar.exportSelectionDeterministicOutcomeSpec

/-- Re-export exact exportSelection outcomes with all supplied span data fixed. -/
theorem exportSelection_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ExportSelectionOrdinaryParses
      DeclarativeGrammar.ExportSelectionRejects :=
  DeclarativeGrammar.exportSelectionExactOutcomeSpec

/-- Two exportSelection successes fix the complete AST and declarative remainder. -/
theorem exportSelection_success_result_unique
    {input leftOutput rightOutput : State} {left right : ExportSelection}
    (leftResult : ExportInternals.exportSelection input = .ok left leftOutput)
    (rightResult : ExportInternals.exportSelection input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportSelection_exactOutcomeSpec.successResultUnique
    (exportSelection_success_ordinaryOutcome_sound leftResult)
    (exportSelection_success_ordinaryOutcome_sound rightResult)

/-- Two exportSelection rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem exportSelection_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.exportSelection input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.exportSelection input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportSelection_exactOutcomeSpec.rejectOutputUnique
    (exportSelection_reject_ordinaryOutcome_sound leftResult)
    (exportSelection_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PathExportOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable path-export rejection records the exact first failing
path, selected suffix, alias suffix, or non-recovering finish stage. -/
theorem pathExport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.pathExport start input =
      .reject failure rejected) :
    DeclarativeGrammar.PathExportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.pathExport at result
  cases pathResult : ExportInternals.exportPath input with
  | invariant error => simp [bind, pathResult] at result
  | reject pathFailure pathRejected =>
      simp only [bind, pathResult] at result
      cases result
      exact .pathRejected
        (exportPath_reject_ordinaryOutcome_sound pathResult)
  | ok path afterPath =>
      have pathParsed := exportPath_success_ordinaryOutcome_sound pathResult
      simp only [bind, pathResult, getState] at result
      by_cases dotPresent : isSymbol afterPath .dot = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .dot .exportDecl dotPresent
          with ⟨dot, dotResult⟩
        have dotParsed := symbol_success_exactTokenParses .dot .exportDecl
          dotResult
        have dotGuard : DeclarativeGrammar.PathExportTokenPresentAt
            afterPath.declarativeRemainder (.symbol .dot) :=
          ⟨dot.span, dotParsed.1⟩
        simp only [dotPresent, if_true, dotResult] at result
        cases selectionResult : ExportInternals.exportSelection
            { afterPath with cursor := afterPath.cursor + 1 } with
        | invariant error => simp [selectionResult] at result
        | reject selectionFailure selectionRejected =>
            simp only [selectionResult] at result
            cases result
            exact .selectionRejected dot.span pathParsed dotGuard dotParsed
              (exportSelection_reject_ordinaryOutcome_sound selectionResult)
        | ok selection afterSelection =>
            have selectionParsed :=
              exportSelection_success_ordinaryOutcome_sound selectionResult
            simp only [selectionResult] at result
            exact .selectionFinishRejected dot.span pathParsed dotGuard
              dotParsed selectionParsed
              (finishExport_reject_ordinaryOutcome_sound start
                (.itemsFrom path selection) result)
      · have dotAbsentBool : isSymbol afterPath .dot = false :=
          Bool.eq_false_iff.mpr dotPresent
        simp only [dotAbsentBool, Bool.false_eq_true, if_false] at result
        have dotAbsent := symbolAbsentAt_of_isSymbol_eq_false .dot
          dotAbsentBool
        by_cases asPresent : isKeyword afterPath .asKw = true
        · rcases keyword_eq_ok_of_isKeyword_eq_true .asKw .exportDecl
              asPresent with ⟨asToken, asResult⟩
          have asParsed := keyword_success_exactTokenParses .asKw .exportDecl
            asResult
          have asGuard : DeclarativeGrammar.PathExportTokenPresentAt
              afterPath.declarativeRemainder (.keyword .asKw) :=
            ⟨asToken.span, asParsed.1⟩
          simp only [asPresent, if_true, asResult] at result
          cases aliasResult : identifier .exportDecl
              { afterPath with cursor := afterPath.cursor + 1 } with
          | invariant error => simp [aliasResult] at result
          | reject aliasFailure aliasRejected =>
              simp only [aliasResult] at result
              cases result
              exact .aliasRejected asToken.span pathParsed dotAbsent asGuard
                asParsed (identifier_reject_sound .exportDecl aliasResult)
          | ok alias afterAlias =>
              have aliasParsed := identifier_success_sound .exportDecl
                aliasResult
              simp only [aliasResult] at result
              exact .aliasFinishRejected asToken.span pathParsed dotAbsent
                asGuard asParsed aliasParsed
                (finishExport_reject_ordinaryOutcome_sound start
                  (.moduleAs path alias) result)
        · have asAbsentBool : isKeyword afterPath .asKw = false :=
            Bool.eq_false_iff.mpr asPresent
          simp only [asAbsentBool, Bool.false_eq_true, if_false] at result
          exact .moduleFinishRejected pathParsed dotAbsent
            (keywordAbsentAt_of_isKeyword_eq_false .asKw asAbsentBool)
            (finishExport_reject_ordinaryOutcome_sound start (.module path)
              result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PathExportOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export path-export success as a broad ordinary outcome. -/
theorem pathExport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ExportDecl}
    (result : ExportInternals.pathExport start input =
      .ok declaration output) :
    DeclarativeGrammar.PathExportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder :=
  pathExport_success_sound start result

/-- Package path-export success and exact prioritized rejection. -/
theorem pathExport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ExportDecl},
      ExportInternals.pathExport start input = .ok declaration output →
        DeclarativeGrammar.PathExportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.pathExport start input = .reject failure rejected →
        DeclarativeGrammar.PathExportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨pathExport_success_ordinaryOutcome_sound start,
    pathExport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive path-export outcomes. -/
theorem pathExport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.PathExportOrdinaryParses start)
      DeclarativeGrammar.PathExportRejects :=
  DeclarativeGrammar.pathExportDeterministicOutcomeSpec start

/-- Re-export exact pathExport outcomes with all supplied span data fixed. -/
theorem pathExport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.PathExportOrdinaryParses start)
      DeclarativeGrammar.PathExportRejects :=
  DeclarativeGrammar.pathExportExactOutcomeSpec start

/-- Two pathExport successes fix the complete AST and declarative remainder. -/
theorem pathExport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ExportDecl}
    (leftResult : ExportInternals.pathExport start input = .ok left leftOutput)
    (rightResult : ExportInternals.pathExport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (pathExport_exactOutcomeSpec start).successResultUnique
    (pathExport_success_ordinaryOutcome_sound start leftResult)
    (pathExport_success_ordinaryOutcome_sound start rightResult)

/-- Two pathExport rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem pathExport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.pathExport start input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.pathExport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (pathExport_exactOutcomeSpec start).rejectOutputUnique
    (pathExport_reject_ordinaryOutcome_sound start leftResult)
    (pathExport_reject_ordinaryOutcome_sound start rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LocalExportItemOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem localExportItemQualifiedStartAt_of_dispatcher_eq_true
    {input : State}
    (present : (isIdentifier input && isSymbol
      { input with cursor := input.cursor + 1 } .dot) = true) :
    DeclarativeGrammar.LocalExportItemQualifiedStartAt
      input.declarativeRemainder := by
  rcases Bool.and_eq_true_iff.mp present with
    ⟨identifierPresent, dotPresent⟩
  rcases identifierPresentAt_of_isIdentifier_eq_true identifierPresent with
    ⟨identifierSpan, text, identifierToken⟩
  rcases symbol_eq_ok_of_isSymbol_eq_true .dot .exportDecl dotPresent with
    ⟨dot, dotResult⟩
  refine ⟨identifierSpan, dot.span, text, identifierToken, ?_⟩
  exact (symbol_success_exactTokenParses .dot .exportDecl dotResult).1

private theorem identifierDotAbsentAt_of_dispatcher_eq_false {input : State}
    (stopped : (isIdentifier input && isSymbol
      { input with cursor := input.cursor + 1 } .dot) = false) :
    DeclarativeGrammar.IdentifierDotAbsentAt input.tokens
      input.window.endIndex input.cursor := by
  rintro ⟨identifierSpan, dotSpan, text, identifierAt, dotAt⟩
  have identifierPresent : isIdentifier input = true := by
    unfold isIdentifier State.peekKind? State.peek?
    simp only [identifierAt.1, ↓reduceIte, identifierAt.2,
      Option.map_some]
  have dotPresent : isSymbol
      { input with cursor := input.cursor + 1 } .dot = true := by
    unfold isSymbol State.peekKind? State.peek?
    simp only [dotAt.1, ↓reduceIte, dotAt.2, Option.map_some]
    rfl
  rw [identifierPresent, dotPresent] at stopped
  contradiction

private theorem exportPathRejects_identifierAbsentAt
    {input rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ExportPathRejects input rejected) :
    DeclarativeGrammar.IdentifierAbsentAt input := by
  cases rejection with
  | firstRejected identifierRejected =>
      cases identifierRejected with
      | absent identifierAbsent => exact identifierAbsent

private theorem exportPath_ne_reject_of_isIdentifier_eq_true
    {input rejected : State} {failure : Failure}
    (present : isIdentifier input = true)
    (result : ExportInternals.exportPath input = .reject failure rejected) :
    False := by
  have identifierAbsent := exportPathRejects_identifierAbsentAt
    (exportPath_reject_ordinaryOutcome_sound result)
  rcases identifierPresentAt_of_isIdentifier_eq_true present with
    ⟨span, text, token⟩
  exact identifierAbsent ⟨span, text, token⟩

/-- Every executable local-export-item rejection records the exact qualified
dot/star failure or the prioritized unqualified export-name failure. -/
theorem localExportItem_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.localExportItem input =
      .reject failure rejected) :
    DeclarativeGrammar.LocalExportItemRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.localExportItem at result
  by_cases qualified : (isIdentifier input && isSymbol
      { input with cursor := input.cursor + 1 } .dot) = true
  · simp only [qualified, if_true] at result
    have qualifiedStart :=
      localExportItemQualifiedStartAt_of_dispatcher_eq_true qualified
    have identifierPresent := (Bool.and_eq_true_iff.mp qualified).1
    cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp [pathResult] at result
    | reject pathFailure pathRejected =>
        exact False.elim
          (exportPath_ne_reject_of_isIdentifier_eq_true identifierPresent
            pathResult)
    | ok path afterPath =>
        have pathParsed := exportPath_success_ordinaryOutcome_sound pathResult
        simp only [pathResult] at result
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at result
        | reject dotFailure dotRejected =>
            have dotRejectedEq := symbol_reject_state_eq .dot .exportDecl
              dotResult
            subst dotRejected
            simp only [dotResult] at result
            cases result
            exact .moduleDotMissing qualifiedStart pathParsed
              (symbol_reject_tokenKindAbsentAt .dot .exportDecl dotResult)
        | ok dot afterDot =>
            have dotParsed := symbol_success_exactTokenParses .dot .exportDecl
              dotResult
            simp only [dotResult] at result
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at result
            | ok marker afterMarker => simp [markerResult] at result
            | reject markerFailure markerRejected =>
                have markerRejectedEq := symbol_reject_state_eq .star
                  .exportDecl markerResult
                subst markerRejected
                simp only [markerResult] at result
                cases result
                exact .moduleStarMissing qualifiedStart pathParsed dot.span
                  dotParsed
                  (symbol_reject_tokenKindAbsentAt .star .exportDecl
                    markerResult)
  · have qualifiedAbsent : (isIdentifier input && isSymbol
        { input with cursor := input.cursor + 1 } .dot) = false :=
      Bool.eq_false_iff.mpr qualified
    simp only [qualifiedAbsent, Bool.false_eq_true, if_false] at result
    have qualifiedMissing :=
      identifierDotAbsentAt_of_dispatcher_eq_false qualifiedAbsent
    cases nameResult : ExportInternals.exportName input with
    | invariant error => simp [nameResult] at result
    | ok name afterName => simp [nameResult] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .nameRejected qualifiedMissing
          (exportName_reject_ordinaryOutcome_sound nameResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LocalExportItemOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export local-export-item success as a broad ordinary outcome. -/
theorem localExportItem_success_ordinaryOutcome_sound
    {input output : State} {item : LocalExportItem}
    (result : ExportInternals.localExportItem input = .ok item output) :
    DeclarativeGrammar.LocalExportItemOrdinaryParses
      input.declarativeRemainder item output.declarativeRemainder :=
  localExportItem_success_sound result

/-- Package local-export-item success and exact prioritized rejection. -/
theorem localExportItem_ordinaryOutcome_sound :
    (∀ {input output : State} {item : LocalExportItem},
      ExportInternals.localExportItem input = .ok item output →
        DeclarativeGrammar.LocalExportItemOrdinaryParses
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.localExportItem input = .reject failure rejected →
        DeclarativeGrammar.LocalExportItemRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨localExportItem_success_ordinaryOutcome_sound,
    localExportItem_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive local-export-item outcomes. -/
theorem localExportItem_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.LocalExportItemOrdinaryParses
      DeclarativeGrammar.LocalExportItemRejects :=
  DeclarativeGrammar.localExportItemDeterministicOutcomeSpec

/-- Re-export exact localExportItem outcomes with all supplied span data fixed. -/
theorem localExportItem_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.LocalExportItemOrdinaryParses
      DeclarativeGrammar.LocalExportItemRejects :=
  DeclarativeGrammar.localExportItemExactOutcomeSpec

/-- Two localExportItem successes fix the complete AST and declarative remainder. -/
theorem localExportItem_success_result_unique
    {input leftOutput rightOutput : State} {left right : LocalExportItem}
    (leftResult : ExportInternals.localExportItem input = .ok left leftOutput)
    (rightResult : ExportInternals.localExportItem input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  localExportItem_exactOutcomeSpec.successResultUnique
    (localExportItem_success_ordinaryOutcome_sound leftResult)
    (localExportItem_success_ordinaryOutcome_sound rightResult)

/-- Two localExportItem rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem localExportItem_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.localExportItem input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.localExportItem input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  localExportItem_exactOutcomeSpec.rejectOutputUnique
    (localExportItem_reject_ordinaryOutcome_sound leftResult)
    (localExportItem_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LocalExportOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for local export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable local-export rejection occurs either in the prioritized
braced item list or at the exact non-recovering semicolon finish. -/
theorem localExport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.localExport start input =
      .reject failure rejected) :
    DeclarativeGrammar.LocalExportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.localExport at result
  cases itemsResult : delimited .leftBrace .rightBrace true
      ExportInternals.localExportItem .exportDecl .topLevel input with
  | invariant error => simp [bind, itemsResult] at result
  | reject itemsFailure itemsRejected =>
      simp only [bind, itemsResult] at result
      cases result
      exact .itemsRejected
        (delimited_reject_sound .leftBrace .rightBrace true
          ExportInternals.localExportItem
          DeclarativeGrammar.LocalExportItemOrdinaryParses
          DeclarativeGrammar.LocalExportItemRejects .exportDecl .topLevel
          localExportItem_success_ordinaryOutcome_sound
          localExportItem_reject_ordinaryOutcome_sound itemsResult)
  | ok items afterItems =>
      have itemsParsed := delimited_allowEmpty_trailing_success_sound
        .leftBrace .rightBrace ExportInternals.localExportItem
        DeclarativeGrammar.LocalExportItemOrdinaryParses .exportDecl .topLevel
        localExportItem_success_ordinaryOutcome_sound
        localExportItem_preservesTokenWindow itemsResult
      simp only [bind, itemsResult] at result
      exact .finishRejected itemsParsed
        (finishExport_reject_ordinaryOutcome_sound start (.local items) result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LocalExportOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for local export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export local-export success as a broad ordinary outcome. -/
theorem localExport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ExportDecl}
    (result : ExportInternals.localExport start input =
      .ok declaration output) :
    DeclarativeGrammar.LocalExportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder :=
  localExport_success_sound start result

/-- Package local-export success and exact prioritized rejection. -/
theorem localExport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ExportDecl},
      ExportInternals.localExport start input = .ok declaration output →
        DeclarativeGrammar.LocalExportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.localExport start input = .reject failure rejected →
        DeclarativeGrammar.LocalExportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨localExport_success_ordinaryOutcome_sound start,
    localExport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive local-export outcomes. -/
theorem localExport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LocalExportOrdinaryParses start)
      DeclarativeGrammar.LocalExportRejects :=
  DeclarativeGrammar.localExportDeterministicOutcomeSpec start

/-- Re-export exact localExport outcomes with all supplied span data fixed. -/
theorem localExport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.LocalExportOrdinaryParses start)
      DeclarativeGrammar.LocalExportRejects :=
  DeclarativeGrammar.localExportExactOutcomeSpec start

/-- Two localExport successes fix the complete AST and declarative remainder. -/
theorem localExport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ExportDecl}
    (leftResult : ExportInternals.localExport start input = .ok left leftOutput)
    (rightResult : ExportInternals.localExport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (localExport_exactOutcomeSpec start).successResultUnique
    (localExport_success_ordinaryOutcome_sound start leftResult)
    (localExport_success_ordinaryOutcome_sound start rightResult)

/-- Two localExport rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem localExport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.localExport start input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.localExport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (localExport_exactOutcomeSpec start).rejectOutputUnique
    (localExport_reject_ordinaryOutcome_sound start leftResult)
    (localExport_reject_ordinaryOutcome_sound start rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportDeclarationOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for complete export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem exportKeyword_reject_tokenKindAbsentAt
    {input rejected : State} {failure : Failure}
    (result : keyword .exportKw .exportDecl input =
      .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword .exportKw) := by
  by_cases present : isKeyword input .exportKw = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true .exportKw .exportDecl present
        with ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact keywordAbsentAt_of_isKeyword_eq_false .exportKw
      (Bool.eq_false_iff.mpr present)

private theorem exportKeyword_reject_state_eq
    {input rejected : State} {failure : Failure}
    (result : keyword .exportKw .exportDecl input =
      .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.keyword .exportKw) .exportDecl
    (· == .keyword .exportKw) result

private theorem exportDeclLeftBracePresentAt_of_isSymbol_eq_true
    {input : State} (present : isSymbol input .leftBrace = true) :
    DeclarativeGrammar.ExportDeclLeftBracePresentAt
      input.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .leftBrace .exportDecl present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses .leftBrace .exportDecl parsed).1⟩

/-- Every executable complete-export rejection records the exact missing
keyword or the uniquely selected local/path payload rejection. -/
theorem exportDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : exportDecl input = .reject failure rejected) :
    DeclarativeGrammar.ExportDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold exportDecl at result
  cases keywordResult : keyword .exportKw .exportDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have keywordRejectedEq := exportKeyword_reject_state_eq keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      exact .keywordMissing
        (exportKeyword_reject_tokenKindAbsentAt keywordResult)
  | ok keyword afterKeyword =>
      have keywordParsed := keyword_success_exactTokenParses .exportKw
        .exportDecl keywordResult
      simp only [bind, keywordResult, getState] at result
      by_cases leftBracePresent : isSymbol afterKeyword .leftBrace = true
      · simp only [leftBracePresent, if_true] at result
        exact .localRejected keyword.span keywordParsed
          (exportDeclLeftBracePresentAt_of_isSymbol_eq_true leftBracePresent)
          (localExport_reject_ordinaryOutcome_sound keyword.span result)
      · have leftBraceAbsent : isSymbol afterKeyword .leftBrace = false :=
          Bool.eq_false_iff.mpr leftBracePresent
        simp only [leftBraceAbsent, Bool.false_eq_true, if_false] at result
        exact .pathRejected keyword.span keywordParsed
          (symbolAbsentAt_of_isSymbol_eq_false .leftBrace leftBraceAbsent)
          (pathExport_reject_ordinaryOutcome_sound keyword.span result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportDeclarationOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export complete-export success as a broad ordinary outcome. -/
theorem exportDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : ExportDecl}
    (result : exportDecl input = .ok declaration output) :
    DeclarativeGrammar.ExportDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder :=
  exportDecl_success_sound result

/-- Package complete-export success and exact prioritized rejection. -/
theorem exportDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ExportDecl},
      exportDecl input = .ok declaration output →
        DeclarativeGrammar.ExportDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      exportDecl input = .reject failure rejected →
        DeclarativeGrammar.ExportDeclRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨exportDecl_success_ordinaryOutcome_sound,
    exportDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive complete-export outcomes. -/
theorem exportDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExportDeclOrdinaryParses
      DeclarativeGrammar.ExportDeclRejects :=
  DeclarativeGrammar.exportDeclDeterministicOutcomeSpec

/-- Re-export exact exportDecl outcomes with all supplied span data fixed. -/
theorem exportDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ExportDeclOrdinaryParses
      DeclarativeGrammar.ExportDeclRejects :=
  DeclarativeGrammar.exportDeclExactOutcomeSpec

/-- Two exportDecl successes fix the complete AST and declarative remainder. -/
theorem exportDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : ExportDecl}
    (leftResult : exportDecl input = .ok left leftOutput)
    (rightResult : exportDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportDecl_exactOutcomeSpec.successResultUnique
    (exportDecl_success_ordinaryOutcome_sound leftResult)
    (exportDecl_success_ordinaryOutcome_sound rightResult)

/-- Two exportDecl rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem exportDecl_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : exportDecl input = .reject leftFailure leftOutput)
    (rightResult : exportDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportDecl_exactOutcomeSpec.rejectOutputUnique
    (exportDecl_reject_ordinaryOutcome_sound leftResult)
    (exportDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ConstructorSelectionOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export constructor-selection success as a broad ordinary outcome. -/
theorem constructorSelection_success_ordinaryOutcome_sound
    {input output : State} {selection : ConstructorSelection}
    (result : ExportInternals.constructorSelection input =
      .ok selection output) :
    DeclarativeGrammar.ConstructorSelectionOrdinaryParses
      input.declarativeRemainder selection output.declarativeRemainder :=
  constructorSelection_success_sound result

/-- Package constructor-selection success and exact prioritized rejection. -/
theorem constructorSelection_ordinaryOutcome_sound :
    (∀ {input output : State} {selection : ConstructorSelection},
      ExportInternals.constructorSelection input = .ok selection output →
        DeclarativeGrammar.ConstructorSelectionOrdinaryParses
          input.declarativeRemainder selection output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.constructorSelection input = .reject failure rejected →
        DeclarativeGrammar.ConstructorSelectionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨constructorSelection_success_ordinaryOutcome_sound,
    constructorSelection_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive constructor-selection outcomes. -/
theorem constructorSelection_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorSelectionOrdinaryParses
      DeclarativeGrammar.ConstructorSelectionRejects :=
  DeclarativeGrammar.constructorSelectionDeterministicOutcomeSpec

/-- Re-export exact constructorSelection outcomes with all supplied span data fixed. -/
theorem constructorSelection_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorSelectionOrdinaryParses
      DeclarativeGrammar.ConstructorSelectionRejects :=
  DeclarativeGrammar.constructorSelectionExactOutcomeSpec

/-- Two constructorSelection successes fix the complete AST and declarative remainder. -/
theorem constructorSelection_success_result_unique
    {input leftOutput rightOutput : State} {left right : ConstructorSelection}
    (leftResult : ExportInternals.constructorSelection input = .ok left leftOutput)
    (rightResult : ExportInternals.constructorSelection input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  constructorSelection_exactOutcomeSpec.successResultUnique
    (constructorSelection_success_ordinaryOutcome_sound leftResult)
    (constructorSelection_success_ordinaryOutcome_sound rightResult)

/-- Two constructorSelection rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem constructorSelection_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.constructorSelection input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.constructorSelection input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  constructorSelection_exactOutcomeSpec.rejectOutputUnique
    (constructorSelection_reject_ordinaryOutcome_sound leftResult)
    (constructorSelection_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaItemsOrdinarySuccessSoundnessProperties
/-! Exact executable ordinary success for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem pragmaItemsTokenPresentAt_of_isSymbol_eq_true
    (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.PragmaItemsTokenPresentAt
      input.declarativeRemainder (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .pragmaDecl present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .pragmaDecl parsed).1⟩

private theorem remainingCount_lt_after_pragma_item
    {fuel : Nat} {input afterComma afterItem : State}
    {comma : Token} {item : Identifier}
    (commaResult : symbol .comma .pragmaDecl input = .ok comma afterComma)
    (itemResult : identifier .pragmaDecl afterComma = .ok item afterItem)
    (adequate : input.remainingCount < fuel + 1) :
    afterItem.remainingCount < fuel := by
  rcases symbol_ok_state_shape .comma .pragmaDecl commaResult with
    ⟨commaFound, rfl⟩
  rcases identifier_ok_state_shape .pragmaDecl itemResult with
    ⟨_token, _found, _span, _tokens, itemCursor⟩
  have itemWindow := identifier_preservesTokenWindow .pragmaDecl
    { input with cursor := input.cursor + 1 }
  rw [itemResult] at itemWindow
  have cursorBeforeEnd :=
    State.cursor_lt_endIndex_of_peek?_eq_some commaFound
  have endIndexEq : afterItem.window.endIndex = input.window.endIndex := by
    simpa using congrArg TokenWindow.endIndex itemWindow.2
  have cursorEq : afterItem.cursor = input.cursor + 2 := by
    simpa only [State.cursor] using itemCursor
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq, cursorEq]
  omega

/-- With adequate fuel, a successful executable tail returns the reverse
accumulator followed by the exact forward suffix parsed from the input. -/
theorem pragmaItemsTail_success_ordinaryOutcome_sound_of_remainingCount_lt :
    ∀ fuel itemsRev input items output,
      input.remainingCount < fuel →
      pragmaItemsTail fuel itemsRev input = .ok items output →
      ∃ suffix,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.PragmaItemsTailOrdinaryParses
          input.declarativeRemainder suffix output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items output adequate
      omega
  | succ fuel inductionHypothesis =>
      intro itemsRev input items output adequate result
      unfold pragmaItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp only [commaPresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (symbolAbsentAt_of_isSymbol_eq_false .comma commaPresent)⟩
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .pragmaDecl input with
          | invariant error => simp [commaResult] at result
          | reject failure rejected =>
              rcases symbol_eq_ok_of_isSymbol_eq_true .comma .pragmaDecl
                  commaPresent with ⟨comma, parsed⟩
              rw [parsed] at commaResult
              contradiction
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases semicolonPresent : isSymbol afterComma .semicolon with
              | true =>
                  simp only [semicolonPresent, if_true] at result
                  cases result
                  exact ⟨[], by simp,
                    .trailing comma.span
                      (pragmaItemsTokenPresentAt_of_isSymbol_eq_true .comma
                        commaPresent)
                      (symbol_success_exactTokenParses .comma .pragmaDecl
                        commaResult)
                      (pragmaItemsTokenPresentAt_of_isSymbol_eq_true
                        .semicolon semicolonPresent)⟩
              | false =>
                  simp only [semicolonPresent, Bool.false_eq_true, if_false]
                    at result
                  cases itemResult : identifier .pragmaDecl afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject failure rejected => simp [itemResult] at result
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      rcases inductionHypothesis (item :: itemsRev) afterItem
                          items output
                          (remainingCount_lt_after_pragma_item commaResult
                            itemResult adequate)
                          result with ⟨suffix, itemsEq, tailParsed⟩
                      refine ⟨item :: suffix, ?_,
                        .next comma.span
                          (pragmaItemsTokenPresentAt_of_isSymbol_eq_true
                            .comma commaPresent)
                          (symbol_success_exactTokenParses .comma .pragmaDecl
                            commaResult)
                          (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                            semicolonPresent)
                          (identifier_success_sound .pragmaDecl itemResult)
                          tailParsed⟩
                      simpa [List.reverse_cons, List.append_assoc] using
                        itemsEq

/-- Production fuel specializes successful tail reflection without exposing
the fuel arithmetic to callers. -/
theorem pragmaItemsTail_production_success_ordinaryOutcome_sound
    (itemsRev : List Identifier) {input output : State}
    {items : List Identifier}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok items output) :
    ∃ suffix,
      items = itemsRev.reverse ++ suffix ∧
      DeclarativeGrammar.PragmaItemsTailOrdinaryParses
        input.declarativeRemainder suffix output.declarativeRemainder :=
  pragmaItemsTail_success_ordinaryOutcome_sound_of_remainingCount_lt
    (input.remainingCount + 1) itemsRev input items output (by omega) result

/-- Every successful public pragma-item scan records exact priority guards,
forward item order, and its final remainder. -/
theorem pragmaItems_success_ordinaryOutcome_sound
    {input output : State} {items : List Identifier}
    (result : pragmaItems input = .ok items output) :
    DeclarativeGrammar.PragmaItemsOrdinaryParses
      input.declarativeRemainder items output.declarativeRemainder := by
  unfold pragmaItems at result
  cases semicolonPresent : isSymbol input .semicolon with
  | true =>
      simp only [semicolonPresent, if_true] at result
      cases result
      exact .empty
        (pragmaItemsTokenPresentAt_of_isSymbol_eq_true .semicolon
          semicolonPresent)
  | false =>
      simp only [semicolonPresent, Bool.false_eq_true, if_false] at result
      cases firstResult : identifier .pragmaDecl input with
      | invariant error => simp [firstResult] at result
      | reject failure rejected => simp [firstResult] at result
      | ok first afterFirst =>
          simp only [firstResult] at result
          rcases pragmaItemsTail_production_success_ordinaryOutcome_sound
              [first] result with ⟨suffix, itemsEq, tailParsed⟩
          have itemsForm : items = first :: suffix := by simpa using itemsEq
          rw [itemsForm]
          exact .nonempty
            (symbolAbsentAt_of_isSymbol_eq_false .semicolon semicolonPresent)
            (identifier_success_sound .pragmaDecl firstResult) tailParsed

end Solcore.Syntax.Parser.PragmaInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaItemsOrdinaryRejectionSoundnessProperties
/-! Exact executable ordinary rejection for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem pragmaItemsTokenPresentAt_of_isSymbol_eq_true_reject
    (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.PragmaItemsTokenPresentAt
      input.declarativeRemainder (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .pragmaDecl present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .pragmaDecl parsed).1⟩

private theorem remainingCount_lt_after_rejected_pragma_item_step
    {fuel : Nat} {input afterComma afterItem : State}
    {comma : Token} {item : Identifier}
    (commaResult : symbol .comma .pragmaDecl input = .ok comma afterComma)
    (itemResult : identifier .pragmaDecl afterComma = .ok item afterItem)
    (adequate : input.remainingCount < fuel + 1) :
    afterItem.remainingCount < fuel := by
  rcases symbol_ok_state_shape .comma .pragmaDecl commaResult with
    ⟨commaFound, rfl⟩
  rcases identifier_ok_state_shape .pragmaDecl itemResult with
    ⟨_token, _found, _span, _tokens, itemCursor⟩
  have itemWindow := identifier_preservesTokenWindow .pragmaDecl
    { input with cursor := input.cursor + 1 }
  rw [itemResult] at itemWindow
  have cursorBeforeEnd :=
    State.cursor_lt_endIndex_of_peek?_eq_some commaFound
  have endIndexEq : afterItem.window.endIndex = input.window.endIndex := by
    simpa using congrArg TokenWindow.endIndex itemWindow.2
  have cursorEq : afterItem.cursor = input.cursor + 2 := by
    simpa only [State.cursor] using itemCursor
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq, cursorEq]
  omega

/-- With adequate fuel, every executable tail rejection records the first
checked identifier rejection reached after exact comma/semicolon priority. -/
theorem pragmaItemsTail_reject_ordinaryOutcome_sound_of_remainingCount_lt :
    ∀ fuel itemsRev input failure rejected,
      input.remainingCount < fuel →
      pragmaItemsTail fuel itemsRev input = .reject failure rejected →
      DeclarativeGrammar.PragmaItemsTailRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input failure rejected adequate
      omega
  | succ fuel inductionHypothesis =>
      intro itemsRev input failure rejected adequate result
      unfold pragmaItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false => simp [commaPresent] at result
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .pragmaDecl input with
          | invariant error => simp [commaResult] at result
          | reject commaFailure commaRejected =>
              rcases symbol_eq_ok_of_isSymbol_eq_true .comma .pragmaDecl
                  commaPresent with ⟨comma, parsed⟩
              rw [parsed] at commaResult
              contradiction
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases semicolonPresent : isSymbol afterComma .semicolon with
              | true => simp [semicolonPresent] at result
              | false =>
                  simp only [semicolonPresent, Bool.false_eq_true, if_false]
                    at result
                  cases itemResult : identifier .pragmaDecl afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject itemFailure itemRejected =>
                      simp only [itemResult] at result
                      cases result
                      exact .identifierRejected comma.span
                        (pragmaItemsTokenPresentAt_of_isSymbol_eq_true_reject
                          .comma commaPresent)
                        (symbol_success_exactTokenParses .comma .pragmaDecl
                          commaResult)
                        (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                          semicolonPresent)
                        (identifier_reject_sound .pragmaDecl itemResult)
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      exact .laterRejected comma.span
                        (pragmaItemsTokenPresentAt_of_isSymbol_eq_true_reject
                          .comma commaPresent)
                        (symbol_success_exactTokenParses .comma .pragmaDecl
                          commaResult)
                        (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                          semicolonPresent)
                        (identifier_success_sound .pragmaDecl itemResult)
                        (inductionHypothesis (item :: itemsRev) afterItem
                          failure rejected
                          (remainingCount_lt_after_rejected_pragma_item_step
                            commaResult itemResult adequate)
                          result)

/-- Production fuel specializes rejected tail reflection without exposing
the fuel arithmetic to callers. -/
theorem pragmaItemsTail_production_reject_ordinaryOutcome_sound
    (itemsRev : List Identifier) {input rejected : State}
    {failure : Failure}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .reject failure rejected) :
    DeclarativeGrammar.PragmaItemsTailRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  pragmaItemsTail_reject_ordinaryOutcome_sound_of_remainingCount_lt
    (input.remainingCount + 1) itemsRev input failure rejected (by omega)
      result

/-- Every rejected public pragma-item scan records whether the first checked
identifier or a committed suffix rejected. -/
theorem pragmaItems_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : pragmaItems input = .reject failure rejected) :
    DeclarativeGrammar.PragmaItemsRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold pragmaItems at result
  cases semicolonPresent : isSymbol input .semicolon with
  | true => simp [semicolonPresent] at result
  | false =>
      simp only [semicolonPresent, Bool.false_eq_true, if_false] at result
      have semicolonAbsent :=
        symbolAbsentAt_of_isSymbol_eq_false .semicolon semicolonPresent
      cases firstResult : identifier .pragmaDecl input with
      | invariant error => simp [firstResult] at result
      | reject firstFailure firstRejected =>
          simp only [firstResult] at result
          cases result
          exact .firstIdentifierRejected semicolonAbsent
            (identifier_reject_sound .pragmaDecl firstResult)
      | ok first afterFirst =>
          simp only [firstResult] at result
          exact .tailRejected semicolonAbsent
            (identifier_success_sound .pragmaDecl firstResult)
            (pragmaItemsTail_production_reject_ordinaryOutcome_sound [first]
              result)

end Solcore.Syntax.Parser.PragmaInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaItemsOrdinaryOutcomeSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaDeclarationOrdinarySuccessSoundnessProperties
/-! Exact executable ordinary success for complete pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

/-- Every executable pragma success records the exact keyword, raw name,
checked item scan, semicolon, AST cover, and final remainder. -/
theorem pragmaDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration output) :
    DeclarativeGrammar.PragmaDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold pragmaDecl at result
  rcases bind_ok_components result with
    ⟨pragmaKeyword, afterKeyword, keywordResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, itemsStage⟩
  rcases bind_ok_components itemsStage with
    ⟨items, afterItems, itemsResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed pragmaKeyword.span semicolon.span
    (keyword_success_exactTokenParses .pragmaKw .pragmaDecl keywordResult)
    (rawIdentifier_success_ordinaryOutcome_sound .pragmaDecl nameResult)
    (PragmaInternals.pragmaItems_success_ordinaryOutcome_sound itemsResult)
    (symbol_success_exactTokenParses .semicolon .pragmaDecl semicolonResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaDeclarationOrdinaryRejectionSoundnessProperties
/-! Exact executable ordinary rejection for complete pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable pragma rejection records the exact first failing keyword,
raw name, checked item scan, or final semicolon stage. -/
theorem pragmaDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : pragmaDecl input = .reject failure rejected) :
    DeclarativeGrammar.PragmaDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have rejectedEq := keyword_reject_state_eq .pragmaKw .pragmaDecl
        keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      exact .keywordMissing
        (keyword_reject_tokenKindAbsentAt .pragmaKw .pragmaDecl
          keywordResult)
  | ok pragmaKeyword afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordParsed := keyword_success_exactTokenParses .pragmaKw
        .pragmaDecl keywordResult
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected pragmaKeyword.span keywordParsed
            (rawIdentifier_reject_ordinaryOutcome_sound .pragmaDecl
              nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := rawIdentifier_success_ordinaryOutcome_sound
            .pragmaDecl nameResult
          cases itemsResult : PragmaInternals.pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject itemsFailure itemsRejected =>
              simp only [itemsResult] at result
              cases result
              exact .itemsRejected pragmaKeyword.span keywordParsed
                nameParsed
                (PragmaInternals.pragmaItems_reject_ordinaryOutcome_sound
                  itemsResult)
          | ok items afterItems =>
              simp only [itemsResult] at result
              have itemsParsed :=
                PragmaInternals.pragmaItems_success_ordinaryOutcome_sound
                  itemsResult
              cases semicolonResult : symbol .semicolon .pragmaDecl
                  afterItems with
              | invariant error => simp [semicolonResult] at result
              | ok semicolon output => simp [semicolonResult, pure] at result
              | reject semicolonFailure semicolonRejected =>
                  have rejectedEq := symbol_reject_state_eq .semicolon
                    .pragmaDecl semicolonResult
                  subst semicolonRejected
                  simp only [semicolonResult] at result
                  cases result
                  exact .semicolonMissing pragmaKeyword.span keywordParsed
                    nameParsed itemsParsed
                    (symbol_reject_tokenKindAbsentAt .semicolon .pragmaDecl
                      semicolonResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaDeclarationOrdinaryOutcomeSoundnessProperties
/-! Complete executable ordinary outcomes for pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable pragma success and rejection. -/
theorem pragmaDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : PragmaDecl},
      pragmaDecl input = .ok declaration output →
        DeclarativeGrammar.PragmaDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      pragmaDecl input = .reject failure rejected →
        DeclarativeGrammar.PragmaDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨pragmaDecl_success_ordinaryOutcome_sound,
    pragmaDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive parser-independent pragma outcomes. -/
theorem pragmaDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PragmaDeclOrdinaryParses
      DeclarativeGrammar.PragmaDeclRejects :=
  DeclarativeGrammar.pragmaDeclDeterministicOutcomeSpec

/-- Re-export unconditional exact ordinary pragma-declaration outcomes. -/
theorem pragmaDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PragmaDeclOrdinaryParses
      DeclarativeGrammar.PragmaDeclRejects :=
  DeclarativeGrammar.pragmaDeclExactOutcomeSpec

/-- Two successful pragma declarations have the same AST and declarative
remainder. -/
theorem pragmaDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : PragmaDecl}
    (leftResult : pragmaDecl input = .ok left leftOutput)
    (rightResult : pragmaDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pragmaDecl_exactOutcomeSpec.successResultUnique
    (pragmaDecl_success_ordinaryOutcome_sound leftResult)
    (pragmaDecl_success_ordinaryOutcome_sound rightResult)

/-- Two rejected pragma declarations have the same declarative endpoint;
no failure diagnostic payload equality is asserted. -/
theorem pragmaDecl_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : pragmaDecl input = .reject leftFailure leftOutput)
    (rightResult : pragmaDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pragmaDecl_exactOutcomeSpec.rejectOutputUnique
    (pragmaDecl_reject_ordinaryOutcome_sound leftResult)
    (pragmaDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionProperties
/-! State and start-token contracts for complete function declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem functionBind_ok_components {α β : Type}
    {first : Parser α} {next : α → Parser β} {input final : State}
    {value : β} (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
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

namespace FunctionInternals

/-- The state-indexed public block wrapper retains its opening-brace start. -/
theorem block_startsAtCurrentTokenOnSuccess
    (policy : TailExpressionPolicy) :
    Parser.StartsAtCurrentTokenOnSuccess (block policy) (·.span) := by
  intro input body next parsed
  unfold block at parsed
  exact coreBlock_startsAtCurrentTokenOnSuccess _ policy
    input body next parsed

/-- A complete signature advances past its initial `function` keyword. -/
theorem functionSignature_cursor_lt_onSuccess
    (location : FunctionLocation) {input final : State}
    {signature : FunctionSignature}
    (parsed : functionSignature location input = .ok signature final) :
    input.cursor < final.cursor := by
  have stages := parsed
  unfold functionSignature at stages
  rcases functionBind_ok_components stages with
    ⟨functionToken, afterKeyword, keywordResult, rest⟩
  rcases functionBind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases functionBind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericResult, rest⟩
  rcases functionBind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases functionBind_ok_components rest with
    ⟨modifiers, afterModifiers, modifiersResult, rest⟩
  rcases functionBind_ok_components rest with
    ⟨returnsClause, afterReturns, returnsResult, rest⟩
  rcases functionBind_ok_components rest with
    ⟨parsedWhereClause, afterWhere, whereResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (acceptToken_cursor_lt_onSuccess (.keyword .functionKw) .topItem
      (fun kind => kind == .keyword .functionKw) keywordResult)
    (Nat.le_trans
      (identifier_cursorMonotoneOnSuccess .topItem afterKeyword name
        afterName nameResult)
      (Nat.le_trans
        (optionalGenericParameters_cursorMonotoneOnSuccess afterName
          genericParameters afterGenerics genericResult)
        (Nat.le_trans
          (functionParameters_cursorMonotoneOnSuccess afterGenerics
            parameters afterParameters parametersResult)
          (Nat.le_trans
            (functionModifiers_cursorMonotoneOnSuccess location
              afterParameters modifiers afterModifiers modifiersResult)
            (Nat.le_trans
              (returnClause_cursorMonotoneOnSuccess afterModifiers
                returnsClause afterReturns returnsResult)
              (whereClause_cursorMonotoneOnSuccess afterReturns
                parsedWhereClause final whereResult))))))

end FunctionInternals

open FunctionInternals

/-- A complete function's signature-to-body cover is source-valid. -/
theorem functionDecl_span_validOnSuccess
    (statementValid : SourceFile → Statement → Prop)
    (location : FunctionLocation)
    (bodyValid : (block .allow).ValidFor
      (Block.ValidFor statementValid))
    {input final : State} {declaration : FunctionDecl}
    (inputValid : input.ValidFor)
    (parsed : functionDecl location input = .ok declaration final) :
    declaration.span.ValidFor input.file := by
  have stages := parsed
  unfold functionDecl at stages
  rcases functionBind_ok_components stages with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases functionBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  have signatureContract := functionSignature_validFor location input inputValid
  rw [signatureResult] at signatureContract
  have isolatedValid := isolateBlock_validFor statementValid
    (block .allow) bodyValid
  have bodyContract := isolatedValid afterSignature signatureContract.2.1
  rw [bodyResult] at bodyContract
  have signatureValidInput : FunctionSignature.ValidFor input.file signature := by
    simpa [signatureContract.2.2] using signatureContract.1
  have bodyValidInput : Block.ValidFor statementValid input.file body := by
    simpa [bodyContract.2.2, signatureContract.2.2] using bodyContract.1
  rcases functionSignature_startsAtCurrentTokenOnSuccess location
      input signature afterSignature signatureResult with
    ⟨functionToken, functionFound, signatureStart⟩
  rcases isolateBlock_startsAtCurrentTokenOnSuccess (block .allow)
      (block_startsAtCurrentTokenOnSuccess .allow)
      afterSignature body afterBody bodyResult with
    ⟨opening, openingFound, bodyStart⟩
  have functionAt := State.getElem?_eq_some_of_peek?_eq_some functionFound
  have openingAtAfter :=
    State.getElem?_eq_some_of_peek?_eq_some openingFound
  have signatureTokens := functionSignature_preservesTokensOnSuccess location
    input signature afterSignature signatureResult
  have openingAt : input.tokens[afterSignature.cursor]? = some opening := by
    simpa [signatureTokens] using openingAtAfter
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt
    functionAt openingAt
    (functionSignature_cursor_lt_onSuccess location signatureResult)
  have functionValid := inputValid.peek?_span_validFor functionFound
  have ordered : signature.span.startByte ≤ body.span.endByte := by
    calc
      signature.span.startByte = functionToken.span.startByte :=
        signatureStart.symm
      _ ≤ functionToken.span.endByte := functionValid.2.1
      _ ≤ opening.span.startByte := separated
      _ = body.span.startByte := bodyStart
      _ ≤ body.span.endByte := bodyValidInput.1.2.1
  cases finished
  exact SourceSpan.cover_validFor signatureValidInput.1
    bodyValidInput.1 ordered

/--
Function declarations retain valid inner syntax when the isolated body does;
only the outer cover-span law remains an explicit premise.
-/
theorem functionDecl_validFor_of_span
    (statementValid : SourceFile → Statement → Prop)
    (location : FunctionLocation)
    (bodyValid : (isolateBlock (block .allow)).ValidFor
      (Block.ValidFor statementValid))
    (spanValidOnSuccess : ∀ input declaration next,
      input.ValidFor → functionDecl location input = .ok declaration next →
      declaration.span.ValidFor input.file) :
    (functionDecl location).ValidFor
      (FunctionDecl.ValidFor statementValid) := by
  have weak : (functionDecl location).ValidFor (fun _ _ => True) := by
    unfold functionDecl
    apply Parser.bind_validFor (functionSignature_validFor location)
    intro signature
    apply Parser.bind_validFor bodyValid
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : functionDecl location input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok declaration final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold functionDecl at stages
      rcases functionBind_ok_components stages with
        ⟨signature, afterSignature, signatureResult, rest⟩
      rcases functionBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have signatureContract := functionSignature_validFor location input inputValid
      rw [signatureResult] at signatureContract
      have bodyContract := bodyValid afterSignature signatureContract.2.1
      rw [bodyResult] at bodyContract
      have signatureValidInput : FunctionSignature.ValidFor input.file signature := by
        simpa [signatureContract.2.2] using signatureContract.1
      have bodyValidInput : Block.ValidFor statementValid input.file body := by
        simpa [bodyContract.2.2, signatureContract.2.2] using bodyContract.1
      have outerValid := spanValidOnSuccess input declaration final inputValid parsed
      cases finished
      exact ⟨⟨outerValid, signatureValidInput, bodyValidInput.1,
        bodyValidInput.2⟩, weakResult.2.1, weakResult.2.2⟩

/-- Complete function declarations retain only source-valid syntax. -/
theorem functionDecl_validFor
    (statementValid : SourceFile → Statement → Prop)
    (location : FunctionLocation)
    (bodyValid : (block .allow).ValidFor
      (Block.ValidFor statementValid)) :
    (functionDecl location).ValidFor
      (FunctionDecl.ValidFor statementValid) :=
  functionDecl_validFor_of_span statementValid location
    (isolateBlock_validFor statementValid (block .allow) bodyValid)
    (fun _ _ _ inputValid parsed =>
      functionDecl_span_validOnSuccess statementValid location bodyValid
        inputValid parsed)

/-- Function declarations preserve token windows when block parsing does. -/
theorem functionDecl_preservesTokenWindow_of_block
    (location : FunctionLocation)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow (functionDecl location) := by
  unfold functionDecl
  apply Parser.bind_preservesTokenWindow
    (functionSignature_preservesTokenWindow location)
  intro signature
  apply Parser.bind_preservesTokenWindow
    (isolateBlock_preservesTokenWindow (block .allow) bodyWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Successful function parsing preserves the immutable token carrier. -/
theorem functionDecl_preservesTokensOnSuccess_of_block
    (location : FunctionLocation)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokensOnSuccess (functionDecl location) :=
  (functionDecl_preservesTokenWindow_of_block location bodyWindow
    ).preservesTokensOnSuccess

/-- Function declarations never rewind when block parsing is monotone. -/
theorem functionDecl_cursorMonotoneOnSuccess_of_block
    (location : FunctionLocation)
    (bodyCursor : Parser.CursorMonotoneOnSuccess (block .allow)) :
    Parser.CursorMonotoneOnSuccess (functionDecl location) := by
  unfold functionDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (functionSignature_cursorMonotoneOnSuccess location)
  intro signature
  apply Parser.bind_cursorMonotoneOnSuccess
    (isolateBlock_cursorMonotoneOnSuccess (block .allow) bodyCursor)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A function declaration starts at its signature's `function` keyword. -/
theorem functionDecl_startsAtCurrentTokenOnSuccess
    (location : FunctionLocation) :
    Parser.StartsAtCurrentTokenOnSuccess (functionDecl location) (·.span) := by
  unfold functionDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (functionSignature_startsAtCurrentTokenOnSuccess location)
  intro signature input declaration final parsed
  simp only [bind] at parsed
  cases bodyResult : isolateBlock (block .allow) input with
  | invariant error => simp [bodyResult] at parsed
  | reject failure rejected => simp [bodyResult] at parsed
  | ok body afterBody =>
      simp only [bodyResult] at parsed
      cases parsed
      rfl

end Solcore.Syntax.Parser
end
