import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Grammar.Yul
import Solcore.Syntax.Internal.YulBlockOutcomes
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Yul
import Solcore.Syntax.Yul

/-!
Soundness of the parsers of Yul blocks, functions and names: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.YulNamesDiagnosticReflectionProperties
/-! Diagnostic reflection for inline-Yul name sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Finishing a Yul name sequence is non-consuming and preserves diagnostics. -/
theorem finishYulNames_reflectsDiagnosticFreeOnSuccess
    (first last : YulIdentifier) (tailRev : List YulIdentifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (finishYulNames first last tailRev) := by
  intro input names next result diagnosticFree
  unfold finishYulNames at result
  cases result
  exact diagnosticFree

/-- Every successful comma-prioritized Yul name tail reflects diagnostic
freedom through its comma, following name, and recursive suffix. -/
theorem yulNamesTail_reflectsDiagnosticFreeOnSuccess
    (first : YulIdentifier) :
    ∀ fuel last tailRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (yulNamesTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input names next result diagnosticFree
      simp [yulNamesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input names next result diagnosticFree
      unfold yulNamesTail at result
      split at result
      · cases commaResult : symbol .comma .yulStatement input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            cases nameResult : yulName afterComma with
            | invariant error => simp [nameResult] at result
            | reject failure rejected => simp [nameResult] at result
            | ok name afterName =>
                simp only [nameResult] at result
                have afterNameFree := inductionHypothesis name
                  (name :: tailRev) afterName names next result diagnosticFree
                have afterCommaFree :=
                  yulName_reflectsDiagnosticFreeOnSuccess afterComma name
                    afterName nameResult afterNameFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                  .yulStatement input comma afterComma commaResult
                    afterCommaFree
      · exact finishYulNames_reflectsDiagnosticFreeOnSuccess first last
          tailRev input names next result diagnosticFree

/-- Public Yul name-sequence parsing reflects diagnostic freedom. -/
theorem yulNames_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulNames := by
  intro input names next result diagnosticFree
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree := yulNamesTail_reflectsDiagnosticFreeOnSuccess first
        (afterFirst.remainingCount + 1) first [] afterFirst names next result
          diagnosticFree
      exact yulName_reflectsDiagnosticFreeOnSuccess input first afterFirst
        firstResult afterFirstFree

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulNamesSoundnessProperties
/-!
Exact diagnostic-free declarative soundness for inline-Yul name sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Finishing fixes the first-to-last cover, forward name order, and unchanged
remainder. -/
theorem finishYulNames_success_sound
    (first last : YulIdentifier) (tailRev : List YulIdentifier)
    {input next : State} {names : YulNameSequence}
    (result : finishYulNames first last tailRev input = .ok names next) :
    DeclarativeGrammar.FinishYulNamesParses first last tailRev
      input.declarativeRemainder names.span names.names
        next.declarativeRemainder := by
  unfold finishYulNames at result
  cases result
  exact .parsed

/-- Every diagnostic-free tail success follows the exact comma-prioritized,
non-trailing grammar and retains each strict name advance. -/
theorem yulNamesTail_success_sound (first : YulIdentifier) :
    ∀ fuel last tailRev, ∀ {input next : State} {names : YulNameSequence},
      next.diagnosticsRev = [] →
      yulNamesTail first fuel last tailRev input = .ok names next →
      DeclarativeGrammar.YulNamesTailParses first input.declarativeRemainder
        last tailRev names.span names.names next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input next names diagnosticFree result
      simp [yulNamesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input next names diagnosticFree result
      unfold yulNamesTail at result
      split at result
      next commaPresent =>
        cases commaResult : symbol .comma .yulStatement input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            cases nameResult : yulName afterComma with
            | invariant error => simp [nameResult] at result
            | reject failure rejected => simp [nameResult] at result
            | ok name afterName =>
                simp only [nameResult] at result
                have afterNameFree :=
                  yulNamesTail_reflectsDiagnosticFreeOnSuccess first fuel name
                    (name :: tailRev) afterName names next result diagnosticFree
                have nameGrammar :=
                  yulName_success_sound_of_diagnosticFree afterNameFree
                    nameResult
                have tailGrammar := inductionHypothesis name
                  (name :: tailRev) diagnosticFree result
                rcases yulName_ok_state_shape nameResult with
                  ⟨token, found, spanEq, tokensEq, cursorEq⟩
                have progress : afterComma.cursor < afterName.cursor := by
                  rw [cursorEq]
                  exact Nat.lt_succ_self _
                exact .next comma.span
                  (symbol_success_exactTokenParses .comma .yulStatement
                    commaResult)
                  nameGrammar progress tailGrammar
      next commaAbsent =>
        have commaAbsentEq : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaAbsent
        exact .done
          (symbolAbsentAt_of_isSymbol_eq_false .comma commaAbsentEq)
          (finishYulNames_success_sound first last tailRev result)

/-- Every diagnostic-free public name-sequence success is nonempty, has no
trailing comma, preserves forward order, and follows the exact token window. -/
theorem yulNames_success_sound {input next : State}
    {names : YulNameSequence} (diagnosticFree : next.diagnosticsRev = [])
    (result : yulNames input = .ok names next) :
    DeclarativeGrammar.YulNamesParses input.declarativeRemainder names.span
      names.names next.declarativeRemainder := by
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree := yulNamesTail_reflectsDiagnosticFreeOnSuccess first
        (afterFirst.remainingCount + 1) first [] afterFirst names next result
          diagnosticFree
      have firstGrammar := yulName_success_sound_of_diagnosticFree
        afterFirstFree firstResult
      have tailGrammar := yulNamesTail_success_sound first
        (afterFirst.remainingCount + 1) first [] diagnosticFree result
      rcases yulName_ok_state_shape firstResult with
        ⟨token, found, spanEq, tokensEq, cursorEq⟩
      have progress : input.cursor < afterFirst.cursor := by
        rw [cursorEq]
        exact Nat.lt_succ_self _
      exact .parsed firstGrammar progress tailGrammar

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulNameOutcomeProperties
/-!
Executable success and rejection bridges for one ordinary inline-Yul name.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem ordinaryKindStops_of_executable_match_false (kind : TokenKind)
    (result : (match some kind with
      | some (.identifier _)
      | some (.yulIdentifier _)
      | some (.symbol .underscore)
      | some (.keyword .fallbackKw) => true
      | _ => false) = false) :
    DeclarativeGrammar.tokenKindStartsOrdinaryYulName kind = false := by
  cases kind with
  | keyword value =>
      cases value <;>
        simp_all [DeclarativeGrammar.tokenKindStartsOrdinaryYulName]
  | symbol value =>
      cases value <;>
        simp_all [DeclarativeGrammar.tokenKindStartsOrdinaryYulName]
  | identifier text => contradiction
  | yulIdentifier text => contradiction
  | decimalLiteral spelling => rfl
  | hexadecimalLiteral spelling => rfl
  | stringLiteral spelling => rfl
  | yulMetaBacktick spelling => rfl
  | yulMetaInterpolation spelling => rfl

private theorem noOrdinaryYulName_of_startsYulName_eq_false {input : State}
    (absent : startsYulName input = false) :
    ¬ ∃ name output,
      DeclarativeGrammar.YulNameOrdinaryParses input.declarativeRemainder name
        output := by
  rintro ⟨name, output, parsed⟩
  rcases parsed.startsAt with ⟨token, ⟨inside, found⟩, tokenStarts⟩
  change input.cursor < input.window.endIndex at inside
  change input.tokens[input.cursor]? = some token at found
  unfold startsYulName State.peekKind? State.peek? at absent
  simp only [inside, ↓reduceIte, found, Option.map_some] at absent
  have tokenStops :
      DeclarativeGrammar.tokenKindStartsOrdinaryYulName token.value = false :=
    ordinaryKindStops_of_executable_match_false token.value absent
  rw [tokenStarts] at tokenStops
  contradiction

private theorem startsYulName_eq_false_of_yulName_reject
    {input rejected : State} {failure : Failure}
    (result : yulName input = .reject failure rejected) :
    startsYulName input = false := by
  unfold yulName at result
  unfold startsYulName State.peekKind?
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result ⊢
      all_goals try { rfl }
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        simp only [identifier, rawIdentifier, found] at result
        split at result <;> contradiction
      case yulIdentifier text => cases result
      case keyword keyword =>
        cases keyword <;> simp only at result ⊢ <;> try rfl
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw => cases result
      case symbol symbol =>
        cases symbol <;> simp only at result ⊢ <;> try rfl
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore => cases result

/-- Every executable Yul-name success is an ordinary success, even when the
checked ordinary identifier emits a hyphen diagnostic. -/
theorem yulName_success_ordinary_sound {input next : State}
    {name : YulIdentifier} (result : yulName input = .ok name next) :
    DeclarativeGrammar.YulNameOrdinaryParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold yulName at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        exact .identifier (identifier_success_sound .yulExpression result)
      case yulIdentifier text =>
        cases result
        exact .marked (tokenAt_of_peek?_eq_some found)
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw =>
          cases result
          exact .fallbackKeyword (tokenAt_of_peek?_eq_some found)
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore =>
          cases result
          exact .underscore (tokenAt_of_peek?_eq_some found)

/-- Ordinary Yul-name rejection returns the exact input parser state. -/
theorem yulName_reject_state_eq {input rejected : State} {failure : Failure}
    (result : yulName input = .reject failure rejected) : rejected = input := by
  unfold yulName at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      cases result
      rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; cases result; rfl }
      case identifier text =>
        simp only [identifier, rawIdentifier, found] at result
        split at result <;> contradiction
      case yulIdentifier text => contradiction
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; cases result; rfl }
        case fallbackKw => contradiction
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; cases result; rfl }
        case underscore => contradiction

/-- Every executable Yul-name rejection follows the exact binary rejection
relation. -/
theorem yulName_reject_sound {input rejected : State} {failure : Failure}
    (result : yulName input = .reject failure rejected) :
    DeclarativeGrammar.YulNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  have rejectedEq := yulName_reject_state_eq result
  subst rejectedEq
  exact .absent (noOrdinaryYulName_of_startsYulName_eq_false
    (startsYulName_eq_false_of_yulName_reject result))

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulNamesOutcomeProperties
/-!
Executable ordinary-success and exact binary-rejection bridges for nonempty
inline-Yul name sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Executable finishing preserves forward order and does not consume input. -/
theorem finishYulNames_success_ordinary_sound
    (first last : YulIdentifier) (tailRev : List YulIdentifier)
    {input next : State} {names : YulNameSequence}
    (result : finishYulNames first last tailRev input = .ok names next) :
    DeclarativeGrammar.FinishYulNamesOrdinaryParses first last tailRev
      input.declarativeRemainder {
        span := names.span
        names := names.names
      } next.declarativeRemainder := by
  unfold finishYulNames at result
  cases result
  exact .parsed

/-- Every executable ordinary tail success records the comma-prioritized,
forward-order sequence, independently of diagnostics. -/
theorem yulNamesTail_success_ordinary_sound (first : YulIdentifier) :
    ∀ fuel last tailRev, ∀ {input next : State} {names : YulNameSequence},
      yulNamesTail first fuel last tailRev input = .ok names next →
      DeclarativeGrammar.YulNamesTailOrdinaryParses first
        input.declarativeRemainder last tailRev {
          span := names.span
          names := names.names
        } next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input next names result
      simp [yulNamesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input next names result
      unfold yulNamesTail at result
      by_cases commaPresent : isSymbol input .comma = true
      · simp only [commaPresent, if_true] at result
        rcases symbol_eq_ok_of_isSymbol_eq_true .comma .yulStatement
            commaPresent with ⟨comma, commaResult⟩
        simp only [commaResult] at result
        cases nameResult : yulName
            { input with cursor := input.cursor + 1 } with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name afterName =>
            simp only [nameResult] at result
            have nameParsed := yulName_success_ordinary_sound nameResult
            have tailParsed := inductionHypothesis name (name :: tailRev)
              result
            have nameInput :
                DeclarativeGrammar.YulNameOrdinaryParses {
                  input.declarativeRemainder with
                    cursor := input.cursor + 1
                } name afterName.declarativeRemainder := by
              simpa [State.declarativeRemainder] using nameParsed
            exact .next comma.span
              (symbol_ok_tokenAt .comma .yulStatement commaResult).1
              nameInput tailParsed
      · have commaFalse : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaPresent
        simp only [commaFalse, Bool.false_eq_true, if_false] at result
        exact .done
          (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse)
          (finishYulNames_success_ordinary_sound first last tailRev result)

/-- Every executable ordinary tail rejection records whether the name directly
after this comma rejected or a later comma/name pair rejected. -/
theorem yulNamesTail_reject_sound (first : YulIdentifier) :
    ∀ fuel last tailRev, ∀ {input rejected : State} {failure : Failure},
      yulNamesTail first fuel last tailRev input = .reject failure rejected →
      DeclarativeGrammar.YulNamesTailRejects first
        input.declarativeRemainder last tailRev
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input rejected failure result
      simp [yulNamesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input rejected failure result
      unfold yulNamesTail at result
      by_cases commaPresent : isSymbol input .comma = true
      · simp only [commaPresent, if_true] at result
        rcases symbol_eq_ok_of_isSymbol_eq_true .comma .yulStatement
            commaPresent with ⟨comma, commaResult⟩
        simp only [commaResult] at result
        cases nameResult : yulName
            { input with cursor := input.cursor + 1 } with
        | invariant error => simp [nameResult] at result
        | reject nameFailure nameRejected =>
            simp only [nameResult] at result
            cases result
            exact .commaNameRejected comma.span
              (symbol_ok_tokenAt .comma .yulStatement commaResult).1
              (by simpa [State.declarativeRemainder] using
                yulName_reject_sound nameResult)
        | ok name afterName =>
            simp only [nameResult] at result
            have nameParsed := yulName_success_ordinary_sound nameResult
            have nameInput :
                DeclarativeGrammar.YulNameOrdinaryParses {
                  input.declarativeRemainder with
                    cursor := input.cursor + 1
                } name afterName.declarativeRemainder := by
              simpa [State.declarativeRemainder] using nameParsed
            exact .laterRejected comma.span
              (symbol_ok_tokenAt .comma .yulStatement commaResult).1
              nameInput
              (inductionHypothesis name (name :: tailRev) result)
      · have commaFalse : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaPresent
        simp [commaFalse, finishYulNames] at result

/-- Every executable public sequence success follows the ordinary nonempty
sequence relation. -/
theorem yulNames_success_ordinary_sound {input next : State}
    {names : YulNameSequence} (result : yulNames input = .ok names next) :
    DeclarativeGrammar.YulNamesOrdinaryParses input.declarativeRemainder {
      span := names.span
      names := names.names
    } next.declarativeRemainder := by
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .parsed (yulName_success_ordinary_sound firstResult)
        (yulNamesTail_success_ordinary_sound first
          (afterFirst.remainingCount + 1) first [] result)

/-- Every executable public sequence rejection is either its first-name
rejection or an exact later tail rejection. -/
theorem yulNames_reject_sound {input rejected : State} {failure : Failure}
    (result : yulNames input = .reject failure rejected) :
    DeclarativeGrammar.YulNamesRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected (yulName_reject_sound firstResult)
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .tailRejected (yulName_success_ordinary_sound firstResult)
        (yulNamesTail_reject_sound first (afterFirst.remainingCount + 1)
          first [] result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulBlockDiagnosticReflectionProperties
/-!
Backward propagation of diagnostic freedom through raw Yul block closing and
item iteration.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem closeYulBlock_reflectsDiagnosticFreeOnSuccess
    (opening : Token) (bodyRev : List YulStmt) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closeYulBlock opening bodyRev) := by
  intro input body next result diagnosticFree
  unfold closeYulBlock at result
  cases closingResult : symbol .rightBrace .yulStatement input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing afterClosing =>
      simp only [closingResult] at result
      cases result
      exact symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .yulStatement
        input closing next closingResult diagnosticFree

theorem yulBlockItems_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (opening : Token) : ∀ fuel bodyRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (yulBlockItems statement opening fuel bodyRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body next result diagnosticFree
      simp [yulBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next result diagnosticFree
      unfold yulBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          exact closeYulBlock_reflectsDiagnosticFreeOnSuccess opening bodyRev
            input body next result diagnosticFree
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .yulStatement input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok item afterItem =>
                  simp only [statementResult] at result
                  by_cases progress : afterItem.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    have afterItemFree := inductionHypothesis
                      (item :: bodyRev) afterItem body next result
                        diagnosticFree
                    exact statementReflects input item afterItem
                      statementResult afterItemFree
                  · simp only [progress, if_false] at result
                    contradiction

theorem yulBlock_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulBlock statement) := by
  intro input body next result diagnosticFree
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have afterOpeningFree :=
        yulBlockItems_reflectsDiagnosticFreeOnSuccess statement
          statementReflects opening (afterOpening.remainingCount + 1) []
            afterOpening body next result diagnosticFree
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .yulStatement
        input opening afterOpening openingResult afterOpeningFree

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulBlockSoundnessProperties
/-!
Exact diagnostic-free soundness for raw Yul block closing, item iteration,
and the public braced block parser.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Closing retains the reversed accumulator and consumes its exact brace. -/
theorem closeYulBlock_success_sound (opening : Token)
    (bodyRev : List YulStmt) {input next : State} {body : YulParsedBlock}
    (result : closeYulBlock opening bodyRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        body := bodyRev.reverse
      } ∧
      DeclarativeGrammar.CloseYulBlockParses opening.span bodyRev.reverse
        input.declarativeRemainder
          (SourceSpan.cover opening.span closingSpan)
            next.declarativeRemainder ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder := by
  unfold closeYulBlock at result
  cases closingResult : symbol .rightBrace .yulStatement input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing afterClosing =>
      simp only [closingResult] at result
      cases result
      have closingParsed := symbol_success_exactTokenParses .rightBrace
        .yulStatement closingResult
      exact ⟨closing.span, rfl, .parsed closing.span closingParsed,
        closingParsed⟩

/--
Successful iteration recovers the forward suffix following its existing
reverse accumulator, together with the exact block span and closing brace.
-/
theorem yulBlockItems_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (opening : Token) : ∀ fuel bodyRev input body next,
      next.diagnosticsRev = [] →
      yulBlockItems statement opening fuel bodyRev input = .ok body next →
      ∃ bodySpan suffix,
        body = {
          span := bodySpan
          body := bodyRev.reverse ++ suffix
        } ∧
        DeclarativeGrammar.YulBlockItemsParses statementParses opening.span
          input.declarativeRemainder bodySpan suffix
            next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body next diagnosticFree result
      simp [yulBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next diagnosticFree result
      unfold yulBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeYulBlock_success_sound opening bodyRev result with
            ⟨closingSpan, bodyEq, _closeGrammar, closingParsed⟩
          have inputFree := closeYulBlock_reflectsDiagnosticFreeOnSuccess
            opening bodyRev input body next result diagnosticFree
          exact ⟨SourceSpan.cover opening.span closingSpan, [],
            by simpa using bodyEq, .close closingSpan closingParsed,
            inputFree⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .yulStatement input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok item afterItem =>
                  simp only [statementResult] at result
                  by_cases progress : afterItem.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (item :: bodyRev) afterItem
                        body next diagnosticFree result with
                      ⟨bodySpan, suffix, bodyEq, tailGrammar,
                        afterItemFree⟩
                    have itemGrammar := statementSound afterItemFree
                      statementResult
                    have inputFree := statementReflects input item afterItem
                      statementResult afterItemFree
                    have notAtEnd : input.cursor < input.window.endIndex := by
                      simpa [State.atEnd] using ended
                    refine ⟨bodySpan, item :: suffix, ?_,
                      .next notAtEnd
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        itemGrammar progress tailGrammar,
                      inputFree⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every diagnostic-free public success follows the abstract block grammar. -/
theorem yulBlock_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {body : YulParsedBlock}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulBlock statement input = .ok body next) :
    DeclarativeGrammar.YulBlockParses statementParses
      input.declarativeRemainder body.span body.body
        next.declarativeRemainder := by
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases yulBlockItems_success_sound statement statementParses
          statementReflects statementSound opening
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨bodySpan, suffix, bodyEq, bodyGrammar, afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.YulBlockParses.parsed opening.span
        (symbol_success_exactTokenParses .leftBrace .yulStatement
          openingResult) bodyGrammar

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulBlockOrdinaryOutcomeSoundnessProperties
/-!
Executable ordinary-success and exact-rejection bridges for braced Yul
blocks, parameterized by matching statement outcome callbacks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful block-item loop follows the ordinary statement grammar,
retaining the forward suffix after its existing reverse accumulator. -/
theorem yulBlockItems_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (opening : Token) : ∀ fuel bodyRev input body output,
      yulBlockItems statement opening fuel bodyRev input = .ok body output →
      ∃ bodySpan suffix,
        body = {
          span := bodySpan
          body := bodyRev.reverse ++ suffix
        } ∧
        DeclarativeGrammar.YulBlockItemsParses statementOrdinary opening.span
          input.declarativeRemainder bodySpan suffix
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body output result
      simp [yulBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body output result
      unfold yulBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeYulBlock_success_sound opening bodyRev result with
            ⟨closingSpan, bodyEq, closeGrammar, closingParsed⟩
          exact ⟨SourceSpan.cover opening.span closingSpan, [],
            by simpa using bodyEq, .close closingSpan closingParsed⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .yulStatement input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok value afterStatement =>
                  simp only [statementResult] at result
                  by_cases progress : afterStatement.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (value :: bodyRev)
                        afterStatement body output result with
                      ⟨bodySpan, suffix, bodyEq, tailGrammar⟩
                    have notAtEnd :
                        input.cursor < input.window.endIndex := by
                      simpa [State.atEnd] using ended
                    refine ⟨bodySpan, value :: suffix, ?_,
                      .next notAtEnd
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        (statementSuccessSound statementResult) progress
                        tailGrammar⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every successful complete block follows the ordinary block grammar. -/
theorem yulBlock_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {body : YulParsedBlock}
    (result : yulBlock statement input = .ok body output) :
    DeclarativeGrammar.YulBlockOrdinaryParses statementOrdinary
      input.declarativeRemainder body.span body.body
        output.declarativeRemainder := by
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases yulBlockItems_success_ordinary_sound statement
          statementOrdinary statementSuccessSound opening
          (afterOpening.remainingCount + 1) [] afterOpening body output result
        with ⟨bodySpan, suffix, bodyEq, itemsParsed⟩
      rw [bodyEq]
      exact .parsed opening.span
        (symbol_success_exactTokenParses .leftBrace .yulStatement
          openingResult) itemsParsed

/-- Every rejected block-item loop follows the exact ordinary-prefix
rejection trace. -/
theorem yulBlockItems_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (opening : Token) : ∀ fuel bodyRev input failure rejected,
      yulBlockItems statement opening fuel bodyRev input =
        .reject failure rejected →
      DeclarativeGrammar.YulBlockItemsRejects statementOrdinary
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input failure rejected result
      simp [yulBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input failure rejected result
      unfold yulBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .yulStatement
              closingPresent with ⟨closing, closingResult⟩
          unfold closeYulBlock at result
          simp [closingResult] at result
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .yulStatement input with
              | invariant error => simp [closingResult] at result
              | ok closing afterClosing => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have rejectedEq := symbol_reject_state_eq .rightBrace
                    .yulStatement closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  exact .missingClose
                    (symbol_reject_tokenKindAbsentAt .rightBrace .yulStatement
                      closingResult)
                    (by simpa [State.atEnd, State.declarativeRemainder]
                      using ended)
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              have notAtEnd : input.cursor < input.window.endIndex := by
                simpa [State.atEnd] using ended
              have closingAbsent :=
                symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject statementFailure statementRejected =>
                  simp only [statementResult] at result
                  cases result
                  exact .statementRejected notAtEnd closingAbsent
                    (statementRejectSound statementResult)
              | ok value afterStatement =>
                  simp only [statementResult] at result
                  by_cases progress : afterStatement.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    exact .laterRejected notAtEnd closingAbsent
                      (statementSuccessSound statementResult) progress
                      (inductionHypothesis (value :: bodyRev) afterStatement
                        failure rejected result)
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every rejected complete block follows opening failure or the exact
ordinary-prefix block-item rejection trace. -/
theorem yulBlock_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulBlock statement input = .reject failure rejected) :
    DeclarativeGrammar.YulBlockRejects statementOrdinary statementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have rejectedEq := symbol_reject_state_eq .leftBrace .yulStatement
        openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .yulStatement
          openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      exact .itemsRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .yulStatement
          openingResult)
        (yulBlockItems_reject_ordinary_sound statement statementOrdinary
          statementRejects statementSuccessSound statementRejectSound opening
          (afterOpening.remainingCount + 1) [] afterOpening failure rejected
          result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ControlProperties
/-! Compositional contracts for canonical inline-Yul control statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulBind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
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
  | reject failure rejected =>
      rw [firstResult] at parsed
      contradiction
  | invariant error =>
      rw [firstResult] at parsed
      contradiction

/--
Yul `if` parsing preserves the keyword, condition, block, and every statement
retained by the block.  The fixed expression parser remains an explicit
dependency until its recursive fuel proof is closed.
-/
theorem yulIfStatement_validFor (statement : Parser YulStmt)
    (expressionValid : yulExpression.ValidFor YulExpr.ValidFor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess yulExpression (·.span))
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    (yulIfStatement statement).ValidFor YulStmt.ValidFor := by
  have weak : (yulIfStatement statement).ValidFor (fun _ _ => True) := by
    unfold yulIfStatement
    apply Parser.bind_validFor (keyword_validFor .ifKw .yulStatement)
    intro marker
    apply Parser.bind_validFor expressionValid
    intro condition
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulIfStatement statement input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulIfStatement at stages
      rcases yulBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨condition, afterCondition, conditionResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerValid := keyword_validFor .ifKw .yulStatement input inputValid
      rw [markerResult] at markerValid
      have conditionValid := expressionValid afterMarker markerValid.2.1
      rw [conditionResult] at conditionValid
      have bodyValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterCondition conditionValid.2.1
      rw [bodyResult] at bodyValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have conditionValidInput :
          YulExpr.ValidFor input.file condition := by
        simpa [markerValid.2.2] using conditionValid.1
      have bodySpanValid : body.span.ValidFor input.file := by
        simpa [conditionValid.2.2, markerValid.2.2] using bodyValid.1.1
      have bodyStatementsValid :
          ∀ retained ∈ body.body, YulStmt.ValidFor input.file retained := by
        intro retained member
        simpa [conditionValid.2.2, markerValid.2.2] using
          bodyValid.1.2 retained member
      have markerShape := acceptToken_ok_state_shape
        (.keyword .ifKw) .yulStatement (· == .keyword .ifKw) markerResult
      have markerAdvanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      rcases expressionStarts afterMarker condition afterCondition
          conditionResult with
        ⟨conditionToken, conditionFound, conditionStart⟩
      rcases yulBlock_startsAtCurrentTokenOnSuccess statement
          statementPreserves afterCondition body afterBody bodyResult with
        ⟨openingToken, openingFound, openingStart⟩
      have markerAt :=
        State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      have openingAtInput :
          input.tokens[afterCondition.cursor]? = some openingToken := by
        have openingAt :=
          State.getElem?_eq_some_of_peek?_eq_some openingFound
        have conditionTokens := expressionPreserves afterMarker condition
          afterCondition conditionResult
        have markerTokens := keyword_preservesTokensOnSuccess .ifKw
          .yulStatement input marker afterMarker markerResult
        simpa [conditionTokens, markerTokens] using openingAt
      have markerOrder :
          marker.span.endByte ≤ condition.span.startByte ∧
            marker.span.endByte ≤ body.span.startByte := by
        constructor
        · rw [← conditionStart]
          exact inputValid.consumed_end_le_peek_start_after_advance
            markerAdvanced conditionFound
        · rw [← openingStart]
          apply inputValid.token_end_le_token_start_of_getElem?_lt
            markerAt openingAtInput
          have conditionCursor := expressionMonotone afterMarker condition
            afterCondition conditionResult
          have cursorAfterMarker :
              input.cursor + 1 ≤ afterCondition.cursor := by
            simpa [markerShape.2] using conditionCursor
          omega
      have outerValid :
          (SourceSpan.cover marker.span body.span).ValidFor input.file := by
        apply SourceSpan.cover_validFor markerSpanValid bodySpanValid
        exact Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerOrder.2 bodySpanValid.2.1)
      cases finished
      exact ⟨YulStmt.ValidFor.ifThen outerValid conditionValidInput
          bodyStatementsValid,
        weakResult.2.1, weakResult.2.2⟩

/-- Yul `if` parsing preserves the immutable lexer token carrier. -/
theorem yulIfStatement_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulIfStatement statement) := by
  unfold yulIfStatement
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .ifKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess expressionPreserves
  intro condition
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_preservesTokensOnSuccess _

/-- Yul `if` parsing never moves the parser cursor backwards. -/
theorem yulIfStatement_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulIfStatement statement) := by
  unfold yulIfStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .ifKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess expressionMonotone
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul `if` statement starts at its current `if` token. -/
theorem yulIfStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulIfStatement statement) (·.span) := by
  unfold yulIfStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .ifKw) .yulStatement (· == .keyword .ifKw))
  intro marker input value final parsed
  rcases yulBind_ok_components parsed with
    ⟨condition, afterCondition, _conditionResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  rfl

/--
Yul `for` parsing preserves every statement in its initializer, post block,
and body together with the loop condition.  The recursive statement parser
and fixed expression parser remain explicit dependencies.
-/
theorem yulForStatement_validFor (statement : Parser YulStmt)
    (expressionValid : yulExpression.ValidFor YulExpr.ValidFor)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    (yulForStatement statement).ValidFor YulStmt.ValidFor := by
  have weak : (yulForStatement statement).ValidFor (fun _ _ => True) := by
    unfold yulForStatement
    apply Parser.bind_validFor (keyword_validFor .forKw .yulStatement)
    intro marker
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro initializer
    apply Parser.bind_validFor expressionValid
    intro condition
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro post
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulForStatement statement input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulForStatement at stages
      rcases yulBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨initializer, afterInitializer, initializerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨condition, afterCondition, conditionResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨post, afterPost, postResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerValid := keyword_validFor .forKw .yulStatement input inputValid
      rw [markerResult] at markerValid
      have initializerValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterMarker markerValid.2.1
      rw [initializerResult] at initializerValid
      have conditionValid := expressionValid afterInitializer
        initializerValid.2.1
      rw [conditionResult] at conditionValid
      have postValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterCondition conditionValid.2.1
      rw [postResult] at postValid
      have bodyValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterPost postValid.2.1
      rw [bodyResult] at bodyValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have initializerStatementsValid :
          ∀ retained ∈ initializer.body,
            YulStmt.ValidFor input.file retained := by
        intro retained member
        simpa [markerValid.2.2] using initializerValid.1.2 retained member
      have conditionValidInput : YulExpr.ValidFor input.file condition := by
        simpa [initializerValid.2.2, markerValid.2.2] using
          conditionValid.1
      have postStatementsValid :
          ∀ retained ∈ post.body, YulStmt.ValidFor input.file retained := by
        intro retained member
        simpa [conditionValid.2.2, initializerValid.2.2,
          markerValid.2.2] using postValid.1.2 retained member
      have bodySpanValid : body.span.ValidFor input.file := by
        simpa [postValid.2.2, conditionValid.2.2,
          initializerValid.2.2, markerValid.2.2] using bodyValid.1.1
      have bodyStatementsValid :
          ∀ retained ∈ body.body, YulStmt.ValidFor input.file retained := by
        intro retained member
        simpa [postValid.2.2, conditionValid.2.2,
          initializerValid.2.2, markerValid.2.2] using
          bodyValid.1.2 retained member
      have markerShape := acceptToken_ok_state_shape
        (.keyword .forKw) .yulStatement (· == .keyword .forKw) markerResult
      have markerAt :=
        State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      rcases yulBlock_startsAtCurrentTokenOnSuccess statement
          statementPreserves afterPost body afterBody bodyResult with
        ⟨openingToken, openingFound, openingStart⟩
      have openingAtInput :
          input.tokens[afterPost.cursor]? = some openingToken := by
        have openingAt :=
          State.getElem?_eq_some_of_peek?_eq_some openingFound
        have postTokens := yulBlock_preservesTokensOnSuccess statement
          statementPreserves afterCondition post afterPost postResult
        have conditionTokens := expressionPreserves afterInitializer condition
          afterCondition conditionResult
        have initializerTokens := yulBlock_preservesTokensOnSuccess statement
          statementPreserves afterMarker initializer afterInitializer
          initializerResult
        have markerTokens := keyword_preservesTokensOnSuccess .forKw
          .yulStatement input marker afterMarker markerResult
        simpa [postTokens, conditionTokens, initializerTokens, markerTokens]
          using openingAt
      have initializerProgress := yulBlock_cursor_lt_onSuccess statement
        statementPreserves initializerResult
      have conditionCursor := expressionMonotone afterInitializer condition
        afterCondition conditionResult
      have postProgress := yulBlock_cursor_lt_onSuccess statement
        statementPreserves postResult
      have initializerAfterMarker :
          input.cursor + 1 < afterInitializer.cursor := by
        simpa [markerShape.2] using initializerProgress
      have markerBeforeOpening : input.cursor < afterPost.cursor := by
        omega
      have markerBeforeBody : marker.span.endByte ≤ body.span.startByte := by
        rw [← openingStart]
        exact inputValid.token_end_le_token_start_of_getElem?_lt markerAt
          openingAtInput markerBeforeOpening
      have outerValid :
          (SourceSpan.cover marker.span body.span).ValidFor input.file := by
        apply SourceSpan.cover_validFor markerSpanValid bodySpanValid
        exact Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeBody bodySpanValid.2.1)
      cases finished
      exact ⟨YulStmt.ValidFor.forLoop outerValid initializerStatementsValid
          conditionValidInput postStatementsValid bodyStatementsValid,
        weakResult.2.1, weakResult.2.2⟩

/-- Yul `for` parsing preserves the immutable lexer token carrier. -/
theorem yulForStatement_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulForStatement statement) := by
  unfold yulForStatement
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .forKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro initializer
  apply Parser.bind_preservesTokensOnSuccess expressionPreserves
  intro condition
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro post
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_preservesTokensOnSuccess _

/-- Yul `for` parsing never moves the parser cursor backwards. -/
theorem yulForStatement_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulForStatement statement) := by
  unfold yulForStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .forKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess expressionMonotone
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro post
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul `for` statement starts at its current `for` token. -/
theorem yulForStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulForStatement statement) (·.span) := by
  unfold yulForStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .forKw) .yulStatement (· == .keyword .forKw))
  intro marker input value final parsed
  rcases yulBind_ok_components parsed with
    ⟨initializer, afterInitializer, _initializerResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨condition, afterCondition, _conditionResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨post, afterPost, _postResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  rfl

private theorem yulReturnClause_validFor :
    YulControl.returnClause.ValidFor YulReturnClause.ValidFor := by
  have weak : YulControl.returnClause.ValidFor (fun _ _ => True) := by
    unfold YulControl.returnClause
    apply Parser.bind_validFor (symbol_validFor .arrow .yulStatement)
    intro arrow
    apply Parser.bind_validFor yulNames_validFor
    intro names
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : YulControl.returnClause input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weakResult; exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold YulControl.returnClause at stages
      rcases yulBind_ok_components stages with
        ⟨arrow, afterArrow, arrowResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨names, afterNames, namesResult, finished⟩
      have arrowValid := symbol_validFor .arrow .yulStatement input inputValid
      rw [arrowResult] at arrowValid
      have namesValid := yulNames_validFor afterArrow arrowValid.2.1
      rw [namesResult] at namesValid
      have arrowSpanValid : arrow.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using arrowValid.1
      have namesSpanValid : names.span.ValidFor input.file := by
        simpa [arrowValid.2.2] using namesValid.1.1
      have arrowShape := symbol_ok_state_shape .arrow .yulStatement arrowResult
      have arrowAdvanced : input.advance? = some (arrow, afterArrow) := by
        unfold State.advance?
        rw [arrowShape.1, arrowShape.2]
        rfl
      rcases yulNames_startsAtCurrentTokenOnSuccess afterArrow names
          afterNames namesResult with ⟨first, firstFound, firstStart⟩
      have arrowBeforeNames : arrow.span.startByte ≤ names.span.endByte :=
        Nat.le_trans arrowSpanValid.2.1 (Nat.le_trans
          (by
            rw [← firstStart]
            exact inputValid.consumed_end_le_peek_start_after_advance
              arrowAdvanced firstFound)
          namesSpanValid.2.1)
      cases finished
      refine ⟨⟨SourceSpan.cover_validFor arrowSpanValid namesSpanValid
          arrowBeforeNames, arrowSpanValid, ?_⟩,
        weakResult.2.1, weakResult.2.2⟩
      intro name member
      simpa [arrowValid.2.2] using namesValid.1.2 name member
theorem yulReturns_validFor : YulControl.returns.ValidFor
      (Option.ValidFor YulReturnClause.ValidFor) := by
  unfold YulControl.returns
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value yulReturnClause_validFor
    intro clause input inputValid clauseValid
    exact ⟨by simpa only [Option.ValidFor] using clauseValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none
      (Option.ValidFor YulReturnClause.ValidFor) (fun _ => trivial)
private theorem yulReturnClause_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess YulControl.returnClause := by
  unfold YulControl.returnClause
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .arrow .yulStatement)
  intro arrow
  apply Parser.bind_preservesTokensOnSuccess
    yulNames_preservesTokensOnSuccess
  intro names
  exact Parser.pure_preservesTokensOnSuccess _
theorem yulReturns_preservesTokensOnSuccess : Parser.PreservesTokensOnSuccess YulControl.returns := by
  unfold YulControl.returns
  apply Parser.bind_preservesTokensOnSuccess getState_preservesTokensOnSuccess
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_preservesTokensOnSuccess
      yulReturnClause_preservesTokensOnSuccess
    intro clause
    exact Parser.pure_preservesTokensOnSuccess _
  · simp only [present]
    exact Parser.pure_preservesTokensOnSuccess none
private theorem yulReturnClause_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess YulControl.returnClause := by
  unfold YulControl.returnClause
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .arrow .yulStatement)
  intro arrow
  apply Parser.bind_cursorMonotoneOnSuccess
    yulNames_cursorMonotoneOnSuccess
  intro names
  exact Parser.pure_cursorMonotoneOnSuccess _
theorem yulReturns_cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess YulControl.returns := by
  unfold YulControl.returns
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      yulReturnClause_cursorMonotoneOnSuccess
    intro clause
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none
/-- Yul function definitions retain every name, delimiter, and body range. -/
theorem yulFunctionStatement_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    (yulFunctionStatement statement).ValidFor YulStmt.ValidFor := by
  have weak : (yulFunctionStatement statement).ValidFor
      (fun _ _ => True) := by
    unfold yulFunctionStatement
    apply Parser.bind_validFor (keyword_validFor .functionKw .yulStatement)
    intro marker
    apply Parser.bind_validFor yulName_validFor
    intro name
    apply Parser.bind_validFor yulParameters_validFor
    intro parameters
    apply Parser.bind_validFor yulReturns_validFor
    intro returns
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulFunctionStatement statement input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weakResult; exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulFunctionStatement at stages
      rcases yulBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨name, afterName, nameResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨parameters, afterParameters, parametersResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨returns, afterReturns, returnsResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerValid := keyword_validFor .functionKw .yulStatement
        input inputValid
      rw [markerResult] at markerValid
      have nameValid := yulName_validFor afterMarker markerValid.2.1
      rw [nameResult] at nameValid
      have parametersValid := yulParameters_validFor afterName nameValid.2.1
      rw [parametersResult] at parametersValid
      have returnsValid := yulReturns_validFor afterParameters
        parametersValid.2.1
      rw [returnsResult] at returnsValid
      have bodyValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterReturns returnsValid.2.1
      rw [bodyResult] at bodyValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have bodySpanValid : body.span.ValidFor input.file := by
        simpa [returnsValid.2.2, parametersValid.2.2, nameValid.2.2,
          markerValid.2.2] using bodyValid.1.1
      have markerShape := acceptToken_ok_state_shape
        (.keyword .functionKw) .yulStatement
        (· == .keyword .functionKw) markerResult
      have markerAt :=
        State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      rcases yulBlock_startsAtCurrentTokenOnSuccess statement
          statementPreserves afterReturns body afterBody bodyResult with
        ⟨opening, openingFound, openingStart⟩
      have openingAtInput : input.tokens[afterReturns.cursor]? = some opening := by
        have openingAt := State.getElem?_eq_some_of_peek?_eq_some openingFound
        simpa [yulReturns_preservesTokensOnSuccess afterParameters returns
          afterReturns returnsResult,
          yulParameters_preservesTokensOnSuccess afterName parameters
            afterParameters parametersResult,
          yulName_preservesTokensOnSuccess afterMarker name afterName nameResult,
          keyword_preservesTokensOnSuccess .functionKw .yulStatement input
            marker afterMarker markerResult] using openingAt
      have nameCursor := yulName_cursorMonotoneOnSuccess afterMarker name
        afterName nameResult
      have parametersCursor := yulParameters_cursorMonotoneOnSuccess afterName
        parameters afterParameters parametersResult
      have returnsCursor := yulReturns_cursorMonotoneOnSuccess afterParameters
        returns afterReturns returnsResult
      have markerBeforeOpening : input.cursor < afterReturns.cursor := by
        have afterMarkerBefore : input.cursor + 1 ≤ afterReturns.cursor := by
          simpa [markerShape.2] using
            Nat.le_trans nameCursor (Nat.le_trans parametersCursor returnsCursor)
        omega
      have markerBeforeBody : marker.span.endByte ≤ body.span.startByte := by
        rw [← openingStart]
        exact inputValid.token_end_le_token_start_of_getElem?_lt markerAt
          openingAtInput markerBeforeOpening
      have outerValid := SourceSpan.cover_validFor markerSpanValid bodySpanValid
        (Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeBody bodySpanValid.2.1))
      cases finished
      exact ⟨YulStmt.ValidFor.functionDef outerValid
          (by simpa only [Located.ValidFor, markerValid.2.2] using nameValid.1)
          (by simpa only [DelimitedList.ValidFor, Located.ValidFor,
            nameValid.2.2, markerValid.2.2] using parametersValid.1)
          (by simpa [parametersValid.2.2, nameValid.2.2,
            markerValid.2.2] using returnsValid.1)
          (by
            intro retained member
            simpa [returnsValid.2.2, parametersValid.2.2, nameValid.2.2,
            markerValid.2.2] using bodyValid.1.2 retained member),
        weakResult.2.1, weakResult.2.2⟩
/-- Yul function parsing preserves the immutable lexer token carrier. -/
theorem yulFunctionStatement_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulFunctionStatement statement) := by
  unfold yulFunctionStatement
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .functionKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess yulName_preservesTokensOnSuccess
  intro name
  apply Parser.bind_preservesTokensOnSuccess
    yulParameters_preservesTokensOnSuccess
  intro parameters
  apply Parser.bind_preservesTokensOnSuccess yulReturns_preservesTokensOnSuccess
  intro returns
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_preservesTokensOnSuccess _
/-- Yul function parsing never rewinds the parser cursor. -/
theorem yulFunctionStatement_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulFunctionStatement statement) := by
  unfold yulFunctionStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .functionKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulName_cursorMonotoneOnSuccess
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    yulParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess yulReturns_cursorMonotoneOnSuccess
  intro returns
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _
/-- A successful Yul function definition starts at its `function` token. -/
theorem yulFunctionStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulFunctionStatement statement) (·.span) := by
  unfold yulFunctionStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .functionKw) .yulStatement (· == .keyword .functionKw))
  intro marker input value final parsed
  rcases yulBind_ok_components parsed with ⟨name, afterName, _, rest⟩
  rcases yulBind_ok_components rest with ⟨parameters, afterParameters, _, rest⟩
  rcases yulBind_ok_components rest with ⟨returns, afterReturns, _, rest⟩
  rcases yulBind_ok_components rest with ⟨body, afterBody, _, finished⟩
  cases finished
  rfl

/-- One Yul switch arm retains its literal, body, and outer source ranges. -/
theorem yulCase_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    (YulControl.caseArm statement).ValidFor YulCase.ValidFor := by
  have weak : (YulControl.caseArm statement).ValidFor
      (fun _ _ => True) := by
    unfold YulControl.caseArm
    apply Parser.bind_validFor (keyword_validFor .caseKw .yulStatement)
    intro marker
    apply Parser.bind_validFor yulLiteral_validFor
    intro literal
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : YulControl.caseArm statement input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weakResult; exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold YulControl.caseArm at stages
      rcases yulBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨literal, afterLiteral, literalResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerValid := keyword_validFor .caseKw .yulStatement input inputValid
      rw [markerResult] at markerValid
      have literalValid := yulLiteral_validFor afterMarker markerValid.2.1
      rw [literalResult] at literalValid
      have bodyValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterLiteral literalValid.2.1
      rw [bodyResult] at bodyValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have bodySpanValid : body.span.ValidFor input.file := by
        simpa [literalValid.2.2, markerValid.2.2] using bodyValid.1.1
      have markerShape := acceptToken_ok_state_shape
        (.keyword .caseKw) .yulStatement (· == .keyword .caseKw) markerResult
      have markerAt :=
        State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      rcases yulBlock_startsAtCurrentTokenOnSuccess statement
          statementPreserves afterLiteral body afterBody bodyResult with
        ⟨opening, openingFound, openingStart⟩
      have openingAtInput : input.tokens[afterLiteral.cursor]? = some opening := by
        have openingAt := State.getElem?_eq_some_of_peek?_eq_some openingFound
        simpa [yulLiteral_preservesTokensOnSuccess afterMarker literal
          afterLiteral literalResult,
          keyword_preservesTokensOnSuccess .caseKw .yulStatement input marker
            afterMarker markerResult] using openingAt
      have literalCursor := yulLiteral_cursorMonotoneOnSuccess afterMarker
        literal afterLiteral literalResult
      have markerBeforeOpening : input.cursor < afterLiteral.cursor := by
        have afterMarkerBefore : input.cursor + 1 ≤ afterLiteral.cursor := by
          simpa [markerShape.2] using literalCursor
        omega
      have markerBeforeBody : marker.span.endByte ≤ body.span.startByte := by
        rw [← openingStart]
        exact inputValid.token_end_le_token_start_of_getElem?_lt markerAt
          openingAtInput markerBeforeOpening
      have outerValid := SourceSpan.cover_validFor markerSpanValid bodySpanValid
        (Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeBody bodySpanValid.2.1))
      cases finished
      exact ⟨YulCase.ValidFor.arm outerValid
          (by simpa [Located.ValidFor, markerValid.2.2] using literalValid.1)
          (by
            intro retained member
            simpa [literalValid.2.2, markerValid.2.2] using
              bodyValid.1.2 retained member),
        weakResult.2.1, weakResult.2.2⟩

/-- Yul switch-arm parsing preserves the immutable lexer token carrier. -/
theorem yulCase_preservesTokensOnSuccess (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (YulControl.caseArm statement) := by
  unfold YulControl.caseArm
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .caseKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess yulLiteral_preservesTokensOnSuccess
  intro literal
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_preservesTokensOnSuccess _

/-- Yul switch-arm parsing never rewinds the parser cursor. -/
theorem yulCase_cursorMonotoneOnSuccess (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (YulControl.caseArm statement) := by
  unfold YulControl.caseArm
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .caseKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulLiteral_cursorMonotoneOnSuccess
  intro literal
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Repeated Yul switch arms retain the nested parser's token carrier. -/
theorem yulCases_preservesTokensOnSuccess (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    ∀ fuel casesRev, Parser.PreservesTokensOnSuccess
      (YulControl.caseList statement fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input value next result
      unfold YulControl.caseList at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro casesRev input value next result
      unfold YulControl.caseList at result
      split at result
      · cases armResult : YulControl.caseArm statement input with
        | ok arm afterArm =>
            simp only [armResult] at result
            split at result
            · exact (inductionHypothesis (arm :: casesRev) afterArm value next
                result).trans
                (yulCase_preservesTokensOnSuccess statement statementPreserves
                  input arm afterArm armResult)
            · contradiction
        | reject failure rejected => simp [armResult] at result
        | invariant error => simp [armResult] at result
      · cases result
        rfl

/-- Repeated Yul switch arms never rewind the parser cursor. -/
theorem yulCases_cursorMonotoneOnSuccess (statement : Parser YulStmt) :
    ∀ fuel casesRev, Parser.CursorMonotoneOnSuccess
      (YulControl.caseList statement fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input value next result
      unfold YulControl.caseList at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro casesRev input value next result
      unfold YulControl.caseList at result
      split at result
      · cases armResult : YulControl.caseArm statement input with
        | ok arm afterArm =>
            simp only [armResult] at result
            split at result
            · exact Nat.le_trans (Nat.le_of_lt (by assumption))
                (inductionHypothesis (arm :: casesRev) afterArm value next
                  result)
            · contradiction
        | reject failure rejected => simp [armResult] at result
        | invariant error => simp [armResult] at result
      · cases result
        exact Nat.le_refl _

private theorem yulCases_validFor_aux (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    ∀ fuel casesRev input,
      input.ValidFor →
      List.ValidFor YulCase.ValidFor input.file casesRev →
      (YulControl.caseList statement fuel casesRev input).ValidFor input
        (List.ValidFor YulCase.ValidFor) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro casesRev input inputValid casesValid
      unfold YulControl.caseList
      split
      · cases armResult : YulControl.caseArm statement input with
        | invariant error => trivial
        | reject failure rejected =>
            have valid := yulCase_validFor statement statementValid
              statementPreserves input inputValid
            rw [armResult] at valid
            exact valid
        | ok arm afterArm =>
            have armValid := yulCase_validFor statement statementValid
              statementPreserves input inputValid
            rw [armResult] at armValid
            simp only
            split
            · apply (inductionHypothesis (arm :: casesRev) afterArm
                  armValid.2.1 ?_).of_file_eq armValid.2.2
              intro retained member
              rcases List.mem_cons.mp member with rfl | member
              · simpa [armValid.2.2] using armValid.1
              · simpa [armValid.2.2] using casesValid retained member
            · trivial
      · exact ⟨by
            intro arm member
            exact casesValid arm (by simpa using member),
          inputValid, rfl⟩

/-- Repeated Yul switch arms preserve every recursively retained range. -/
theorem yulCases_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    (fuel : Nat) :
    Parser.ValidFor (YulControl.caseList statement fuel [])
      (List.ValidFor YulCase.ValidFor) := by
  intro input inputValid
  exact yulCases_validFor_aux statement statementValid statementPreserves
    fuel [] input inputValid (by simp [List.ValidFor])

private theorem yulCase_starts_aux (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (YulControl.caseArm statement) (·.span) := by
  unfold YulControl.caseArm
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .caseKw) .yulStatement (· == .keyword .caseKw))
  intro marker input value final parsed
  rcases yulBind_ok_components parsed with ⟨literal, afterLiteral, _, rest⟩
  rcases yulBind_ok_components rest with ⟨body, afterBody, _, finished⟩
  cases finished
  rfl

/-- Every accumulated switch arm begins after a supplied consumed token. -/
theorem yulCases_ordered_after (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    ∀ fuel casesRev input output next anchorIndex anchor,
      input.ValidFor →
      input.tokens[anchorIndex]? = some anchor →
      anchorIndex < input.cursor →
      (∀ arm ∈ casesRev,
        anchor.span.endByte ≤ arm.span.startByte) →
      YulControl.caseList statement fuel casesRev input = .ok output next →
      ∀ arm ∈ output, anchor.span.endByte ≤ arm.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro casesRev input output next anchorIndex anchor inputValid
        anchorFound anchorBeforeCursor casesOrdered result
      unfold YulControl.caseList at result
      split at result
      · cases armResult : YulControl.caseArm statement input with
        | ok arm afterArm =>
            simp only [armResult] at result
            have armValid := yulCase_validFor statement statementValid
              statementPreserves input inputValid
            rw [armResult] at armValid
            split at result
            · rcases yulCase_starts_aux statement input arm
                  afterArm armResult with ⟨marker, markerFound, armStart⟩
              apply inductionHypothesis (arm :: casesRev) afterArm output next
                anchorIndex anchor armValid.2.1
              · simpa [yulCase_preservesTokensOnSuccess statement
                    statementPreserves input arm afterArm armResult] using
                  anchorFound
              · omega
              · intro retained member
                rcases List.mem_cons.mp member with rfl | member
                · rw [← armStart]
                  exact inputValid.token_end_le_token_start_of_getElem?_lt
                    anchorFound
                    (State.getElem?_eq_some_of_peek?_eq_some markerFound)
                    anchorBeforeCursor
                · exact casesOrdered retained member
              · exact result
            · contradiction
        | reject failure rejected => simp [armResult] at result
        | invariant error => simp [armResult] at result
      · intro arm member
        cases result
        exact casesOrdered arm (by simpa using member)

/-- A present default block begins after every earlier consumed token. -/
theorem optionalYulDefault_some_ordered_after
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {body : YulParsedBlock}
    {anchorIndex : Nat} {anchor : Token}
    (inputValid : input.ValidFor)
    (anchorFound : input.tokens[anchorIndex]? = some anchor)
    (anchorBeforeCursor : anchorIndex < input.cursor)
    (result : YulControl.optionalDefault statement input = .ok (some body) next) :
    anchor.span.endByte ≤ body.span.startByte := by
  unfold YulControl.optionalDefault getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    rcases yulBind_ok_components result with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases yulBind_ok_components rest with
      ⟨parsedBody, afterBody, bodyResult, finished⟩
    have bodyStarts := yulBlock_startsAtCurrentTokenOnSuccess statement
      statementPreserves afterMarker parsedBody afterBody bodyResult
    cases finished
    rcases bodyStarts with
      ⟨opening, openingFound, openingStart⟩
    rw [← openingStart]
    apply inputValid.token_end_le_token_start_of_getElem?_lt anchorFound
    · simpa [keyword_preservesTokensOnSuccess .defaultKw .yulStatement
          input marker afterMarker markerResult] using
        State.getElem?_eq_some_of_peek?_eq_some openingFound
    · have shape := acceptToken_ok_state_shape
          (.keyword .defaultKw) .yulStatement
          (· == .keyword .defaultKw) markerResult
      simpa [shape.2] using
        Nat.lt_trans anchorBeforeCursor (Nat.lt_succ_self input.cursor)
  · simp only [present, Bool.false_eq_true, if_false] at result
    cases result

/-- A successful Yul switch arm starts at its current `case` token. -/
theorem yulCase_startsAtCurrentTokenOnSuccess (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (YulControl.caseArm statement) (·.span) :=
  yulCase_starts_aux statement

/-- A successful Yul switch arm consumes its marker, literal, and block. -/
theorem yulCase_cursor_lt_onSuccess (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {arm : YulCase}
    (result : YulControl.caseArm statement input = .ok arm next) :
    input.cursor < next.cursor := by
  have stages := result
  unfold YulControl.caseArm at stages
  rcases yulBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨literal, afterLiteral, literalResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  have markerShape := acceptToken_ok_state_shape
    (.keyword .caseKw) .yulStatement (· == .keyword .caseKw) markerResult
  have literalCursor := yulLiteral_cursorMonotoneOnSuccess afterMarker literal
    afterLiteral literalResult
  have bodyProgress := yulBlock_cursor_lt_onSuccess statement
    statementPreserves bodyResult
  cases finished
  simp [markerShape.2] at literalCursor
  omega

/-- Optional Yul defaults preserve their block and statement provenance. -/
theorem optionalYulDefault_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    (YulControl.optionalDefault statement).ValidFor
      (Option.ValidFor (YulParsedBlock.ValidFor YulStmt.ValidFor)) := by
  unfold YulControl.optionalDefault
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_validFor (keyword_validFor .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_validFor_of_value
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body input inputValid bodyValid
    exact ⟨by simpa only [Option.ValidFor] using bodyValid, inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional Yul defaults preserve the immutable lexer token carrier. -/
theorem optionalYulDefault_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess
      (YulControl.optionalDefault statement) := by
  unfold YulControl.optionalDefault
  apply Parser.bind_preservesTokensOnSuccess getState_preservesTokensOnSuccess
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokensOnSuccess
      (keyword_preservesTokensOnSuccess .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_preservesTokensOnSuccess
      (yulBlock_preservesTokensOnSuccess statement statementPreserves)
    intro body
    exact Parser.pure_preservesTokensOnSuccess _
  · simp only [present]
    exact Parser.pure_preservesTokensOnSuccess none

/-- Optional Yul defaults never rewind the parser cursor. -/
theorem optionalYulDefault_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess
      (YulControl.optionalDefault statement) := by
  unfold YulControl.optionalDefault
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
    intro body
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

private theorem yulControl_getState_preservesTokenWindow :
    Parser.PreservesTokenWindow getState := by
  intro input
  exact ⟨rfl, rfl⟩

/-- Yul `if` parsing preserves every ordinary token window. -/
theorem yulIfStatement_preservesTokenWindow (statement : Parser YulStmt)
    (expressionShape : Parser.PreservesTokenWindow yulExpression)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (yulIfStatement statement) := by
  unfold yulIfStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .ifKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow expressionShape
  intro condition
  apply Parser.bind_preservesTokenWindow
    (yulBlock_preservesTokenWindow statement statementShape)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Yul `for` parsing preserves every ordinary token window. -/
theorem yulForStatement_preservesTokenWindow (statement : Parser YulStmt)
    (expressionShape : Parser.PreservesTokenWindow yulExpression)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (yulForStatement statement) := by
  unfold yulForStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .forKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (yulBlock_preservesTokenWindow statement statementShape)
  intro initializer
  apply Parser.bind_preservesTokenWindow expressionShape
  intro condition
  apply Parser.bind_preservesTokenWindow
    (yulBlock_preservesTokenWindow statement statementShape)
  intro post
  apply Parser.bind_preservesTokenWindow
    (yulBlock_preservesTokenWindow statement statementShape)
  intro body
  exact Parser.pure_preservesTokenWindow _

private theorem yulReturnClause_preservesTokenWindow :
    Parser.PreservesTokenWindow YulControl.returnClause := by
  unfold YulControl.returnClause
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .arrow .yulStatement)
  intro arrow
  apply Parser.bind_preservesTokenWindow yulNames_preservesTokenWindow
  intro names
  exact Parser.pure_preservesTokenWindow _

/-- Optional Yul return clauses preserve every ordinary token window. -/
theorem yulReturns_preservesTokenWindow :
    Parser.PreservesTokenWindow YulControl.returns := by
  unfold YulControl.returns
  apply Parser.bind_preservesTokenWindow yulControl_getState_preservesTokenWindow
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow yulReturnClause_preservesTokenWindow
    intro clause
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

/-- Yul function parsing preserves every ordinary token window. -/
theorem yulFunctionStatement_preservesTokenWindow
    (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (yulFunctionStatement statement) := by
  unfold yulFunctionStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .functionKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow yulName_preservesTokenWindow
  intro name
  apply Parser.bind_preservesTokenWindow yulParameters_preservesTokenWindow
  intro parameters
  apply Parser.bind_preservesTokenWindow yulReturns_preservesTokenWindow
  intro returns
  apply Parser.bind_preservesTokenWindow
    (yulBlock_preservesTokenWindow statement statementShape)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- One Yul switch arm preserves every ordinary token window. -/
theorem yulCase_preservesTokenWindow (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (YulControl.caseArm statement) := by
  unfold YulControl.caseArm
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .caseKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow yulLiteral_preservesTokenWindow
  intro literal
  apply Parser.bind_preservesTokenWindow
    (yulBlock_preservesTokenWindow statement statementShape)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Repeated Yul switch arms preserve every ordinary token window. -/
theorem yulCases_preservesTokenWindow (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement) :
    ∀ fuel casesRev, Parser.PreservesTokenWindow
      (YulControl.caseList statement fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero => intro casesRev input; trivial
  | succ fuel inductionHypothesis =>
      intro casesRev input
      unfold YulControl.caseList
      split
      · have armShape := yulCase_preservesTokenWindow statement
            statementShape input
        cases armResult : YulControl.caseArm statement input with
        | ok arm next =>
            rw [armResult] at armShape
            change (if next.cursor > input.cursor then
              YulControl.caseList statement fuel (arm :: casesRev) next
              else .invariant (.noProgress .yul next.currentSpan)
              ).PreservesTokenWindow input
            split
            · exact (inductionHypothesis (arm :: casesRev) next).trans
                armShape
            · trivial
        | reject failure rejected =>
            rw [armResult] at armShape
            exact armShape
        | invariant error => trivial
      · exact ⟨rfl, rfl⟩

/-- Optional Yul default arms preserve every ordinary token window. -/
theorem optionalYulDefault_preservesTokenWindow
    (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (YulControl.optionalDefault statement) := by
  unfold YulControl.optionalDefault
  apply Parser.bind_preservesTokenWindow yulControl_getState_preservesTokenWindow
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (yulBlock_preservesTokenWindow statement statementShape)
    intro body
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none


end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulFunctionDiagnosticReflectionProperties
/-! Diagnostic reflection for inline-Yul function signatures and bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The allow-empty Yul parameter list reflects through every strict name. -/
theorem yulParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulParameters :=
  delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
    yulName .yulStatement .yul yulName_reflectsDiagnosticFreeOnSuccess

namespace YulControl

/-- A return clause reflects through its arrow and nonempty name sequence. -/
theorem returnClause_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess returnClause := by
  unfold returnClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .arrow .yulStatement)
  intro arrow
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulNames_reflectsDiagnosticFreeOnSuccess
  intro names
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Optional returns reflect through the preferred arrow branch. -/
theorem returns_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess returns := by
  unfold returns
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      returnClause_reflectsDiagnosticFreeOnSuccess
    intro clause
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end YulControl

/-- Complete function parsing reflects through signature and recursive body. -/
theorem yulFunctionStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulFunctionStatement statement) := by
  unfold yulFunctionStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .functionKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulName_reflectsDiagnosticFreeOnSuccess
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    YulControl.returns_reflectsDiagnosticFreeOnSuccess
  intro returns
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulFunctionSoundnessProperties
/-! Exact diagnostic-free soundness for inline-Yul functions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
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

/-- Every diagnostic-free Yul parameter-list success follows the exact
allow-empty, trailing-comma name grammar. -/
theorem yulParameters_success_sound {input next : State}
    {parameters : DelimitedList YulIdentifier}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulParameters input = .ok parameters next) :
    DeclarativeGrammar.YulParametersParses input.declarativeRemainder
      parameters next.declarativeRemainder := by
  unfold DeclarativeGrammar.YulParametersParses
  exact delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
    .leftParen .rightParen yulName DeclarativeGrammar.YulNameParses
    .yulStatement .yul
    (fun outputFree parsed =>
      yulName_success_sound_of_diagnosticFree outputFree parsed)
    yulName_reflectsDiagnosticFreeOnSuccess yulName_preservesTokenWindow
    diagnosticFree result

namespace YulControl

/-- Every diagnostic-free return clause retains its arrow, forward names,
covering span, and exact remainder. -/
theorem returnClause_success_sound {input next : State}
    {clause : YulReturnClause} (diagnosticFree : next.diagnosticsRev = [])
    (result : returnClause input = .ok clause next) :
    DeclarativeGrammar.YulReturnClauseParses input.declarativeRemainder clause
      next.declarativeRemainder := by
  unfold returnClause at result
  rcases bind_ok_components result with
    ⟨arrow, afterArrow, arrowResult, namesStage⟩
  rcases bind_ok_components namesStage with
    ⟨names, afterNames, namesResult, finished⟩
  cases finished
  exact .parsed arrow.span names.span
    (symbol_success_exactTokenParses .arrow .yulStatement arrowResult)
    (yulNames_success_sound diagnosticFree namesResult)

/-- Every optional-return success retains the preferred arrow branch or exact
arrow absence. -/
theorem returns_success_sound {input next : State}
    {returnsValue : Option YulReturnClause}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : returns input = .ok returnsValue next) :
    DeclarativeGrammar.YulReturnsParses input.declarativeRemainder returnsValue
      next.declarativeRemainder := by
  unfold returns getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨clause, afterClause, clauseResult, finished⟩
    cases finished
    exact .present (returnClause_success_sound diagnosticFree clauseResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .arrow absent)

end YulControl

/-- Every diagnostic-free Yul function success follows its exact signature,
optional returns, recursive body, cover span, AST, and remainder. -/
theorem yulFunctionStatement_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulFunctionStatement statement input = .ok value next) :
    DeclarativeGrammar.YulFunctionStatementParses statementParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulFunctionStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, parametersStage⟩
  rcases bind_ok_components parametersStage with
    ⟨parameters, afterParameters, parametersResult, returnsStage⟩
  rcases bind_ok_components returnsStage with
    ⟨returnsValue, afterReturns, returnsResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterReturnsFree := yulBlock_reflectsDiagnosticFreeOnSuccess statement
    statementReflects afterReturns body next bodyResult diagnosticFree
  have afterParametersFree := YulControl.returns_reflectsDiagnosticFreeOnSuccess
    afterParameters returnsValue afterReturns returnsResult afterReturnsFree
  have afterNameFree := yulParameters_reflectsDiagnosticFreeOnSuccess afterName
    parameters afterParameters parametersResult afterParametersFree
  exact .parsed marker.span body.span
    (keyword_success_exactTokenParses .functionKw .yulStatement markerResult)
    (yulName_success_sound_of_diagnosticFree afterNameFree nameResult)
    (yulParameters_success_sound afterParametersFree parametersResult)
    (YulControl.returns_success_sound afterReturnsFree returnsResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound diagnosticFree bodyResult)

end Solcore.Syntax.Parser
end
