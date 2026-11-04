import Solcore.Syntax.Internal.PatternOutcomes
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.PatternProofs
import Solcore.Syntax.Grammar.Patterns
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.ExpressionProofs
import Solcore.Syntax.Parser.Internal.DelimitedSoundness

/-!
Soundness of the parsers of basic and constructor patterns: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternComptimeOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for Core compile-time patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · rcases contextual_eq_ok_of_isContextual_eq_true value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

/-- Every executable compile-time-pattern success follows the supplied
ordinary expression relation. -/
theorem comptimePattern_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {pattern : Pattern}
    (result : comptimePattern expression input = .ok pattern output) :
    DeclarativeGrammar.ComptimePatternOrdinaryParses expressionOrdinary
      input.declarativeRemainder pattern output.declarativeRemainder := by
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | reject failure rejected => simp [expressionResult] at result
      | ok value afterExpression =>
          simp only [expressionResult] at result
          cases result
          exact .parsed marker.span
            (contextual_success_exactTokenParses .comptime .pattern
              markerResult)
            (expressionSuccessSound expressionResult)

/-- Every executable compile-time-pattern rejection is the missing marker or
the exact supplied-expression rejection after that marker. -/
theorem comptimePattern_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : comptimePattern expression input = .reject failure rejected) :
    DeclarativeGrammar.ComptimePatternRejects expressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject markerFailure afterMarker =>
      simp only [markerResult] at result
      have rejectedEq : afterMarker = rejected := by injection result
      subst rejected
      have stateEq := contextual_reject_state_eq .comptime .pattern
        markerResult
      rw [stateEq]
      exact .markerMissing
        (contextual_reject_tokenKindAbsentAt .comptime .pattern markerResult)
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | ok value afterExpression => simp [expressionResult] at result
      | reject expressionFailure afterExpression =>
          simp only [expressionResult] at result
          have rejectedEq : afterExpression = rejected := by injection result
          subst rejected
          exact .expressionRejected marker.span
            (contextual_success_exactTokenParses .comptime .pattern
              markerResult)
            (expressionRejectSound expressionResult)

/-- Package both executable compile-time-pattern outcomes. -/
theorem comptimePattern_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {pattern : Pattern},
      comptimePattern expression input = .ok pattern output →
        DeclarativeGrammar.ComptimePatternOrdinaryParses expressionOrdinary
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      comptimePattern expression input = .reject failure rejected →
        DeclarativeGrammar.ComptimePatternRejects expressionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨comptimePattern_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    comptimePattern_reject_ordinary_sound expression expressionRejects
      expressionRejectSound⟩

/-- Re-export deterministic compile-time-pattern outcomes. -/
theorem comptimePattern_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ComptimePatternOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ComptimePatternRejects expressionRejects) :=
  DeclarativeGrammar.comptimePatternDeterministicOutcomeSpec
    expressionOutcomes

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternComptimeSoundnessProperties
/-!
Diagnostic reflection and exact parser-independent soundness for the Core
compile-time pattern.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Compile-time-pattern success reflects diagnostic freedom through the
supplied expression parser. -/
theorem comptimePattern_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (comptimePattern expression) := by
  intro input pattern next result diagnosticFree
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | reject failure rejected => simp [expressionResult] at result
      | ok value afterExpression =>
          simp only [expressionResult] at result
          cases result
          have afterMarkerFree := expressionReflects afterMarker value
            next expressionResult diagnosticFree
          exact contextual_reflectsDiagnosticFreeOnSuccess .comptime .pattern
            input marker afterMarker markerResult afterMarkerFree

/-- Every diagnostic-free compile-time-pattern success consumes the exact
contextual marker and follows the supplied expression grammar. -/
theorem comptimePattern_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {pattern : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : comptimePattern expression input = .ok pattern next) :
    DeclarativeGrammar.ComptimePatternParses expressionParses
      input.declarativeRemainder pattern next.declarativeRemainder := by
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | reject failure rejected => simp [expressionResult] at result
      | ok value afterExpression =>
          simp only [expressionResult] at result
          cases result
          exact .parsed marker.span
            (contextual_success_exactTokenParses .comptime .pattern
              markerResult)
            (expressionSound diagnosticFree expressionResult)

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternBasicDiagnosticReflectionProperties
/-!
Diagnostic reflection for basic Core pattern leaves and parenthesized
patterns.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Wildcard-pattern success never removes an earlier diagnostic. -/
theorem wildcardPattern_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess wildcardPattern := by
  unfold wildcardPattern
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .underscore .pattern)
  intro marker
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Literal-pattern success never removes an earlier diagnostic. -/
theorem literalPattern_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess literalPattern := by
  unfold literalPattern
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    coreLiteral_reflectsDiagnosticFreeOnSuccess
  intro literal
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Boolean-binder success never removes an earlier diagnostic. -/
theorem booleanBinderPattern_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess booleanBinderPattern := by
  unfold booleanBinderPattern
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    booleanIdentifier_reflectsDiagnosticFreeOnSuccess
  intro name
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Closing a pattern tuple never removes an earlier diagnostic. -/
theorem closePatternTuple_reflectsDiagnosticFreeOnSuccess
    (opening : Token) (elementsRev : List Pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closePatternTuple opening elementsRev) := by
  unfold closePatternTuple
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .pattern)
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  | cons head tail =>
      cases tail with
      | nil => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
      | cons second rest => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Tuple-tail success reflects through every nested pattern. -/
theorem patternTupleTail_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (opening : Token) : ∀ fuel elementsRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (patternTupleTail nested opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input value next result diagnosticFree
      simp [patternTupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input value next result diagnosticFree
      unfold patternTupleTail at result
      cases commaResult : symbol .comma .pattern input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          split at result
          · have afterCommaFree :=
              closePatternTuple_reflectsDiagnosticFreeOnSuccess opening
                elementsRev afterComma value next result diagnosticFree
            exact symbol_reflectsDiagnosticFreeOnSuccess .comma .pattern
              input comma afterComma commaResult afterCommaFree
          · cases elementResult : nested afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok element afterElement =>
                simp only [elementResult] at result
                split at result
                · contradiction
                · split at result
                  · have afterElementFree := inductionHypothesis
                        (element :: elementsRev) afterElement value next result
                          diagnosticFree
                    have afterCommaFree := nestedReflects afterComma element
                      afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .pattern input comma afterComma commaResult
                        afterCommaFree
                  · have afterElementFree :=
                        closePatternTuple_reflectsDiagnosticFreeOnSuccess
                          opening (element :: elementsRev) afterElement value
                            next result diagnosticFree
                    have afterCommaFree := nestedReflects afterComma element
                      afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .pattern input comma afterComma commaResult
                        afterCommaFree

/-- Parenthesized-pattern success reflects through its nested parser. -/
theorem parenthesizedPattern_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parenthesizedPattern nested) := by
  intro input value next result diagnosticFree
  unfold parenthesizedPattern at result
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      split at result
      · have afterOpeningFree :=
          closePatternTuple_reflectsDiagnosticFreeOnSuccess opening []
            afterOpening value next result diagnosticFree
        exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen .pattern
          input opening afterOpening openingResult afterOpeningFree
      · cases elementResult : nested afterOpening with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first afterFirst =>
            simp only [elementResult] at result
            split at result
            · contradiction
            · split at result
              · have afterFirstFree :=
                    patternTupleTail_reflectsDiagnosticFreeOnSuccess nested
                      nestedReflects opening (afterFirst.remainingCount + 1)
                        [first] afterFirst value next result diagnosticFree
                have afterOpeningFree := nestedReflects afterOpening first
                  afterFirst elementResult afterFirstFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen
                  .pattern input opening afterOpening openingResult
                    afterOpeningFree
              · have afterFirstFree :=
                    closePatternTuple_reflectsDiagnosticFreeOnSuccess opening
                      [first] afterFirst value next result diagnosticFree
                have afterOpeningFree := nestedReflects afterOpening first
                  afterFirst elementResult afterFirstFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen
                  .pattern input opening afterOpening openingResult
                    afterOpeningFree

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternBasicSoundnessProperties
/-!
Exact diagnostic-free soundness for basic Core pattern leaves and
parenthesized patterns.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem bind_success_components {alpha beta : Type}
    {first : Parser alpha} {nextParser : alpha → Parser beta}
    {input final : State} {value : beta}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every successful wildcard pattern consumes its exact marker token. -/
theorem wildcardPattern_success_sound {input next : State}
    {pattern : Pattern}
    (result : wildcardPattern input = .ok pattern next) :
    DeclarativeGrammar.WildcardPatternParses input.declarativeRemainder
      pattern next.declarativeRemainder := by
  unfold wildcardPattern at result
  rcases bind_success_components result with
    ⟨marker, afterMarker, markerResult, finished⟩
  cases finished
  exact .parsed marker.span
    (symbol_success_exactTokenParses .underscore .pattern markerResult)

/-- Every successful literal pattern follows the exact literal grammar. -/
theorem literalPattern_success_sound {input next : State}
    {pattern : Pattern}
    (result : literalPattern input = .ok pattern next) :
    DeclarativeGrammar.LiteralPatternParses input.declarativeRemainder
      pattern next.declarativeRemainder := by
  unfold literalPattern at result
  rcases bind_success_components result with
    ⟨literal, afterLiteral, literalResult, finished⟩
  cases finished
  exact .parsed (coreLiteral_success_sound literalResult)

/-- Every successful Boolean binder follows the exact builtin grammar. -/
theorem booleanBinderPattern_success_sound {input next : State}
    {pattern : Pattern}
    (result : booleanBinderPattern input = .ok pattern next) :
    DeclarativeGrammar.BooleanBinderPatternParses input.declarativeRemainder
      pattern next.declarativeRemainder := by
  unfold booleanBinderPattern at result
  rcases bind_success_components result with
    ⟨name, afterName, nameResult, finished⟩
  cases finished
  exact .parsed (booleanIdentifier_success_sound nameResult)

private theorem closeParenthesizedPattern_eq_tuple_of_length_ne_one
    (openingSpan closingSpan : SourceSpan) (elements : List Pattern)
    (lengthNe : elements.length ≠ 1) :
    DeclarativeGrammar.closeParenthesizedPattern openingSpan closingSpan
      elements = {
        span := SourceSpan.cover openingSpan closingSpan
        value := .tuple {
          span := SourceSpan.cover openingSpan closingSpan
          elements
        }
      } := by
  unfold DeclarativeGrammar.closeParenthesizedPattern
  cases elements with
  | nil => rfl
  | cons head tail =>
      cases tail with
      | nil => simp at lengthNe
      | cons second rest => rfl

theorem closePatternTuple_success_sound (opening : Token)
    (elementsRev : List Pattern) {input next : State} {value : Pattern}
    (result : closePatternTuple opening elementsRev input = .ok value next) :
    ∃ closingSpan,
      value = DeclarativeGrammar.closeParenthesizedPattern opening.span
        closingSpan elementsRev.reverse ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
        input.declarativeRemainder closingSpan next.declarativeRemainder := by
  unfold closePatternTuple at result
  rcases bind_success_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have closingParsed := symbol_success_exactTokenParses .rightParen
    .pattern closingResult
  cases elementsRev with
  | nil =>
      cases finished
      exact ⟨closing.span, by
        simp [DeclarativeGrammar.closeParenthesizedPattern], closingParsed⟩
  | cons head tail =>
      cases tail with
      | nil =>
          cases finished
          exact ⟨closing.span, by
            simp [DeclarativeGrammar.closeParenthesizedPattern],
              closingParsed⟩
      | cons second rest =>
          cases finished
          refine ⟨closing.span, ?_, closingParsed⟩
          rw [closeParenthesizedPattern_eq_tuple_of_length_ne_one]
          simp

theorem patternTupleTail_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input value next,
      next.diagnosticsRev = [] →
      patternTupleTail nested opening fuel elementsRev input =
        .ok value next →
      ∃ suffix closingSpan,
        value = DeclarativeGrammar.closeParenthesizedPattern opening.span
          closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedPatternTupleTailParses nestedParses
          input.declarativeRemainder suffix closingSpan
            next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input value next diagnosticFree result
      simp [patternTupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input value next diagnosticFree result
      unfold patternTupleTail at result
      cases commaResult : symbol .comma .pattern input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .pattern commaResult
          split at result
          · rcases closePatternTuple_success_sound opening elementsRev result
              with ⟨closingSpan, valueEq, closingParsed⟩
            exact ⟨[], closingSpan, by simpa using valueEq,
              .trailing comma.span closingSpan commaParsed closingParsed⟩
          · have closingAbsentBool :
                isSymbol afterComma .rightParen = false := by simp_all
            have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
              .rightParen closingAbsentBool
            cases elementResult : nested afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok element afterElement =>
                simp only [elementResult] at result
                split at result
                next noProgress => contradiction
                next progressBranch =>
                  have elementProgress :
                      afterComma.cursor < afterElement.cursor :=
                    Nat.lt_of_not_ge progressBranch
                  split at result
                  next commaPresent =>
                    rcases inductionHypothesis (element :: elementsRev)
                        afterElement value next diagnosticFree result with
                      ⟨suffix, closingSpan, valueEq, tailGrammar⟩
                    have afterElementFree :=
                      patternTupleTail_reflectsDiagnosticFreeOnSuccess nested
                        nestedReflects opening fuel (element :: elementsRev)
                          afterElement value next result diagnosticFree
                    have elementGrammar := nestedSound afterElementFree
                      elementResult
                    refine ⟨element :: suffix, closingSpan, ?_,
                      .next comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) tailGrammar⟩
                    simpa [List.reverse_cons, List.append_assoc] using valueEq
                  next commaAbsentBranch =>
                    rcases closePatternTuple_success_sound opening
                        (element :: elementsRev) result with
                      ⟨closingSpan, valueEq, closingParsed⟩
                    have afterElementFree :=
                      closePatternTuple_reflectsDiagnosticFreeOnSuccess
                        opening (element :: elementsRev) afterElement value
                          next result diagnosticFree
                    have elementGrammar := nestedSound afterElementFree
                      elementResult
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                      .comma (input := afterElement) (by simp_all)
                    refine ⟨[element], closingSpan, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) commaAbsent closingParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using valueEq

/-- Every diagnostic-free parenthesized success follows its exact grammar. -/
theorem parenthesizedPattern_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : parenthesizedPattern nested input = .ok value next) :
    DeclarativeGrammar.ParenthesizedPatternParses nestedParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold parenthesizedPattern at result
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .pattern openingResult
      split at result
      · rcases closePatternTuple_success_sound opening [] result with
          ⟨closingSpan, valueEq, closingParsed⟩
        subst value
        exact .empty opening.span closingSpan openingParsed closingParsed
      · have closingAbsentBool :
            isSymbol afterOpening .rightParen = false := by simp_all
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
          .rightParen closingAbsentBool
        cases elementResult : nested afterOpening with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first afterFirst =>
            simp only [elementResult] at result
            split at result
            next noProgress => contradiction
            next progressBranch =>
              have firstProgress : afterOpening.cursor < afterFirst.cursor :=
                Nat.lt_of_not_ge progressBranch
              split at result
              next commaPresent =>
                rcases patternTupleTail_success_sound nested
                    nestedParses nestedReflects nestedSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst value
                        next diagnosticFree result with
                  ⟨rest, closingSpan, valueEq, tailGrammar⟩
                have afterFirstFree :=
                  patternTupleTail_reflectsDiagnosticFreeOnSuccess nested
                    nestedReflects opening (afterFirst.remainingCount + 1)
                      [first] afterFirst value next result diagnosticFree
                have firstGrammar := nestedSound afterFirstFree elementResult
                subst value
                simpa using
                  (DeclarativeGrammar.ParenthesizedPatternParses.tuple
                    opening.span closingSpan openingParsed closingAbsent
                      firstGrammar (by
                        simpa [State.declarativeRemainder] using
                          firstProgress) tailGrammar)
              next commaAbsentBranch =>
                rcases closePatternTuple_success_sound opening [first]
                    result with ⟨closingSpan, valueEq, closingParsed⟩
                have afterFirstFree :=
                  closePatternTuple_reflectsDiagnosticFreeOnSuccess opening
                    [first] afterFirst value next result diagnosticFree
                have firstGrammar := nestedSound afterFirstFree elementResult
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                  .comma (input := afterFirst) (by simp_all)
                subst value
                exact .group opening.span closingSpan openingParsed
                  closingAbsent firstGrammar (by
                    simpa [State.declarativeRemainder] using firstProgress)
                      commaAbsent closingParsed

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternCoreOutcomeLeafSoundnessProperties
/-! Exact executable ordinary outcomes of the three `patternCore` leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem rejectAt_rejected_state_eq {alpha : Type}
    {input rejected : State} {failure : Failure}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    (result : (rejectAt input expected context : Reply alpha) =
      .reject failure rejected) : rejected = input := by
  unfold rejectAt at result
  cases result
  rfl

private theorem bind_pure_reject_first {alpha beta : Type}
    {first : Parser alpha} {finish : alpha → beta}
    {input rejected : State} {failure : Failure}
    (result : (first >>= fun value => pure (finish value)) input =
      .reject failure rejected) :
    first input = .reject failure rejected := by
  change (match first input with
    | .ok value afterFirst => (pure (finish value) : Parser beta) afterFirst
    | .reject firstFailure firstRejected =>
        .reject firstFailure firstRejected
    | .invariant error => .invariant error) = .reject failure rejected at result
  cases firstResult : first input with
  | ok value afterFirst => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction
  | reject firstFailure firstRejected =>
      rw [firstResult] at result
      cases result
      rfl

/-- Wildcard rejection is exact and non-consuming. -/
theorem wildcardPattern_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : wildcardPattern input = .reject failure rejected) :
    DeclarativeGrammar.WildcardPatternRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold wildcardPattern at result
  have markerResult : symbol .underscore .pattern input =
      .reject failure rejected := bind_pure_reject_first result
  have rejectedEq := symbol_reject_state_eq .underscore .pattern markerResult
  subst rejected
  exact .absent
    (symbol_reject_tokenKindAbsentAt .underscore .pattern markerResult)

/-- A positive wildcard guard cannot reject. -/
theorem wildcardPattern_ne_reject_of_isSymbol_eq_true
    {input rejected : State} {failure : Failure}
    (present : isSymbol input .underscore = true)
    (result : wildcardPattern input = .reject failure rejected) : False := by
  unfold wildcardPattern at result
  have markerResult : symbol .underscore .pattern input =
      .reject failure rejected := bind_pure_reject_first result
  rcases symbol_eq_ok_of_isSymbol_eq_true .underscore .pattern present with
    ⟨token, parsed⟩
  rw [parsed] at markerResult
  contradiction

/-- Literal-pattern rejection is the exact literal primitive rejection. -/
theorem literalPattern_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : literalPattern input = .reject failure rejected) :
    DeclarativeGrammar.LiteralPatternRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold literalPattern at result
  have literalResult : coreLiteral input = .reject failure rejected :=
    bind_pure_reject_first result
  have rejectedEq := coreLiteral_reject_state_eq literalResult
  subst rejected
  exact .absent (coreLiteral_reject_coreLiteralAbsentAt literalResult)

/-- A positive literal guard cannot reject. -/
theorem literalPattern_ne_reject_of_isCoreLiteral_eq_true
    {input rejected : State} {failure : Failure}
    (present : isCoreLiteral input = true)
    (result : literalPattern input = .reject failure rejected) : False := by
  unfold literalPattern at result
  exact coreLiteral_ne_reject_of_isCoreLiteral_eq_true present
    (bind_pure_reject_first result)

private theorem booleanIdentifier_reject_state_eq
    {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) :
    rejected = input := by
  unfold booleanIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_rejected_state_eq result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_rejected_state_eq result }
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_rejected_state_eq result }
        all_goals try { contradiction }

private theorem booleanIdentifier_reject_booleanPatternAbsentAt
    {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) :
    DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder := by
  constructor
  · rintro ⟨span, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.keyword .trueKw
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.keyword .trueKw
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold booleanIdentifier at result
    simp [found] at result
  · rintro ⟨span, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.keyword .falseKw
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.keyword .falseKw
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold booleanIdentifier at result
    simp [found] at result

/-- Boolean-binder rejection is exact and non-consuming. -/
theorem booleanBinderPattern_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : booleanBinderPattern input = .reject failure rejected) :
    DeclarativeGrammar.BooleanBinderPatternRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold booleanBinderPattern at result
  have nameResult : booleanIdentifier input = .reject failure rejected :=
    bind_pure_reject_first result
  have rejectedEq := booleanIdentifier_reject_state_eq nameResult
  subst rejected
  exact .absent (booleanIdentifier_reject_booleanPatternAbsentAt nameResult)

/-- A positive Boolean guard cannot reject. -/
theorem booleanBinderPattern_ne_reject_of_isBooleanValue_eq_true
    {input rejected : State} {failure : Failure}
    (present : isBooleanValue input = true)
    (result : booleanBinderPattern input = .reject failure rejected) : False := by
  unfold booleanBinderPattern at result
  have nameResult : booleanIdentifier input = .reject failure rejected :=
    bind_pure_reject_first result
  unfold isBooleanValue isKeyword State.peekKind? at present
  unfold booleanIdentifier at nameResult
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at present nameResult
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at present nameResult
        all_goals try { contradiction }

/-- Package executable wildcard success and exact rejection. -/
theorem wildcardPattern_ordinaryOutcome_sound :
    (∀ {input output : State} {pattern : Pattern},
      wildcardPattern input = .ok pattern output →
        DeclarativeGrammar.WildcardPatternOrdinaryParses
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      wildcardPattern input = .reject failure rejected →
        DeclarativeGrammar.WildcardPatternRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨wildcardPattern_success_sound, wildcardPattern_reject_ordinary_sound⟩

/-- Package executable literal-pattern success and exact rejection. -/
theorem literalPattern_ordinaryOutcome_sound :
    (∀ {input output : State} {pattern : Pattern},
      literalPattern input = .ok pattern output →
        DeclarativeGrammar.LiteralPatternOrdinaryParses
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      literalPattern input = .reject failure rejected →
        DeclarativeGrammar.LiteralPatternRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨literalPattern_success_sound, literalPattern_reject_ordinary_sound⟩

/-- Package executable Boolean-binder success and exact rejection. -/
theorem booleanBinderPattern_ordinaryOutcome_sound :
    (∀ {input output : State} {pattern : Pattern},
      booleanBinderPattern input = .ok pattern output →
        DeclarativeGrammar.BooleanBinderPatternOrdinaryParses
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      booleanBinderPattern input = .reject failure rejected →
        DeclarativeGrammar.BooleanBinderPatternRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨booleanBinderPattern_success_sound,
    booleanBinderPattern_reject_ordinary_sound⟩

/-- Package all three leaf deterministic outcome specifications. -/
theorem patternCoreLeaf_ordinaryOutcomeSpec :
    (DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.WildcardPatternOrdinaryParses
      DeclarativeGrammar.WildcardPatternRejects) ∧
    (DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.LiteralPatternOrdinaryParses
      DeclarativeGrammar.LiteralPatternRejects) ∧
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.BooleanBinderPatternOrdinaryParses
      DeclarativeGrammar.BooleanBinderPatternRejects :=
  ⟨DeclarativeGrammar.wildcardPatternDeterministicOutcomeSpec,
    DeclarativeGrammar.literalPatternDeterministicOutcomeSpec,
    DeclarativeGrammar.booleanBinderPatternDeterministicOutcomeSpec⟩

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternCoreOutcomeSuccessSoundnessProperties
/-! Generic ordinary-success reflection for the ordered `patternCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Every executable success records the selected branch and all earlier
failed guards.  The four recursive branch grammars are supplied by callbacks. -/
theorem patternCore_success_ordinary_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : DeclarativeGrammar.Remainder → Pattern →
        DeclarativeGrammar.Remainder → Prop)
    (parenthesizedSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        parenthesizedPattern nested input = .ok pattern output →
          parenthesizedOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (dotConstructorSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        dotConstructorPattern nested input = .ok pattern output →
          dotConstructorOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (comptimeSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        comptimePattern expression input = .ok pattern output →
          comptimeOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (qualifiedSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        qualifiedPattern nested input = .ok pattern output →
          qualifiedOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    {input output : State} {pattern : Pattern}
    (result : patternCore nested expression input = .ok pattern output) :
    DeclarativeGrammar.PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder := by
  unfold patternCore at result
  split at result
  next underscorePresent =>
    rcases symbolTokenAt_of_isSymbol_eq_true .underscore underscorePresent
      with ⟨span, marker⟩
    exact .selected (.wildcard marker)
      (.wildcard (wildcardPattern_success_sound result))
  next underscoreAbsent =>
    have noUnderscore := symbolAbsentAt_of_isSymbol_eq_false .underscore
      (Bool.eq_false_iff.mpr underscoreAbsent)
    split at result
    next literalPresent =>
      have starts := coreLiteralStartsAt_of_isCoreLiteral_eq_true
        literalPresent
      exact .selected (.literal noUnderscore starts)
        (.literal (literalPattern_success_sound result))
    next literalAbsent =>
      have noLiteral :=
        ExpressionAtomInternals.not_coreLiteralStartsAt_of_isCoreLiteral_eq_false
          (Bool.eq_false_iff.mpr literalAbsent)
      split at result
      next booleanPresent =>
        have starts := booleanPatternStartsAt_of_isBooleanValue_eq_true
          booleanPresent
        exact .selected (.boolean noUnderscore noLiteral starts)
          (.boolean (booleanBinderPattern_success_sound result))
      next booleanAbsent =>
        have noBoolean :=
          not_booleanPatternStartsAt_of_isBooleanValue_eq_false
            (Bool.eq_false_iff.mpr booleanAbsent)
        split at result
        next leftParenPresent =>
          rcases symbolTokenAt_of_isSymbol_eq_true .leftParen
              leftParenPresent with ⟨span, marker⟩
          exact .selected
            (.parenthesized noUnderscore noLiteral noBoolean marker)
            (.parenthesized (parenthesizedSuccessSound result))
        next leftParenAbsent =>
          have noLeftParen := symbolAbsentAt_of_isSymbol_eq_false .leftParen
            (Bool.eq_false_iff.mpr leftParenAbsent)
          split at result
          next dotPresent =>
            rcases symbolTokenAt_of_isSymbol_eq_true .dot dotPresent with
              ⟨span, marker⟩
            exact .selected
              (.dotConstructor noUnderscore noLiteral noBoolean noLeftParen
                marker)
              (.dotConstructor (dotConstructorSuccessSound result))
          next dotAbsent =>
            have noDot := symbolAbsentAt_of_isSymbol_eq_false .dot
              (Bool.eq_false_iff.mpr dotAbsent)
            split at result
            next comptimePresent =>
              rcases contextualTokenAt_of_isContextual_eq_true .comptime
                  comptimePresent with ⟨span, marker⟩
              exact .selected
                (.comptime noUnderscore noLiteral noBoolean noLeftParen
                  noDot marker)
                (.comptime (comptimeSuccessSound result))
            next comptimeAbsent =>
              have noComptime := contextualAbsentAt_of_isContextual_eq_false
                .comptime (Bool.eq_false_iff.mpr comptimeAbsent)
              split at result
              next identifierPresent =>
                rcases identifierPresentAt_of_isIdentifier_eq_true
                    identifierPresent with ⟨span, spelling, marker⟩
                exact .selected
                  (.qualified noUnderscore noLiteral noBoolean noLeftParen
                    noDot noComptime marker)
                  (.qualified (qualifiedSuccessSound result))
              next identifierAbsent =>
                simp [rejectAt] at result

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternCoreOutcomeRejectionSoundnessProperties
/-! Generic exact ordinary-rejection reflection for `patternCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Every executable rejection is either the exact selected recursive-branch
rejection or the final non-consuming dispatcher rejection. -/
theorem patternCore_reject_ordinary_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : DeclarativeGrammar.Remainder →
        DeclarativeGrammar.Remainder → Prop)
    (parenthesizedRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        parenthesizedPattern nested input = .reject failure rejected →
          parenthesizedRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (dotConstructorRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        dotConstructorPattern nested input = .reject failure rejected →
          dotConstructorRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (comptimeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        comptimePattern expression input = .reject failure rejected →
          comptimeRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (qualifiedRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        qualifiedPattern nested input = .reject failure rejected →
          qualifiedRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : patternCore nested expression input =
      .reject failure rejected) :
    DeclarativeGrammar.PatternCoreRejects parenthesizedRejects
      dotConstructorRejects comptimeRejects qualifiedRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  unfold patternCore at result
  split at result
  next underscorePresent =>
    exact False.elim
      (wildcardPattern_ne_reject_of_isSymbol_eq_true underscorePresent result)
  next underscoreAbsent =>
    have noUnderscore := symbolAbsentAt_of_isSymbol_eq_false .underscore
      (Bool.eq_false_iff.mpr underscoreAbsent)
    split at result
    next literalPresent =>
      exact False.elim
        (literalPattern_ne_reject_of_isCoreLiteral_eq_true literalPresent
          result)
    next literalAbsent =>
      have noLiteral :=
        ExpressionAtomInternals.not_coreLiteralStartsAt_of_isCoreLiteral_eq_false
          (Bool.eq_false_iff.mpr literalAbsent)
      split at result
      next booleanPresent =>
        exact False.elim
          (booleanBinderPattern_ne_reject_of_isBooleanValue_eq_true
            booleanPresent result)
      next booleanAbsent =>
        have noBoolean :=
          not_booleanPatternStartsAt_of_isBooleanValue_eq_false
            (Bool.eq_false_iff.mpr booleanAbsent)
        split at result
        next leftParenPresent =>
          rcases symbolTokenAt_of_isSymbol_eq_true .leftParen
              leftParenPresent with ⟨span, marker⟩
          exact .selected
            (.parenthesized noUnderscore noLiteral noBoolean marker)
            (.parenthesized (parenthesizedRejectSound result))
        next leftParenAbsent =>
          have noLeftParen := symbolAbsentAt_of_isSymbol_eq_false .leftParen
            (Bool.eq_false_iff.mpr leftParenAbsent)
          split at result
          next dotPresent =>
            rcases symbolTokenAt_of_isSymbol_eq_true .dot dotPresent with
              ⟨span, marker⟩
            exact .selected
              (.dotConstructor noUnderscore noLiteral noBoolean noLeftParen
                marker)
              (.dotConstructor (dotConstructorRejectSound result))
          next dotAbsent =>
            have noDot := symbolAbsentAt_of_isSymbol_eq_false .dot
              (Bool.eq_false_iff.mpr dotAbsent)
            split at result
            next comptimePresent =>
              rcases contextualTokenAt_of_isContextual_eq_true .comptime
                  comptimePresent with ⟨span, marker⟩
              exact .selected
                (.comptime noUnderscore noLiteral noBoolean noLeftParen
                  noDot marker)
                (.comptime (comptimeRejectSound result))
            next comptimeAbsent =>
              have noComptime := contextualAbsentAt_of_isContextual_eq_false
                .comptime (Bool.eq_false_iff.mpr comptimeAbsent)
              split at result
              next identifierPresent =>
                rcases identifierPresentAt_of_isIdentifier_eq_true
                    identifierPresent with ⟨span, spelling, marker⟩
                exact .selected
                  (.qualified noUnderscore noLiteral noBoolean noLeftParen
                    noDot noComptime marker)
                  (.qualified (qualifiedRejectSound result))
              next identifierAbsent =>
                have noIdentifier := identifierAbsentAt_of_isIdentifier_eq_false
                  (Bool.eq_false_iff.mpr identifierAbsent)
                unfold rejectAt at result
                cases result
                exact .final (.final noUnderscore noLiteral noBoolean
                  noLeftParen noDot noComptime noIdentifier)

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternCoreOutcomeSoundnessProperties
/-! Packaged generic executable ordinary outcomes for `patternCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Package executable success and rejection reflection over four supplied
recursive-branch outcome bridges. -/
theorem patternCore_ordinaryOutcome_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : DeclarativeGrammar.Remainder → Pattern →
        DeclarativeGrammar.Remainder → Prop)
    (parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : DeclarativeGrammar.Remainder →
        DeclarativeGrammar.Remainder → Prop)
    (parenthesizedSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        parenthesizedPattern nested input = .ok pattern output →
          parenthesizedOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (dotConstructorSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        dotConstructorPattern nested input = .ok pattern output →
          dotConstructorOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (comptimeSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        comptimePattern expression input = .ok pattern output →
          comptimeOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (qualifiedSuccessSound :
      ∀ {input output : State} {pattern : Pattern},
        qualifiedPattern nested input = .ok pattern output →
          qualifiedOrdinary input.declarativeRemainder pattern
            output.declarativeRemainder)
    (parenthesizedRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        parenthesizedPattern nested input = .reject failure rejected →
          parenthesizedRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (dotConstructorRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        dotConstructorPattern nested input = .reject failure rejected →
          dotConstructorRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (comptimeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        comptimePattern expression input = .reject failure rejected →
          comptimeRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (qualifiedRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        qualifiedPattern nested input = .reject failure rejected →
          qualifiedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :
    (∀ {input output : State} {pattern : Pattern},
      patternCore nested expression input = .ok pattern output →
        DeclarativeGrammar.PatternCoreOrdinaryParses parenthesizedOrdinary
          dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary
            input.declarativeRemainder pattern
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      patternCore nested expression input = .reject failure rejected →
        DeclarativeGrammar.PatternCoreRejects parenthesizedRejects
          dotConstructorRejects comptimeRejects qualifiedRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨patternCore_success_ordinary_sound nested expression
      parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
        qualifiedOrdinary parenthesizedSuccessSound
          dotConstructorSuccessSound comptimeSuccessSound
            qualifiedSuccessSound,
    patternCore_reject_ordinary_sound nested expression
      parenthesizedRejects dotConstructorRejects comptimeRejects
        qualifiedRejects parenthesizedRejectSound dotConstructorRejectSound
          comptimeRejectSound qualifiedRejectSound⟩

/-- Lift four deterministic recursive outcomes through the public executable
dispatcher relations. -/
theorem patternCore_ordinaryOutcomeSpec
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : DeclarativeGrammar.Remainder → Pattern →
        DeclarativeGrammar.Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : DeclarativeGrammar.Remainder →
        DeclarativeGrammar.Remainder → Prop}
    (parenthesizedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      comptimeOrdinary comptimeRejects)
    (qualifiedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      qualifiedOrdinary qualifiedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.PatternCoreOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary)
      (DeclarativeGrammar.PatternCoreRejects parenthesizedRejects
        dotConstructorRejects comptimeRejects qualifiedRejects) :=
  DeclarativeGrammar.patternCoreDeterministicOutcomeSpec
    parenthesizedOutcomes dotConstructorOutcomes comptimeOutcomes
      qualifiedOutcomes

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternParenthesizedOrdinarySuccessSoundnessProperties
/-! Unconditional ordinary-success reflection for parenthesized patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Successful tuple-tail execution follows the exact forward-order grammar.
Fuel exhaustion and non-progress cannot inhabit this theorem. -/
theorem patternTupleTail_success_ordinary_sound_strong
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input pattern output,
      patternTupleTail nested opening fuel elementsRev input =
        .ok pattern output →
      ∃ suffix closingSpan,
        pattern = DeclarativeGrammar.closeParenthesizedPattern opening.span
          closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedPatternTupleTailParses nestedOrdinary
          input.declarativeRemainder suffix closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input pattern output result
      simp [patternTupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input pattern output result
      unfold patternTupleTail at result
      cases commaResult : symbol .comma .pattern input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .pattern commaResult
          split at result
          · rcases closePatternTuple_success_sound opening elementsRev result
                with ⟨closingSpan, patternEq, closingParsed⟩
            exact ⟨[], closingSpan, by simpa using patternEq,
              .trailing comma.span closingSpan commaParsed closingParsed⟩
          · have closingAbsentBool :
                isSymbol afterComma .rightParen = false := by simp_all
            have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
              .rightParen closingAbsentBool
            cases elementResult : nested afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok element afterElement =>
                simp only [elementResult] at result
                split at result
                next noProgress => contradiction
                next progressBranch =>
                  have elementProgress :
                      afterComma.cursor < afterElement.cursor :=
                    Nat.lt_of_not_ge progressBranch
                  have elementGrammar := nestedSuccessSound elementResult
                  split at result
                  next commaPresent =>
                    rcases inductionHypothesis (element :: elementsRev)
                        afterElement pattern output result with
                      ⟨suffix, closingSpan, patternEq, tailGrammar⟩
                    refine ⟨element :: suffix, closingSpan, ?_,
                      .next comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) tailGrammar⟩
                    simpa [List.reverse_cons, List.append_assoc] using
                      patternEq
                  next commaAbsentBranch =>
                    rcases closePatternTuple_success_sound opening
                        (element :: elementsRev) result with
                      ⟨closingSpan, patternEq, closingParsed⟩
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                      .comma (input := afterElement) (by simp_all)
                    refine ⟨[element], closingSpan, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) commaAbsent closingParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using
                      patternEq

/-- Every executable success has the exact empty, group, or tuple shape. -/
theorem parenthesizedPattern_success_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    {input output : State} {pattern : Pattern}
    (result : parenthesizedPattern nested input = .ok pattern output) :
    DeclarativeGrammar.ParenthesizedPatternOrdinaryParses nestedOrdinary
      input.declarativeRemainder pattern output.declarativeRemainder := by
  unfold parenthesizedPattern at result
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .pattern openingResult
      split at result
      · rcases closePatternTuple_success_sound opening [] result with
          ⟨closingSpan, patternEq, closingParsed⟩
        subst pattern
        exact .empty opening.span closingSpan openingParsed closingParsed
      · have closingAbsentBool :
            isSymbol afterOpening .rightParen = false := by simp_all
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen
          closingAbsentBool
        cases firstResult : nested afterOpening with
        | invariant error => simp [firstResult] at result
        | reject failure rejected => simp [firstResult] at result
        | ok first afterFirst =>
            simp only [firstResult] at result
            split at result
            next noProgress => contradiction
            next progressBranch =>
              have firstProgress : afterOpening.cursor < afterFirst.cursor :=
                Nat.lt_of_not_ge progressBranch
              have firstGrammar := nestedSuccessSound firstResult
              split at result
              next commaPresent =>
                rcases patternTupleTail_success_ordinary_sound_strong nested
                    nestedOrdinary nestedSuccessSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst
                        pattern output result with
                  ⟨rest, closingSpan, patternEq, tailGrammar⟩
                subst pattern
                simpa using
                  (DeclarativeGrammar.ParenthesizedPatternParses.tuple
                    opening.span closingSpan openingParsed closingAbsent
                      firstGrammar (by
                        simpa [State.declarativeRemainder] using firstProgress)
                        tailGrammar)
              next commaAbsentBranch =>
                rcases closePatternTuple_success_sound opening [first] result
                    with ⟨closingSpan, patternEq, closingParsed⟩
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                  .comma (input := afterFirst) (by simp_all)
                subst pattern
                exact .group opening.span closingSpan openingParsed
                  closingAbsent firstGrammar (by
                    simpa [State.declarativeRemainder] using firstProgress)
                      commaAbsent closingParsed

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternParenthesizedOrdinaryRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for parenthesized patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem closePatternTuple_reject_ordinary_sound (opening : Token)
    (elementsRev : List Pattern) {input rejected : State}
    {failure : Failure}
    (result : closePatternTuple opening elementsRev input =
      .reject failure rejected) :
    rejected = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.symbol .rightParen) := by
  unfold closePatternTuple at result
  cases closingResult : symbol .rightParen .pattern input with
  | invariant error => simp [bind, closingResult] at result
  | ok closing afterClosing =>
      simp only [bind, closingResult] at result
      cases elementsRev with
      | nil => simp [pure] at result
      | cons head tail =>
          cases tail with
          | nil => simp [pure] at result
          | cons second rest => simp [pure] at result
  | reject closingFailure closingRejected =>
      simp only [bind, closingResult] at result
      cases result
      exact ⟨symbol_reject_state_eq .rightParen .pattern closingResult,
        symbol_reject_tokenKindAbsentAt .rightParen .pattern closingResult⟩

/-- Every tuple-tail rejection under its positive comma guard is exact. -/
theorem patternTupleTail_reject_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input failure rejected,
      isSymbol input .comma = true →
      patternTupleTail nested opening fuel elementsRev input =
        .reject failure rejected →
      DeclarativeGrammar.ParenthesizedPatternTupleTailRejects nestedOrdinary
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input failure rejected commaPresent result
      simp [patternTupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input failure rejected commaPresent result
      unfold patternTupleTail at result
      cases commaResult : symbol .comma .pattern input with
      | invariant error => simp [commaResult] at result
      | reject commaFailure commaRejected =>
          rcases symbol_eq_ok_of_isSymbol_eq_true .comma .pattern commaPresent
              with ⟨comma, parsed⟩
          rw [parsed] at commaResult
          contradiction
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .pattern commaResult
          by_cases closingPresent : isSymbol afterComma .rightParen
          · simp only [closingPresent, if_true] at result
            rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .pattern
                closingPresent with ⟨closing, closingResult⟩
            unfold closePatternTuple at result
            simp only [bind, closingResult] at result
            cases elementsRev with
            | nil => simp [pure] at result
            | cons head tail =>
                cases tail with
                | nil => simp [pure] at result
                | cons second rest => simp [pure] at result
          · have closingAbsentBool :
                isSymbol afterComma .rightParen = false :=
              Bool.eq_false_iff.mpr closingPresent
            simp only [closingAbsentBool, Bool.false_eq_true, if_false]
              at result
            have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
              .rightParen closingAbsentBool
            cases elementResult : nested afterComma with
            | invariant error => simp [elementResult] at result
            | reject elementFailure elementRejected =>
                simp only [elementResult] at result
                cases result
                exact .elementRejected comma.span commaParsed closingAbsent
                  (nestedRejectSound elementResult)
            | ok element afterElement =>
                simp only [elementResult] at result
                by_cases noProgress :
                    afterElement.cursor ≤ afterComma.cursor
                · simp [noProgress] at result
                · simp only [noProgress, if_false] at result
                  have elementParsed := nestedSuccessSound elementResult
                  have progress : afterComma.declarativeRemainder.cursor <
                      afterElement.declarativeRemainder.cursor := by
                    simpa [State.declarativeRemainder] using
                      (Nat.lt_of_not_ge noProgress)
                  by_cases commaAgain : isSymbol afterElement .comma
                  · simp only [commaAgain, if_true] at result
                    exact .laterRejected comma.span commaParsed closingAbsent
                      elementParsed progress
                      (inductionHypothesis (element :: elementsRev)
                        afterElement failure rejected commaAgain result)
                  · have commaAbsentBool :
                        isSymbol afterElement .comma = false :=
                      Bool.eq_false_iff.mpr commaAgain
                    simp only [commaAbsentBool, Bool.false_eq_true, if_false]
                      at result
                    rcases closePatternTuple_reject_ordinary_sound opening
                        (element :: elementsRev) result with
                      ⟨rejectedEq, rightParenAbsent⟩
                    subst rejectedEq
                    exact .closingMissing comma.span commaParsed closingAbsent
                      elementParsed progress
                      (symbolAbsentAt_of_isSymbol_eq_false .comma
                        commaAbsentBool) rightParenAbsent

/-- Every public parenthesized-pattern rejection follows its exact branch. -/
theorem parenthesizedPattern_reject_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : parenthesizedPattern nested input = .reject failure rejected) :
    DeclarativeGrammar.ParenthesizedPatternRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold parenthesizedPattern at result
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure afterOpening =>
      simp only [openingResult] at result
      have rejectedEq : afterOpening = rejected := by injection result
      subst rejected
      have stateEq := symbol_reject_state_eq .leftParen .pattern
        openingResult
      rw [stateEq]
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftParen .pattern openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .pattern openingResult
      by_cases closingPresent : isSymbol afterOpening .rightParen
      · simp only [closingPresent, if_true] at result
        rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .pattern
            closingPresent with ⟨closing, closingResult⟩
        unfold closePatternTuple at result
        simp [bind, closingResult, pure] at result
      · have closingAbsentBool :
            isSymbol afterOpening .rightParen = false :=
          Bool.eq_false_iff.mpr closingPresent
        simp only [closingAbsentBool, Bool.false_eq_true, if_false] at result
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen
          closingAbsentBool
        cases firstResult : nested afterOpening with
        | invariant error => simp [firstResult] at result
        | reject firstFailure firstRejected =>
            simp only [firstResult] at result
            cases result
            exact .firstRejected opening.span openingParsed closingAbsent
              (nestedRejectSound firstResult)
        | ok first afterFirst =>
            simp only [firstResult] at result
            by_cases noProgress : afterFirst.cursor ≤ afterOpening.cursor
            · simp [noProgress] at result
            · simp only [noProgress, if_false] at result
              have firstParsed := nestedSuccessSound firstResult
              have progress : afterOpening.declarativeRemainder.cursor <
                  afterFirst.declarativeRemainder.cursor := by
                simpa [State.declarativeRemainder] using
                  (Nat.lt_of_not_ge noProgress)
              by_cases commaPresent : isSymbol afterFirst .comma
              · simp only [commaPresent, if_true] at result
                exact .tailRejected opening.span openingParsed closingAbsent
                  firstParsed progress
                  (patternTupleTail_reject_ordinary_sound nested
                    nestedOrdinary nestedRejects nestedSuccessSound
                      nestedRejectSound opening
                        (afterFirst.remainingCount + 1) [first] afterFirst
                          failure rejected commaPresent result)
              · have commaAbsentBool : isSymbol afterFirst .comma = false :=
                  Bool.eq_false_iff.mpr commaPresent
                simp only [commaAbsentBool, Bool.false_eq_true, if_false]
                  at result
                rcases closePatternTuple_reject_ordinary_sound opening [first]
                    result with ⟨rejectedEq, rightParenAbsent⟩
                subst rejectedEq
                exact .closingMissing opening.span openingParsed closingAbsent
                  firstParsed progress
                    (symbolAbsentAt_of_isSymbol_eq_false .comma
                      commaAbsentBool) rightParenAbsent

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternParenthesizedOrdinaryOutcomeSoundnessProperties
/-! Packaged executable ordinary outcomes for parenthesized patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Package unconditional executable success and rejection reflection. -/
theorem parenthesizedPattern_ordinaryOutcome_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {pattern : Pattern},
      parenthesizedPattern nested input = .ok pattern output →
        DeclarativeGrammar.ParenthesizedPatternOrdinaryParses nestedOrdinary
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      parenthesizedPattern nested input = .reject failure rejected →
        DeclarativeGrammar.ParenthesizedPatternRejects nestedOrdinary
          nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨parenthesizedPattern_success_ordinary_sound nested nestedOrdinary
      nestedSuccessSound,
    parenthesizedPattern_reject_ordinary_sound nested nestedOrdinary
      nestedRejects nestedSuccessSound nestedRejectSound⟩

/-- Re-export deterministic parenthesized-pattern outcomes. -/
theorem parenthesizedPattern_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ParenthesizedPatternOrdinaryParses nestedOrdinary)
      (DeclarativeGrammar.ParenthesizedPatternRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.parenthesizedPatternDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternConstructorArgumentSoundnessProperties
/-!
Diagnostic reflection and exact token soundness for constructor-pattern names
and their transactional argument lists.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem bindOkComponents {alpha beta : Type} {first : Parser alpha}
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

private theorem leftParenTokenAtOfIsSymbol
    {input : State} (present : isSymbol input .leftParen = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .leftParen } := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol .leftParen) = true at present
      have parsed : symbol .leftParen .pattern input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold symbol acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span, (symbol_ok_tokenAt .leftParen .pattern parsed).1⟩

/-- Pattern-name success reflects through the Boolean-first branch. -/
theorem patternName_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess patternName := by
  intro input name next result diagnosticFree
  unfold patternName at result
  split at result
  · exact booleanIdentifier_reflectsDiagnosticFreeOnSuccess input name next
      result diagnosticFree
  · exact identifier_reflectsDiagnosticFreeOnSuccess .pattern input name
      next result diagnosticFree

/-- Nonempty refinement is non-consuming and cannot erase diagnostics. -/
theorem requirePatternArguments_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList Pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requirePatternArguments values) := by
  intro input arguments next result diagnosticFree
  unfold requirePatternArguments at result
  cases elements : values.elements with
  | nil => simp [elements] at result
  | cons head tail =>
      simp only [elements, pure] at result
      cases result
      exact diagnosticFree

/-- Required argument parsing reflects through delimiters and nested values. -/
theorem constructorArguments_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (constructorArguments nested) := by
  unfold constructorArguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess .leftParen
      .rightParen false nested .pattern .pattern nestedReflects)
  exact requirePatternArguments_reflectsDiagnosticFreeOnSuccess

/-- Transactional optional arguments reflect through either successful path. -/
theorem optionalConstructorArguments_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalConstructorArguments nested) := by
  intro input arguments next result diagnosticFree
  unfold optionalConstructorArguments at result
  split at result
  · exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
      (Parser.bind_reflectsDiagnosticFreeOnSuccess
        (constructorArguments_reflectsDiagnosticFreeOnSuccess nested
          nestedReflects)
        (fun values => Parser.pure_reflectsDiagnosticFreeOnSuccess
          (some values)))
      (Parser.pure_reflectsDiagnosticFreeOnSuccess none)
      input arguments next result diagnosticFree
  · cases result
    exact diagnosticFree

/-- Diagnostic-free checked identifiers exclude the parser's hyphen error. -/
theorem identifier_hyphenAbsent_of_diagnosticFree (context : ParseContext)
    {input next : State} {name : Identifier}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : identifier context input = .ok name next) :
    name.value.toList.contains '-' = false := by
  unfold identifier at result
  cases rawResult : rawIdentifier context input with
  | invariant error => simp [rawResult] at result
  | reject failure rejected => simp [rawResult] at result
  | ok parsedName afterName =>
      simp only [rawResult] at result
      split at result
      · cases result
        simp [State.emit] at diagnosticFree
      · cases result
        exact Bool.eq_false_iff.mpr (by assumption)

/--
Every diagnostic-free name retains exact Boolean-first priority and excludes
the checked ordinary-identifier hyphen diagnostic.
-/
theorem patternName_success_sound {input next : State} {name : Identifier}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : patternName input = .ok name next) :
    DeclarativeGrammar.PatternNameParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold patternName at result
  split at result
  · exact .boolean (booleanIdentifier_success_sound result)
  · have booleanAbsent : isBooleanValue input = false :=
      Bool.eq_false_iff.mpr (by assumption)
    have absences :
        isKeyword input .trueKw = false ∧
          isKeyword input .falseKw = false :=
      Bool.or_eq_false_iff.mp (by
        simpa only [isBooleanValue] using booleanAbsent)
    exact .identifier
      (keywordAbsentAt_of_isKeyword_eq_false .trueKw absences.1)
      (keywordAbsentAt_of_isKeyword_eq_false .falseKw absences.2)
      (identifier_hyphenAbsent_of_diagnosticFree .pattern diagnosticFree
        result)
      (identifier_success_sound .pattern result)

/-- Successful refinement fixes the nonempty carrier and changes no state. -/
theorem requirePatternArguments_success_sound
    {values : DelimitedList Pattern} {input next : State}
    {arguments : NonemptyDelimitedList Pattern}
    (result : requirePatternArguments values input = .ok arguments next) :
    DeclarativeGrammar.RequirePatternArgumentsParses values
      input.declarativeRemainder arguments next.declarativeRemainder := by
  rcases values with ⟨span, elements⟩
  unfold requirePatternArguments at result
  cases elements with
  | nil => simp at result
  | cons head tail =>
      simp only [pure] at result
      cases result
      exact .parsed

/-- Diagnostic-free required arguments have exact nonempty no-trailing syntax. -/
theorem constructorArguments_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {arguments : NonemptyDelimitedList Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : constructorArguments nested input = .ok arguments next) :
    DeclarativeGrammar.ConstructorArgumentsParses nestedParses
      input.declarativeRemainder arguments next.declarativeRemainder := by
  unfold constructorArguments at result
  rcases bindOkComponents result with
    ⟨values, afterValues, valuesResult, requiredResult⟩
  rcases values with ⟨span, elements⟩
  have afterValuesFree :=
    requirePatternArguments_reflectsDiagnosticFreeOnSuccess
      { span := span, elements := elements }
      afterValues arguments next requiredResult diagnosticFree
  have valuesGrammar :=
    delimitedNoTrailing_nonempty_success_sound_of_diagnosticFree
      .leftParen .rightParen nested nestedParses .pattern .pattern
      nestedSound nestedReflects nestedShape afterValuesFree valuesResult
  unfold requirePatternArguments at requiredResult
  cases elements with
  | nil => simp at requiredResult
  | cons head tail =>
      simp only [pure] at requiredResult
      cases requiredResult
      simpa only [DeclarativeGrammar.ConstructorArgumentsParses,
        NonemptyList.toList] using valuesGrammar

/--
Optional arguments distinguish absence, successful presence, and an exact
rewind after a leading-parenthesis attempt rejected.
-/
theorem optionalConstructorArguments_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.ConstructorArgumentsFallbackSpec nestedParses)
    (argumentsRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      constructorArguments nested input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State}
    {arguments : Option (NonemptyDelimitedList Pattern)}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalConstructorArguments nested input =
      .ok arguments next) :
    DeclarativeGrammar.OptionalConstructorArgumentsParses nestedParses
      fallback input.declarativeRemainder arguments
        next.declarativeRemainder := by
  unfold optionalConstructorArguments at result
  by_cases present : isSymbol input .leftParen = true
  · simp only [present, if_true] at result
    unfold orElse at result
    cases argumentsResult : constructorArguments nested input with
    | invariant error => simp [bind, argumentsResult] at result
    | reject failure rejected =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        rcases leftParenTokenAtOfIsSymbol present with
          ⟨openingSpan, openingToken⟩
        exact .rewound openingSpan openingToken
          (argumentsRejectionSound argumentsResult)
    | ok values afterArguments =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        exact .present (constructorArguments_success_sound nested nestedParses
          nestedReflects nestedSound nestedShape diagnosticFree argumentsResult)
  · have absentBool : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absentBool, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen absentBool)

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternQualifiedNameOrdinaryOutcomeSoundnessProperties
/-! Exact executable ordinary outcomes for qualified Core pattern paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Every qualified pattern-path success follows the maximal ordinary
qualified-name relation. -/
theorem patternQualifiedName_success_ordinary_sound
    {input output : State} {path : QualifiedName}
    (result : qualifiedName .pattern .pattern input = .ok path output) :
    DeclarativeGrammar.PatternQualifiedNameOrdinaryParses
      input.declarativeRemainder path output.declarativeRemainder :=
  qualifiedName_success_sound .pattern .pattern result

/-- Every qualified pattern-path rejection follows the exact first-or-dotted
identifier rejection trace. -/
theorem patternQualifiedName_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : qualifiedName .pattern .pattern input =
      .reject failure rejected) :
    DeclarativeGrammar.PatternQualifiedNameRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  qualifiedName_reject_type_sound .pattern .pattern result

/-- Package both executable qualified pattern-path outcomes. -/
theorem patternQualifiedName_ordinaryOutcome_sound :
    (∀ {input output : State} {path : QualifiedName},
      qualifiedName .pattern .pattern input = .ok path output →
        DeclarativeGrammar.PatternQualifiedNameOrdinaryParses
          input.declarativeRemainder path output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      qualifiedName .pattern .pattern input = .reject failure rejected →
        DeclarativeGrammar.PatternQualifiedNameRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨patternQualifiedName_success_ordinary_sound,
    patternQualifiedName_reject_ordinary_sound⟩

/-- Re-export deterministic qualified pattern-path outcomes. -/
theorem patternQualifiedName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PatternQualifiedNameOrdinaryParses
      DeclarativeGrammar.PatternQualifiedNameRejects :=
  DeclarativeGrammar.patternQualifiedNameDeterministicOutcomeSpec

end Solcore.Syntax.Parser.PatternInternals
end
