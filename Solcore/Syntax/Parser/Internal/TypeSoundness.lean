import Solcore.Syntax.Parser.Internal.TypeBasics
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Grammar.Types

/-!
Soundness of the parsers of types and qualified names: each success and each rejection has
its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.TypeStrictProperties
/-! Strict cursor progress for every successful canonical type parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_cursor_lt_onSuccess_of_first {α β : Type}
    {first : Parser α} {next : α → Parser β}
    (firstStrict : ∀ {input middle : State} {value : α},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok firstValue middle => next firstValue middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [firstResult] at parsed
  | invariant error => simp [firstResult] at parsed

/-- A named type consumes the first component of its qualified name. -/
theorem parseNamedType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    {input final : State} {value : TypeExpr}
    (parsed : parseNamedType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseNamedType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (qualifiedName_cursor_lt_onSuccess .typeExpr .typeExpr) ?_ parsed
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    (parseNamedTypeArguments_cursorMonotoneOnSuccess nested)
  intro arguments
  exact finishNamedType_cursorMonotoneOnSuccess name arguments

/-- A mapping type consumes its contextual `mapping` marker. -/
theorem parseMappingType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input final : State} {value : TypeExpr}
    (parsed : parseMappingType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseMappingType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.contextual .mapping) .typeExpr (·.isContextual .mapping) result)
    ?_ parsed
  intro mapping
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .typeExpr)
  intro opening
  apply Parser.bind_cursorMonotoneOnSuccess nestedMonotone
  intro key
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .fatArrow .typeExpr)
  intro arrow
  apply Parser.bind_cursorMonotoneOnSuccess nestedMonotone
  intro mapped
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .typeExpr)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A comptime type consumes its contextual `comptime` marker. -/
theorem parseComptimeType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input final : State} {value : TypeExpr}
    (parsed : parseComptimeType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseComptimeType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.contextual .comptime) .typeExpr (·.isContextual .comptime) result)
    ?_ parsed
  intro comptime
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .less .typeExpr)
  intro opening
  apply Parser.bind_cursorMonotoneOnSuccess nestedMonotone
  intro inner
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .greater .typeExpr)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A proxy type consumes its leading `@` marker. -/
theorem parseProxyType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input final : State} {value : TypeExpr}
    (parsed : parseProxyType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseProxyType at parsed
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp [markerResult] at parsed
  | reject failure rejected => simp [markerResult] at parsed
  | ok marker afterMarker =>
      simp only [markerResult] at parsed
      cases innerResult : nested afterMarker with
      | invariant error => simp [innerResult] at parsed
      | reject failure rejected => simp [innerResult] at parsed
      | ok inner next =>
          simp only [innerResult] at parsed
          have innerMonotone :=
            nestedMonotone afterMarker inner next innerResult
          cases parsed
          exact Nat.lt_of_lt_of_le
            (acceptToken_cursor_lt_onSuccess (.symbol .at) .typeExpr
              (· == .symbol .at) markerResult)
            innerMonotone

/-- A tuple type consumes its opening delimiter. -/
theorem parseTupleType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    {input final : State} {value : TypeExpr}
    (parsed : parseTupleType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseTupleType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (delimitedWithPolicy_cursor_lt_onSuccess .leftParen .rightParen true true
      nested .typeExpr .typeExpr) ?_ parsed
  intro tuple
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem parseFunctionReturns_cursorMonotoneOnSuccess
    (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess
      (TypeFunctionInternals.parseFunctionReturns nested) := by
  unfold TypeFunctionInternals.parseFunctionReturns
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isContextual observed .returns
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (contextual_cursorMonotoneOnSuccess .returns .typeExpr)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true nested
        .typeExpr .typeExpr)
    intro values
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A function type consumes its leading `function` keyword. -/
theorem parseFunctionType_cursor_lt_onSuccess (nested : Parser TypeExpr)
    {input final : State} {value : TypeExpr}
    (parsed : parseFunctionType nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold parseFunctionType at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.keyword .functionKw) .typeExpr (· == .keyword .functionKw) result)
    ?_ parsed
  intro functionKeyword
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true nested
      .typeExpr .typeExpr)
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    (parseFunctionReturns_cursorMonotoneOnSuccess nested)
  intro returns
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Every successful fuel-bounded type parse consumes at least one token. -/
theorem typeExprWithFuel_cursor_lt_onSuccess (fuel : Nat)
    {input final : State} {value : TypeExpr}
    (parsed : typeExprWithFuel fuel input = .ok value final) :
    input.cursor < final.cursor := by
  cases fuel with
  | zero => simp [typeExprWithFuel] at parsed
  | succ fuel =>
      simp only [typeExprWithFuel] at parsed
      split at parsed
      · exact parseFunctionType_cursor_lt_onSuccess
          (typeExprWithFuel fuel) parsed
      · split at parsed
        · exact parseComptimeType_cursor_lt_onSuccess
            (typeExprWithFuel fuel)
            (typeExprWithFuel_cursorMonotoneOnSuccess fuel) parsed
        · split at parsed
          · exact parseMappingType_cursor_lt_onSuccess
              (typeExprWithFuel fuel)
              (typeExprWithFuel_cursorMonotoneOnSuccess fuel) parsed
          · split at parsed
            · exact parseProxyType_cursor_lt_onSuccess
                (typeExprWithFuel fuel)
                (typeExprWithFuel_cursorMonotoneOnSuccess fuel) parsed
            · split at parsed
              · exact parseTupleType_cursor_lt_onSuccess
                  (typeExprWithFuel fuel) parsed
              · split at parsed
                · exact parseNamedType_cursor_lt_onSuccess
                    (typeExprWithFuel fuel) parsed
                · unfold rejectAt at parsed
                  contradiction

/-- Public recursive type parsing strictly consumes on success. -/
theorem typeExpr_cursor_lt_onSuccess {input final : State} {value : TypeExpr}
    (parsed : typeExpr input = .ok value final) :
    input.cursor < final.cursor := by
  unfold typeExpr at parsed
  exact typeExprWithFuel_cursor_lt_onSuccess
    (input.remainingCount + 1) parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeMappingSoundnessProperties
/-! Success soundness for canonical mapping type parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem mappingTypeBind_success_components {α β : Type}
    {first : Parser α} {nextParser : α → Parser β}
    {input final : State} {value : β}
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

/-- Successful mapping parsing follows its exact recursive token grammar. -/
theorem parseMappingType_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {resultValue : TypeExpr}
    (result : parseMappingType nested input = .ok resultValue next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder resultValue
      next.declarativeRemainder := by
  unfold parseMappingType at result
  rcases mappingTypeBind_success_components result with
    ⟨mapping, afterMapping, mappingResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨key, afterKey, keyResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨arrow, afterArrow, arrowResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨value, afterValue, valueResult, rest⟩
  rcases mappingTypeBind_success_components rest with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact .mapping mapping.span opening.span arrow.span closing.span
    (contextual_success_exactTokenParses .mapping .typeExpr mappingResult)
    (symbol_success_exactTokenParses .leftParen .typeExpr openingResult)
    (symbol_success_exactTokenParses .fatArrow .typeExpr arrowResult)
    (symbol_success_exactTokenParses .rightParen .typeExpr closingResult)
    rfl (nestedSound keyResult) (nestedSound valueResult)

/-- Mapping grammar soundness composes with recursive source validity. -/
theorem parseMappingType_success_sound_and_validFor
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span))
    (nestedShape : Parser.PreservesTokenWindow nested)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    {input next : State} {resultValue : TypeExpr}
    (inputValid : input.ValidFor)
    (result : parseMappingType nested input = .ok resultValue next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder resultValue
        next.declarativeRemainder ∧
      TypeExpr.ValidFor input.file resultValue := by
  refine ⟨parseMappingType_success_sound nested nestedSound result, ?_⟩
  have valid := parseMappingType_validFor nested nestedValid nestedStarts
    nestedShape.preservesTokensOnSuccess nestedMonotone input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties
/-! Diagnostic-free reflection for recursive type-expression parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open QualifiedNameInternals

private theorem qualifiedNameTail_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (qualifiedNameTail context phase first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input value next parsed diagnosticFree
      simp [qualifiedNameTail] at parsed
  | succ fuel inductionHypothesis =>
      intro last tailRev input value next parsed diagnosticFree
      unfold qualifiedNameTail at parsed
      split at parsed
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at parsed
        | reject failure rejected => simp [dotResult] at parsed
        | ok dot afterDot =>
            simp only [dotResult] at parsed
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at parsed
            | reject failure rejected => simp [componentResult] at parsed
            | ok component afterComponent =>
                simp only [componentResult] at parsed
                have afterComponentFree := inductionHypothesis component
                  (component :: tailRev) afterComponent value next parsed
                    diagnosticFree
                have afterDotFree :=
                  identifier_reflectsDiagnosticFreeOnSuccess context afterDot
                    component afterComponent componentResult afterComponentFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .dot context input
                  dot afterDot dotResult afterDotFree
      · unfold finishQualifiedName at parsed
        cases parsed
        exact diagnosticFree

private theorem qualifiedName_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) (phase : ParserPhase) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (qualifiedName context phase) := by
  intro input value next parsed diagnosticFree
  unfold qualifiedName at parsed
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at parsed
  | reject failure rejected => simp [firstResult] at parsed
  | ok first afterFirst =>
      simp only [firstResult] at parsed
      have afterFirstFree :=
        qualifiedNameTail_reflectsDiagnosticFreeOnSuccess context phase first
          (afterFirst.remainingCount + 1) first [] afterFirst value next parsed
            diagnosticFree
      exact identifier_reflectsDiagnosticFreeOnSuccess context input first
        afterFirst firstResult afterFirstFree

private theorem requireNonempty_reflectsDiagnosticFreeOnSuccess
    {alpha : Type} (parsed : DelimitedList alpha) (phase : ParserPhase) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requireNonempty parsed phase) := by
  unfold requireNonempty
  cases parsed.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail =>
      exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseNamedTypeArguments_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimited_reflectsDiagnosticFreeOnSuccess .less .greater false nested
        .typeExpr .typeExpr nestedReflects)
    intro parsed
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (requireNonempty_reflectsDiagnosticFreeOnSuccess parsed .typeExpr)
    intro nonempty
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

private theorem finishNamedType_reflectsDiagnosticFreeOnSuccess
    (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (finishNamedType name arguments) := by
  unfold finishNamedType
  dsimp only
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseNamedType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (qualifiedName_reflectsDiagnosticFreeOnSuccess .typeExpr .typeExpr)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (parseNamedTypeArguments_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects)
  intro arguments
  exact finishNamedType_reflectsDiagnosticFreeOnSuccess name arguments

private theorem parseMappingType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseMappingType nested) := by
  unfold parseMappingType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .mapping .typeExpr)
  intro mapping
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .leftParen .typeExpr)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess nestedReflects
  intro key
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .fatArrow .typeExpr)
  intro arrow
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess nestedReflects
  intro value
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .typeExpr)
  intro closing
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseComptimeType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseComptimeType nested) := by
  unfold parseComptimeType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .comptime .typeExpr)
  intro comptime
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .less .typeExpr)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess nestedReflects
  intro inner
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .greater .typeExpr)
  intro closing
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseProxyType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseProxyType nested) := by
  intro input value next parsed diagnosticFree
  unfold parseProxyType at parsed
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp [markerResult] at parsed
  | reject failure rejected => simp [markerResult] at parsed
  | ok marker afterMarker =>
      simp only [markerResult] at parsed
      cases innerResult : nested afterMarker with
      | invariant error => simp [innerResult] at parsed
      | reject failure rejected => simp [innerResult] at parsed
      | ok inner afterInner =>
          simp only [innerResult] at parsed
          cases parsed
          have afterMarkerFree := nestedReflects afterMarker inner next
            innerResult diagnosticFree
          exact symbol_reflectsDiagnosticFreeOnSuccess .at .typeExpr input
            marker afterMarker markerResult afterMarkerFree

private theorem parseTupleType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseTupleType nested) := by
  unfold parseTupleType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
      nested .typeExpr .typeExpr nestedReflects)
  intro tuple
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseFunctionReturns_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (TypeFunctionInternals.parseFunctionReturns nested) := by
  unfold TypeFunctionInternals.parseFunctionReturns
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (contextual_reflectsDiagnosticFreeOnSuccess .returns .typeExpr)
    intro returnsKeyword
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
        nested .typeExpr .typeExpr nestedReflects)
    intro values
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

private theorem parseFunctionType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseFunctionType nested) := by
  unfold parseFunctionType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .functionKw .typeExpr)
  intro functionKeyword
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
      nested .typeExpr .typeExpr nestedReflects)
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (parseFunctionReturns_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects)
  intro returns
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- A diagnostic-free successful bounded type parse had a diagnostic-free input. -/
theorem typeExprWithFuel_reflectsDiagnosticFreeOnSuccess :
    ∀ fuel,
      Parser.ReflectsDiagnosticFreeOnSuccess (typeExprWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input value next parsed diagnosticFree
      simp [typeExprWithFuel] at parsed
  | succ fuel inductionHypothesis =>
      intro input value next parsed diagnosticFree
      simp only [typeExprWithFuel] at parsed
      split at parsed
      · exact parseFunctionType_reflectsDiagnosticFreeOnSuccess
          (typeExprWithFuel fuel) inductionHypothesis input value next parsed
            diagnosticFree
      · split at parsed
        · exact parseComptimeType_reflectsDiagnosticFreeOnSuccess
            (typeExprWithFuel fuel) inductionHypothesis input value next parsed
              diagnosticFree
        · split at parsed
          · exact parseMappingType_reflectsDiagnosticFreeOnSuccess
              (typeExprWithFuel fuel) inductionHypothesis input value next parsed
                diagnosticFree
          · split at parsed
            · exact parseProxyType_reflectsDiagnosticFreeOnSuccess
                (typeExprWithFuel fuel) inductionHypothesis input value next
                  parsed diagnosticFree
            · split at parsed
              · exact parseTupleType_reflectsDiagnosticFreeOnSuccess
                  (typeExprWithFuel fuel) inductionHypothesis input value next
                    parsed diagnosticFree
              · split at parsed
                · exact parseNamedType_reflectsDiagnosticFreeOnSuccess
                    (typeExprWithFuel fuel) inductionHypothesis input value next
                      parsed diagnosticFree
                · unfold rejectAt at parsed
                  contradiction

/-- A diagnostic-free successful public type parse had a diagnostic-free input. -/
theorem typeExpr_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess typeExpr := by
  intro input value next parsed diagnosticFree
  unfold typeExpr at parsed
  exact typeExprWithFuel_reflectsDiagnosticFreeOnSuccess
    (input.remainingCount + 1) input value next parsed diagnosticFree

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeDelimitedSoundnessProperties
/-! Adapters from generic delimiter grammar to recursive type grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Generic recursive type tails embed in the concrete mutual type grammar. -/
theorem typeExprTrailingDelimitedTailParses_of_generic
    {closing : Symbol} {input output : DeclarativeGrammar.Remainder}
    {elements : List TypeExpr} {closingSpan : SourceSpan}
    (parsed : DeclarativeGrammar.TrailingDelimitedTailParses closing
      DeclarativeGrammar.TypeExprParses input elements closingSpan output) :
    DeclarativeGrammar.TypeExprTrailingDelimitedTailParses closing input
      elements closingSpan output := by
  induction parsed with
  | close commaAbsent closingToken =>
      exact .close commaAbsent closingToken
  | trailing commaToken closingToken =>
      exact .trailing commaToken closingToken
  | next commaToken closingAbsent elementParsed progress tail
      inductionHypothesis =>
      exact .next commaToken closingAbsent progress rfl elementParsed
        inductionHypothesis

/-- Generic possibly-empty type lists embed in the concrete mutual grammar. -/
theorem typeExprTrailingDelimitedListParses_of_generic
    {opening closing : Symbol}
    {input output : DeclarativeGrammar.Remainder}
    {values : DelimitedList TypeExpr}
    (parsed : DeclarativeGrammar.TrailingDelimitedListParses opening closing
      DeclarativeGrammar.TypeExprParses input values output) :
    DeclarativeGrammar.TypeExprTrailingDelimitedListParses opening closing
      input values output := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact .empty openingSpan closingSpan rfl rfl openingToken closingToken
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact .nonempty openingSpan closingSpan closingAbsent openingToken
        progress tokensEq endIndexEq elementsEq spanEq firstParsed
        (typeExprTrailingDelimitedTailParses_of_generic tail)

/-- A generic nonempty angle list supplies present named-type arguments. -/
theorem optionalNamedTypeArguments_present_of_nonemptyTrailing
    {input output : DeclarativeGrammar.Remainder}
    {arguments : NonemptyDelimitedList TypeExpr}
    (parsed : DeclarativeGrammar.NonemptyTrailingDelimitedListParses
      .less .greater DeclarativeGrammar.TypeExprParses input {
        span := arguments.span
        elements := arguments.elements.toList
      } output) :
    DeclarativeGrammar.OptionalNamedTypeArgumentsParses input
      (some arguments) output := by
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact .present openingSpan closingSpan openingToken progress tokensEq
    endIndexEq elementsEq spanEq firstParsed
    (typeExprTrailingDelimitedTailParses_of_generic tail)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeSimpleSoundnessProperties
/-! Success soundness for comptime, proxy, and tuple type parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {α β : Type} {first : Parser α}
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

/-- Successful comptime parsing follows the exact recursive type grammar. -/
theorem parseComptimeType_success_sound (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {value : TypeExpr}
    (result : parseComptimeType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseComptimeType at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases bind_ok_components rest with
    ⟨inner, afterInner, innerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact .comptime marker.span opening.span closing.span
    (contextual_success_exactTokenParses .comptime .typeExpr markerResult)
    (symbol_success_exactTokenParses .less .typeExpr openingResult)
    (symbol_success_exactTokenParses .greater .typeExpr closingResult)
    rfl (nestedSound innerResult)

/-- Successful proxy parsing follows the exact recursive type grammar. -/
theorem parseProxyType_success_sound (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {value : TypeExpr}
    (result : parseProxyType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseProxyType at result
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases innerResult : nested afterMarker with
      | invariant error => simp [innerResult] at result
      | reject failure rejected => simp [innerResult] at result
      | ok inner final =>
          simp only [innerResult] at result
          cases result
          exact .proxy marker.span
            (symbol_success_exactTokenParses .at .typeExpr markerResult)
            rfl (nestedSound innerResult)

/-- Successful tuple parsing follows the exact recursive type grammar. -/
theorem parseTupleType_success_sound (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : TypeExpr}
    (result : parseTupleType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseTupleType at result
  rcases bind_ok_components result with
    ⟨values, afterValues, valuesResult, finished⟩
  cases finished
  have generic := delimited_allowEmpty_trailing_success_sound
    .leftParen .rightParen nested DeclarativeGrammar.TypeExprParses
    .typeExpr .typeExpr nestedSound nestedShape valuesResult
  exact .tuple rfl
    (typeExprTrailingDelimitedListParses_of_generic generic)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeFunctionSoundnessProperties
/-! Success soundness for recursive function types and their return suffix. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem typeFunctionBind_success_components {α β : Type}
    {first : Parser α} {nextParser : α → Parser β}
    {input final : State} {value : β}
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

/-- Optional function returns retain their exact marker and recursive list. -/
theorem TypeFunctionInternals.parseFunctionReturns_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {returns : Option (DelimitedList TypeExpr)}
    (result : TypeFunctionInternals.parseFunctionReturns nested input =
      .ok returns next) :
    DeclarativeGrammar.OptionalFunctionTypeReturnsParses
      input.declarativeRemainder returns next.declarativeRemainder := by
  unfold TypeFunctionInternals.parseFunctionReturns getState at result
  simp only [bind] at result
  split at result
  next hasReturns =>
    rcases typeFunctionBind_success_components result with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases typeFunctionBind_success_components rest with
      ⟨values, afterValues, valuesResult, finished⟩
    cases finished
    have markerGrammar := contextual_success_exactTokenParses
      .returns .typeExpr markerResult
    have valuesGeneric := delimited_allowEmpty_trailing_success_sound
      .leftParen .rightParen nested DeclarativeGrammar.TypeExprParses
      .typeExpr .typeExpr nestedSound nestedShape valuesResult
    exact .present marker.span markerGrammar
      (typeExprTrailingDelimitedListParses_of_generic valuesGeneric)
  next noReturns =>
    cases result
    exact .absent (by
      simpa only [State.declarativeRemainder] using
        contextualAbsentAt_of_isContextual_eq_false .returns
          (Bool.eq_false_iff.mpr noReturns))

/-- Every successful function-type parse follows the recursive type grammar. -/
theorem parseFunctionType_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : TypeExpr}
    (result : parseFunctionType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseFunctionType at result
  rcases typeFunctionBind_success_components result with
    ⟨keywordToken, afterKeyword, keywordResult, rest⟩
  rcases typeFunctionBind_success_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases typeFunctionBind_success_components rest with
    ⟨returns, afterReturns, returnsResult, finished⟩
  cases finished
  have keywordGrammar := keyword_success_exactTokenParses
    .functionKw .typeExpr keywordResult
  have parametersGeneric := delimited_allowEmpty_trailing_success_sound
    .leftParen .rightParen nested DeclarativeGrammar.TypeExprParses
    .typeExpr .typeExpr nestedSound nestedShape parametersResult
  have parametersGrammar :=
    typeExprTrailingDelimitedListParses_of_generic parametersGeneric
  have returnsGrammar :=
    TypeFunctionInternals.parseFunctionReturns_success_sound nested
      nestedSound nestedShape returnsResult
  exact .function keywordToken.span keywordGrammar rfl parametersGrammar
    returnsGrammar

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.QualifiedNameSoundnessProperties
/-! Success soundness of canonical qualified-name parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem qualifiedNameTail_success_sound
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input name next,
      QualifiedNameInternals.qualifiedNameTail context phase first fuel last
          tailRev input = .ok name next →
      ∃ components,
        name.value.components.head = first ∧
        name.value.components.tail = tailRev.reverse ++ components ∧
        DeclarativeGrammar.DottedIdentifierTailParses input.tokens
          input.window.endIndex input.cursor components next.cursor ∧
        name.span = SourceSpan.cover first.span
          (DeclarativeGrammar.finalIdentifier last components).span ∧
        next.tokens = input.tokens ∧ next.window = input.window := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input name next result
      simp [QualifiedNameInternals.qualifiedNameTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input name next result
      unfold QualifiedNameInternals.qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotSound := symbol_ok_tokenAt .dot context dotResult
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                have componentSound := identifier_ok_tokenAt context
                  componentResult
                simp only [componentResult] at result
                rcases inductionHypothesis component (component :: tailRev)
                    afterComponent name next result with
                  ⟨components, headEq, componentsEq, tailGrammar, spanEq,
                    nextTokens, nextWindow⟩
                have componentToken :
                    DeclarativeGrammar.TokenAt input.tokens
                      input.window.endIndex (input.cursor + 1) {
                        span := component.span
                        value := .identifier component.value
                      } := by
                  simpa only [dotSound.2, State.tokens, State.window,
                    State.cursor] using componentSound.1
                have recursiveTail :
                    DeclarativeGrammar.DottedIdentifierTailParses input.tokens
                      input.window.endIndex (input.cursor + 2) components
                      next.cursor := by
                  simpa only [componentSound.2.1, componentSound.2.2.1,
                    componentSound.2.2.2, dotSound.2, State.tokens,
                    State.window, State.cursor, Nat.add_assoc] using tailGrammar
                refine ⟨component :: components, headEq, ?_,
                  .next dot.span dotSound.1 componentToken recursiveTail,
                  ?_, ?_, ?_⟩
                · calc
                    name.value.components.tail =
                        (component :: tailRev).reverse ++ components :=
                      componentsEq
                    _ = tailRev.reverse ++ (component :: components) := by
                      simp [List.reverse_cons, List.append_assoc]
                · simpa only [DeclarativeGrammar.finalIdentifier] using spanEq
                · exact nextTokens.trans
                    (componentSound.2.1.trans (by rw [dotSound.2]))
                · exact nextWindow.trans
                    (componentSound.2.2.1.trans (by rw [dotSound.2]))
      · have absent : isSymbol input .dot = false :=
          Bool.eq_false_iff.mpr (by assumption)
        have stopped := symbolAbsentAt_of_isSymbol_eq_false .dot
          (input := input) absent
        unfold QualifiedNameInternals.finishQualifiedName at result
        cases result
        exact ⟨[], rfl, by simp,
          .done input.cursor stopped, by simp [DeclarativeGrammar.finalIdentifier],
          rfl, rfl⟩

/-- Every successful qualified-name parse follows the independent token grammar. -/
theorem qualifiedName_success_sound (context : ParseContext)
    (phase : ParserPhase) {input next : State} {name : QualifiedName}
    (result : qualifiedName context phase input = .ok name next) :
    DeclarativeGrammar.QualifiedNameParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      have firstSound := identifier_ok_tokenAt context firstResult
      simp only [firstResult] at result
      rcases qualifiedNameTail_success_sound context phase first
          (afterFirst.remainingCount + 1) first [] afterFirst name next result with
        ⟨components, headEq, componentsEq, tailGrammar, spanEq,
          nextTokens, nextWindow⟩
      have tailEq : name.value.components.tail = components := by
        simpa using componentsEq
      unfold DeclarativeGrammar.QualifiedNameParses
        State.declarativeRemainder
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact nextTokens.trans firstSound.2.1
      · exact congrArg TokenWindow.endIndex
          (nextWindow.trans firstSound.2.2.1)
      · simpa only [headEq] using firstSound.1
      · simpa only [firstSound.2.1, firstSound.2.2.1,
          firstSound.2.2.2, tailEq] using tailGrammar
      · simpa only [headEq, tailEq] using spanEq

/-- Success soundness composes with the established source-provenance contract. -/
theorem qualifiedName_success_sound_and_validFor (context : ParseContext)
    (phase : ParserPhase) {input next : State} {name : QualifiedName}
    (inputValid : input.ValidFor)
    (result : qualifiedName context phase input = .ok name next) :
    DeclarativeGrammar.QualifiedNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      name.ValidFor input.file := by
  refine ⟨qualifiedName_success_sound context phase result, ?_⟩
  have valid := qualifiedName_validFor context phase input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeNamedSoundnessProperties
/-! Success soundness for named type parsing and optional type arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem namedTypeBind_success_components {α β : Type}
    {first : Parser α} {nextParser : α → Parser β}
    {input final : State} {value : β}
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

/-- Requiring nonempty contents preserves state, span, and element order. -/
theorem requireNonempty_success_shape {α : Type}
    {parsed : DelimitedList α} {phase : ParserPhase}
    {input next : State} {nonempty : NonemptyDelimitedList α}
    (result : requireNonempty parsed phase input = .ok nonempty next) :
    next = input ∧ nonempty.span = parsed.span ∧
      nonempty.elements.toList = parsed.elements := by
  unfold requireNonempty at result
  cases elements : parsed.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact ⟨rfl, rfl, by simp [NonemptyList.toList]⟩

/-- Optional named arguments follow their prioritized angle-list grammar. -/
theorem parseNamedTypeArguments_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State}
    {arguments : Option (NonemptyDelimitedList TypeExpr)}
    (result : parseNamedTypeArguments nested input = .ok arguments next) :
    DeclarativeGrammar.OptionalNamedTypeArgumentsParses
      input.declarativeRemainder arguments next.declarativeRemainder := by
  unfold parseNamedTypeArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .less
  · simp only [present, if_true] at result
    rcases namedTypeBind_success_components result with
      ⟨parsed, afterParsed, parsedResult, rest⟩
    rcases namedTypeBind_success_components rest with
      ⟨nonempty, afterNonempty, nonemptyResult, finished⟩
    have parsedGrammar := delimited_nonempty_trailing_success_sound
      .less .greater nested DeclarativeGrammar.TypeExprParses
      .typeExpr .typeExpr nestedSound nestedShape parsedResult
    have shape := requireNonempty_success_shape nonemptyResult
    cases finished
    rw [shape.1]
    apply optionalNamedTypeArguments_present_of_nonemptyTrailing
    simpa only [shape.2.1, shape.2.2] using parsedGrammar
  · have absent : isSymbol input .less = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .less absent)

/-- Finishing a named type changes only its AST and parser diagnostics. -/
theorem finishNamedType_success_shape
    {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList TypeExpr)}
    {input next : State} {value : TypeExpr}
    (result : finishNamedType name arguments input = .ok value next) :
    value = makeNamedType name arguments ∧
      next.declarativeRemainder = input.declarativeRemainder := by
  unfold finishNamedType at result
  dsimp only at result
  split at result
  · unfold emitDiagnostic modifyState at result
    simp only [bind] at result
    cases result
    exact ⟨rfl, by simp [State.emit, State.declarativeRemainder]⟩
  · cases result
    exact ⟨rfl, rfl⟩

/-- Successful named parsing follows its exact prioritized recursive grammar. -/
theorem parseNamedType_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : TypeExpr}
    (comptimeAbsent : DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder .comptime .less)
    (mappingAbsent : DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder .mapping .leftParen)
    (result : parseNamedType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseNamedType at result
  rcases namedTypeBind_success_components result with
    ⟨name, afterName, nameResult, rest⟩
  rcases namedTypeBind_success_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  have nameGrammar := qualifiedName_success_sound .typeExpr .typeExpr
    nameResult
  have argumentsGrammar := parseNamedTypeArguments_success_sound nested
    nestedSound nestedShape argumentsResult
  have finishShape := finishNamedType_success_shape finished
  apply DeclarativeGrammar.TypeExprParses.named comptimeAbsent mappingAbsent
    nameGrammar
  · rw [finishShape.1]
    unfold makeNamedType
    rfl
  · rw [finishShape.2]
    exact argumentsGrammar

/-- Named grammar soundness composes with recursive source validity. -/
theorem parseNamedType_success_sound_and_validFor
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    {input next : State} {value : TypeExpr}
    (inputValid : input.ValidFor)
    (comptimeAbsent : DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder .comptime .less)
    (mappingAbsent : DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder .mapping .leftParen)
    (result : parseNamedType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      TypeExpr.ValidFor input.file value := by
  refine ⟨parseNamedType_success_sound nested nestedSound nestedShape
    comptimeAbsent mappingAbsent result, ?_⟩
  have valid := parseNamedType_validFor nested nestedValid
    nestedShape.preservesTokensOnSuccess input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeExprSoundnessProperties
/-! Aggregate success soundness for recursive type-expression parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextualSymbolPairAbsentAt_of_composite_eq_false
    (keyword : ContextualKeyword) (following : Symbol) {input : State}
    (absent : (isContextual input keyword &&
      (input.peekOffsetKind? 1 == some (.symbol following))) = false) :
    DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder keyword following := by
  rintro ⟨keywordSpan, followingSpan, keywordToken, followingToken⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor {
      span := keywordSpan
      value := .identifier keyword.spelling
    } at keywordToken
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    (input.cursor + 1) {
      span := followingSpan
      value := .symbol following
    } at followingToken
  have keywordPresent : isContextual input keyword = true := by
    unfold isContextual State.peekKind? State.peek?
    simp only [keywordToken.1, ↓reduceIte, keywordToken.2, Option.map_some,
      TokenKind.isContextual]
    exact beq_iff_eq.mpr rfl
  have followingPresent :
      (input.peekOffsetKind? 1 == some (.symbol following)) = true := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [followingToken.1, ↓reduceIte, followingToken.2,
      Option.map_some]
    change instBEqTokenKind.beq (.symbol following)
      (.symbol following) = true
    simp only [instBEqTokenKind.beq]
    change instBEqSymbol.beq following following = true
    unfold instBEqSymbol.beq
    cases following <;> rfl
  rw [keywordPresent, followingPresent] at absent
  contradiction

/-- Every successful fuel-bounded type parse follows the recursive grammar. -/
theorem typeExprWithFuel_success_sound :
    ∀ fuel {input next : State} {value : TypeExpr},
      typeExprWithFuel fuel input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input next value result
      simp [typeExprWithFuel] at result
  | succ fuel inductionHypothesis =>
      intro input next value result
      simp only [typeExprWithFuel] at result
      split at result
      next functionPresent =>
        exact parseFunctionType_success_sound (typeExprWithFuel fuel)
          inductionHypothesis (typeExprWithFuel_preservesTokenWindow fuel)
          result
      next functionAbsent =>
        split at result
        next comptimePresent =>
          exact parseComptimeType_success_sound (typeExprWithFuel fuel)
            inductionHypothesis result
        next comptimeAbsent =>
          split at result
          next mappingPresent =>
            exact parseMappingType_success_sound (typeExprWithFuel fuel)
              inductionHypothesis result
          next mappingAbsent =>
            split at result
            next proxyPresent =>
              exact parseProxyType_success_sound (typeExprWithFuel fuel)
                inductionHypothesis result
            next proxyAbsent =>
              split at result
              next tuplePresent =>
                exact parseTupleType_success_sound (typeExprWithFuel fuel)
                  inductionHypothesis
                  (typeExprWithFuel_preservesTokenWindow fuel) result
              next tupleAbsent =>
                split at result
                next namedPresent =>
                  have comptimeFalse :
                      (isContextual input .comptime &&
                        (input.peekOffsetKind? 1 ==
                          some (.symbol .less))) = false := by
                    apply Bool.eq_false_iff.mpr
                    change ¬ (isContextual input .comptime &&
                      (input.peekOffsetKind? 1 ==
                        some (.symbol .less))) = true at comptimeAbsent
                    exact comptimeAbsent
                  have mappingFalse :
                      (isContextual input .mapping &&
                        (input.peekOffsetKind? 1 ==
                          some (.symbol .leftParen))) = false := by
                    apply Bool.eq_false_iff.mpr
                    change ¬ (isContextual input .mapping &&
                      (input.peekOffsetKind? 1 ==
                        some (.symbol .leftParen))) = true at mappingAbsent
                    exact mappingAbsent
                  exact parseNamedType_success_sound (typeExprWithFuel fuel)
                    inductionHypothesis
                    (typeExprWithFuel_preservesTokenWindow fuel)
                    (contextualSymbolPairAbsentAt_of_composite_eq_false
                      .comptime .less comptimeFalse)
                    (contextualSymbolPairAbsentAt_of_composite_eq_false
                      .mapping .leftParen mappingFalse)
                    result
                next namedAbsent =>
                  unfold rejectAt at result
                  contradiction

/-- Every successful public type parse follows the recursive grammar. -/
theorem typeExpr_success_sound {input next : State} {value : TypeExpr}
    (result : typeExpr input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold typeExpr at result
  exact typeExprWithFuel_success_sound (input.remainingCount + 1) result

/-- Public type grammar soundness composes with source validity. -/
theorem typeExpr_success_sound_and_validFor {input next : State}
    {value : TypeExpr} (inputValid : input.ValidFor)
    (result : typeExpr input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      TypeExpr.ValidFor input.file value := by
  refine ⟨typeExpr_success_sound result, ?_⟩
  have valid := typeExpr_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
/-! Executable lookahead bridges shared by exact Core-type outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Positive hard-keyword lookahead determines its primitive parse. -/
theorem keyword_eq_ok_of_isKeyword_eq_true (value : HardKeyword)
    (context : ParseContext) {input : State}
    (present : isKeyword input value = true) :
    ∃ token, keyword value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      have accepted : (token.value == .keyword value) = true := by
        simpa using present
      refine ⟨token, ?_⟩
      unfold keyword acceptToken
      simp only [found, accepted, ↓reduceIte]

/-- Positive contextual-word lookahead determines its primitive parse. -/
theorem contextual_eq_ok_of_isContextual_eq_true
    (value : ContextualKeyword) (context : ParseContext) {input : State}
    (present : isContextual input value = true) :
    ∃ token, contextual value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isContextual State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      refine ⟨token, ?_⟩
      unfold contextual acceptToken
      simp only [found, present, ↓reduceIte]

/-- Offset-one symbol lookahead is current lookahead after one exact token. -/
theorem isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true
    (value : Symbol) {input : State}
    (present : (input.peekOffsetKind? 1 == some (.symbol value)) = true) :
    isSymbol { input with cursor := input.cursor + 1 } value = true := by
  have shifted :
      ({ input with cursor := input.cursor + 1 } : State).peekKind? =
        input.peekOffsetKind? 1 := rfl
  unfold isSymbol
  rw [shifted]
  exact present

/-- A failed composite contextual-symbol guard excludes that exact pair. -/
theorem contextualSymbolPairAbsentAt_of_guard_eq_false
    (keywordValue : ContextualKeyword) (following : Symbol) {input : State}
    (absent : (isContextual input keywordValue &&
      (input.peekOffsetKind? 1 == some (.symbol following))) = false) :
    DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder keywordValue following := by
  rintro ⟨keywordSpan, followingSpan, keywordToken, followingToken⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor {
      span := keywordSpan
      value := .identifier keywordValue.spelling
    } at keywordToken
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    (input.cursor + 1) {
      span := followingSpan
      value := .symbol following
    } at followingToken
  have keywordPresent : isContextual input keywordValue = true := by
    unfold isContextual State.peekKind? State.peek?
    simp only [keywordToken.1, ↓reduceIte, keywordToken.2, Option.map_some,
      TokenKind.isContextual]
    exact beq_iff_eq.mpr rfl
  have followingPresent :
      (input.peekOffsetKind? 1 == some (.symbol following)) = true := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [followingToken.1, ↓reduceIte, followingToken.2,
      Option.map_some]
    change instBEqTokenKind.beq (.symbol following)
      (.symbol following) = true
    simp only [instBEqTokenKind.beq]
    change instBEqSymbol.beq following following = true
    unfold instBEqSymbol.beq
    cases following <;> rfl
  rw [keywordPresent, followingPresent] at absent
  contradiction

/-- Failed generic identifier lookahead excludes every identifier spelling. -/
theorem identifierAbsentAt_of_isIdentifier_eq_false {input : State}
    (absent : isIdentifier input = false) :
    DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
  rintro ⟨span, text, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := .identifier text } at token
  unfold isIdentifier State.peekKind? State.peek? at absent
  simp only [token.1, ↓reduceIte, token.2, Option.map_some] at absent
  contradiction

/-- Positive generic identifier lookahead exposes its exact current token. -/
theorem identifierPresentAt_of_isIdentifier_eq_true {input : State}
    (present : isIdentifier input = true) :
    ∃ span text, DeclarativeGrammar.TokenAt input.tokens
      input.window.endIndex input.cursor { span, value := .identifier text } := by
  unfold isIdentifier State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at present
      all_goals try contradiction
      case identifier text =>
        exact ⟨span, text, tokenAt_of_peek?_eq_some found⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTypeSimpleRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for simple recursive Core-type forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A selected `comptime<...>` branch rejects at its nested type or missing
closing angle token. -/
theorem parseComptimeType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isContextual input .comptime = true)
    (followingPresent :
      (input.peekOffsetKind? 1 == some (.symbol .less)) = true)
    (result : parseComptimeType nested input = .reject failure rejected) :
    DeclarativeGrammar.ComptimeTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases contextual_eq_ok_of_isContextual_eq_true .comptime .typeExpr
      markerPresent with ⟨marker, markerResult⟩
  have openingPresent :=
    isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true .less followingPresent
  rcases symbol_eq_ok_of_isSymbol_eq_true .less .typeExpr openingPresent with
    ⟨opening, openingResult⟩
  unfold parseComptimeType at result
  simp only [bind, markerResult, openingResult] at result
  cases innerResult : nested
      { input with cursor := input.cursor + 1 + 1 } with
  | invariant error => simp [innerResult] at result
  | reject innerFailure innerRejected =>
      simp only [innerResult] at result
      cases result
      exact .innerRejected marker.span opening.span
        (contextual_success_exactTokenParses .comptime .typeExpr markerResult)
        (symbol_success_exactTokenParses .less .typeExpr openingResult)
        (nestedRejectSound innerResult)
  | ok inner afterInner =>
      simp only [innerResult] at result
      cases closingResult : symbol .greater .typeExpr afterInner with
      | invariant error => simp [closingResult] at result
      | ok closing afterClosing => simp [closingResult, pure] at result
      | reject closingFailure closingRejected =>
          have rejectedEq := symbol_reject_state_eq .greater .typeExpr
            closingResult
          subst rejectedEq
          simp only [closingResult] at result
          cases result
          exact .closingMissing marker.span opening.span
            (contextual_success_exactTokenParses .comptime .typeExpr
              markerResult)
            (symbol_success_exactTokenParses .less .typeExpr openingResult)
            (nestedSuccessSound innerResult)
            (symbol_reject_tokenKindAbsentAt .greater .typeExpr closingResult)

/-- A selected canonical mapping branch rejects at its key, arrow, value, or
closing parenthesis, in that exact order. -/
theorem parseMappingType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isContextual input .mapping = true)
    (followingPresent :
      (input.peekOffsetKind? 1 == some (.symbol .leftParen)) = true)
    (result : parseMappingType nested input = .reject failure rejected) :
    DeclarativeGrammar.MappingTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases contextual_eq_ok_of_isContextual_eq_true .mapping .typeExpr
      markerPresent with ⟨marker, markerResult⟩
  have openingPresent :=
    isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true .leftParen
      followingPresent
  rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr openingPresent
      with ⟨opening, openingResult⟩
  unfold parseMappingType at result
  simp only [bind, markerResult, openingResult] at result
  cases keyResult : nested { input with cursor := input.cursor + 1 + 1 } with
  | invariant error => simp [keyResult] at result
  | reject keyFailure keyRejected =>
      simp only [keyResult] at result
      cases result
      exact .keyRejected marker.span opening.span
        (contextual_success_exactTokenParses .mapping .typeExpr markerResult)
        (symbol_success_exactTokenParses .leftParen .typeExpr openingResult)
        (nestedRejectSound keyResult)
  | ok key afterKey =>
      simp only [keyResult] at result
      cases arrowResult : symbol .fatArrow .typeExpr afterKey with
      | invariant error => simp [arrowResult] at result
      | reject arrowFailure arrowRejected =>
          have rejectedEq := symbol_reject_state_eq .fatArrow .typeExpr
            arrowResult
          subst rejectedEq
          simp only [arrowResult] at result
          cases result
          exact .arrowMissing marker.span opening.span
            (contextual_success_exactTokenParses .mapping .typeExpr
              markerResult)
            (symbol_success_exactTokenParses .leftParen .typeExpr openingResult)
            (nestedSuccessSound keyResult)
            (symbol_reject_tokenKindAbsentAt .fatArrow .typeExpr arrowResult)
      | ok arrow afterArrow =>
          simp only [arrowResult] at result
          cases valueResult : nested afterArrow with
          | invariant error => simp [valueResult] at result
          | reject valueFailure valueRejected =>
              simp only [valueResult] at result
              cases result
              exact .valueRejected marker.span opening.span arrow.span
                (contextual_success_exactTokenParses .mapping .typeExpr
                  markerResult)
                (symbol_success_exactTokenParses .leftParen .typeExpr
                  openingResult)
                (nestedSuccessSound keyResult)
                (symbol_success_exactTokenParses .fatArrow .typeExpr
                  arrowResult)
                (nestedRejectSound valueResult)
          | ok value afterValue =>
              simp only [valueResult] at result
              cases closingResult : symbol .rightParen .typeExpr afterValue with
              | invariant error => simp [closingResult] at result
              | ok closing afterClosing => simp [closingResult, pure] at result
              | reject closingFailure closingRejected =>
                  have rejectedEq := symbol_reject_state_eq .rightParen
                    .typeExpr closingResult
                  subst rejectedEq
                  simp only [closingResult] at result
                  cases result
                  exact .closingMissing marker.span opening.span arrow.span
                    (contextual_success_exactTokenParses .mapping .typeExpr
                      markerResult)
                    (symbol_success_exactTokenParses .leftParen .typeExpr
                      openingResult)
                    (nestedSuccessSound keyResult)
                    (symbol_success_exactTokenParses .fatArrow .typeExpr
                      arrowResult)
                    (nestedSuccessSound valueResult)
                    (symbol_reject_tokenKindAbsentAt .rightParen .typeExpr
                      closingResult)

/-- A selected proxy type propagates exactly its nested rejection. -/
theorem parseProxyType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isSymbol input .at = true)
    (result : parseProxyType nested input = .reject failure rejected) :
    DeclarativeGrammar.ProxyTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .at .typeExpr markerPresent with
    ⟨marker, markerResult⟩
  unfold parseProxyType at result
  simp only [markerResult] at result
  cases innerResult : nested { input with cursor := input.cursor + 1 } with
  | invariant error => simp [innerResult] at result
  | ok inner afterInner => simp [innerResult] at result
  | reject innerFailure innerRejected =>
      simp only [innerResult] at result
      cases result
      exact .innerRejected marker.span
        (symbol_success_exactTokenParses .at .typeExpr markerResult)
        (nestedRejectSound innerResult)

/-- Tuple rejection is exactly generic allow-empty trailing-list rejection. -/
theorem parseTupleType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (openingPresent : isSymbol input .leftParen = true)
    (result : parseTupleType nested input = .reject failure rejected) :
    DeclarativeGrammar.TupleTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold parseTupleType at result
  cases valuesResult : delimited .leftParen .rightParen true nested
      .typeExpr .typeExpr input with
  | invariant error => simp [bind, valuesResult] at result
  | ok values afterValues => simp [bind, valuesResult, pure] at result
  | reject valuesFailure valuesRejected =>
      simp only [bind, valuesResult] at result
      cases result
      rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr
          openingPresent with ⟨opening, openingResult⟩
      exact .selected opening.span
        (symbol_success_exactTokenParses .leftParen .typeExpr openingResult)
        (delimited_reject_sound .leftParen .rightParen true nested
          DeclarativeGrammar.TypeExprParses nestedRejects .typeExpr .typeExpr
          nestedSuccessSound nestedRejectSound valuesResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreFunctionTypeRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for Core function types. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional function returns can reject only in the delimited return-type
list after the positively guarded contextual marker. -/
theorem TypeFunctionInternals.parseFunctionReturns_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : TypeFunctionInternals.parseFunctionReturns nested input =
      .reject failure rejected) :
    DeclarativeGrammar.FunctionTypeReturnsRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold TypeFunctionInternals.parseFunctionReturns getState at result
  simp only [bind] at result
  split at result
  next markerPresent =>
    rcases contextual_eq_ok_of_isContextual_eq_true .returns .typeExpr
        markerPresent with ⟨marker, markerResult⟩
    simp only [markerResult] at result
    cases valuesResult : delimited .leftParen .rightParen true nested
        .typeExpr .typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [valuesResult] at result
    | ok values afterValues => simp [valuesResult, pure] at result
    | reject valuesFailure valuesRejected =>
        simp only [valuesResult] at result
        cases result
        exact .valuesRejected marker.span
          (contextual_success_exactTokenParses .returns .typeExpr markerResult)
          (delimited_reject_sound .leftParen .rightParen true nested
            DeclarativeGrammar.TypeExprParses nestedRejects .typeExpr .typeExpr
            nestedSuccessSound nestedRejectSound valuesResult)
  next markerAbsent =>
    simp [pure] at result

/-- A selected function-type branch rejects first in its parameter list, then
in its optional returns list after exact ordinary parameter success. -/
theorem parseFunctionType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input rejected : State} {failure : Failure}
    (keywordPresent : isKeyword input .functionKw = true)
    (result : parseFunctionType nested input = .reject failure rejected) :
    DeclarativeGrammar.FunctionTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .typeExpr
      keywordPresent with ⟨keywordToken, keywordResult⟩
  unfold parseFunctionType at result
  simp only [bind, keywordResult] at result
  cases parametersResult : delimited .leftParen .rightParen true nested
      .typeExpr .typeExpr { input with cursor := input.cursor + 1 } with
  | invariant error => simp [parametersResult] at result
  | reject parametersFailure parametersRejected =>
      simp only [parametersResult] at result
      cases result
      exact .parametersRejected keywordToken.span
        (keyword_success_exactTokenParses .functionKw .typeExpr keywordResult)
        (delimited_reject_sound .leftParen .rightParen true nested
          DeclarativeGrammar.TypeExprParses nestedRejects .typeExpr .typeExpr
          nestedSuccessSound nestedRejectSound parametersResult)
  | ok parameters afterParameters =>
      simp only [parametersResult] at result
      cases returnsResult :
          TypeFunctionInternals.parseFunctionReturns nested afterParameters with
      | invariant error => simp [returnsResult] at result
      | ok returns afterReturns => simp [returnsResult, pure] at result
      | reject returnsFailure returnsRejected =>
          simp only [returnsResult] at result
          cases result
          exact .returnsRejected keywordToken.span
            (keyword_success_exactTokenParses .functionKw .typeExpr
              keywordResult)
            (delimited_allowEmpty_trailing_success_sound .leftParen
              .rightParen nested DeclarativeGrammar.TypeExprParses .typeExpr
              .typeExpr nestedSuccessSound nestedShape parametersResult)
            (TypeFunctionInternals.parseFunctionReturns_reject_type_sound
              nested nestedRejects nestedSuccessSound nestedRejectSound
              returnsResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTypeQualifiedNameRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for Core-type qualified names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A rejected dotted-name tail records the first missing component and every
preceding exact dot and identifier. -/
theorem qualifiedNameTail_reject_type_sound
    (context : ParseContext) (phase : ParserPhase)
    (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      QualifiedNameInternals.qualifiedNameTail context phase first fuel last
          tailRev input = .reject failure rejected →
        DeclarativeGrammar.TypeQualifiedNameTailRejects
          input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input failure rejected result
      simp [QualifiedNameInternals.qualifiedNameTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input failure rejected result
      unfold QualifiedNameInternals.qualifiedNameTail at result
      split at result
      next dotPresent =>
        cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject dotFailure dotRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .dot context dotPresent with
              ⟨dot, parsed⟩
            rw [parsed] at dotResult
            contradiction
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject componentFailure componentRejected =>
                simp only [componentResult] at result
                cases result
                exact .componentRejected dot.span
                  (symbol_success_exactTokenParses .dot context dotResult)
                  (identifier_reject_sound context componentResult)
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact .laterRejected dot.span
                  (symbol_success_exactTokenParses .dot context dotResult)
                  (identifier_success_sound context componentResult)
                  (inductionHypothesis component (component :: tailRev)
                    afterComponent failure rejected result)
      next dotAbsent =>
        unfold QualifiedNameInternals.finishQualifiedName at result
        contradiction

/-- A rejected qualified name either lacks its first identifier or rejects at
the exact missing dotted component. -/
theorem qualifiedName_reject_type_sound
    (context : ParseContext) (phase : ParserPhase)
    {input rejected : State} {failure : Failure}
    (result : qualifiedName context phase input = .reject failure rejected) :
    DeclarativeGrammar.TypeQualifiedNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected (identifier_reject_sound context firstResult)
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .tailRejected (identifier_success_sound context firstResult)
        (qualifiedNameTail_reject_type_sound context phase first
          (afterFirst.remainingCount + 1) first [] afterFirst failure rejected
          result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTypeNamedRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for named Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional named-type arguments reject only inside the selected nonempty
angle-list parser. -/
theorem parseNamedTypeArguments_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : parseNamedTypeArguments nested input =
      .reject failure rejected) :
    DeclarativeGrammar.NamedTypeArgumentsRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold parseNamedTypeArguments getState at result
  simp only [bind] at result
  split at result
  next argumentsPresent =>
    rcases symbol_eq_ok_of_isSymbol_eq_true .less .typeExpr argumentsPresent
      with ⟨opening, openingResult⟩
    cases valuesResult : delimited .less .greater false nested
        .typeExpr .typeExpr input with
    | invariant error => simp [valuesResult] at result
    | reject valuesFailure valuesRejected =>
        simp only [valuesResult] at result
        cases result
        exact .selected opening.span
          (symbol_success_exactTokenParses .less .typeExpr openingResult)
          (delimited_reject_sound .less .greater false nested
            DeclarativeGrammar.TypeExprParses nestedRejects .typeExpr .typeExpr
            nestedSuccessSound nestedRejectSound valuesResult)
    | ok values afterValues =>
        simp only [valuesResult] at result
        unfold requireNonempty at result
        cases elements : values.elements <;> simp [elements, pure] at result
  next argumentsAbsent =>
    simp [pure] at result

/-- A named-type rejection records either the missing qualified-name component
or the exact rejected generic-argument list.  Canonical-`mapping` spelling
diagnostics occur only after successful arguments and therefore remain
ordinary successes, not rejection constructors. -/
theorem parseNamedType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : parseNamedType nested input = .reject failure rejected) :
    DeclarativeGrammar.NamedTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold parseNamedType at result
  cases nameResult : qualifiedName .typeExpr .typeExpr input with
  | invariant error => simp [bind, nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [bind, nameResult] at result
      cases result
      exact .nameRejected
        (qualifiedName_reject_type_sound .typeExpr .typeExpr nameResult)
  | ok name afterName =>
      simp only [bind, nameResult] at result
      cases argumentsResult : parseNamedTypeArguments nested afterName with
      | invariant error => simp [argumentsResult] at result
      | reject argumentsFailure argumentsRejected =>
          simp only [argumentsResult] at result
          cases result
          exact .argumentsRejected
            (qualifiedName_success_sound .typeExpr .typeExpr nameResult)
            (parseNamedTypeArguments_reject_type_sound nested nestedRejects
              nestedSuccessSound nestedRejectSound argumentsResult)
      | ok arguments afterArguments =>
          simp only [argumentsResult] at result
          unfold finishNamedType emitDiagnostic modifyState at result
          simp only [bind] at result
          split at result <;> contradiction

end Solcore.Syntax.Parser
end
