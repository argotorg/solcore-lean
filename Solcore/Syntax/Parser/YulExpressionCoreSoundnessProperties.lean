import Solcore.Syntax.Parser.YulCallArgumentsSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionLeafSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionLookaheadProperties
import Solcore.Syntax.Parser.YulExpressionRecoveryDiagnosticProperties

/-!
Diagnostic reflection and exact diagnostic-free soundness for the ordered
non-recovering inline-Yul expression layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The non-recovering Yul expression layer reflects diagnostic freedom
through literal, name/arguments, and forbidden-meta branches. -/
theorem yulExpressionCore_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulExpressionCore nested) := by
  intro input expression next result diagnosticFree
  unfold yulExpressionCore at result
  split at result
  · cases literalResult : yulLiteral input with
    | invariant error => simp [literalResult] at result
    | reject failure rejected => simp [literalResult] at result
    | ok literal afterLiteral =>
        simp only [literalResult] at result
        cases result
        exact yulLiteral_reflectsDiagnosticFreeOnSuccess input literal next
          literalResult diagnosticFree
  · split at result
    · cases nameResult : yulName input with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              have afterNameFree :=
                optionalYulCallArguments_reflectsDiagnosticFreeOnSuccess
                  nested nestedReflects afterName arguments afterArguments
                    argumentsResult (by
                      cases arguments <;> cases result
                      all_goals exact diagnosticFree)
              exact yulName_reflectsDiagnosticFreeOnSuccess input name
                afterName nameResult afterNameFree
    · split at result <;> try {
          exact rejectedMeta_reflectsDiagnosticFreeOnSuccess input expression
            next result diagnosticFree }
      unfold rejectAt at result
      contradiction

private theorem yulNamedExpression_success_sound
    (nested : Parser YulExpr)
    (nestedParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback : DeclarativeGrammar.YulCallArgumentsFallbackSpec nestedParses)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (rejectSound : ∀ {input failed : State} {failure : Failure},
      delimited .leftParen .rightParen true nested .yulExpression .yul input =
          .reject failure failed →
        fallback.rejects input.declarativeRemainder)
    {input afterName next : State} {name : YulIdentifier}
    {arguments : Option (DelimitedList YulExpr)}
    (diagnosticFree : next.diagnosticsRev = [])
    (nameResult : yulName input = .ok name afterName)
    (argumentsResult : optionalYulCallArguments nested afterName =
      .ok arguments next) :
    ∃ expression,
      (match arguments with
        | none => expression = {
            span := name.span
            value := .identifier name
          }
        | some values => expression = {
            span := SourceSpan.cover name.span values.span
            value := .call name values
          }) ∧
      DeclarativeGrammar.YulNamedExpressionParses nestedParses fallback
        input.declarativeRemainder expression next.declarativeRemainder := by
  have afterNameFree :=
    optionalYulCallArguments_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects afterName arguments next argumentsResult diagnosticFree
  have nameGrammar := yulName_success_sound_of_diagnosticFree afterNameFree
    nameResult
  have argumentsGrammar := optionalYulCallArguments_success_sound nested
    nestedParses fallback nestedReflects nestedSound nestedShape rejectSound
      diagnosticFree argumentsResult
  cases arguments with
  | none =>
      exact ⟨_, rfl, .identifier nameGrammar argumentsGrammar⟩
  | some values =>
      exact ⟨_, rfl, .call nameGrammar argumentsGrammar⟩

/-- Every diagnostic-free `yulExpressionCore` success follows the exact
literal-before-name declarative grammar. Forbidden meta syntax is excluded by
its mandatory constraint diagnostic. -/
theorem yulExpressionCore_success_sound
    (nested : Parser YulExpr)
    (nestedParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback : DeclarativeGrammar.YulCallArgumentsFallbackSpec nestedParses)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : YulExpr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (rejectSound : ∀ {input failed : State} {failure : Failure},
      delimited .leftParen .rightParen true nested .yulExpression .yul input =
          .reject failure failed →
        fallback.rejects input.declarativeRemainder)
    {input next : State} {expression : YulExpr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulExpressionCore nested input = .ok expression next) :
    DeclarativeGrammar.YulExpressionCoreParses nestedParses fallback
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold yulExpressionCore at result
  split at result
  next literalPresent =>
    cases literalResult : yulLiteral input with
    | invariant error => simp [literalResult] at result
    | reject failure rejected => simp [literalResult] at result
    | ok literal afterLiteral =>
        simp only [literalResult] at result
        cases result
        exact .literal (yulLiteral_success_sound literalResult)
  next literalAbsent =>
    have literalAbsentEq : startsYulLiteral input = false :=
      Bool.eq_false_iff.mpr literalAbsent
    have noLiteral :=
      not_yulLiteralStartsAt_of_startsYulLiteral_eq_false literalAbsentEq
    split at result
    next namePresent =>
      cases nameResult : yulName input with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              cases arguments with
              | none =>
                  cases result
                  rcases yulNamedExpression_success_sound nested nestedParses
                      fallback nestedReflects nestedSound nestedShape
                      rejectSound diagnosticFree nameResult argumentsResult with
                    ⟨named, namedEq, namedGrammar⟩
                  cases namedEq
                  exact .named noLiteral namedGrammar
              | some values =>
                  cases result
                  rcases yulNamedExpression_success_sound nested nestedParses
                      fallback nestedReflects nestedSound nestedShape
                      rejectSound diagnosticFree nameResult argumentsResult with
                    ⟨named, namedEq, namedGrammar⟩
                  cases namedEq
                  exact .named noLiteral namedGrammar
    next nameAbsent =>
      split at result <;> try {
          exact False.elim
            (rejectedMeta_diagnostics_ne_nil_onSuccess result diagnosticFree) }
      unfold rejectAt at result
      contradiction

end Solcore.Syntax.Parser
