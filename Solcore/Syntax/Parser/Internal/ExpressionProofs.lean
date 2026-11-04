import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Terms
import Solcore.Syntax.ValidityBasics
import Solcore.Syntax.Validity

/-!
Proofs about the parsers of whole expressions, names and leading-dot constructors:
token-window and cursor laws, source validity, soundness against the declarative grammar,
and exact outcomes.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLiteralSoundnessProperties
/-! Diagnostic reflection and declarative soundness for Core literal leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Core-literal success never removes an earlier diagnostic. -/
theorem coreLiteral_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess coreLiteral := by
  intro input literal next result diagnosticFree
  rw [coreLiteral_ok_state_shape result] at diagnosticFree
  exact diagnosticFree

/-- Boolean-identifier success never removes an earlier diagnostic. -/
theorem booleanIdentifier_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess booleanIdentifier := by
  intro input name next result diagnosticFree
  rw [booleanIdentifier_ok_state_shape result] at diagnosticFree
  exact diagnosticFree

/-- Every successful Core literal is the exact current literal token. -/
theorem coreLiteral_success_sound {input next : State}
    {literal : CoreLiteral}
    (result : coreLiteral input = .ok literal next) :
    DeclarativeGrammar.CoreLiteralParses input.declarativeRemainder literal
      next.declarativeRemainder := by
  unfold coreLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case decimalLiteral spelling =>
        cases result
        exact .decimal (tokenAt_of_peek?_eq_some found)
      case hexadecimalLiteral spelling =>
        cases result
        exact .hexadecimal (tokenAt_of_peek?_eq_some found)
      case stringLiteral spelling =>
        cases result
        exact .string (tokenAt_of_peek?_eq_some found)

/-- Every successful Boolean builtin name is its exact keyword token. -/
theorem booleanIdentifier_success_sound {input next : State}
    {name : Identifier}
    (result : booleanIdentifier input = .ok name next) :
    DeclarativeGrammar.BooleanIdentifierParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold booleanIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case trueKw =>
          cases result
          exact .trueKeyword (tokenAt_of_peek?_eq_some found)
        case falseKw =>
          cases result
          exact .falseKeyword (tokenAt_of_peek?_eq_some found)

namespace ExpressionAtomInternals

/-- Expression-name success reflects diagnostic freedom through its branch. -/
theorem expressionName_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess expressionName := by
  intro input name next result diagnosticFree
  unfold expressionName at result
  split at result
  · exact booleanIdentifier_reflectsDiagnosticFreeOnSuccess input name next
      result diagnosticFree
  · exact identifier_reflectsDiagnosticFreeOnSuccess .expression input name
      next result diagnosticFree

end ExpressionAtomInternals

/--
Every successful expression name follows the Boolean-first ordered grammar.
-/
theorem expressionName_success_sound {input next : State}
    {name : Identifier}
    (result : ExpressionAtomInternals.expressionName input = .ok name next) :
    DeclarativeGrammar.ExpressionNameParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold ExpressionAtomInternals.expressionName at result
  split at result
  · exact .boolean (booleanIdentifier_success_sound result)
  · have booleanAbsent : isBooleanValue input = false :=
      Bool.eq_false_iff.mpr (by assumption)
    have absences :
        isKeyword input .trueKw = false ∧
          isKeyword input .falseKw = false := by
      exact Bool.or_eq_false_iff.mp (by
        simpa only [isBooleanValue] using booleanAbsent)
    exact .identifier
      (keywordAbsentAt_of_isKeyword_eq_false .trueKw absences.1)
      (keywordAbsentAt_of_isKeyword_eq_false .falseKw absences.2)
      (identifier_success_sound .expression result)

/-- Core-literal grammar soundness composes with source provenance. -/
theorem coreLiteral_success_sound_and_validFor {input next : State}
    {literal : CoreLiteral} (inputValid : input.ValidFor)
    (result : coreLiteral input = .ok literal next) :
    DeclarativeGrammar.CoreLiteralParses input.declarativeRemainder literal
        next.declarativeRemainder ∧
      Located.ValidFor input.file literal := by
  refine ⟨coreLiteral_success_sound result, ?_⟩
  have valid := coreLiteral_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Boolean-name grammar soundness composes with source provenance. -/
theorem booleanIdentifier_success_sound_and_validFor {input next : State}
    {name : Identifier} (inputValid : input.ValidFor)
    (result : booleanIdentifier input = .ok name next) :
    DeclarativeGrammar.BooleanIdentifierParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      Located.ValidFor input.file name := by
  refine ⟨booleanIdentifier_success_sound result, ?_⟩
  have valid := booleanIdentifier_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Expression-name grammar soundness composes with source provenance. -/
theorem expressionName_success_sound_and_validFor {input next : State}
    {name : Identifier} (inputValid : input.ValidFor)
    (result : ExpressionAtomInternals.expressionName input = .ok name next) :
    DeclarativeGrammar.ExpressionNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      Located.ValidFor input.file name := by
  refine ⟨expressionName_success_sound result, ?_⟩
  have valid := ExpressionAtomInternals.expressionName_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionNameOutcomeSoundnessProperties
/-! Exact executable ordinary outcomes for one Boolean-first Core name. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem booleanIdentifier_ne_reject_of_isBooleanValue
    {input rejected : State} {failure : Failure}
    (starts : isBooleanValue input = true)
    (result : booleanIdentifier input = .reject failure rejected) : False := by
  unfold isBooleanValue isKeyword State.peekKind? at starts
  unfold booleanIdentifier at result
  cases found : input.peek? with
  | none => simp [found] at starts
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at starts result
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at starts result
        all_goals try { contradiction }

/-- Every executable expression-name rejection is the exact identifier-token
absence branch after both Boolean guards fail. -/
theorem expressionName_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : expressionName input = .reject failure rejected) :
    DeclarativeGrammar.ExpressionNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold expressionName at result
  by_cases starts : isBooleanValue input = true
  · simp only [starts, if_true] at result
    exact False.elim
      (booleanIdentifier_ne_reject_of_isBooleanValue starts result)
  · have startsFalse : isBooleanValue input = false :=
      Bool.eq_false_iff.mpr starts
    simp only [startsFalse, Bool.false_eq_true, if_false] at result
    have rejectedEq := identifier_reject_state_eq .expression result
    subst rejected
    have booleanAbsences :
        isKeyword input .trueKw = false ∧
          isKeyword input .falseKw = false :=
      Bool.or_eq_false_iff.mp (by
        simpa only [isBooleanValue] using startsFalse)
    exact .absent ⟨
      keywordAbsentAt_of_isKeyword_eq_false .trueKw booleanAbsences.1,
      keywordAbsentAt_of_isKeyword_eq_false .falseKw booleanAbsences.2,
      identifier_reject_identifierAbsentAt .expression result⟩

/-- Package the existing unconditional success bridge with exact rejection. -/
theorem expressionName_ordinaryOutcome_sound :
    (∀ {input output : State} {name : Identifier},
      expressionName input = .ok name output →
        DeclarativeGrammar.ExpressionNameOrdinaryParses
          input.declarativeRemainder name output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionName input = .reject failure rejected →
        DeclarativeGrammar.ExpressionNameRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨expressionName_success_sound, expressionName_reject_ordinary_sound⟩

/-- Re-export the deterministic expression-name outcome at its executable
boundary. -/
theorem expressionName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExpressionNameOrdinaryParses
      DeclarativeGrammar.ExpressionNameRejects :=
  DeclarativeGrammar.expressionNameDeterministicOutcomeSpec

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionDotConstructorSoundnessProperties
/-!
Diagnostic reflection and exact declarative soundness for leading-dot Core
expression constructors.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

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

/-- Optional leading-dot arguments reflect through every nested element. -/
theorem optionalDotConstructorArguments_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalDotConstructorArguments nested) := by
  unfold optionalDotConstructorArguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
        .leftParen .rightParen true nested .expression .expression
          nestedReflects)
    intro arguments
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- Leading-dot construction reflects through its name and arguments. -/
theorem dotConstructor_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (dotConstructor nested) := by
  unfold dotConstructor
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .dot .expression)
  intro dot
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    expressionName_reflectsDiagnosticFreeOnSuccess
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalDotConstructorArguments_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects)
  intro arguments
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/--
Diagnostic-free optional arguments preserve opening-token priority and the
exact no-trailing delimited grammar.
-/
theorem optionalDotConstructorArguments_success_sound
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {arguments : Option (DelimitedList Expr)}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalDotConstructorArguments nested input =
      .ok arguments next) :
    DeclarativeGrammar.OptionalDotConstructorArgumentsParses nestedParses
      input.declarativeRemainder arguments next.declarativeRemainder := by
  unfold optionalDotConstructorArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases argumentsResult : delimitedNoTrailing .leftParen .rightParen true
        nested .expression .expression input with
    | invariant error => simp [argumentsResult] at result
    | reject failure rejected => simp [argumentsResult] at result
    | ok values afterArguments =>
        simp only [argumentsResult, pure] at result
        cases result
        exact .present
          (delimitedNoTrailing_allowEmpty_success_sound_of_diagnosticFree
            .leftParen .rightParen nested nestedParses .expression .expression
            nestedSound nestedReflects nestedShape diagnosticFree
            argumentsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

/--
Every diagnostic-free leading-dot constructor success retains its exact dot,
Boolean-first name, optional arguments, span, AST, and final remainder.
-/
theorem dotConstructor_success_sound
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {expression : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : dotConstructor nested input = .ok expression next) :
    DeclarativeGrammar.DotConstructorParses nestedParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold dotConstructor at result
  rcases bind_ok_components result with
    ⟨dot, afterDot, dotResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  have argumentsGrammar := optionalDotConstructorArguments_success_sound
    nested nestedParses nestedReflects nestedSound nestedShape diagnosticFree
      argumentsResult
  exact .parsed dot.span
    (symbol_success_exactTokenParses .dot .expression dotResult)
    (expressionName_success_sound nameResult) argumentsGrammar

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionDotConstructorArgumentsOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for optional leading-dot arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every optional-argument success takes exactly the absent branch or the
committed allow-empty, no-trailing parenthesized branch. -/
theorem optionalDotConstructorArguments_success_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State}
    {arguments : Option (DelimitedList Expr)}
    (result : optionalDotConstructorArguments nested input =
      .ok arguments output) :
    DeclarativeGrammar.OptionalDotConstructorArgumentsOrdinaryParses
      nestedOrdinary input.declarativeRemainder arguments
        output.declarativeRemainder := by
  unfold optionalDotConstructorArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases argumentsResult :
        delimitedNoTrailing .leftParen .rightParen true nested .expression
          .expression input with
    | invariant error => simp [argumentsResult] at result
    | reject failure rejected => simp [argumentsResult] at result
    | ok values afterArguments =>
        simp only [argumentsResult, pure] at result
        cases result
        exact .present
          (delimitedNoTrailing_allowEmpty_success_sound .leftParen
            .rightParen nested nestedOrdinary .expression .expression
              nestedSuccessSound nestedShape argumentsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

/-- Every optional-argument rejection occurs only after a positive opening
guard and carries the exact delimited-list rejection trace. -/
theorem optionalDotConstructorArguments_reject_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalDotConstructorArguments nested input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalDotConstructorArgumentsRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalDotConstructorArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases argumentsResult :
        delimitedNoTrailing .leftParen .rightParen true nested .expression
          .expression input with
    | invariant error => simp [argumentsResult] at result
    | ok values afterArguments => simp [argumentsResult, pure] at result
    | reject argumentsFailure argumentsRejected =>
        simp only [argumentsResult] at result
        cases result
        rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression present
          with ⟨opening, openingResult⟩
        exact .present opening.span
          (symbol_success_exactTokenParses .leftParen .expression
            openingResult).1
          (delimitedNoTrailing_reject_sound .leftParen .rightParen true
            nested nestedOrdinary nestedRejects .expression .expression
              nestedSuccessSound nestedRejectSound argumentsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package the executable optional-argument ordinary outcome. -/
theorem optionalDotConstructorArguments_ordinaryOutcome_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    (∀ {input output : State}
      {arguments : Option (DelimitedList Expr)},
      optionalDotConstructorArguments nested input = .ok arguments output →
        DeclarativeGrammar.OptionalDotConstructorArgumentsOrdinaryParses
          nestedOrdinary input.declarativeRemainder arguments
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalDotConstructorArguments nested input =
        .reject failure rejected →
        DeclarativeGrammar.OptionalDotConstructorArgumentsRejects
          nestedOrdinary nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨optionalDotConstructorArguments_success_ordinary_sound nested
      nestedOrdinary nestedSuccessSound nestedShape,
    optionalDotConstructorArguments_reject_ordinary_sound nested
      nestedOrdinary nestedRejects nestedSuccessSound nestedRejectSound⟩

/-- Lift a deterministic nested outcome to optional arguments. -/
theorem optionalDotConstructorArguments_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalDotConstructorArgumentsOrdinaryParses
        nestedOrdinary)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsRejects
        nestedOrdinary nestedRejects) :=
  DeclarativeGrammar.optionalDotConstructorArgumentsDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionDotConstructorOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for the guarded leading-dot constructor. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable leading-dot success retains its exact dot, Boolean-first
name, optional arguments, constructed AST, span, and final remainder. -/
theorem dotConstructor_success_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State} {expression : Expr}
    (result : dotConstructor nested input = .ok expression output) :
    DeclarativeGrammar.DotConstructorOrdinaryParses nestedOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold dotConstructor at result
  cases dotResult : symbol .dot .expression input with
  | invariant error => simp [bind, dotResult] at result
  | reject failure rejected => simp [bind, dotResult] at result
  | ok dot afterDot =>
      simp only [bind, dotResult] at result
      cases nameResult : expressionName afterDot with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalDotConstructorArguments nested
              afterName with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult, pure] at result
              cases result
              exact .parsed dot.span
                (symbol_success_exactTokenParses .dot .expression dotResult)
                (expressionName_success_sound nameResult)
                (optionalDotConstructorArguments_success_ordinary_sound
                  nested nestedOrdinary nestedSuccessSound nestedShape
                    argumentsResult)

/-- Under the atom dispatcher's positive dot guard, executable constructor
rejection occurs exactly at the name or optional-argument stage. -/
theorem dotConstructor_reject_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (dotPresent : isSymbol input .dot = true)
    (result : dotConstructor nested input = .reject failure rejected) :
    DeclarativeGrammar.DotConstructorRejects nestedOrdinary nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .dot .expression dotPresent with
    ⟨dot, dotResult⟩
  unfold dotConstructor at result
  simp only [bind, dotResult] at result
  cases nameResult : expressionName { input with cursor := input.cursor + 1 }
      with
  | invariant error => simp [nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [nameResult] at result
      cases result
      exact .nameRejected dot.span
        (symbol_success_exactTokenParses .dot .expression dotResult)
        (expressionName_reject_ordinary_sound nameResult)
  | ok name afterName =>
      simp only [nameResult] at result
      cases argumentsResult : optionalDotConstructorArguments nested afterName
          with
      | invariant error => simp [argumentsResult] at result
      | ok arguments afterArguments =>
          simp [argumentsResult, pure] at result
      | reject argumentsFailure argumentsRejected =>
          simp only [argumentsResult] at result
          cases result
          exact .argumentsRejected dot.span
            (symbol_success_exactTokenParses .dot .expression dotResult)
            (expressionName_success_sound nameResult)
            (optionalDotConstructorArguments_reject_ordinary_sound nested
              nestedOrdinary nestedRejects nestedSuccessSound nestedRejectSound
                argumentsResult)

/-- Package unconditional success with rejection under the dispatcher's
positive dot guard. -/
theorem dotConstructor_guardedOrdinaryOutcome_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    (∀ {input output : State} {expression : Expr},
      dotConstructor nested input = .ok expression output →
        DeclarativeGrammar.DotConstructorOrdinaryParses nestedOrdinary
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isSymbol input .dot = true →
        dotConstructor nested input = .reject failure rejected →
          DeclarativeGrammar.DotConstructorRejects nestedOrdinary
            nestedRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨dotConstructor_success_ordinary_sound nested nestedOrdinary
      nestedSuccessSound nestedShape,
    dotConstructor_reject_ordinary_sound nested nestedOrdinary nestedRejects
      nestedSuccessSound nestedRejectSound⟩

/-- Lift deterministic nested outcomes to the guarded leading-dot branch. -/
theorem dotConstructor_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.DotConstructorOrdinaryParses nestedOrdinary)
      (DeclarativeGrammar.DotConstructorRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.dotConstructorDeterministicOutcomeSpec nestedOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionAtomLeafSoundnessProperties
/-!
Diagnostic reflection and declarative soundness for Core expression leaves.
-/

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

namespace ExpressionAtomInternals

/-- Literal-expression success never removes an earlier diagnostic. -/
theorem literalExpression_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess literalExpression := by
  unfold literalExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    coreLiteral_reflectsDiagnosticFreeOnSuccess
  intro literal
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Identifier-expression success never removes an earlier diagnostic. -/
theorem identifierExpression_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess identifierExpression := by
  unfold identifierExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    expressionName_reflectsDiagnosticFreeOnSuccess
  intro name
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Proxy-expression success reflects through its marker and nested type. -/
theorem proxyExpression_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess proxyExpression := by
  unfold proxyExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .at .expression)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    typeExpr_reflectsDiagnosticFreeOnSuccess
  intro type
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every successful literal expression follows its exact leaf grammar. -/
theorem literalExpression_success_sound {input next : State}
    {expression : Expr}
    (result : literalExpression input = .ok expression next) :
    DeclarativeGrammar.LiteralExpressionParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold literalExpression at result
  rcases bind_ok_components result with
    ⟨literal, afterLiteral, literalResult, finished⟩
  cases finished
  exact .parsed (coreLiteral_success_sound literalResult)

/-- Every successful identifier expression follows its exact leaf grammar. -/
theorem identifierExpression_success_sound {input next : State}
    {expression : Expr}
    (result : identifierExpression input = .ok expression next) :
    DeclarativeGrammar.IdentifierExpressionParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold identifierExpression at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, finished⟩
  cases finished
  exact .parsed (expressionName_success_sound nameResult)

/-- Every successful proxy expression follows its exact leaf grammar. -/
theorem proxyExpression_success_sound {input next : State}
    {expression : Expr}
    (result : proxyExpression input = .ok expression next) :
    DeclarativeGrammar.ProxyExpressionParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold proxyExpression at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨type, afterType, typeResult, finished⟩
  cases finished
  exact .parsed marker.span
    (symbol_success_exactTokenParses .at .expression markerResult)
    (typeExpr_success_sound typeResult)

/-- Literal leaf soundness composes with source provenance. -/
theorem literalExpression_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    {input next : State} {expression : Expr} (inputValid : input.ValidFor)
    (result : literalExpression input = .ok expression next) :
    DeclarativeGrammar.LiteralExpressionParses
        input.declarativeRemainder expression next.declarativeRemainder ∧
      Expr.ValidFor statementValid input.file expression := by
  refine ⟨literalExpression_success_sound result, ?_⟩
  have valid := literalExpression_validFor statementValid input inputValid
  rw [result] at valid
  exact valid.1

/-- Identifier leaf soundness composes with source provenance. -/
theorem identifierExpression_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    {input next : State} {expression : Expr} (inputValid : input.ValidFor)
    (result : identifierExpression input = .ok expression next) :
    DeclarativeGrammar.IdentifierExpressionParses
        input.declarativeRemainder expression next.declarativeRemainder ∧
      Expr.ValidFor statementValid input.file expression := by
  refine ⟨identifierExpression_success_sound result, ?_⟩
  have valid := identifierExpression_validFor statementValid input inputValid
  rw [result] at valid
  exact valid.1

/-- Proxy leaf soundness composes with source provenance. -/
theorem proxyExpression_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    {input next : State} {expression : Expr} (inputValid : input.ValidFor)
    (result : proxyExpression input = .ok expression next) :
    DeclarativeGrammar.ProxyExpressionParses
        input.declarativeRemainder expression next.declarativeRemainder ∧
      Expr.ValidFor statementValid input.file expression := by
  refine ⟨proxyExpression_success_sound result, ?_⟩
  have valid := proxyExpression_validFor statementValid input inputValid
  rw [result] at valid
  exact valid.1

end ExpressionAtomInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreIdentifierExpressionOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for a Core identifier expression leaf. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Identifier-expression rejection is exactly rejection of its wrapped
Boolean-first expression name. -/
theorem identifierExpression_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : identifierExpression input = .reject failure rejected) :
    DeclarativeGrammar.IdentifierExpressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold identifierExpression at result
  cases nameResult : expressionName input with
  | invariant error => simp [bind, nameResult] at result
  | ok name afterName => simp [bind, nameResult, pure] at result
  | reject nameFailure nameRejected =>
      simp only [bind, nameResult] at result
      cases result
      exact .nameRejected (expressionName_reject_ordinary_sound nameResult)

/-- Package unconditional identifier-expression success and rejection. -/
theorem identifierExpression_ordinaryOutcome_sound :
    (∀ {input output : State} {expression : Expr},
      identifierExpression input = .ok expression output →
        DeclarativeGrammar.IdentifierExpressionOrdinaryParses
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      identifierExpression input = .reject failure rejected →
        DeclarativeGrammar.IdentifierExpressionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨identifierExpression_success_sound,
    identifierExpression_reject_ordinary_sound⟩

/-- Re-export the deterministic identifier-expression outcome at its
executable boundary. -/
theorem identifierExpression_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.IdentifierExpressionOrdinaryParses
      DeclarativeGrammar.IdentifierExpressionRejects :=
  DeclarativeGrammar.identifierExpressionDeterministicOutcomeSpec

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLiteralOutcomeSoundnessProperties
/-! Exact executable ordinary outcomes for Core literal leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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
    | .ok value afterFirst =>
        (pure (finish value) : Parser beta) afterFirst
    | .reject firstFailure firstRejected =>
        Reply.reject firstFailure firstRejected
    | .invariant error => Reply.invariant error) =
      Reply.reject failure rejected at result
  cases firstResult : first input with
  | ok value afterFirst => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction
  | reject firstFailure firstRejected =>
      rw [firstResult] at result
      cases result
      rfl

/-- Core-literal rejection returns the complete input state unchanged. -/
theorem coreLiteral_reject_state_eq {input rejected : State}
    {failure : Failure}
    (result : coreLiteral input = .reject failure rejected) :
    rejected = input := by
  unfold coreLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_rejected_state_eq result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_rejected_state_eq result }
      all_goals contradiction

/-- Core-literal rejection proves absence of every admitted literal token. -/
theorem coreLiteral_reject_coreLiteralAbsentAt
    {input rejected : State} {failure : Failure}
    (result : coreLiteral input = .reject failure rejected) :
    DeclarativeGrammar.CoreLiteralAbsentAt input.declarativeRemainder := by
  constructor
  · rintro ⟨span, spelling, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.decimalLiteral spelling
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.decimalLiteral spelling
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold coreLiteral at result
    simp [found] at result
  constructor
  · rintro ⟨span, spelling, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.hexadecimalLiteral spelling
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.hexadecimalLiteral spelling
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold coreLiteral at result
    simp [found] at result
  · rintro ⟨span, spelling, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.stringLiteral spelling
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.stringLiteral spelling
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold coreLiteral at result
    simp [found] at result

/-- Every executable Core-literal rejection is exact and non-consuming. -/
theorem coreLiteral_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : coreLiteral input = .reject failure rejected) :
    DeclarativeGrammar.CoreLiteralRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  have rejectedEq := coreLiteral_reject_state_eq result
  subst rejected
  exact .absent (coreLiteral_reject_coreLiteralAbsentAt result)

/-- A positive Core-literal guard cannot enter the rejection path. -/
theorem coreLiteral_ne_reject_of_isCoreLiteral_eq_true
    {input rejected : State} {failure : Failure}
    (starts : isCoreLiteral input = true)
    (result : coreLiteral input = .reject failure rejected) : False := by
  unfold isCoreLiteral State.peekKind? at starts
  unfold coreLiteral at result
  cases found : input.peek? with
  | none => simp [found] at starts
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at starts result
      all_goals contradiction

/-- Package unconditional Core-literal success with exact rejection. -/
theorem coreLiteral_ordinaryOutcome_sound :
    (∀ {input output : State} {literal : CoreLiteral},
      coreLiteral input = .ok literal output →
        DeclarativeGrammar.CoreLiteralOrdinaryParses
          input.declarativeRemainder literal output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreLiteral input = .reject failure rejected →
        DeclarativeGrammar.CoreLiteralRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨coreLiteral_success_sound, coreLiteral_reject_ordinary_sound⟩

/-- Re-export the deterministic Core-literal outcome at its executable
boundary. -/
theorem coreLiteral_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.CoreLiteralOrdinaryParses
      DeclarativeGrammar.CoreLiteralRejects :=
  DeclarativeGrammar.coreLiteralDeterministicOutcomeSpec

namespace ExpressionAtomInternals

/-- Literal-expression rejection returns the complete input state unchanged. -/
theorem literalExpression_reject_state_eq
    {input rejected : State} {failure : Failure}
    (result : literalExpression input = .reject failure rejected) :
    rejected = input := by
  unfold literalExpression at result
  have literalResult : coreLiteral input = .reject failure rejected :=
    bind_pure_reject_first result
  exact coreLiteral_reject_state_eq literalResult

/-- Every literal-expression rejection is its primitive literal rejection. -/
theorem literalExpression_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : literalExpression input = .reject failure rejected) :
    DeclarativeGrammar.LiteralExpressionRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold literalExpression at result
  have literalResult : coreLiteral input = .reject failure rejected :=
    bind_pure_reject_first result
  have rejectedEq := literalExpression_reject_state_eq result
  subst rejected
  exact .absent (coreLiteral_reject_coreLiteralAbsentAt literalResult)

/-- A positive literal guard also excludes wrapper-level rejection. -/
theorem literalExpression_ne_reject_of_isCoreLiteral_eq_true
    {input rejected : State} {failure : Failure}
    (starts : isCoreLiteral input = true)
    (result : literalExpression input = .reject failure rejected) : False := by
  unfold literalExpression at result
  have literalResult : coreLiteral input = .reject failure rejected :=
    bind_pure_reject_first result
  exact coreLiteral_ne_reject_of_isCoreLiteral_eq_true starts literalResult

/-- Package literal-expression success with exact primitive rejection. -/
theorem literalExpression_ordinaryOutcome_sound :
    (∀ {input output : State} {expression : Expr},
      literalExpression input = .ok expression output →
        DeclarativeGrammar.LiteralExpressionOrdinaryParses
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      literalExpression input = .reject failure rejected →
        DeclarativeGrammar.LiteralExpressionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨literalExpression_success_sound,
    literalExpression_reject_ordinary_sound⟩

/-- Re-export the deterministic literal-expression outcome at its executable
boundary. -/
theorem literalExpression_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.LiteralExpressionOrdinaryParses
      DeclarativeGrammar.LiteralExpressionRejects :=
  DeclarativeGrammar.literalExpressionDeterministicOutcomeSpec

end ExpressionAtomInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreProxyExpressionOrdinaryOutcomeSoundnessProperties
/-!
Executable ordinary outcomes for the guarded Core proxy-expression branch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable proxy success retains its exact marker, nested type,
outer span, AST, and remainder through a supplied ordinary type bridge. -/
theorem proxyExpression_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output →
        typeOrdinary input.declarativeRemainder type
          output.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : proxyExpression input = .ok expression output) :
    DeclarativeGrammar.ProxyExpressionOrdinaryParses typeOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold proxyExpression at result
  cases markerResult : symbol .at .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases typeResult : typeExpr afterMarker with
      | invariant error => simp [typeResult] at result
      | reject failure rejected => simp [typeResult] at result
      | ok type afterType =>
          simp only [typeResult, pure] at result
          cases result
          exact .parsed marker.span
            (symbol_success_exactTokenParses .at .expression markerResult)
            (typeSuccessSound typeResult)

/-- Under the dispatcher's positive `@` guard, executable proxy rejection can
only be the exact rejection reported by the nested type parser. -/
theorem proxyExpression_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected →
        typeRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isSymbol input .at = true)
    (result : proxyExpression input = .reject failure rejected) :
    DeclarativeGrammar.ProxyExpressionRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .at .expression markerPresent with
    ⟨marker, markerResult⟩
  unfold proxyExpression at result
  simp only [bind, markerResult] at result
  cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
  | invariant error => simp [typeResult] at result
  | ok type afterType => simp [typeResult, pure] at result
  | reject typeFailure typeRejected =>
      simp only [typeResult] at result
      cases result
      exact .typeRejected marker.span
        (symbol_success_exactTokenParses .at .expression markerResult)
        (typeRejectSound typeResult)

/-- Package unconditional success and guarded rejection over supplied
executable type callbacks. -/
theorem proxyExpression_guardedOrdinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output →
        typeOrdinary input.declarativeRemainder type
          output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected →
        typeRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      proxyExpression input = .ok expression output →
        DeclarativeGrammar.ProxyExpressionOrdinaryParses typeOrdinary
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isSymbol input .at = true →
        proxyExpression input = .reject failure rejected →
          DeclarativeGrammar.ProxyExpressionRejects typeRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨proxyExpression_success_ordinary_sound typeOrdinary typeSuccessSound,
    proxyExpression_reject_ordinary_sound typeRejects typeRejectSound⟩

/-- Lift a deterministic nested type outcome to the guarded proxy branch. -/
theorem proxyExpression_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ProxyExpressionOrdinaryParses typeOrdinary)
      (DeclarativeGrammar.ProxyExpressionRejects typeRejects) :=
  DeclarativeGrammar.proxyExpressionDeterministicOutcomeSpec typeOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionProperties
/-! Provenance and state contracts for canonical Core expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ExpressionInternals

namespace ConditionalHead

/-- Every range retained by a pending conditional prefix belongs to one source. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (head : ConditionalHead) : Prop :=
  Expr.ValidFor statementValid file head.condition ∧
    head.question.ValidFor file ∧
    Expr.ValidFor statementValid file head.thenBranch ∧
    head.colon.ValidFor file

end ConditionalHead

/-- Attaching one conditional prefix preserves the else branch's source end. -/
theorem foldConditionalHead_preservesElseEnd
    (elseBranch : Expr) (head : ConditionalHead) :
    (foldConditionalHead elseBranch head).span.endByte =
      elseBranch.span.endByte := by
  rfl

@[simp] theorem foldConditionalHead_startByte
    (elseBranch : Expr) (head : ConditionalHead) :
    (foldConditionalHead elseBranch head).span.startByte =
      head.condition.span.startByte := rfl

/-- Folding the same pending prefixes depends only on the base's left edge. -/
theorem foldConditionalHeads_start_congr
    (heads : List ConditionalHead) (first second : Expr)
    (sameStart : first.span.startByte = second.span.startByte) :
    (heads.foldl foldConditionalHead first).span.startByte =
      (heads.foldl foldConditionalHead second).span.startByte := by
  induction heads generalizing first second with
  | nil => exact sameStart
  | cons head rest inductionHypothesis =>
      simp only [List.foldl]
      exact inductionHypothesis _ _ rfl

/-- Attaching a valid conditional prefix retains every recursive source range. -/
theorem foldConditionalHead_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (elseBranch : Expr) (head : ConditionalHead)
    (headValid : head.ValidFor statementValid file)
    (elseValid : Expr.ValidFor statementValid file elseBranch)
    (ordered : head.condition.span.startByte ≤
      elseBranch.span.endByte) :
    Expr.ValidFor statementValid file
      (foldConditionalHead elseBranch head) := by
  rcases headValid with
    ⟨conditionValid, questionValid, thenValid, colonValid⟩
  have outerValid := SourceSpan.cover_validFor conditionValid.span_valid
    elseValid.span_valid ordered
  exact Expr.ValidFor.conditional outerValid conditionValid questionValid
    thenValid colonValid elseValid

/-- Folding pending prefixes preserves the final else branch's source end. -/
theorem foldConditionalHeads_preservesBaseEnd
    (heads : List ConditionalHead) (base : Expr) :
    (heads.foldl foldConditionalHead base).span.endByte =
      base.span.endByte := by
  induction heads generalizing base with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      simpa only [List.foldl] using
        (inductionHypothesis (foldConditionalHead base head)).trans
          (foldConditionalHead_preservesElseEnd base head)

/-- Folding valid pending prefixes retains every recursive source range. -/
theorem foldConditionalHeads_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (heads : List ConditionalHead) (base : Expr)
    (headsValid : List.ValidFor
      (ConditionalHead.ValidFor statementValid) file heads)
    (baseValid : Expr.ValidFor statementValid file base)
    (ordered : ∀ head ∈ heads,
      head.condition.span.startByte ≤ base.span.endByte) :
    Expr.ValidFor statementValid file
      (heads.foldl foldConditionalHead base) := by
  induction heads generalizing base with
  | nil => simpa only [List.foldl] using baseValid
  | cons head rest inductionHypothesis =>
      have headValid := headsValid head (by simp)
      have restValid : List.ValidFor
          (ConditionalHead.ValidFor statementValid) file rest := by
        intro retained member
        exact headsValid retained (by simp [member])
      have attachedValid := foldConditionalHead_validFor statementValid file
        base head headValid baseValid (ordered head (by simp))
      apply inductionHypothesis (foldConditionalHead base head) restValid
        attachedValid
      intro retained member
      rw [foldConditionalHead_preservesElseEnd]
      exact ordered retained (by simp [member])

/-- The conditional-prefix loop preserves every ordinary token window. -/
theorem conditionalTail_preservesTokenWindow
    (nested alternative : Parser Expr)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (alternativeWindow : Parser.PreservesTokenWindow alternative) :
    ∀ fuel heads condition,
      Parser.PreservesTokenWindow
        (conditionalTail nested alternative fuel heads condition) := by
  intro fuel
  induction fuel with
  | zero => intro heads condition input; trivial
  | succ fuel inductionHypothesis =>
      intro heads condition input
      unfold conditionalTail
      by_cases present : isSymbol input .question
      · simp only [present, if_true]
        have questionShape :=
          symbol_preservesTokenWindow .question .expression input
        cases questionResult : symbol .question .expression input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [questionResult] at questionShape
            exact questionShape
        | ok question afterQuestion =>
            rw [questionResult] at questionShape
            simp only
            have thenShape := nestedWindow afterQuestion
            cases thenResult : nested afterQuestion with
            | invariant error => trivial
            | reject failure rejected =>
                rw [thenResult] at thenShape
                exact thenShape.trans questionShape
            | ok thenBranch afterThen =>
                rw [thenResult] at thenShape
                simp only
                have colonShape :=
                  symbol_preservesTokenWindow .colon .expression afterThen
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => trivial
                | reject failure rejected =>
                    rw [colonResult] at colonShape
                    exact (colonShape.trans thenShape).trans questionShape
                | ok colon afterColon =>
                    rw [colonResult] at colonShape
                    simp only
                    have alternativeShape := alternativeWindow afterColon
                    cases alternativeResult : alternative afterColon with
                    | invariant error => trivial
                    | reject failure rejected =>
                        rw [alternativeResult] at alternativeShape
                        exact ((alternativeShape.trans colonShape).trans
                          thenShape).trans questionShape
                    | ok nextCondition next =>
                        rw [alternativeResult] at alternativeShape
                        exact ((((inductionHypothesis ({
                            condition
                            question := question.span
                            thenBranch
                            colon := colon.span
                          } :: heads) nextCondition next).trans
                            alternativeShape).trans colonShape).trans
                              thenShape).trans questionShape
      · simp only [present]
        exact ⟨rfl, rfl⟩

theorem conditionalTail_preservesTokensOnSuccess
    (nested alternative : Parser Expr)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (alternativeWindow : Parser.PreservesTokenWindow alternative)
    (fuel : Nat) (heads : List ConditionalHead) (condition : Expr) :
    Parser.PreservesTokensOnSuccess
      (conditionalTail nested alternative fuel heads condition) :=
  (conditionalTail_preservesTokenWindow nested alternative nestedWindow
    alternativeWindow fuel heads condition).preservesTokensOnSuccess

/-- Successful conditional-prefix parsing never rewinds its caller. -/
theorem conditionalTail_cursorMonotoneOnSuccess
    (nested alternative : Parser Expr)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (alternativeCursor : Parser.CursorMonotoneOnSuccess alternative) :
    ∀ fuel heads condition,
      Parser.CursorMonotoneOnSuccess
        (conditionalTail nested alternative fuel heads condition) := by
  intro fuel
  induction fuel with
  | zero =>
      intro heads condition input expression final parsed
      unfold conditionalTail at parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro heads condition input expression final parsed
      unfold conditionalTail at parsed
      by_cases present : isSymbol input .question
      · simp only [present, if_true] at parsed
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at parsed
        | reject failure rejected => simp [questionResult] at parsed
        | ok question afterQuestion =>
            simp only [questionResult] at parsed
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at parsed
            | reject failure rejected => simp [thenResult] at parsed
            | ok thenBranch afterThen =>
                simp only [thenResult] at parsed
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at parsed
                | reject failure rejected => simp [colonResult] at parsed
                | ok colon afterColon =>
                    simp only [colonResult] at parsed
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at parsed
                    | reject failure rejected =>
                        simp [alternativeResult] at parsed
                    | ok nextCondition next =>
                        simp only [alternativeResult] at parsed
                        exact Nat.le_trans
                          (symbol_cursorMonotoneOnSuccess .question .expression
                            input question afterQuestion questionResult)
                          (Nat.le_trans
                            (nestedCursor afterQuestion thenBranch afterThen
                              thenResult)
                            (Nat.le_trans
                              (symbol_cursorMonotoneOnSuccess .colon .expression
                                afterThen colon afterColon colonResult)
                              (Nat.le_trans
                                (alternativeCursor afterColon nextCondition next
                                  alternativeResult)
                                (inductionHypothesis ({
                                    condition
                                    question := question.span
                                    thenBranch
                                    colon := colon.span
                                  } :: heads) nextCondition next expression
                                    final parsed))))
      · simp only [present] at parsed
        cases parsed
        exact Nat.le_refl _

/-- A conditional tail preserves the left edge represented by its accumulator. -/
theorem conditionalTail_preservesFoldStartOnSuccess
    (nested alternative : Parser Expr) :
    ∀ fuel heads condition input expression final,
      conditionalTail nested alternative fuel heads condition input =
        .ok expression final →
      expression.span.startByte =
        (heads.foldl foldConditionalHead condition).span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro heads condition input expression final parsed
      unfold conditionalTail at parsed
      by_cases present : isSymbol input .question
      · simp only [present, if_true] at parsed
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at parsed
        | reject failure rejected => simp [questionResult] at parsed
        | ok question afterQuestion =>
            simp only [questionResult] at parsed
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at parsed
            | reject failure rejected => simp [thenResult] at parsed
            | ok thenBranch afterThen =>
                simp only [thenResult] at parsed
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at parsed
                | reject failure rejected => simp [colonResult] at parsed
                | ok colon afterColon =>
                    simp only [colonResult] at parsed
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at parsed
                    | reject failure rejected =>
                        simp [alternativeResult] at parsed
                    | ok nextCondition next =>
                        simp only [alternativeResult] at parsed
                        calc
                          expression.span.startByte =
                              (({
                                condition
                                question := question.span
                                thenBranch
                                colon := colon.span
                              } :: heads).foldl foldConditionalHead
                                nextCondition).span.startByte :=
                            inductionHypothesis _ _ next expression final parsed
                          _ = (heads.foldl foldConditionalHead
                              (foldConditionalHead nextCondition {
                                condition
                                question := question.span
                                thenBranch
                                colon := colon.span
                              })).span.startByte := rfl
                          _ = (heads.foldl foldConditionalHead
                              condition).span.startByte :=
                            foldConditionalHeads_start_congr heads _ _ rfl
      · simp only [present] at parsed
        cases parsed
        rfl

/-- The conditional-prefix loop retains every pending and parsed source range. -/
theorem conditionalTail_validFor
    (nested alternative : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedTokens : Parser.PreservesTokensOnSuccess nested)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (alternativeValid : alternative.ValidFor
      (Expr.ValidFor statementValid))
    (alternativeTokens : Parser.PreservesTokensOnSuccess alternative)
    (alternativeCursorLt : ∀ {input next : State} {value : Expr},
      alternative input = .ok value next → input.cursor < next.cursor)
    (alternativeStarts :
      Parser.StartsAtCurrentTokenOnSuccess alternative (·.span)) :
    ∀ fuel heads condition input,
      input.ValidFor →
      List.ValidFor (ConditionalHead.ValidFor statementValid)
        input.file heads →
      Expr.ValidFor statementValid input.file condition →
      (∀ head ∈ heads, head.condition.span.startByte ≤
        condition.span.startByte) →
      (∀ token, input.peek? = some token →
        condition.span.startByte ≤ token.span.startByte) →
      (conditionalTail nested alternative fuel heads condition input).ValidFor
        input (Expr.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro heads condition input inputValid headsValid conditionValid
        headsBefore conditionBefore
      unfold conditionalTail
      by_cases present : isSymbol input .question
      · simp only [present, if_true]
        cases questionResult : symbol .question .expression input with
        | invariant error => trivial
        | reject failure rejected =>
            have reply := symbol_validFor .question .expression input inputValid
            rw [questionResult] at reply
            exact reply
        | ok question afterQuestion =>
            have questionReply := symbol_validFor .question .expression input
              inputValid
            rw [questionResult] at questionReply
            simp only
            cases thenResult : nested afterQuestion with
            | invariant error => trivial
            | reject failure rejected =>
                have reply := nestedValid afterQuestion questionReply.2.1
                rw [thenResult] at reply
                exact reply.of_file_eq questionReply.2.2
            | ok thenBranch afterThen =>
                have thenReply := nestedValid afterQuestion questionReply.2.1
                rw [thenResult] at thenReply
                simp only
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => trivial
                | reject failure rejected =>
                    have reply := symbol_validFor .colon .expression afterThen
                      thenReply.2.1
                    rw [colonResult] at reply
                    exact reply.of_file_eq
                      (thenReply.2.2.trans questionReply.2.2)
                | ok colon afterColon =>
                    have colonReply := symbol_validFor .colon .expression
                      afterThen thenReply.2.1
                    rw [colonResult] at colonReply
                    simp only
                    cases alternativeResult : alternative afterColon with
                    | invariant error => trivial
                    | reject failure rejected =>
                        have reply := alternativeValid afterColon colonReply.2.1
                        rw [alternativeResult] at reply
                        exact reply.of_file_eq (colonReply.2.2.trans
                          (thenReply.2.2.trans questionReply.2.2))
                    | ok nextCondition next =>
                        have alternativeReply := alternativeValid afterColon
                          colonReply.2.1
                        rw [alternativeResult] at alternativeReply
                        have questionShape := symbol_ok_state_shape .question
                          .expression questionResult
                        have colonShape := symbol_ok_state_shape .colon
                          .expression colonResult
                        have questionAt :=
                          State.getElem?_eq_some_of_peek?_eq_some
                            questionShape.1
                        rcases alternativeStarts afterColon nextCondition next
                            alternativeResult with
                          ⟨nextToken, nextFound, nextStart⟩
                        have nextAtAfterColon :=
                          State.getElem?_eq_some_of_peek?_eq_some nextFound
                        have questionTokens :=
                          symbol_preservesTokensOnSuccess .question .expression
                            input question afterQuestion questionResult
                        have thenTokens := nestedTokens afterQuestion thenBranch
                          afterThen thenResult
                        have colonTokens :=
                          symbol_preservesTokensOnSuccess .colon .expression
                            afterThen colon afterColon colonResult
                        have nextAtInput : input.tokens[afterColon.cursor]? =
                            some nextToken := by
                          simpa [colonTokens, thenTokens, questionTokens] using
                            nextAtAfterColon
                        have questionBeforeNext :=
                          inputValid.token_end_le_token_start_of_getElem?_lt
                            questionAt nextAtInput
                            (Nat.lt_of_lt_of_le
                              (acceptToken_cursor_lt_onSuccess
                                (.symbol .question) .expression
                                (· == .symbol .question) questionResult)
                              (Nat.le_trans
                                (nestedCursor afterQuestion thenBranch afterThen
                                  thenResult)
                                (symbol_cursorMonotoneOnSuccess .colon
                                  .expression afterThen colon afterColon
                                  colonResult)))
                        have questionSpan : question.span.ValidFor input.file := by
                          simpa only [Located.ValidFor] using questionReply.1
                        have conditionBeforeNext :
                            condition.span.startByte ≤
                              nextCondition.span.startByte := by
                          calc
                            condition.span.startByte ≤
                                question.span.startByte :=
                              conditionBefore question questionShape.1
                            _ ≤ question.span.endByte := questionSpan.2.1
                            _ ≤ nextToken.span.startByte := questionBeforeNext
                            _ = nextCondition.span.startByte := nextStart
                        have thenValidInput : Expr.ValidFor statementValid
                            input.file thenBranch := by
                          simpa [thenReply.2.2, questionReply.2.2] using
                            thenReply.1
                        have colonSpan : colon.span.ValidFor input.file := by
                          simpa only [Located.ValidFor, thenReply.2.2,
                            questionReply.2.2] using colonReply.1
                        have nextFileEq : next.file = input.file :=
                          alternativeReply.2.2.trans (colonReply.2.2.trans
                            (thenReply.2.2.trans questionReply.2.2))
                        have nextConditionValidInput :
                            Expr.ValidFor statementValid input.file
                              nextCondition := by
                          simpa [colonReply.2.2, thenReply.2.2,
                            questionReply.2.2] using alternativeReply.1
                        have accumulatedInput : List.ValidFor
                            (ConditionalHead.ValidFor statementValid) input.file
                            ({
                              condition
                              question := question.span
                              thenBranch
                              colon := colon.span
                            } :: heads) := by
                          intro head member
                          rcases List.mem_cons.mp member with rfl | member
                          · exact ⟨conditionValid, questionSpan,
                              thenValidInput, colonSpan⟩
                          · exact headsValid head member
                        have accumulatedNext : List.ValidFor
                            (ConditionalHead.ValidFor statementValid) next.file
                            ({
                              condition
                              question := question.span
                              thenBranch
                              colon := colon.span
                            } :: heads) := by
                          simpa [nextFileEq] using accumulatedInput
                        have headsBeforeNext : ∀ head ∈ ({
                              condition
                              question := question.span
                              thenBranch
                              colon := colon.span
                            } :: heads),
                            head.condition.span.startByte ≤
                              nextCondition.span.startByte := by
                          intro head member
                          rcases List.mem_cons.mp member with rfl | member
                          · exact conditionBeforeNext
                          · exact Nat.le_trans (headsBefore head member)
                              conditionBeforeNext
                        have nextConditionBefore : ∀ future,
                            next.peek? = some future →
                            nextCondition.span.startByte ≤
                              future.span.startByte := by
                          intro future futureFound
                          have nextAt :=
                            State.getElem?_eq_some_of_peek?_eq_some nextFound
                          have futureAtNext :=
                            State.getElem?_eq_some_of_peek?_eq_some futureFound
                          have alternativeCarrier := alternativeTokens afterColon
                            nextCondition next alternativeResult
                          have futureAt : afterColon.tokens[next.cursor]? =
                              some future := by
                            simpa [alternativeCarrier] using futureAtNext
                          have separated :=
                            colonReply.2.1.token_end_le_token_start_of_getElem?_lt
                              nextAt futureAt
                                (alternativeCursorLt alternativeResult)
                          calc
                            nextCondition.span.startByte =
                                nextToken.span.startByte := nextStart.symm
                            _ ≤ nextToken.span.endByte :=
                              (colonReply.2.1.peek?_span_validFor nextFound).2.1
                            _ ≤ future.span.startByte := separated
                        have recursive := inductionHypothesis ({
                            condition
                            question := question.span
                            thenBranch
                            colon := colon.span
                          } :: heads) nextCondition next alternativeReply.2.1
                            accumulatedNext
                            (by simpa [nextFileEq] using
                              nextConditionValidInput)
                            headsBeforeNext nextConditionBefore
                        exact recursive.of_file_eq nextFileEq
      · simp only [present]
        have folded := foldConditionalHeads_validFor statementValid input.file
          heads condition headsValid conditionValid (by
            intro head member
            exact Nat.le_trans (headsBefore head member)
              conditionValid.span_valid.2.1)
        exact ⟨folded, inputValid, rfl⟩

/-- A complete conditional layer preserves every ordinary token window. -/
theorem conditional_preservesTokenWindow
    (nested alternative : Parser Expr)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (alternativeWindow : Parser.PreservesTokenWindow alternative) :
    Parser.PreservesTokenWindow (conditional nested alternative) := by
  intro input
  unfold conditional
  have alternativeShape := alternativeWindow input
  cases alternativeResult : alternative input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [alternativeResult] at alternativeShape
      exact alternativeShape
  | ok condition next =>
      rw [alternativeResult] at alternativeShape
      exact (conditionalTail_preservesTokenWindow nested alternative
        nestedWindow alternativeWindow (next.remainingCount + 1) [] condition
          next).trans alternativeShape

theorem conditional_preservesTokensOnSuccess
    (nested alternative : Parser Expr)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (alternativeWindow : Parser.PreservesTokenWindow alternative) :
    Parser.PreservesTokensOnSuccess (conditional nested alternative) :=
  (conditional_preservesTokenWindow nested alternative nestedWindow
    alternativeWindow).preservesTokensOnSuccess

/-- A complete conditional layer never rewinds the token cursor. -/
theorem conditional_cursorMonotoneOnSuccess
    (nested alternative : Parser Expr)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (alternativeCursor : Parser.CursorMonotoneOnSuccess alternative) :
    Parser.CursorMonotoneOnSuccess (conditional nested alternative) := by
  intro input expression final parsed
  unfold conditional at parsed
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at parsed
  | reject failure rejected => simp [alternativeResult] at parsed
  | ok condition next =>
      simp only [alternativeResult] at parsed
      exact Nat.le_trans
        (alternativeCursor input condition next alternativeResult)
        (conditionalTail_cursorMonotoneOnSuccess nested alternative
          nestedCursor alternativeCursor (next.remainingCount + 1) []
            condition next expression final parsed)

/-- A complete conditional layer retains its first alternative's left edge. -/
theorem conditional_startsAtCurrentTokenOnSuccess
    (nested alternative : Parser Expr)
    (alternativeStarts :
      Parser.StartsAtCurrentTokenOnSuccess alternative (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (conditional nested alternative) (·.span) := by
  intro input expression final parsed
  unfold conditional at parsed
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at parsed
  | reject failure rejected => simp [alternativeResult] at parsed
  | ok condition next =>
      simp only [alternativeResult] at parsed
      rcases alternativeStarts input condition next alternativeResult with
        ⟨token, found, starts⟩
      have retained := conditionalTail_preservesFoldStartOnSuccess nested
        alternative (next.remainingCount + 1) [] condition next expression
          final parsed
      exact ⟨token, found, starts.trans (by simpa using retained.symm)⟩

/-- A complete conditional layer retains every recursive source range. -/
theorem conditional_validFor
    (nested alternative : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (nestedValid : nested.ValidFor (Expr.ValidFor statementValid))
    (nestedTokens : Parser.PreservesTokensOnSuccess nested)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (alternativeValid : alternative.ValidFor
      (Expr.ValidFor statementValid))
    (alternativeTokens : Parser.PreservesTokensOnSuccess alternative)
    (alternativeCursorLt : ∀ {input next : State} {value : Expr},
      alternative input = .ok value next → input.cursor < next.cursor)
    (alternativeStarts :
      Parser.StartsAtCurrentTokenOnSuccess alternative (·.span)) :
    (conditional nested alternative).ValidFor
      (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold conditional
  cases alternativeResult : alternative input with
  | invariant error => trivial
  | reject failure rejected =>
      have reply := alternativeValid input inputValid
      rw [alternativeResult] at reply
      exact reply
  | ok condition next =>
      have alternativeReply := alternativeValid input inputValid
      rw [alternativeResult] at alternativeReply
      rcases alternativeStarts input condition next alternativeResult with
        ⟨firstToken, firstFound, firstStart⟩
      have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
      have carrier := alternativeTokens input condition next alternativeResult
      have conditionBefore : ∀ future, next.peek? = some future →
          condition.span.startByte ≤ future.span.startByte := by
        intro future futureFound
        have futureAtNext :=
          State.getElem?_eq_some_of_peek?_eq_some futureFound
        have futureAt : input.tokens[next.cursor]? = some future := by
          simpa [carrier] using futureAtNext
        have separated := inputValid.token_end_le_token_start_of_getElem?_lt
          firstAt futureAt (alternativeCursorLt alternativeResult)
        have firstValid := inputValid.peek?_span_validFor firstFound
        calc
          condition.span.startByte = firstToken.span.startByte := firstStart.symm
          _ ≤ firstToken.span.endByte := firstValid.2.1
          _ ≤ future.span.startByte := separated
      have recursive := conditionalTail_validFor nested alternative
        statementValid nestedValid nestedTokens nestedCursor alternativeValid
          alternativeTokens alternativeCursorLt alternativeStarts
            (next.remainingCount + 1) [] condition next alternativeReply.2.1
              (by simp [List.ValidFor])
              (by simpa [alternativeReply.2.2] using alternativeReply.1)
                (by simp)
                conditionBefore
      exact recursive.of_file_eq alternativeReply.2.2

/-- Prefix unary scanning preserves operator spans and parser-state validity. -/
theorem unaryOperators_validFor :
    ∀ fuel operatorsRev input,
      input.ValidFor →
      List.ValidFor Located.ValidFor input.file operatorsRev →
      (unaryOperators fuel operatorsRev input).ValidFor input
        (List.ValidFor Located.ValidFor) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro operatorsRev input inputValid operatorsValid
      unfold unaryOperators
      cases found : input.peek? with
      | none =>
          exact ⟨by
            intro operator member
            exact operatorsValid operator (by simpa using member),
            inputValid, rfl⟩
      | some token =>
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded]
              exact ⟨by
                intro operator member
                exact operatorsValid operator (by simpa using member),
                inputValid, rfl⟩
          | some operator =>
              simp only [decoded]
              have advanced : input.advance? = some (token,
                  { input with cursor := input.cursor + 1 }) := by
                unfold State.advance?
                rw [found]
                rfl
              have nextValid := inputValid.advance?_validFor advanced
              have tokenValid := inputValid.peek?_span_validFor found
              have accumulatedValid : List.ValidFor Located.ValidFor
                  ({ input with cursor := input.cursor + 1 } : State).file
                  ({ span := token.span, value := operator } ::
                    operatorsRev) := by
                intro retained member
                rcases List.mem_cons.mp member with rfl | member
                · simpa only [Located.ValidFor] using tokenValid
                · simpa using operatorsValid retained member
              exact (inductionHypothesis
                ({ span := token.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 }
                nextValid accumulatedValid).of_file_eq rfl

/-- Prefix unary scanning preserves the complete immutable token window. -/
theorem unaryOperators_preservesTokenWindow (fuel : Nat)
    (operatorsRev : List (Located UnaryOp)) :
    Parser.PreservesTokenWindow (unaryOperators fuel operatorsRev) := by
  intro input
  induction fuel generalizing operatorsRev input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold unaryOperators
      cases found : input.peek? with
      | none => exact ⟨rfl, rfl⟩
      | some token =>
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded]
              exact ⟨rfl, rfl⟩
          | some operator =>
              simp only [decoded]
              exact (inductionHypothesis
                ({ span := token.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 }).trans ⟨rfl, rfl⟩

theorem unaryOperators_preservesTokensOnSuccess (fuel : Nat)
    (operatorsRev : List (Located UnaryOp)) :
    Parser.PreservesTokensOnSuccess (unaryOperators fuel operatorsRev) :=
  (unaryOperators_preservesTokenWindow fuel
    operatorsRev).preservesTokensOnSuccess

/-- Prefix unary scanning never rewinds its input cursor. -/
theorem unaryOperators_cursorMonotoneOnSuccess (fuel : Nat)
    (operatorsRev : List (Located UnaryOp)) :
    Parser.CursorMonotoneOnSuccess (unaryOperators fuel operatorsRev) := by
  intro input operators next parsed
  induction fuel generalizing operatorsRev input with
  | zero => contradiction
  | succ fuel inductionHypothesis =>
      unfold unaryOperators at parsed
      cases found : input.peek? with
      | none =>
          simp only [found] at parsed
          cases parsed
          exact Nat.le_refl _
      | some token =>
          simp only [found] at parsed
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded] at parsed
              cases parsed
              exact Nat.le_refl _
          | some operator =>
              simp only [decoded] at parsed
              exact Nat.le_trans (by simp)
                (inductionHypothesis
                  ({ span := token.span, value := operator } :: operatorsRev)
                  { input with cursor := input.cursor + 1 } parsed)

/-- Every scanned unary operator ends before the scanner's next token. -/
theorem unaryOperators_endBeforeCurrentOnSuccess :
    ∀ fuel operatorsRev input operators next,
      input.ValidFor →
      (∀ retained ∈ operatorsRev, ∀ token,
        input.peek? = some token →
        retained.span.endByte ≤ token.span.startByte) →
      unaryOperators fuel operatorsRev input = .ok operators next →
      ∀ retained ∈ operators, ∀ token,
        next.peek? = some token →
        retained.span.endByte ≤ token.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro operatorsRev input operators next inputValid accumulatedBefore parsed
      unfold unaryOperators at parsed
      cases found : input.peek? with
      | none =>
          simp only [found] at parsed
          cases parsed
          intro retained member token futureFound
          have retainedMember : retained ∈ operatorsRev := by
            simpa using member
          exact accumulatedBefore retained retainedMember token futureFound
      | some current =>
          simp only [found] at parsed
          cases decoded : unaryOp? current.value with
          | none =>
              simp only [decoded] at parsed
              cases parsed
              intro retained member token futureFound
              have retainedMember : retained ∈ operatorsRev := by
                simpa using member
              exact accumulatedBefore retained retainedMember token futureFound
          | some operator =>
              simp only [decoded] at parsed
              have advanced : input.advance? = some (current,
                  { input with cursor := input.cursor + 1 }) := by
                unfold State.advance?
                rw [found]
                rfl
              have nextValid := inputValid.advance?_validFor advanced
              have nextAccumulated : ∀ retained ∈
                  ({ span := current.span, value := operator } :: operatorsRev),
                  ∀ token,
                    ({ input with cursor := input.cursor + 1 } : State).peek? =
                      some token →
                    retained.span.endByte ≤ token.span.startByte := by
                intro retained member token futureFound
                have currentAt :=
                  State.getElem?_eq_some_of_peek?_eq_some found
                have futureAtNext :=
                  State.getElem?_eq_some_of_peek?_eq_some futureFound
                have futureAt : input.tokens[input.cursor + 1]? = some token := by
                  simpa using futureAtNext
                have separated :=
                  inputValid.token_end_le_token_start_of_getElem?_lt currentAt
                    futureAt (by omega)
                rcases List.mem_cons.mp member with rfl | member
                · exact separated
                · exact Nat.le_trans
                    (accumulatedBefore retained member current found)
                    (Nat.le_trans
                      (inputValid.peek?_span_validFor found).2.1 separated)
              exact inductionHypothesis
                ({ span := current.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 } operators next
                  nextValid nextAccumulated parsed

/-- Scanning retains the reversed accumulator as an output prefix. -/
theorem unaryOperators_retainsAccumulatorPrefixOnSuccess :
    ∀ fuel operatorsRev input operators next,
      unaryOperators fuel operatorsRev input = .ok operators next →
      ∃ suffix, operators = operatorsRev.reverse ++ suffix := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro operatorsRev input operators next parsed
      unfold unaryOperators at parsed
      cases found : input.peek? with
      | none =>
          simp only [found] at parsed
          cases parsed
          exact ⟨[], by simp⟩
      | some current =>
          simp only [found] at parsed
          cases decoded : unaryOp? current.value with
          | none =>
              simp only [decoded] at parsed
              cases parsed
              exact ⟨[], by simp⟩
          | some operator =>
              simp only [decoded] at parsed
              rcases inductionHypothesis
                  ({ span := current.span, value := operator } :: operatorsRev)
                  { input with cursor := input.cursor + 1 } operators next
                    parsed with
                ⟨suffix, output⟩
              exact ⟨{ span := current.span, value := operator } :: suffix,
                by simpa [List.reverse_cons, List.append_assoc] using output⟩

/-- An initial scan either stays put or retains its first token first. -/
theorem unaryOperators_initialShapeOnSuccess
    (fuel : Nat) (input : State) (operators : List (Located UnaryOp))
    (next : State)
    (parsed : unaryOperators fuel [] input = .ok operators next) :
    (operators = [] ∧ next = input) ∨
      ∃ first rest token,
        input.peek? = some token ∧ first.span = token.span ∧
          operators = first :: rest := by
  cases fuel with
  | zero => contradiction
  | succ fuel =>
      unfold unaryOperators at parsed
      cases found : input.peek? with
      | none =>
          simp only [found] at parsed
          cases parsed
          exact Or.inl ⟨rfl, rfl⟩
      | some current =>
          simp only [found] at parsed
          cases decoded : unaryOp? current.value with
          | none =>
              simp only [decoded] at parsed
              cases parsed
              exact Or.inl ⟨rfl, rfl⟩
          | some operator =>
              simp only [decoded] at parsed
              rcases unaryOperators_retainsAccumulatorPrefixOnSuccess fuel
                  [{ span := current.span, value := operator }]
                  { input with cursor := input.cursor + 1 } operators next
                    parsed with
                ⟨suffix, output⟩
              exact Or.inr ⟨{ span := current.span, value := operator },
                suffix, current, rfl, rfl, by simpa using output⟩

/-- Unary wrapping preserves the final operand's source end. -/
theorem applyUnaryOperators_preservesBaseEnd
    (operators : List (Located UnaryOp)) (base : Expr) :
    (applyUnaryOperators operators base).span.endByte =
      base.span.endByte := by
  induction operators with
  | nil => rfl
  | cons operator rest inductionHypothesis =>
      simpa only [applyUnaryOperators, List.foldr, SourceSpan.cover] using
        inductionHypothesis

@[simp] theorem applyUnaryOperators_startByte
    (operator : Located UnaryOp) (rest : List (Located UnaryOp))
    (base : Expr) :
    (applyUnaryOperators (operator :: rest) base).span.startByte =
      operator.span.startByte := rfl

/-- Unary wrapping retains every operator and operand source range. -/
theorem applyUnaryOperators_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (operators : List (Located UnaryOp)) (base : Expr)
    (operatorsValid : List.ValidFor Located.ValidFor file operators)
    (baseValid : Expr.ValidFor statementValid file base)
    (ordered : ∀ operator ∈ operators,
      operator.span.startByte ≤ base.span.endByte) :
    Expr.ValidFor statementValid file
      (applyUnaryOperators operators base) := by
  induction operators with
  | nil => simpa only [applyUnaryOperators, List.foldr] using baseValid
  | cons operator rest inductionHypothesis =>
      have operatorValid : operator.span.ValidFor file := by
        simpa only [Located.ValidFor] using
          operatorsValid operator (by simp)
      have restValid : List.ValidFor Located.ValidFor file rest := by
        intro retained member
        exact operatorsValid retained (by simp [member])
      have restOrdered : ∀ retained ∈ rest,
          retained.span.startByte ≤ base.span.endByte := by
        intro retained member
        exact ordered retained (by simp [member])
      have operandValid := inductionHypothesis restValid restOrdered
      have outerValid := SourceSpan.cover_validFor operatorValid
        operandValid.span_valid (by
          rw [applyUnaryOperators_preservesBaseEnd]
          exact ordered operator (by simp))
      simpa only [applyUnaryOperators, List.foldr] using
        (Expr.ValidFor.unary outerValid operatorValid operandValid)

/-- Unary parsing retains every scanned operator and postfix source range. -/
theorem expressionUnary_validFor
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (postfixValid : (expressionPostfix nested block).ValidFor
      (Expr.ValidFor statementValid))
    (postfixStarts : Parser.StartsAtCurrentTokenOnSuccess
      (expressionPostfix nested block) (·.span)) :
    (expressionUnary nested block).ValidFor
      (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold expressionUnary
  cases operatorsResult : unaryOperators (input.remainingCount + 1) [] input with
  | invariant error => trivial
  | reject failure rejected =>
      have reply := unaryOperators_validFor (input.remainingCount + 1) [] input
        inputValid (by simp [List.ValidFor])
      rw [operatorsResult] at reply
      exact reply
  | ok operators afterOperators =>
      have operatorsReply := unaryOperators_validFor
        (input.remainingCount + 1) [] input inputValid
          (by simp [List.ValidFor])
      rw [operatorsResult] at operatorsReply
      simp only
      cases postfixResult : expressionPostfix nested block afterOperators with
      | invariant error => trivial
      | reject failure rejected =>
          have reply := postfixValid afterOperators operatorsReply.2.1
          rw [postfixResult] at reply
          exact reply.of_file_eq operatorsReply.2.2
      | ok base next =>
          have postfixReply := postfixValid afterOperators operatorsReply.2.1
          rw [postfixResult] at postfixReply
          rcases postfixStarts afterOperators base next postfixResult with
            ⟨first, firstFound, baseStart⟩
          have baseValid : Expr.ValidFor statementValid input.file base := by
            simpa [operatorsReply.2.2] using postfixReply.1
          have ordered : ∀ retained ∈ operators,
              retained.span.startByte ≤ base.span.endByte := by
            intro retained member
            have retainedValid := operatorsReply.1 retained member
            have beforeFirst := unaryOperators_endBeforeCurrentOnSuccess
              (input.remainingCount + 1) [] input operators afterOperators
                inputValid (by simp) operatorsResult retained member first
                  firstFound
            exact Nat.le_trans retainedValid.2.1
              (Nat.le_trans beforeFirst (by
                rw [baseStart]
                exact baseValid.span_valid.2.1))
          have wrappedValid := applyUnaryOperators_validFor statementValid
            input.file operators base operatorsReply.1 baseValid ordered
          exact ⟨wrappedValid, postfixReply.2.1,
            postfixReply.2.2.trans operatorsReply.2.2⟩

/-- Unary parsing preserves token windows when postfix parsing does. -/
theorem expressionUnary_preservesTokenWindow
    (nested : Parser Expr) (block : Parser Block)
    (postfixWindow : Parser.PreservesTokenWindow
      (expressionPostfix nested block)) :
    Parser.PreservesTokenWindow (expressionUnary nested block) := by
  intro input
  unfold expressionUnary
  have operatorsShape := unaryOperators_preservesTokenWindow
    (input.remainingCount + 1) [] input
  cases operatorsResult : unaryOperators (input.remainingCount + 1) [] input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [operatorsResult] at operatorsShape
      exact operatorsShape
  | ok operators afterOperators =>
      rw [operatorsResult] at operatorsShape
      simp only
      have postfixShape := postfixWindow afterOperators
      cases postfixResult : expressionPostfix nested block afterOperators with
      | invariant error => simp only; trivial
      | reject failure rejected =>
          rw [postfixResult] at postfixShape
          simp only
          exact postfixShape.trans operatorsShape
      | ok base next =>
          rw [postfixResult] at postfixShape
          simp only
          exact postfixShape.trans operatorsShape

theorem expressionUnary_preservesTokensOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (postfixWindow : Parser.PreservesTokenWindow
      (expressionPostfix nested block)) :
    Parser.PreservesTokensOnSuccess (expressionUnary nested block) :=
  (expressionUnary_preservesTokenWindow nested block
    postfixWindow).preservesTokensOnSuccess

/-- Unary parsing never rewinds when postfix parsing does not. -/
theorem expressionUnary_cursorMonotoneOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (postfixCursor : Parser.CursorMonotoneOnSuccess
      (expressionPostfix nested block)) :
    Parser.CursorMonotoneOnSuccess (expressionUnary nested block) := by
  intro input expression final parsed
  unfold expressionUnary at parsed
  cases operatorsResult : unaryOperators (input.remainingCount + 1) [] input with
  | invariant error => simp [operatorsResult] at parsed
  | reject failure rejected => simp [operatorsResult] at parsed
  | ok operators afterOperators =>
      simp only [operatorsResult] at parsed
      cases postfixResult : expressionPostfix nested block afterOperators with
      | invariant error => simp [postfixResult] at parsed
      | reject failure rejected => simp [postfixResult] at parsed
      | ok base next =>
          simp only [postfixResult] at parsed
          have postfixMonotone :=
            postfixCursor afterOperators base next postfixResult
          cases parsed
          exact Nat.le_trans
            (unaryOperators_cursorMonotoneOnSuccess
              (input.remainingCount + 1) [] input operators afterOperators
                operatorsResult)
            postfixMonotone

/-- A unary expression starts at its first operator or postfix token. -/
theorem expressionUnary_startsAtCurrentTokenOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (postfixStarts : Parser.StartsAtCurrentTokenOnSuccess
      (expressionPostfix nested block) (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (expressionUnary nested block) (·.span) := by
  intro input expression final parsed
  unfold expressionUnary at parsed
  cases operatorsResult : unaryOperators (input.remainingCount + 1) [] input with
  | invariant error => simp [operatorsResult] at parsed
  | reject failure rejected => simp [operatorsResult] at parsed
  | ok operators afterOperators =>
      simp only [operatorsResult] at parsed
      cases postfixResult : expressionPostfix nested block afterOperators with
      | invariant error => simp [postfixResult] at parsed
      | reject failure rejected => simp [postfixResult] at parsed
      | ok base next =>
          simp only [postfixResult] at parsed
          rcases unaryOperators_initialShapeOnSuccess
              (input.remainingCount + 1) input operators afterOperators
                operatorsResult with
            ⟨operatorsEmpty, stateEq⟩ | ⟨first, rest, token, found,
              firstSpan, operatorsEq⟩
          · subst operators
            subst afterOperators
            rcases postfixStarts input base next postfixResult with
              ⟨token, tokenFound, starts⟩
            cases parsed
            exact ⟨token, tokenFound, starts⟩
          · subst operators
            cases parsed
            exact ⟨token, found, by
              simp only [applyUnaryOperators_startByte, firstSpan]⟩

/-- A unary result retains the endpoint of its parsed postfix base. -/
theorem expressionUnary_retainsPostfixEndOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    {input final : State} {expression : Expr}
    (parsed : expressionUnary nested block input = .ok expression final) :
    ∃ operators afterOperators base,
      unaryOperators (input.remainingCount + 1) [] input =
        .ok operators afterOperators ∧
      expressionPostfix nested block afterOperators = .ok base final ∧
      expression.span.endByte = base.span.endByte := by
  unfold expressionUnary at parsed
  cases operatorsResult : unaryOperators (input.remainingCount + 1) [] input with
  | invariant error => simp [operatorsResult] at parsed
  | reject failure rejected => simp [operatorsResult] at parsed
  | ok operators afterOperators =>
      simp only [operatorsResult] at parsed
      cases postfixResult : expressionPostfix nested block afterOperators with
      | invariant error => simp [postfixResult] at parsed
      | reject failure rejected => simp [postfixResult] at parsed
      | ok base next =>
          simp only [postfixResult] at parsed
          cases parsed
          exact ⟨operators, afterOperators, base, rfl,
            by simpa using postfixResult,
            applyUnaryOperators_preservesBaseEnd operators base⟩

/-- Successful precedence lookup decodes the operator whose first token is the
current token, inside the active window. -/
theorem binaryAtPrecedence?_some_state_shape {input : State}
    {precedence : Nat} {operator : Located BinaryOp}
    (result : binaryAtPrecedence? input precedence = some operator) :
    ∃ token, input.peek? = some token ∧
      BinaryOp.at? input.tokens input.window.endIndex input.cursor = some operator ∧
      operator.value.precedence = precedence ∧
      input.cursor + operator.value.tokenCount ≤ input.window.endIndex := by
  unfold binaryAtPrecedence? at result
  cases decoded : BinaryOp.at? input.tokens input.window.endIndex input.cursor with
  | none => simp [decoded] at result
  | some found =>
      simp only [decoded] at result
      split at result
      · rename_i selected
        cases result
        rcases BinaryOp.at?_cases decoded with ⟨first, firstWithin, _⟩
        exact ⟨first, firstWithin, rfl, beq_iff_eq.mp selected,
          BinaryOp.at?_bound decoded⟩
      · contradiction

/-- Every recognized binary operator belongs to the active source. -/
theorem binaryAtPrecedence?_validFor {input : State}
    {precedence : Nat} {operator : Located BinaryOp}
    (inputValid : input.ValidFor)
    (result : binaryAtPrecedence? input precedence = some operator) :
    Located.ValidFor input.file operator := by
  rcases binaryAtPrecedence?_some_state_shape result with
    ⟨_token, _found, decoded, _precedence, _bound⟩
  rcases BinaryOp.at?_cases decoded with
    ⟨first, firstWithin, ⟨_, span⟩ | ⟨_, next, _, nextWithin, touching, span⟩⟩
  · have firstValid := inputValid.token_span_validFor_of_getElem?_eq_some
      (tokenWithin?_some firstWithin).2
    simpa only [Located.ValidFor, span] using firstValid
  · have firstValid := inputValid.token_span_validFor_of_getElem?_eq_some
      (tokenWithin?_some firstWithin).2
    have nextValid := inputValid.token_span_validFor_of_getElem?_eq_some
      (tokenWithin?_some nextWithin).2
    simp only [Located.ValidFor, span]
    apply SourceSpan.cover_validFor firstValid nextValid
    have firstOrdered := firstValid.2.1
    have nextOrdered := nextValid.2.1
    omega

/-- Binary consumption is the exact cursor update over the operator's tokens. -/
theorem consumeBinary_ok_state_shape (operator : Located BinaryOp)
    (input : State) :
    consumeBinary operator input =
      .ok () { input with cursor := input.cursor + operator.value.tokenCount } := rfl

/-- Consuming the tokens of a recognized operator preserves state validity. -/
theorem consumeBinary_reply_validFor (operator : Located BinaryOp)
    {input : State} (inputValid : input.ValidFor)
    (bound : input.cursor + operator.value.tokenCount ≤ input.window.endIndex) :
    (consumeBinary operator input).ValidFor input (fun _ _ => True) := by
  unfold consumeBinary modifyState Reply.ValidFor
  exact ⟨trivial, { inputValid with cursor_le_endIndex := bound }, rfl⟩

/-- Binary consumption preserves the immutable token window. -/
theorem consumeBinary_preservesTokenWindow (operator : Located BinaryOp) :
    Parser.PreservesTokenWindow (consumeBinary operator) :=
  modifyState_preservesTokenWindow _ (fun _ => ⟨rfl, rfl⟩)

theorem consumeBinary_preservesTokensOnSuccess
    (operator : Located BinaryOp) :
    Parser.PreservesTokensOnSuccess (consumeBinary operator) :=
  (consumeBinary_preservesTokenWindow operator).preservesTokensOnSuccess

/-- Binary consumption advances the cursor. -/
theorem consumeBinary_cursor_lt_onSuccess (operator : Located BinaryOp)
    {input final : State} {value : Unit}
    (result : consumeBinary operator input = .ok value final) :
    input.cursor < final.cursor := by
  unfold consumeBinary modifyState at result
  cases result
  have positive := BinaryOp.tokenCount_pos operator.value
  simp only
  omega

theorem consumeBinary_cursorMonotoneOnSuccess
    (operator : Located BinaryOp) :
    Parser.CursorMonotoneOnSuccess (consumeBinary operator) := by
  intro input value final result
  exact Nat.le_of_lt (consumeBinary_cursor_lt_onSuccess operator result)

/-- A binary node retains its two operands and operator provenance. -/
theorem binaryNode_validFor
    (statementValid : SourceFile → Statement → Prop) (file : SourceFile)
    (left : Expr) (operator : Located BinaryOp) (right : Expr)
    (leftValid : Expr.ValidFor statementValid file left)
    (operatorValid : Located.ValidFor file operator)
    (rightValid : Expr.ValidFor statementValid file right)
    (ordered : left.span.startByte ≤ right.span.endByte) :
    Expr.ValidFor statementValid file (binaryNode left operator right) := by
  unfold binaryNode
  exact Expr.ValidFor.binary
    (SourceSpan.cover_validFor leftValid.span_valid rightValid.span_valid ordered)
    leftValid (by simpa only [Located.ValidFor] using operatorValid) rightValid

@[simp] theorem binaryNode_startByte (left : Expr)
    (operator : Located BinaryOp) (right : Expr) :
    (binaryNode left operator right).span.startByte = left.span.startByte := rfl

@[simp] theorem binaryNode_endByte (left : Expr)
    (operator : Located BinaryOp) (right : Expr) :
    (binaryNode left operator right).span.endByte = right.span.endByte := rfl

/-- A left-associative tail preserves every ordinary token window. -/
theorem leftAssociativeTail_preservesTokenWindow (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) : ∀ fuel left,
    Parser.PreservesTokenWindow
      (leftAssociativeTail operand precedence fuel left) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input
      trivial
  | succ fuel inductionHypothesis =>
      intro left input
      unfold leftAssociativeTail
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => exact ⟨rfl, rfl⟩
      | some operator =>
          simp only
          have consumedShape := consumeBinary_preservesTokenWindow
            operator input
          cases consumedResult : consumeBinary operator input with
          | invariant error =>
              simp only
              trivial
          | reject failure rejected =>
              rw [consumedResult] at consumedShape
              simp only
              exact consumedShape
          | ok value afterOperator =>
              rw [consumedResult] at consumedShape
              simp only
              have operandShape := operandWindow afterOperator
              cases operandResult : operand afterOperator with
              | invariant error =>
                  simp only
                  trivial
              | reject failure rejected =>
                  rw [operandResult] at operandShape
                  simp only
                  exact operandShape.trans consumedShape
              | ok right next =>
                  rw [operandResult] at operandShape
                  simp only
                  exact (inductionHypothesis
                    (binaryNode left operator right) next).trans
                      (operandShape.trans consumedShape)

theorem leftAssociativeTail_preservesTokensOnSuccess
    (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence fuel : Nat) (left : Expr) :
    Parser.PreservesTokensOnSuccess
      (leftAssociativeTail operand precedence fuel left) :=
  (leftAssociativeTail_preservesTokenWindow operand operandWindow precedence
    fuel left).preservesTokensOnSuccess

/-- A left-associative tail never rewinds the parser cursor. -/
theorem leftAssociativeTail_cursorMonotoneOnSuccess
    (operand : Parser Expr)
    (operandCursor : Parser.CursorMonotoneOnSuccess operand)
    (precedence : Nat) : ∀ fuel left,
    Parser.CursorMonotoneOnSuccess
      (leftAssociativeTail operand precedence fuel left) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input expression final parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro left input expression final parsed
      unfold leftAssociativeTail at parsed
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          exact Nat.le_refl _
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator input with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              have consumedMonotone :=
                consumeBinary_cursorMonotoneOnSuccess operator input value
                  afterOperator consumedResult
              cases operandResult : operand afterOperator with
              | invariant error => simp [operandResult] at parsed
              | reject failure rejected => simp [operandResult] at parsed
              | ok right next =>
                  simp only [operandResult] at parsed
                  exact Nat.le_trans consumedMonotone
                    (Nat.le_trans
                      (operandCursor afterOperator right next operandResult)
                      (inductionHypothesis
                        (binaryNode left operator right) next expression final
                          parsed))

/-- Every successful left-associative tail keeps its original left edge. -/
theorem leftAssociativeTail_preservesLeftStartOnSuccess
    (operand : Parser Expr) (precedence : Nat) :
    ∀ fuel left input expression final,
      leftAssociativeTail operand precedence fuel left input =
        .ok expression final →
      expression.span.startByte = left.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro left input expression final parsed
      unfold leftAssociativeTail at parsed
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          rfl
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator input with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              cases operandResult : operand afterOperator with
              | invariant error => simp [operandResult] at parsed
              | reject failure rejected => simp [operandResult] at parsed
              | ok right next =>
                  simp only [operandResult] at parsed
                  simpa using inductionHypothesis
                    (binaryNode left operator right) next expression final
                      parsed

/-- A left-associative tail retains every operand and operator source range. -/
theorem leftAssociativeTail_validFor
    (operand : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (operandValid : operand.ValidFor (Expr.ValidFor statementValid))
    (operandTokens : Parser.PreservesTokensOnSuccess operand)
    (operandCursor : Parser.CursorMonotoneOnSuccess operand)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) : ∀ fuel left input,
    input.ValidFor →
    Expr.ValidFor statementValid input.file left →
    (∀ token, input.peek? = some token →
      left.span.startByte ≤ token.span.startByte) →
    (leftAssociativeTail operand precedence fuel left input).ValidFor input
      (Expr.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro left input inputValid leftValid leftBefore
      unfold leftAssociativeTail
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => exact ⟨leftValid, inputValid, rfl⟩
      | some operator =>
          simp only
          rcases binaryAtPrecedence?_some_state_shape operatorResult with
            ⟨operatorToken, operatorFound, _decoded, _precedence, operatorBound⟩
          have operatorPositive := BinaryOp.tokenCount_pos operator.value
          have operatorValid := binaryAtPrecedence?_validFor inputValid
            operatorResult
          have consumedReply := consumeBinary_reply_validFor operator
            inputValid operatorBound
          cases consumedResult : consumeBinary operator input with
          | invariant error => trivial
          | reject failure rejected =>
              rw [consumedResult] at consumedReply
              simp only
              exact consumedReply
          | ok value afterOperator =>
              rw [consumedResult] at consumedReply
              have exactConsumed := consumeBinary_ok_state_shape operator input
              rw [consumedResult] at exactConsumed
              cases exactConsumed
              simp only
              cases operandResult : operand
                  { input with cursor := input.cursor + operator.value.tokenCount } with
              | invariant error => trivial
              | reject failure rejected =>
                  have rejectedValid := operandValid
                    { input with cursor := input.cursor + operator.value.tokenCount }
                    consumedReply.2.1
                  rw [operandResult] at rejectedValid
                  simp only
                  exact rejectedValid.of_file_eq consumedReply.2.2
              | ok right next =>
                  have rightReply := operandValid
                    { input with cursor := input.cursor + operator.value.tokenCount }
                    consumedReply.2.1
                  rw [operandResult] at rightReply
                  have rightValidInput :
                      Expr.ValidFor statementValid input.file right := by
                    simpa [rightReply.2.2, consumedReply.2.2] using rightReply.1
                  rcases operandStarts
                      { input with cursor := input.cursor + operator.value.tokenCount } right next
                      operandResult with
                    ⟨rightToken, rightFound, rightStart⟩
                  have operatorAt :=
                    State.getElem?_eq_some_of_peek?_eq_some operatorFound
                  have rightAt : input.tokens[input.cursor + operator.value.tokenCount]? =
                      some rightToken := by
                    simpa using
                      State.getElem?_eq_some_of_peek?_eq_some rightFound
                  have separated :=
                    inputValid.token_end_le_token_start_of_getElem?_lt
                      operatorAt rightAt (by omega)
                  have operatorSpanValid :
                      operatorToken.span.ValidFor input.file :=
                    inputValid.peek?_span_validFor operatorFound
                  have ordered : left.span.startByte ≤ right.span.endByte := by
                    calc
                      left.span.startByte ≤ operatorToken.span.startByte :=
                        leftBefore operatorToken operatorFound
                      _ ≤ operatorToken.span.endByte := operatorSpanValid.2.1
                      _ ≤ rightToken.span.startByte := separated
                      _ = right.span.startByte := rightStart
                      _ ≤ right.span.endByte := rightValidInput.span_valid.2.1
                  have combinedValidInput := binaryNode_validFor statementValid
                    input.file left operator right leftValid operatorValid
                      rightValidInput ordered
                  have combinedValidNext : Expr.ValidFor statementValid
                      next.file (binaryNode left operator right) := by
                    simpa [rightReply.2.2, consumedReply.2.2] using
                      combinedValidInput
                  have tokensEq := operandTokens
                    { input with cursor := input.cursor + operator.value.tokenCount } right next
                      operandResult
                  have cursorOrder : input.cursor < next.cursor :=
                    Nat.lt_of_lt_of_le
                      (show input.cursor < input.cursor + operator.value.tokenCount by omega)
                      (operandCursor
                        { input with cursor := input.cursor + operator.value.tokenCount } right next
                          operandResult)
                  have combinedBefore : ∀ future,
                      next.peek? = some future →
                      (binaryNode left operator right).span.startByte ≤
                        future.span.startByte := by
                    intro future futureFound
                    have futureAtNext :=
                      State.getElem?_eq_some_of_peek?_eq_some futureFound
                    have futureAt : input.tokens[next.cursor]? = some future := by
                      simpa [tokensEq] using futureAtNext
                    have beforeFuture :=
                      inputValid.token_end_le_token_start_of_getElem?_lt
                        operatorAt futureAt cursorOrder
                    rw [binaryNode_startByte]
                    exact Nat.le_trans (leftBefore operatorToken operatorFound)
                      (Nat.le_trans operatorSpanValid.2.1 beforeFuture)
                  have recursive := inductionHypothesis
                    (binaryNode left operator right) next rightReply.2.1
                      combinedValidNext combinedBefore
                  simp only
                  exact recursive.of_file_eq
                    (rightReply.2.2.trans consumedReply.2.2)

/-- A complete left-associative layer preserves every ordinary token window. -/
theorem leftAssociative_preservesTokenWindow (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) :
    Parser.PreservesTokenWindow (leftAssociative operand precedence) := by
  intro input
  unfold leftAssociative
  have operandShape := operandWindow input
  cases operandResult : operand input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [operandResult] at operandShape
      exact operandShape
  | ok left next =>
      rw [operandResult] at operandShape
      exact (leftAssociativeTail_preservesTokenWindow operand operandWindow
        precedence (next.remainingCount + 1) left next).trans operandShape

theorem leftAssociative_preservesTokensOnSuccess (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) :
    Parser.PreservesTokensOnSuccess (leftAssociative operand precedence) :=
  (leftAssociative_preservesTokenWindow operand operandWindow
    precedence).preservesTokensOnSuccess

/-- A complete left-associative layer never rewinds the parser cursor. -/
theorem leftAssociative_cursorMonotoneOnSuccess (operand : Parser Expr)
    (operandCursor : Parser.CursorMonotoneOnSuccess operand)
    (precedence : Nat) :
    Parser.CursorMonotoneOnSuccess (leftAssociative operand precedence) := by
  intro input expression final parsed
  unfold leftAssociative at parsed
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at parsed
  | reject failure rejected => simp [operandResult] at parsed
  | ok left next =>
      simp only [operandResult] at parsed
      exact Nat.le_trans (operandCursor input left next operandResult)
        (leftAssociativeTail_cursorMonotoneOnSuccess operand operandCursor
          precedence (next.remainingCount + 1) left next expression final
            parsed)

/-- A complete left-associative layer retains its first operand's token. -/
theorem leftAssociative_startsAtCurrentTokenOnSuccess
    (operand : Parser Expr)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) :
    Parser.StartsAtCurrentTokenOnSuccess
      (leftAssociative operand precedence) (·.span) := by
  intro input expression final parsed
  unfold leftAssociative at parsed
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at parsed
  | reject failure rejected => simp [operandResult] at parsed
  | ok left next =>
      simp only [operandResult] at parsed
      rcases operandStarts input left next operandResult with
        ⟨first, found, starts⟩
      have retained := leftAssociativeTail_preservesLeftStartOnSuccess operand
        precedence (next.remainingCount + 1) left next expression final parsed
      exact ⟨first, found, starts.trans retained.symm⟩

/-- A complete left-associative layer retains all recursive source ranges. -/
theorem leftAssociative_validFor
    (operand : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (operandValid : operand.ValidFor (Expr.ValidFor statementValid))
    (operandTokens : Parser.PreservesTokensOnSuccess operand)
    (operandCursorLt : ∀ {input next : State} {value : Expr},
      operand input = .ok value next → input.cursor < next.cursor)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) :
    (leftAssociative operand precedence).ValidFor
      (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold leftAssociative
  cases operandResult : operand input with
  | invariant error => trivial
  | reject failure rejected =>
      have rejectedValid := operandValid input inputValid
      rw [operandResult] at rejectedValid
      exact rejectedValid
  | ok left next =>
      have leftReply := operandValid input inputValid
      rw [operandResult] at leftReply
      have leftValidNext : Expr.ValidFor statementValid next.file left := by
        simpa [leftReply.2.2] using leftReply.1
      have tokensEq := operandTokens input left next operandResult
      rcases operandStarts input left next operandResult with
        ⟨first, firstFound, firstStart⟩
      have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
      have firstValid := inputValid.peek?_span_validFor firstFound
      have leftBefore : ∀ token, next.peek? = some token →
          left.span.startByte ≤ token.span.startByte := by
        intro token found
        have tokenAtNext := State.getElem?_eq_some_of_peek?_eq_some found
        have tokenAt : input.tokens[next.cursor]? = some token := by
          simpa [tokensEq] using tokenAtNext
        have separated := inputValid.token_end_le_token_start_of_getElem?_lt
          firstAt tokenAt (operandCursorLt operandResult)
        exact Nat.le_trans (by simpa [firstStart] using firstValid.2.1)
          separated
      have recursive := leftAssociativeTail_validFor operand statementValid
        operandValid operandTokens
          (fun _ _ _ result => Nat.le_of_lt (operandCursorLt result))
          operandStarts precedence (next.remainingCount + 1) left next
          leftReply.2.1 leftValidNext leftBefore
      exact recursive.of_file_eq leftReply.2.2

/-- A non-associative precedence layer preserves every ordinary token window. -/
theorem nonAssociative_preservesTokenWindow (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) :
    Parser.PreservesTokenWindow (nonAssociative operand precedence) := by
  intro input
  unfold nonAssociative
  have leftShape := operandWindow input
  cases leftResult : operand input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [leftResult] at leftShape
      exact leftShape
  | ok left next =>
      rw [leftResult] at leftShape
      simp only
      cases operatorResult : binaryAtPrecedence? next precedence with
      | none =>
          simp only
          exact leftShape
      | some operator =>
          simp only
          have consumedShape := consumeBinary_preservesTokenWindow
            operator next
          cases consumedResult : consumeBinary operator next with
          | invariant error =>
              simp only
              trivial
          | reject failure rejected =>
              rw [consumedResult] at consumedShape
              simp only
              exact consumedShape.trans leftShape
          | ok value afterOperator =>
              rw [consumedResult] at consumedShape
              simp only
              have rightShape := operandWindow afterOperator
              cases rightResult : operand afterOperator with
              | invariant error =>
                  simp only
                  trivial
              | reject failure rejected =>
                  rw [rightResult] at rightShape
                  simp only
                  exact rightShape.trans (consumedShape.trans leftShape)
              | ok right final =>
                  rw [rightResult] at rightShape
                  simp only
                  exact rightShape.trans (consumedShape.trans leftShape)

theorem nonAssociative_preservesTokensOnSuccess (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) :
    Parser.PreservesTokensOnSuccess (nonAssociative operand precedence) :=
  (nonAssociative_preservesTokenWindow operand operandWindow
    precedence).preservesTokensOnSuccess

/-- A non-associative precedence layer never rewinds the parser cursor. -/
theorem nonAssociative_cursorMonotoneOnSuccess (operand : Parser Expr)
    (operandCursor : Parser.CursorMonotoneOnSuccess operand)
    (precedence : Nat) :
    Parser.CursorMonotoneOnSuccess (nonAssociative operand precedence) := by
  intro input expression final parsed
  unfold nonAssociative at parsed
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at parsed
  | reject failure rejected => simp [leftResult] at parsed
  | ok left next =>
      simp only [leftResult] at parsed
      have leftMonotone := operandCursor input left next leftResult
      cases operatorResult : binaryAtPrecedence? next precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          exact leftMonotone
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator next with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              have consumedMonotone :=
                consumeBinary_cursorMonotoneOnSuccess operator next value
                  afterOperator consumedResult
              cases rightResult : operand afterOperator with
              | invariant error => simp [rightResult] at parsed
              | reject failure rejected => simp [rightResult] at parsed
              | ok right afterRight =>
                  simp only [rightResult] at parsed
                  have rightMonotone :=
                    operandCursor afterOperator right afterRight rightResult
                  cases parsed
                  exact Nat.le_trans leftMonotone
                    (Nat.le_trans consumedMonotone rightMonotone)

/-- A non-associative layer retains its first operand's start token. -/
theorem nonAssociative_startsAtCurrentTokenOnSuccess
    (operand : Parser Expr)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) :
    Parser.StartsAtCurrentTokenOnSuccess
      (nonAssociative operand precedence) (·.span) := by
  intro input expression final parsed
  unfold nonAssociative at parsed
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at parsed
  | reject failure rejected => simp [leftResult] at parsed
  | ok left next =>
      simp only [leftResult] at parsed
      rcases operandStarts input left next leftResult with
        ⟨first, found, starts⟩
      cases operatorResult : binaryAtPrecedence? next precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          exact ⟨first, found, starts⟩
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator next with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              cases rightResult : operand afterOperator with
              | invariant error => simp [rightResult] at parsed
              | reject failure rejected => simp [rightResult] at parsed
              | ok right afterRight =>
                  simp only [rightResult] at parsed
                  cases parsed
                  exact ⟨first, found, by simpa using starts⟩

/-- A non-associative precedence layer retains all recursive source ranges. -/
theorem nonAssociative_validFor
    (operand : Parser Expr)
    (statementValid : SourceFile → Statement → Prop)
    (operandValid : operand.ValidFor (Expr.ValidFor statementValid))
    (operandTokens : Parser.PreservesTokensOnSuccess operand)
    (operandCursorLt : ∀ {input next : State} {value : Expr},
      operand input = .ok value next → input.cursor < next.cursor)
    (operandStarts :
      Parser.StartsAtCurrentTokenOnSuccess operand (·.span))
    (precedence : Nat) :
    (nonAssociative operand precedence).ValidFor
      (Expr.ValidFor statementValid) := by
  intro input inputValid
  unfold nonAssociative
  cases leftResult : operand input with
  | invariant error => trivial
  | reject failure rejected =>
      have rejectedValid := operandValid input inputValid
      rw [leftResult] at rejectedValid
      exact rejectedValid
  | ok left next =>
      have leftReply := operandValid input inputValid
      rw [leftResult] at leftReply
      simp only
      cases operatorResult : binaryAtPrecedence? next precedence with
      | none =>
          simp only
          exact leftReply
      | some operator =>
          simp only
          rcases binaryAtPrecedence?_some_state_shape operatorResult with
            ⟨operatorToken, operatorFound, _decoded, _precedence, operatorBound⟩
          have operatorPositive := BinaryOp.tokenCount_pos operator.value
          have operatorValidNext := binaryAtPrecedence?_validFor
            leftReply.2.1 operatorResult
          have leftTokens := operandTokens input left next leftResult
          rcases operandStarts input left next leftResult with
            ⟨leftToken, leftFound, leftStart⟩
          have leftAt := State.getElem?_eq_some_of_peek?_eq_some leftFound
          have operatorAtNext :=
            State.getElem?_eq_some_of_peek?_eq_some operatorFound
          have operatorAt : input.tokens[next.cursor]? = some operatorToken := by
            simpa [leftTokens] using operatorAtNext
          have beforeOperator :=
            inputValid.token_end_le_token_start_of_getElem?_lt leftAt
              operatorAt (operandCursorLt leftResult)
          have leftTokenValid := inputValid.peek?_span_validFor leftFound
          have leftBeforeOperator : left.span.startByte ≤
              operatorToken.span.startByte := by
            exact Nat.le_trans
              (by simpa [leftStart] using leftTokenValid.2.1) beforeOperator
          have consumedReply := consumeBinary_reply_validFor operator
            leftReply.2.1 operatorBound
          cases consumedResult : consumeBinary operator next with
          | invariant error =>
              simp only
              trivial
          | reject failure rejected =>
              rw [consumedResult] at consumedReply
              simp only
              exact consumedReply.of_file_eq leftReply.2.2
          | ok value afterOperator =>
              rw [consumedResult] at consumedReply
              have exactConsumed := consumeBinary_ok_state_shape operator next
              rw [consumedResult] at exactConsumed
              cases exactConsumed
              simp only
              cases rightResult : operand
                  { next with cursor := next.cursor + operator.value.tokenCount } with
              | invariant error =>
                  simp only
                  trivial
              | reject failure rejected =>
                  have rejectedValid := operandValid
                    { next with cursor := next.cursor + operator.value.tokenCount }
                    consumedReply.2.1
                  rw [rightResult] at rejectedValid
                  simp only
                  exact rejectedValid.of_file_eq
                    (consumedReply.2.2.trans leftReply.2.2)
              | ok right afterRight =>
                  have rightReply := operandValid
                    { next with cursor := next.cursor + operator.value.tokenCount }
                    consumedReply.2.1
                  rw [rightResult] at rightReply
                  have rightValidInput :
                      Expr.ValidFor statementValid input.file right := by
                    simpa [rightReply.2.2, consumedReply.2.2,
                      leftReply.2.2] using rightReply.1
                  rcases operandStarts
                      { next with cursor := next.cursor + operator.value.tokenCount } right afterRight
                      rightResult with
                    ⟨rightToken, rightFound, rightStart⟩
                  have rightAtAfter :=
                    State.getElem?_eq_some_of_peek?_eq_some rightFound
                  have rightAt : input.tokens[next.cursor + operator.value.tokenCount]? =
                      some rightToken := by
                    simpa [leftTokens] using rightAtAfter
                  have operatorBeforeRight :=
                    inputValid.token_end_le_token_start_of_getElem?_lt
                      operatorAt rightAt (by omega)
                  have operatorTokenValid :=
                    inputValid.token_span_validFor_of_getElem?_eq_some
                      operatorAt
                  have ordered : left.span.startByte ≤ right.span.endByte := by
                    calc
                      left.span.startByte ≤ operatorToken.span.startByte :=
                        leftBeforeOperator
                      _ ≤ operatorToken.span.endByte := operatorTokenValid.2.1
                      _ ≤ rightToken.span.startByte := operatorBeforeRight
                      _ = right.span.startByte := rightStart
                      _ ≤ right.span.endByte := rightValidInput.span_valid.2.1
                  have operatorValidInput : Located.ValidFor input.file
                      operator := by
                    simpa [leftReply.2.2] using operatorValidNext
                  have binaryValid := binaryNode_validFor statementValid
                    input.file left operator right leftReply.1
                      operatorValidInput rightValidInput ordered
                  exact ⟨binaryValid, rightReply.2.1,
                    rightReply.2.2.trans
                      (consumedReply.2.2.trans leftReply.2.2)⟩

/-- A conditional layer advances whenever its first alternative advances. -/
theorem conditional_cursor_lt_onSuccess
    (nested alternative : Parser Expr)
    (nestedCursor : Parser.CursorMonotoneOnSuccess nested)
    (alternativeCursorLt : ∀ {input next : State} {value : Expr},
      alternative input = .ok value next → input.cursor < next.cursor)
    {input final : State} {expression : Expr}
    (parsed : conditional nested alternative input = .ok expression final) :
    input.cursor < final.cursor := by
  unfold conditional at parsed
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at parsed
  | reject failure rejected => simp [alternativeResult] at parsed
  | ok condition next =>
      simp only [alternativeResult] at parsed
      exact Nat.lt_of_lt_of_le (alternativeCursorLt alternativeResult)
        (conditionalTail_cursorMonotoneOnSuccess nested alternative
          nestedCursor
          (fun _ _ _ result => Nat.le_of_lt (alternativeCursorLt result))
          (next.remainingCount + 1) [] condition next expression final parsed)

/-- Unary parsing advances whenever its postfix base advances. -/
theorem expressionUnary_cursor_lt_onSuccess
    (nested : Parser Expr) (block : Parser Block)
    (postfixCursorLt : ∀ {input next : State} {value : Expr},
      expressionPostfix nested block input = .ok value next →
        input.cursor < next.cursor)
    {input final : State} {expression : Expr}
    (parsed : expressionUnary nested block input = .ok expression final) :
    input.cursor < final.cursor := by
  unfold expressionUnary at parsed
  cases operatorsResult : unaryOperators (input.remainingCount + 1) [] input with
  | invariant error => simp [operatorsResult] at parsed
  | reject failure rejected => simp [operatorsResult] at parsed
  | ok operators afterOperators =>
      simp only [operatorsResult] at parsed
      cases postfixResult : expressionPostfix nested block afterOperators with
      | invariant error => simp [postfixResult] at parsed
      | reject failure rejected => simp [postfixResult] at parsed
      | ok base next =>
          simp only [postfixResult] at parsed
          cases parsed
          exact Nat.lt_of_le_of_lt
            (unaryOperators_cursorMonotoneOnSuccess
              (input.remainingCount + 1) [] input operators afterOperators
                operatorsResult)
            (postfixCursorLt postfixResult)

/-- A left-associative layer advances whenever its first operand advances. -/
theorem leftAssociative_cursor_lt_onSuccess
    (operand : Parser Expr)
    (operandCursorLt : ∀ {input next : State} {value : Expr},
      operand input = .ok value next → input.cursor < next.cursor)
    (precedence : Nat) {input final : State} {expression : Expr}
    (parsed : leftAssociative operand precedence input = .ok expression final) :
    input.cursor < final.cursor := by
  unfold leftAssociative at parsed
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at parsed
  | reject failure rejected => simp [operandResult] at parsed
  | ok left next =>
      simp only [operandResult] at parsed
      exact Nat.lt_of_lt_of_le (operandCursorLt operandResult)
        (leftAssociativeTail_cursorMonotoneOnSuccess operand
          (fun _ _ _ result => Nat.le_of_lt (operandCursorLt result))
          precedence (next.remainingCount + 1) left next expression final
            parsed)

/-- A non-associative layer advances whenever its first operand advances. -/
theorem nonAssociative_cursor_lt_onSuccess
    (operand : Parser Expr)
    (operandCursorLt : ∀ {input next : State} {value : Expr},
      operand input = .ok value next → input.cursor < next.cursor)
    (precedence : Nat) {input final : State} {expression : Expr}
    (parsed : nonAssociative operand precedence input = .ok expression final) :
    input.cursor < final.cursor := by
  unfold nonAssociative at parsed
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at parsed
  | reject failure rejected => simp [leftResult] at parsed
  | ok left next =>
      simp only [leftResult] at parsed
      have leftStrict := operandCursorLt leftResult
      cases operatorResult : binaryAtPrecedence? next precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          exact leftStrict
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator next with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              have consumedMonotone :=
                consumeBinary_cursorMonotoneOnSuccess operator next value
                  afterOperator consumedResult
              cases rightResult : operand afterOperator with
              | invariant error => simp [rightResult] at parsed
              | reject failure rejected => simp [rightResult] at parsed
              | ok right afterRight =>
                  simp only [rightResult] at parsed
                  cases parsed
                  exact Nat.lt_of_lt_of_le leftStrict
                    (Nat.le_trans consumedMonotone
                      (Nat.le_of_lt (operandCursorLt rightResult)))

/-- The compositional proof boundary required by one expression parser layer. -/
structure ExpressionContract
    (statementValid : SourceFile → Statement → Prop)
    (parser : Parser Expr) : Prop where
  validFor : parser.ValidFor (Expr.ValidFor statementValid)
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorLtOnSuccess : ∀ {input next : State} {value : Expr},
    parser input = .ok value next → input.cursor < next.cursor
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess parser (·.span)

namespace ExpressionContract

theorem preservesTokensOnSuccess
    {statementValid : SourceFile → Statement → Prop} {parser : Parser Expr}
    (contract : ExpressionContract statementValid parser) :
    Parser.PreservesTokensOnSuccess parser :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

theorem cursorMonotoneOnSuccess
    {statementValid : SourceFile → Statement → Prop} {parser : Parser Expr}
    (contract : ExpressionContract statementValid parser) :
    Parser.CursorMonotoneOnSuccess parser := by
  intro input value next parsed
  exact Nat.le_of_lt (contract.cursorLtOnSuccess parsed)

/-- Assemble the concrete recoverable atom contract. -/
theorem atom
    (statementValid : SourceFile → Statement → Prop)
    (nested : Parser Expr) (block : Parser Block)
    (nestedContract : ExpressionContract statementValid nested)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span)) :
    ExpressionContract statementValid (expressionAtom nested block) := {
  validFor := ExpressionAtomInternals.expressionAtom_validFor nested block
    statementValid nestedContract.validFor nestedContract.preservesTokenWindow
      blockValid blockStarts blockWindow
  preservesTokenWindow :=
    ExpressionAtomInternals.expressionAtom_preservesTokenWindow nested block
      nestedContract.preservesTokenWindow blockWindow
  cursorLtOnSuccess := fun parsed =>
    ExpressionAtomInternals.expressionAtom_cursor_lt_onSuccess nested block
      nestedContract.cursorMonotoneOnSuccess blockCursor parsed
  startsAtCurrentTokenOnSuccess :=
    ExpressionAtomInternals.expressionAtom_startsAtCurrentTokenOnSuccess
      nested block nestedContract.preservesTokenWindow blockWindow
}

/-- Assemble concrete atom and postfix parsing into one expression contract. -/
theorem concretePostfix
    (statementValid : SourceFile → Statement → Prop)
    (nested : Parser Expr) (block : Parser Block)
    (nestedContract : ExpressionContract statementValid nested)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span)) :
    ExpressionContract statementValid
      (expressionPostfix nested block) := by
  let atomContract := atom statementValid nested block nestedContract
    blockValid blockWindow blockCursor blockStarts
  exact {
    validFor := ExpressionAtomInternals.expressionPostfix_validFor nested block
      statementValid atomContract.validFor
        atomContract.preservesTokensOnSuccess atomContract.cursorLtOnSuccess
          atomContract.startsAtCurrentTokenOnSuccess nestedContract.validFor
            nestedContract.preservesTokensOnSuccess
              nestedContract.cursorMonotoneOnSuccess
    preservesTokenWindow :=
      ExpressionAtomInternals.expressionPostfix_preservesTokenWindow
        nested block atomContract.preservesTokenWindow
          nestedContract.preservesTokenWindow
    cursorLtOnSuccess := fun parsed =>
      ExpressionAtomInternals.expressionPostfix_cursor_lt_onSuccess
        nested block nestedContract.cursorMonotoneOnSuccess blockCursor parsed
    startsAtCurrentTokenOnSuccess :=
      ExpressionAtomInternals.expressionPostfix_startsAtCurrentTokenOnSuccess
        nested block atomContract.startsAtCurrentTokenOnSuccess
  }

/-- Lift a postfix contract through prefix unary parsing. -/
theorem unary
    (statementValid : SourceFile → Statement → Prop)
    (nested : Parser Expr) (block : Parser Block)
    (postfixContract : ExpressionContract statementValid
      (expressionPostfix nested block)) :
    ExpressionContract statementValid (expressionUnary nested block) := {
  validFor := expressionUnary_validFor nested block statementValid
    postfixContract.validFor postfixContract.startsAtCurrentTokenOnSuccess
  preservesTokenWindow := expressionUnary_preservesTokenWindow nested block
    postfixContract.preservesTokenWindow
  cursorLtOnSuccess := fun parsed =>
    expressionUnary_cursor_lt_onSuccess nested block
      postfixContract.cursorLtOnSuccess parsed
  startsAtCurrentTokenOnSuccess :=
    expressionUnary_startsAtCurrentTokenOnSuccess nested block
      postfixContract.startsAtCurrentTokenOnSuccess
}

/-- Lift an operand contract through one left-associative precedence. -/
theorem leftAssociative
    {statementValid : SourceFile → Statement → Prop} {operand : Parser Expr}
    (contract : ExpressionContract statementValid operand)
    (precedence : Nat) :
    ExpressionContract statementValid
      (ExpressionInternals.leftAssociative operand precedence) := {
  validFor := ExpressionInternals.leftAssociative_validFor operand
    statementValid contract.validFor contract.preservesTokensOnSuccess
      contract.cursorLtOnSuccess contract.startsAtCurrentTokenOnSuccess
        precedence
  preservesTokenWindow :=
    ExpressionInternals.leftAssociative_preservesTokenWindow operand
      contract.preservesTokenWindow precedence
  cursorLtOnSuccess := fun parsed =>
    ExpressionInternals.leftAssociative_cursor_lt_onSuccess operand
      contract.cursorLtOnSuccess precedence parsed
  startsAtCurrentTokenOnSuccess :=
    ExpressionInternals.leftAssociative_startsAtCurrentTokenOnSuccess operand
      contract.startsAtCurrentTokenOnSuccess precedence
}

/-- Lift an operand contract through one non-associative precedence. -/
theorem nonAssociative
    {statementValid : SourceFile → Statement → Prop} {operand : Parser Expr}
    (contract : ExpressionContract statementValid operand)
    (precedence : Nat) :
    ExpressionContract statementValid
      (ExpressionInternals.nonAssociative operand precedence) := {
  validFor := ExpressionInternals.nonAssociative_validFor operand
    statementValid contract.validFor contract.preservesTokensOnSuccess
      contract.cursorLtOnSuccess contract.startsAtCurrentTokenOnSuccess
        precedence
  preservesTokenWindow :=
    ExpressionInternals.nonAssociative_preservesTokenWindow operand
      contract.preservesTokenWindow precedence
  cursorLtOnSuccess := fun parsed =>
    ExpressionInternals.nonAssociative_cursor_lt_onSuccess operand
      contract.cursorLtOnSuccess precedence parsed
  startsAtCurrentTokenOnSuccess :=
    ExpressionInternals.nonAssociative_startsAtCurrentTokenOnSuccess operand
      contract.startsAtCurrentTokenOnSuccess precedence
}

/-- Lift recursive and alternative contracts through conditional parsing. -/
theorem conditional
    {statementValid : SourceFile → Statement → Prop}
    {nested alternative : Parser Expr}
    (nestedContract : ExpressionContract statementValid nested)
    (alternativeContract : ExpressionContract statementValid alternative) :
    ExpressionContract statementValid
      (ExpressionInternals.conditional nested alternative) := {
  validFor := ExpressionInternals.conditional_validFor nested alternative
    statementValid nestedContract.validFor
      nestedContract.preservesTokensOnSuccess
      nestedContract.cursorMonotoneOnSuccess alternativeContract.validFor
      alternativeContract.preservesTokensOnSuccess
      alternativeContract.cursorLtOnSuccess
      alternativeContract.startsAtCurrentTokenOnSuccess
  preservesTokenWindow :=
    ExpressionInternals.conditional_preservesTokenWindow nested alternative
      nestedContract.preservesTokenWindow
      alternativeContract.preservesTokenWindow
  cursorLtOnSuccess := fun parsed =>
    ExpressionInternals.conditional_cursor_lt_onSuccess nested alternative
      nestedContract.cursorMonotoneOnSuccess
      alternativeContract.cursorLtOnSuccess parsed
  startsAtCurrentTokenOnSuccess :=
    ExpressionInternals.conditional_startsAtCurrentTokenOnSuccess nested
      alternative alternativeContract.startsAtCurrentTokenOnSuccess
}

end ExpressionContract

/-- Assemble the complete precedence and conditional expression contract. -/
theorem expressionLayer_contract
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedContract : ExpressionContract statementValid nested)
    (postfixContract : ExpressionContract statementValid
      (expressionPostfix nested block)) :
    ExpressionContract statementValid (expressionLayer nested block) := by
  have unaryContract := ExpressionContract.unary statementValid nested block
    postfixContract
  have multiplyContract := ExpressionContract.leftAssociative unaryContract 9
  have addContract := ExpressionContract.leftAssociative multiplyContract 8
  have shiftContract := ExpressionContract.leftAssociative addContract 7
  have bitAndContract := ExpressionContract.leftAssociative shiftContract 6
  have bitXorContract := ExpressionContract.leftAssociative bitAndContract 5
  have bitOrContract := ExpressionContract.leftAssociative bitXorContract 4
  have relationalContract :=
    ExpressionContract.nonAssociative bitOrContract 3
  have equalityContract :=
    ExpressionContract.nonAssociative relationalContract 2
  have logicalAndContract :=
    ExpressionContract.leftAssociative equalityContract 1
  have logicalOrContract :=
    ExpressionContract.leftAssociative logicalAndContract 0
  simpa only [expressionLayer] using
    ExpressionContract.conditional nestedContract logicalOrContract

/-- Build the complete concrete expression layer from recursive and block
contracts, including recoverable atoms and postfix syntax. -/
theorem expressionLayer_concrete_contract
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedContract : ExpressionContract statementValid nested)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span)) :
    ExpressionContract statementValid (expressionLayer nested block) :=
  expressionLayer_contract nested block statementValid nestedContract
    (ExpressionContract.concretePostfix statementValid nested block nestedContract
      blockValid blockWindow blockCursor blockStarts)

theorem expressionLayer_validFor
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedContract : ExpressionContract statementValid nested)
    (postfixContract : ExpressionContract statementValid
      (expressionPostfix nested block)) :
    (expressionLayer nested block).ValidFor
      (Expr.ValidFor statementValid) :=
  (expressionLayer_contract nested block statementValid nestedContract
    postfixContract).validFor

theorem expressionLayer_preservesTokenWindow
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedContract : ExpressionContract statementValid nested)
    (postfixContract : ExpressionContract statementValid
      (expressionPostfix nested block)) :
    Parser.PreservesTokenWindow (expressionLayer nested block) :=
  (expressionLayer_contract nested block statementValid nestedContract
    postfixContract).preservesTokenWindow

theorem expressionLayer_preservesTokensOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedContract : ExpressionContract statementValid nested)
    (postfixContract : ExpressionContract statementValid
      (expressionPostfix nested block)) :
    Parser.PreservesTokensOnSuccess (expressionLayer nested block) :=
  (expressionLayer_contract nested block statementValid nestedContract
    postfixContract).preservesTokensOnSuccess

theorem expressionLayer_cursor_lt_onSuccess
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedContract : ExpressionContract statementValid nested)
    (postfixContract : ExpressionContract statementValid
      (expressionPostfix nested block))
    {input next : State} {value : Expr}
    (parsed : expressionLayer nested block input = .ok value next) :
    input.cursor < next.cursor :=
  (expressionLayer_contract nested block statementValid nestedContract
    postfixContract).cursorLtOnSuccess parsed

theorem expressionLayer_cursorMonotoneOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedContract : ExpressionContract statementValid nested)
    (postfixContract : ExpressionContract statementValid
      (expressionPostfix nested block)) :
    Parser.CursorMonotoneOnSuccess (expressionLayer nested block) :=
  (expressionLayer_contract nested block statementValid nestedContract
    postfixContract).cursorMonotoneOnSuccess

theorem expressionLayer_startsAtCurrentTokenOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (nestedContract : ExpressionContract statementValid nested)
    (postfixContract : ExpressionContract statementValid
      (expressionPostfix nested block)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (expressionLayer nested block) (·.span) :=
  (expressionLayer_contract nested block statementValid nestedContract
    postfixContract).startsAtCurrentTokenOnSuccess

end ExpressionInternals
end Solcore.Syntax.Parser
end
