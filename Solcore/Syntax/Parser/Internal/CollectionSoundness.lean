import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Internal.ExpressionOutcomes

/-!
Soundness of the parsers of parenthesized forms, array literals and postfix tails: each
success and each rejection has its declarative derivation, and diagnostic-free runs
reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionAtomRecoveryDiagnosticProperties
/-!
Diagnostic commitments at the public Core expression-atom recovery boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Finishing a recovered atom always commits its recovery diagnostic. -/
theorem finishRecoveredAtom_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) {input next : State} {value : Expr}
    (result : finishRecoveredAtom first last input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold finishRecoveredAtom at result
  cases result
  simp [State.emit]

/-- Every successful auxiliary atom recovery retains a diagnostic, including
success at a token boundary or at the active window end. -/
theorem recoverAtomAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : Expr},
      recoverAtomAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverAtomAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverAtomAux at recovered
      split at recovered
      · exact finishRecoveredAtom_diagnostics_ne_nil_onSuccess first last
          recovered
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            exact finishRecoveredAtom_diagnostics_ne_nil_onSuccess first last
              recovered
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- Every successful complete atom recovery commits a recovery diagnostic. -/
theorem recoverAtom_diagnostics_ne_nil_onSuccess
    {input next : State} {value : Expr}
    (recovered : recoverAtom input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold recoverAtom at recovered
  cases advanced : input.advance? with
  | none =>
      simp [advanced, rejectAt] at recovered
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at recovered
      exact recoverAtomAux_diagnostics_ne_nil_onSuccess token.span token.span
        (afterToken.remainingCount + 1) recovered

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- A diagnostic-free public atom success is exactly the unchanged successful
result of the non-recovering Core atom parser. -/
theorem expressionAtomCore_of_diagnosticFree_success
    (nested : Parser Expr) (block : Parser Block)
    {input next : State} {value : Expr}
    (result : expressionAtom nested block input = .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    ExpressionAtomInternals.expressionAtomCore nested block input =
      .ok value next := by
  unfold expressionAtom at result
  cases coreResult : ExpressionAtomInternals.expressionAtomCore nested block
      input with
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if ExpressionAtomInternals.isAtomBoundary rewound then
          .reject failure rewound
        else ExpressionAtomInternals.recoverAtom
          (rewound.emit failure.toDiagnostic)) = .ok value next at result
      split at result
      · contradiction
      · exact False.elim
          (ExpressionAtomInternals.recoverAtom_diagnostics_ne_nil_onSuccess
            result diagnosticFree)
  | invariant error =>
      simp [coreResult] at result

/-- Diagnostic reflection for the public recoverable atom parser reduces to
diagnostic reflection for its non-recovering Core branch. -/
theorem expressionAtom_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (coreReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (ExpressionAtomInternals.expressionAtomCore nested block)) :
    Parser.ReflectsDiagnosticFreeOnSuccess (expressionAtom nested block) := by
  intro input value next result diagnosticFree
  exact coreReflects input value next
    (expressionAtomCore_of_diagnosticFree_success nested block result
      diagnosticFree)
    diagnosticFree

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionCollectionAtomDiagnosticReflectionProperties
/-!
Diagnostic reflection for parenthesized and array Core expression atoms.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem closeTuple_reflectsDiagnosticFreeOnSuccess
    (opening : Token) (elementsRev : List Expr) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closeTuple opening elementsRev) := by
  unfold closeTuple
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .expression)
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  | cons head tail =>
      cases tail with
      | nil => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
      | cons second rest => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Tuple-tail success reflects diagnostic freedom through every element. -/
theorem tupleTail_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (opening : Token) : ∀ fuel elementsRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (tupleTail nested opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input value next result
      simp [tupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input value next result diagnosticFree
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          split at result
          · have afterCommaFree :=
              closeTuple_reflectsDiagnosticFreeOnSuccess opening elementsRev
                afterComma value next result diagnosticFree
            exact symbol_reflectsDiagnosticFreeOnSuccess .comma .expression
              input comma afterComma commaResult afterCommaFree
          · cases elementResult : nested afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok element afterElement =>
                simp only [elementResult] at result
                split at result
                · split at result
                  · have afterElementFree := inductionHypothesis
                        (element :: elementsRev) afterElement value next result
                          diagnosticFree
                    have afterCommaFree := nestedReflects afterComma element
                      afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .expression input comma afterComma commaResult
                        afterCommaFree
                  · have afterElementFree :=
                        closeTuple_reflectsDiagnosticFreeOnSuccess opening
                          (element :: elementsRev) afterElement value next
                            result diagnosticFree
                    have afterCommaFree := nestedReflects afterComma element
                      afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .expression input comma afterComma commaResult
                        afterCommaFree
                · contradiction

/-- Parenthesized atom success reflects through its nested parser. -/
theorem parenthesized_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parenthesized nested) := by
  intro input value next result diagnosticFree
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      split at result
      · have afterOpeningFree :=
          closeTuple_reflectsDiagnosticFreeOnSuccess opening [] afterOpening
            value next result diagnosticFree
        exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen .expression
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
                    tupleTail_reflectsDiagnosticFreeOnSuccess nested
                      nestedReflects opening (afterFirst.remainingCount + 1)
                        [first] afterFirst value next result diagnosticFree
                have afterOpeningFree := nestedReflects afterOpening first
                  afterFirst elementResult afterFirstFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen
                  .expression input opening afterOpening openingResult
                    afterOpeningFree
              · have afterFirstFree :=
                    closeTuple_reflectsDiagnosticFreeOnSuccess opening [first]
                      afterFirst value next result diagnosticFree
                have afterOpeningFree := nestedReflects afterOpening first
                  afterFirst elementResult afterFirstFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen
                  .expression input opening afterOpening openingResult
                    afterOpeningFree

/-- Array atom success reflects through every nested element. -/
theorem arrayLiteral_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (arrayLiteral nested) := by
  unfold arrayLiteral
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess .leftBracket
      .rightBracket true nested .expression .expression nestedReflects)
  intro values
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionCollectionAtomSoundnessProperties
/-!
Exact diagnostic-free soundness for parenthesized and array Core atoms.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

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

private theorem closeParenthesizedExpression_eq_tuple_of_length_ne_one
    (openingSpan closingSpan : SourceSpan) (elements : List Expr)
    (lengthNe : elements.length ≠ 1) :
    DeclarativeGrammar.closeParenthesizedExpression openingSpan closingSpan
      elements = {
        span := SourceSpan.cover openingSpan closingSpan
        value := .tuple {
          span := SourceSpan.cover openingSpan closingSpan
          elements
        }
      } := by
  unfold DeclarativeGrammar.closeParenthesizedExpression
  cases elements with
  | nil => rfl
  | cons head tail =>
      cases tail with
      | nil => simp at lengthNe
      | cons second rest => rfl

private theorem closeTuple_success_sound (opening : Token)
    (elementsRev : List Expr) {input next : State} {value : Expr}
    (result : closeTuple opening elementsRev input = .ok value next) :
    ∃ closingSpan,
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span
        closingSpan elementsRev.reverse ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
        input.declarativeRemainder closingSpan next.declarativeRemainder := by
  unfold closeTuple at result
  rcases bind_success_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have closingParsed := symbol_success_exactTokenParses .rightParen
    .expression closingResult
  cases elementsRev with
  | nil =>
      cases finished
      exact ⟨closing.span, by
        simp [DeclarativeGrammar.closeParenthesizedExpression], closingParsed⟩
  | cons head tail =>
      cases tail with
      | nil =>
          cases finished
          exact ⟨closing.span, by
            simp [DeclarativeGrammar.closeParenthesizedExpression],
              closingParsed⟩
      | cons second rest =>
          cases finished
          refine ⟨closing.span, ?_, closingParsed⟩
          rw [closeParenthesizedExpression_eq_tuple_of_length_ne_one]
          simp

private theorem tupleTail_success_sound_strong
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input value next,
      next.diagnosticsRev = [] →
      tupleTail nested opening fuel elementsRev input = .ok value next →
      ∃ suffix closingSpan,
        value = DeclarativeGrammar.closeParenthesizedExpression opening.span
          closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedTupleTailParses nestedParses
          input.declarativeRemainder suffix closingSpan
            next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input value next diagnosticFree result
      simp [tupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input value next diagnosticFree result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .expression commaResult
          split at result
          · rcases closeTuple_success_sound opening elementsRev result with
              ⟨closingSpan, valueEq, closingParsed⟩
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
                next elementProgress =>
                  split at result
                  next commaPresent =>
                    rcases inductionHypothesis (element :: elementsRev)
                        afterElement value next diagnosticFree result with
                      ⟨suffix, closingSpan, valueEq, tailGrammar⟩
                    have afterElementFree :=
                      tupleTail_reflectsDiagnosticFreeOnSuccess nested
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
                    rcases closeTuple_success_sound opening
                        (element :: elementsRev) result with
                      ⟨closingSpan, valueEq, closingParsed⟩
                    have afterElementFree :=
                      closeTuple_reflectsDiagnosticFreeOnSuccess opening
                        (element :: elementsRev) afterElement value next result
                          diagnosticFree
                    have elementGrammar := nestedSound afterElementFree
                      elementResult
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                      .comma (input := afterElement) (by simp_all)
                    refine ⟨[element], closingSpan, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) commaAbsent
                          closingParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using valueEq
                next noProgress => contradiction

/-- Every diagnostic-free parenthesized success follows its exact grammar. -/
theorem parenthesized_success_sound
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : parenthesized nested input = .ok value next) :
    DeclarativeGrammar.ParenthesizedExpressionParses nestedParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .expression openingResult
      split at result
      · rcases closeTuple_success_sound opening [] result with
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
                rcases tupleTail_success_sound_strong nested nestedParses
                    nestedReflects nestedSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst value
                        next diagnosticFree result with
                  ⟨rest, closingSpan, valueEq, tailGrammar⟩
                have afterFirstFree :=
                  tupleTail_reflectsDiagnosticFreeOnSuccess nested
                    nestedReflects opening (afterFirst.remainingCount + 1)
                      [first] afterFirst value next result diagnosticFree
                have firstGrammar := nestedSound afterFirstFree elementResult
                subst value
                simpa using (DeclarativeGrammar.ParenthesizedExpressionParses.tuple
                  opening.span closingSpan openingParsed closingAbsent
                    firstGrammar (by
                      simpa [State.declarativeRemainder] using
                        firstProgress) tailGrammar)
              next commaAbsentBranch =>
                rcases closeTuple_success_sound opening [first] result with
                  ⟨closingSpan, valueEq, closingParsed⟩
                have afterFirstFree :=
                  closeTuple_reflectsDiagnosticFreeOnSuccess opening [first]
                    afterFirst value next result diagnosticFree
                have firstGrammar := nestedSound afterFirstFree elementResult
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                  .comma (input := afterFirst) (by simp_all)
                subst value
                exact .group opening.span closingSpan openingParsed
                  closingAbsent firstGrammar (by
                    simpa [State.declarativeRemainder] using
                      firstProgress) commaAbsent
                    closingParsed

/-- Every diagnostic-free array success follows its no-trailing grammar. -/
theorem arrayLiteral_success_sound
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : arrayLiteral nested input = .ok value next) :
    DeclarativeGrammar.ArrayLiteralExpressionParses nestedParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold arrayLiteral at result
  rcases bind_success_components result with
    ⟨values, afterValues, valuesResult, finished⟩
  cases finished
  exact .parsed
    (delimitedNoTrailing_allowEmpty_success_sound_of_diagnosticFree
      .leftBracket .rightBracket nested nestedParses .expression .expression
        nestedSound nestedReflects nestedShape diagnosticFree valuesResult)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreArrayLiteralOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for guarded Core array literals. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable array-literal success retains its exact brackets,
source-order elements, covering span, AST, and output remainder. -/
theorem arrayLiteral_success_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State} {expression : Expr}
    (result : arrayLiteral nested input = .ok expression output) :
    DeclarativeGrammar.ArrayLiteralExpressionOrdinaryParses nestedOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold arrayLiteral at result
  cases valuesResult :
      delimitedNoTrailing .leftBracket .rightBracket true nested .expression
        .expression input with
  | invariant error => simp [bind, valuesResult] at result
  | reject failure rejected => simp [bind, valuesResult] at result
  | ok values afterValues =>
      simp only [bind, valuesResult, pure] at result
      cases result
      exact .parsed
        (delimitedNoTrailing_allowEmpty_success_sound .leftBracket
          .rightBracket nested nestedOrdinary .expression .expression
            nestedSuccessSound nestedShape valuesResult)

/-- Under the dispatcher's positive `[` guard, every executable rejection is
the exact allow-empty, no-trailing delimiter rejection. -/
theorem arrayLiteral_reject_ordinary_sound
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
    (openingPresent : isSymbol input .leftBracket = true)
    (result : arrayLiteral nested input = .reject failure rejected) :
    DeclarativeGrammar.ArrayLiteralExpressionRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold arrayLiteral at result
  cases valuesResult :
      delimitedNoTrailing .leftBracket .rightBracket true nested .expression
        .expression input with
  | invariant error => simp [bind, valuesResult] at result
  | ok values afterValues => simp [bind, valuesResult, pure] at result
  | reject valuesFailure valuesRejected =>
      simp only [bind, valuesResult] at result
      cases result
      rcases symbol_eq_ok_of_isSymbol_eq_true .leftBracket .expression
          openingPresent with ⟨opening, openingResult⟩
      exact .present opening.span
        (symbol_success_exactTokenParses .leftBracket .expression
          openingResult).1
        (delimitedNoTrailing_reject_sound .leftBracket .rightBracket true
          nested nestedOrdinary nestedRejects .expression .expression
            nestedSuccessSound nestedRejectSound valuesResult)

/-- Package executable array success and guarded rejection. -/
theorem arrayLiteral_guardedOrdinaryOutcome_sound
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
      arrayLiteral nested input = .ok expression output →
        DeclarativeGrammar.ArrayLiteralExpressionOrdinaryParses
          nestedOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isSymbol input .leftBracket = true →
        arrayLiteral nested input = .reject failure rejected →
          DeclarativeGrammar.ArrayLiteralExpressionRejects nestedOrdinary
            nestedRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨arrayLiteral_success_ordinary_sound nested nestedOrdinary
      nestedSuccessSound nestedShape,
    arrayLiteral_reject_ordinary_sound nested nestedOrdinary nestedRejects
      nestedSuccessSound nestedRejectSound⟩

/-- Lift a deterministic nested expression outcome to arrays. -/
theorem arrayLiteral_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ArrayLiteralExpressionOrdinaryParses
        nestedOrdinary)
      (DeclarativeGrammar.ArrayLiteralExpressionRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.arrayLiteralExpressionDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreParenthesizedOrdinarySuccessSoundnessProperties
/-! Unconditional ordinary-success reflection for Core parentheses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem closeTuple_success_ordinary_sound (opening : Token)
    (elementsRev : List Expr) {input output : State} {expression : Expr}
    (result : closeTuple opening elementsRev input = .ok expression output) :
    ∃ closingSpan,
      expression = DeclarativeGrammar.closeParenthesizedExpression
        opening.span closingSpan elementsRev.reverse ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
        input.declarativeRemainder closingSpan
          output.declarativeRemainder := by
  unfold closeTuple at result
  rcases bind_success_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have closingParsed := symbol_success_exactTokenParses .rightParen
    .expression closingResult
  cases elementsRev with
  | nil =>
      cases finished
      exact ⟨closing.span, by
        simp [DeclarativeGrammar.closeParenthesizedExpression],
          closingParsed⟩
  | cons head tail =>
      cases tail with
      | nil =>
          cases finished
          exact ⟨closing.span, by
            simp [DeclarativeGrammar.closeParenthesizedExpression],
              closingParsed⟩
      | cons second rest =>
          cases finished
          refine ⟨closing.span, ?_, closingParsed⟩
          rw [closeParenthesizedExpression_eq_tuple_of_length_ne_one]
          simp

/-- Successful tuple-tail execution follows the exact source-order ordinary
tail grammar. Fuel exhaustion and no-progress cannot inhabit this theorem. -/
theorem tupleTail_success_ordinary_sound_strong
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input expression output,
      tupleTail nested opening fuel elementsRev input = .ok expression output →
      ∃ suffix closingSpan,
        expression = DeclarativeGrammar.closeParenthesizedExpression
          opening.span closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedTupleTailParses nestedOrdinary
          input.declarativeRemainder suffix closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input expression output result
      simp [tupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input expression output result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .expression commaResult
          split at result
          · rcases closeTuple_success_ordinary_sound opening elementsRev
                result with ⟨closingSpan, expressionEq, closingParsed⟩
            exact ⟨[], closingSpan, by simpa using expressionEq,
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
                next elementProgress =>
                  have elementGrammar := nestedSuccessSound elementResult
                  split at result
                  next commaPresent =>
                    rcases inductionHypothesis (element :: elementsRev)
                        afterElement expression output result with
                      ⟨suffix, closingSpan, expressionEq, tailGrammar⟩
                    refine ⟨element :: suffix, closingSpan, ?_,
                      .next comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) tailGrammar⟩
                    simpa [List.reverse_cons, List.append_assoc] using
                      expressionEq
                  next commaAbsentBranch =>
                    rcases closeTuple_success_ordinary_sound opening
                        (element :: elementsRev) result with
                      ⟨closingSpan, expressionEq, closingParsed⟩
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                      .comma (input := afterElement) (by simp_all)
                    refine ⟨[element], closingSpan, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) commaAbsent closingParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using
                      expressionEq
                next noProgress => contradiction

/-- Every executable parenthesized success follows the exact empty, group,
or tuple ordinary grammar without requiring diagnostic freedom. -/
theorem parenthesized_success_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : parenthesized nested input = .ok expression output) :
    DeclarativeGrammar.ParenthesizedExpressionOrdinaryParses nestedOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .expression openingResult
      split at result
      · rcases closeTuple_success_ordinary_sound opening [] result with
          ⟨closingSpan, expressionEq, closingParsed⟩
        subst expression
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
              have firstGrammar := nestedSuccessSound elementResult
              split at result
              next commaPresent =>
                rcases tupleTail_success_ordinary_sound_strong nested
                    nestedOrdinary nestedSuccessSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst
                        expression output result with
                  ⟨rest, closingSpan, expressionEq, tailGrammar⟩
                subst expression
                simpa using
                  (DeclarativeGrammar.ParenthesizedExpressionParses.tuple
                    opening.span closingSpan openingParsed closingAbsent
                      firstGrammar (by
                        simpa [State.declarativeRemainder] using firstProgress)
                        tailGrammar)
              next commaAbsentBranch =>
                rcases closeTuple_success_ordinary_sound opening [first]
                    result with
                  ⟨closingSpan, expressionEq, closingParsed⟩
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                  .comma (input := afterFirst) (by simp_all)
                subst expression
                exact .group opening.span closingSpan openingParsed
                  closingAbsent firstGrammar (by
                    simpa [State.declarativeRemainder] using firstProgress)
                      commaAbsent closingParsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreParenthesizedOrdinaryRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for guarded Core parentheses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem closeTuple_reject_ordinary_sound (opening : Token)
    (elementsRev : List Expr) {input rejected : State} {failure : Failure}
    (result : closeTuple opening elementsRev input =
      .reject failure rejected) :
    rejected = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.symbol .rightParen) := by
  unfold closeTuple at result
  cases closingResult : symbol .rightParen .expression input with
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
      exact ⟨symbol_reject_state_eq .rightParen .expression closingResult,
        symbol_reject_tokenKindAbsentAt .rightParen .expression
          closingResult⟩

/-- Every tuple-tail rejection under its positive comma guard follows exactly
the nested-element, missing-closing, or later-tail branch. -/
theorem tupleTail_reject_ordinary_sound
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
    (opening : Token) : ∀ fuel elementsRev input failure rejected,
      isSymbol input .comma = true →
      tupleTail nested opening fuel elementsRev input =
        .reject failure rejected →
      DeclarativeGrammar.ParenthesizedTupleTailRejects nestedOrdinary
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input failure rejected commaPresent result
      simp [tupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input failure rejected commaPresent result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject commaFailure commaRejected =>
          rcases symbol_eq_ok_of_isSymbol_eq_true .comma .expression
              commaPresent with ⟨comma, parsed⟩
          rw [parsed] at commaResult
          contradiction
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .expression commaResult
          by_cases closingPresent : isSymbol afterComma .rightParen
          · simp only [closingPresent, if_true] at result
            rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression
                closingPresent with ⟨closing, closingResult⟩
            unfold closeTuple at result
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
                by_cases progressed : afterElement.cursor > afterComma.cursor
                · simp only [progressed, if_true] at result
                  have elementParsed := nestedSuccessSound elementResult
                  have progress : afterComma.declarativeRemainder.cursor <
                      afterElement.declarativeRemainder.cursor := by
                    simpa [State.declarativeRemainder] using progressed
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
                    rcases closeTuple_reject_ordinary_sound opening
                        (element :: elementsRev) result with
                      ⟨rejectedEq, rightParenAbsent⟩
                    subst rejectedEq
                    exact .closingMissing comma.span commaParsed closingAbsent
                      elementParsed progress
                      (symbolAbsentAt_of_isSymbol_eq_false .comma
                        commaAbsentBool) rightParenAbsent
                · simp [progressed] at result

/-- Under the dispatcher's positive `(` guard, every parenthesized rejection
is the exact first-element, closing, or tuple-tail rejection. -/
theorem parenthesized_reject_ordinary_sound
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
    (openingPresent : isSymbol input .leftParen = true)
    (result : parenthesized nested input = .reject failure rejected) :
    DeclarativeGrammar.ParenthesizedExpressionRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression
          openingPresent with ⟨opening, parsed⟩
      rw [parsed] at openingResult
      contradiction
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .expression openingResult
      by_cases closingPresent : isSymbol afterOpening .rightParen
      · simp only [closingPresent, if_true] at result
        rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression
            closingPresent with ⟨closing, closingResult⟩
        unfold closeTuple at result
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
            by_cases progressed : afterFirst.cursor > afterOpening.cursor
            · have notLe : ¬ afterFirst.cursor ≤ afterOpening.cursor := by
                exact Nat.not_le_of_lt progressed
              simp only [notLe, if_false] at result
              have firstParsed := nestedSuccessSound firstResult
              have progress : afterOpening.declarativeRemainder.cursor <
                  afterFirst.declarativeRemainder.cursor := by
                simpa [State.declarativeRemainder] using progressed
              by_cases commaPresent : isSymbol afterFirst .comma
              · simp only [commaPresent, if_true] at result
                exact .tailRejected opening.span openingParsed closingAbsent
                  firstParsed progress
                  (tupleTail_reject_ordinary_sound nested nestedOrdinary
                    nestedRejects nestedSuccessSound nestedRejectSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst
                        failure rejected commaPresent result)
              · have commaAbsentBool : isSymbol afterFirst .comma = false :=
                  Bool.eq_false_iff.mpr commaPresent
                simp only [commaAbsentBool, Bool.false_eq_true, if_false]
                  at result
                rcases closeTuple_reject_ordinary_sound opening [first]
                    result with ⟨rejectedEq, rightParenAbsent⟩
                subst rejectedEq
                exact .closingMissing opening.span openingParsed closingAbsent
                  firstParsed progress
                    (symbolAbsentAt_of_isSymbol_eq_false .comma
                      commaAbsentBool) rightParenAbsent
            · have le : afterFirst.cursor ≤ afterOpening.cursor :=
                Nat.le_of_not_gt progressed
              simp [le] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreParenthesizedOrdinaryOutcomeSoundnessProperties
/-! Packaged executable ordinary outcomes for guarded Core parentheses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Package unconditional parenthesized success with exact rejection under
the atom dispatcher's positive opening-parenthesis guard. -/
theorem parenthesized_guardedOrdinaryOutcome_sound
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
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      parenthesized nested input = .ok expression output →
        DeclarativeGrammar.ParenthesizedExpressionOrdinaryParses
          nestedOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isSymbol input .leftParen = true →
        parenthesized nested input = .reject failure rejected →
          DeclarativeGrammar.ParenthesizedExpressionRejects nestedOrdinary
            nestedRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨parenthesized_success_ordinary_sound nested nestedOrdinary
      nestedSuccessSound,
    parenthesized_reject_ordinary_sound nested nestedOrdinary nestedRejects
      nestedSuccessSound nestedRejectSound⟩

/-- Lift a deterministic nested expression outcome to parentheses. -/
theorem parenthesized_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ParenthesizedExpressionOrdinaryParses
        nestedOrdinary)
      (DeclarativeGrammar.ParenthesizedExpressionRejects nestedOrdinary
        nestedRejects) :=
  DeclarativeGrammar.parenthesizedExpressionDeterministicOutcomeSpec
    nestedOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionPostfixOrdinaryRejectionSoundnessProperties
/-!
Exact executable rejection bridges for maximal Core postfix expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable postfix-tail rejection follows the exact selected suffix
branch and subordinate ordinary outcome. -/
theorem postfixTail_reject_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
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
    ∀ fuel base input failure rejected,
      postfixTail nested block fuel base input = .reject failure rejected →
      DeclarativeGrammar.PostfixTailRejects nestedOrdinary nestedRejects
        input.declarativeRemainder base rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro base input failure rejected result
      simp [postfixTail] at result
  | succ fuel inductionHypothesis =>
      intro base input failure rejected result
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at result
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject openingFailure openingRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .leftBracket .expression
                indexed with ⟨opening, parsed⟩
            rw [parsed] at openingResult
            contradiction
        | ok opening afterOpening =>
            simp only [openingResult] at result
            have openingParsed := symbol_success_exactTokenParses .leftBracket
              .expression openingResult
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at result
            | reject indexFailure indexRejected =>
                simp only [indexResult] at result
                cases result
                exact .indexNestedRejected opening.span openingParsed
                  (nestedRejectSound indexResult)
            | ok index afterIndex =>
                simp only [indexResult] at result
                have indexParsed := nestedSuccessSound indexResult
                cases closingResult : symbol .rightBracket .expression
                    afterIndex with
                | invariant error => simp [closingResult] at result
                | reject closingFailure closingRejected =>
                    have rejectedEq := symbol_reject_state_eq .rightBracket
                      .expression closingResult
                    subst rejectedEq
                    simp only [closingResult] at result
                    cases result
                    exact .indexClosingMissing opening.span openingParsed
                      indexParsed
                      (symbol_reject_tokenKindAbsentAt .rightBracket
                        .expression closingResult)
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    exact .indexLaterRejected opening.span closing.span
                      openingParsed indexParsed
                      (symbol_success_exactTokenParses .rightBracket
                        .expression closingResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span closing.span
                        value := .index base
                          (SourceSpan.cover opening.span closing.span) index
                      } afterClosing failure rejected result)
      · have indexedFalse : isSymbol input .leftBracket = false :=
          Bool.eq_false_iff.mpr indexed
        simp only [indexedFalse, Bool.false_eq_true, if_false] at result
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftBracket
          indexedFalse
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at result
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject argumentsFailure argumentsRejected =>
              simp only [argumentsResult] at result
              cases result
              rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression
                  called with ⟨opening, openingResult⟩
              exact .callArgumentsRejected opening.span indexAbsent
                (symbol_success_exactTokenParses .leftParen .expression
                  openingResult).1
                (delimitedNoTrailing_reject_sound .leftParen .rightParen true
                  nested nestedOrdinary nestedRejects .expression .expression
                    nestedSuccessSound nestedRejectSound argumentsResult)
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              exact .callLaterRejected indexAbsent
                (delimitedNoTrailing_allowEmpty_success_sound .leftParen
                  .rightParen nested nestedOrdinary .expression .expression
                    nestedSuccessSound nestedShape argumentsResult)
                (inductionHypothesis {
                  span := SourceSpan.cover base.span arguments.span
                  value := .call base arguments
                } afterArguments failure rejected result)
        · have calledFalse : isSymbol input .leftParen = false :=
            Bool.eq_false_iff.mpr called
          simp only [calledFalse, Bool.false_eq_true, if_false] at result
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftParen
            calledFalse
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at result
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject dotFailure dotRejected =>
                rcases symbol_eq_ok_of_isSymbol_eq_true .dot .expression field
                  with ⟨dot, parsed⟩
                rw [parsed] at dotResult
                contradiction
            | ok dot afterDot =>
                simp only [dotResult] at result
                have dotParsed := symbol_success_exactTokenParses .dot
                  .expression dotResult
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at result
                | reject nameFailure nameRejected =>
                    simp only [nameResult] at result
                    cases result
                    exact .fieldNameRejected dot.span indexAbsent callAbsent
                      dotParsed (identifier_reject_sound .expression nameResult)
                | ok name afterName =>
                    simp only [nameResult] at result
                    exact .fieldLaterRejected dot.span indexAbsent callAbsent
                      dotParsed (identifier_success_sound .expression
                        nameResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span name.span
                        value := .field base dot.span name
                      } afterName failure rejected result)
          · have fieldFalse : isSymbol input .dot = false :=
              Bool.eq_false_iff.mpr field
            simp [fieldFalse] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- Every executable complete-postfix rejection is either atom rejection or
an exact rejection after ordinary atom success. -/
theorem expressionPostfix_reject_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomOrdinary nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomRejects nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (atomSuccessSound : ∀ {input output : State} {expression : Expr},
      expressionAtom nested block input = .ok expression output →
        atomOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (atomRejectSound : ∀ {input rejected : State} {failure : Failure},
      expressionAtom nested block input = .reject failure rejected →
        atomRejects input.declarativeRemainder rejected.declarativeRemainder)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input rejected : State} {failure : Failure}
    (result : expressionPostfix nested block input =
      .reject failure rejected) :
    DeclarativeGrammar.ExpressionPostfixRejects atomOrdinary nestedOrdinary
      atomRejects nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject atomFailure atomRejected =>
      simp only [atomResult] at result
      cases result
      exact .atomRejected (atomRejectSound atomResult)
  | ok base afterAtom =>
      simp only [atomResult] at result
      exact .tailRejected (atomSuccessSound atomResult)
        (ExpressionAtomInternals.postfixTail_reject_ordinary_sound nested block
          nestedOrdinary nestedRejects nestedSuccessSound nestedRejectSound
            nestedShape (afterAtom.remainingCount + 1) base afterAtom failure
              rejected result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionPostfixDiagnosticReflectionProperties
/-!
Backward propagation of diagnostic freedom through Core postfix parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- A successful postfix tail cannot erase an incoming diagnostic. -/
theorem postfixTail_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    ∀ fuel base,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (postfixTail nested block fuel base) := by
  intro fuel
  induction fuel with
  | zero =>
      intro base input expression next result diagnosticFree
      simp [postfixTail] at result
  | succ fuel inductionHypothesis =>
      intro base input expression next result diagnosticFree
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at result
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject failure rejected => simp [openingResult] at result
        | ok opening afterOpening =>
            simp only [openingResult] at result
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at result
            | reject failure rejected => simp [indexResult] at result
            | ok index afterIndex =>
                simp only [indexResult] at result
                cases closingResult : symbol .rightBracket .expression
                    afterIndex with
                | invariant error => simp [closingResult] at result
                | reject failure rejected => simp [closingResult] at result
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    have afterClosingFree := inductionHypothesis {
                      span := SourceSpan.cover base.span closing.span
                      value := .index base
                        (SourceSpan.cover opening.span closing.span) index
                    } afterClosing expression next result diagnosticFree
                    have afterIndexFree :=
                      symbol_reflectsDiagnosticFreeOnSuccess .rightBracket
                        .expression afterIndex closing afterClosing
                          closingResult afterClosingFree
                    have afterOpeningFree := nestedReflects afterOpening index
                      afterIndex indexResult afterIndexFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .leftBracket
                      .expression input opening afterOpening openingResult
                        afterOpeningFree
      · simp only [indexed, Bool.false_eq_true, if_false] at result
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at result
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              have afterArgumentsFree := inductionHypothesis {
                span := SourceSpan.cover base.span arguments.span
                value := .call base arguments
              } afterArguments expression next result diagnosticFree
              exact delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
                .leftParen .rightParen true nested .expression .expression
                  nestedReflects input arguments afterArguments
                    argumentsResult afterArgumentsFree
        · simp only [called, Bool.false_eq_true, if_false] at result
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at result
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject failure rejected => simp [dotResult] at result
            | ok dot afterDot =>
                simp only [dotResult] at result
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at result
                | reject failure rejected => simp [nameResult] at result
                | ok name afterName =>
                    simp only [nameResult] at result
                    have afterNameFree := inductionHypothesis {
                      span := SourceSpan.cover base.span name.span
                      value := .field base dot.span name
                    } afterName expression next result diagnosticFree
                    have afterDotFree :=
                      identifier_reflectsDiagnosticFreeOnSuccess .expression
                        afterDot name afterName nameResult afterNameFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .dot
                      .expression input dot afterDot dotResult afterDotFree
          · simp only [field] at result
            cases result
            exact diagnosticFree

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- Complete postfix parsing reflects diagnostic freedom through its atom and
all recursively parsed suffix contents. -/
theorem expressionPostfix_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (atomReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtom nested block))
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block) := by
  intro input expression next result diagnosticFree
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base afterAtom =>
      simp only [atomResult] at result
      have afterAtomFree :=
        ExpressionAtomInternals.postfixTail_reflectsDiagnosticFreeOnSuccess
          nested block nestedReflects (afterAtom.remainingCount + 1) base
            afterAtom expression next result diagnosticFree
      exact atomReflects input base afterAtom atomResult afterAtomFree

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionPostfixSoundnessProperties
/-!
Exact parser-independent soundness for maximal Core postfix parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every diagnostic-free postfix-tail success follows the exact maximal
index/call/field grammar, including branch priority and stopping evidence. -/
theorem postfixTail_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    ∀ fuel base input expression next,
      next.diagnosticsRev = [] →
      postfixTail nested block fuel base input = .ok expression next →
      DeclarativeGrammar.PostfixTailParses nestedParses
        input.declarativeRemainder base expression
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro base input expression next diagnosticFree result
      simp [postfixTail] at result
  | succ fuel inductionHypothesis =>
      intro base input expression next diagnosticFree result
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at result
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject failure rejected => simp [openingResult] at result
        | ok opening afterOpening =>
            simp only [openingResult] at result
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at result
            | reject failure rejected => simp [indexResult] at result
            | ok index afterIndex =>
                simp only [indexResult] at result
                cases closingResult : symbol .rightBracket .expression
                    afterIndex with
                | invariant error => simp [closingResult] at result
                | reject failure rejected => simp [closingResult] at result
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    have afterClosingFree :=
                      postfixTail_reflectsDiagnosticFreeOnSuccess nested block
                        nestedReflects fuel {
                          span := SourceSpan.cover base.span closing.span
                          value := .index base
                            (SourceSpan.cover opening.span closing.span) index
                        } afterClosing expression next result diagnosticFree
                    have afterIndexFree :=
                      symbol_reflectsDiagnosticFreeOnSuccess .rightBracket
                        .expression afterIndex closing afterClosing
                          closingResult afterClosingFree
                    exact .index opening.span closing.span
                      (symbol_success_exactTokenParses .leftBracket
                        .expression openingResult)
                      (nestedSound afterIndexFree indexResult)
                      (symbol_success_exactTokenParses .rightBracket
                        .expression closingResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span closing.span
                        value := .index base
                          (SourceSpan.cover opening.span closing.span) index
                      } afterClosing expression next diagnosticFree result)
      · simp only [indexed, Bool.false_eq_true, if_false] at result
        have indexedFalse : isSymbol input .leftBracket = false := by
          simp_all
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false
          .leftBracket indexedFalse
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at result
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              have afterArgumentsFree :=
                postfixTail_reflectsDiagnosticFreeOnSuccess nested block
                  nestedReflects fuel {
                    span := SourceSpan.cover base.span arguments.span
                    value := .call base arguments
                  } afterArguments expression next result diagnosticFree
              exact .call indexAbsent
                (delimitedNoTrailing_allowEmpty_success_sound_of_diagnosticFree
                  .leftParen .rightParen nested nestedParses .expression
                    .expression nestedSound nestedReflects nestedShape
                      afterArgumentsFree argumentsResult)
                (inductionHypothesis {
                  span := SourceSpan.cover base.span arguments.span
                  value := .call base arguments
                } afterArguments expression next diagnosticFree result)
        · simp only [called, Bool.false_eq_true, if_false] at result
          have calledFalse : isSymbol input .leftParen = false := by
            simp_all
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false
            .leftParen calledFalse
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at result
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject failure rejected => simp [dotResult] at result
            | ok dot afterDot =>
                simp only [dotResult] at result
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at result
                | reject failure rejected => simp [nameResult] at result
                | ok name afterName =>
                    simp only [nameResult] at result
                    exact .field dot.span indexAbsent callAbsent
                      (symbol_success_exactTokenParses .dot .expression
                        dotResult)
                      (identifier_success_sound .expression nameResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span name.span
                        value := .field base dot.span name
                      } afterName expression next diagnosticFree result)
          · simp only [field] at result
            cases result
            have fieldFalse : isSymbol input .dot = false := by
              simp_all
            exact .done ⟨indexAbsent, callAbsent,
              symbolAbsentAt_of_isSymbol_eq_false .dot fieldFalse⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free complete postfix success consists of one supplied
atom followed by its exact maximal postfix suffix sequence. -/
theorem expressionPostfix_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomParses nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] →
      expressionAtom nested block input = .ok value next →
      atomParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {expression : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionPostfix nested block input = .ok expression next) :
    DeclarativeGrammar.ExpressionPostfixParses atomParses nestedParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base afterAtom =>
      simp only [atomResult] at result
      have afterAtomFree :=
        ExpressionAtomInternals.postfixTail_reflectsDiagnosticFreeOnSuccess
          nested block nestedReflects (afterAtom.remainingCount + 1) base
            afterAtom expression next result diagnosticFree
      exact ⟨base, afterAtom.declarativeRemainder,
        atomSound afterAtomFree atomResult,
        ExpressionAtomInternals.postfixTail_success_sound nested block
          nestedParses nestedReflects nestedSound nestedShape
            (afterAtom.remainingCount + 1) base afterAtom expression next
              diagnosticFree result⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionPostfixOrdinarySuccessSoundnessProperties
/-!
Unconditional ordinary-success bridges for maximal Core postfix parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable postfix-tail success follows the exact prioritized,
maximal ordinary suffix grammar, independently of diagnostics. -/
theorem postfixTail_success_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {value : Expr},
      nested input = .ok value output →
        nestedOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    ∀ fuel base input expression output,
      postfixTail nested block fuel base input = .ok expression output →
        DeclarativeGrammar.PostfixTailOrdinaryParses nestedOrdinary
          input.declarativeRemainder base expression
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro base input expression output result
      simp [postfixTail] at result
  | succ fuel inductionHypothesis =>
      intro base input expression output result
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at result
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject failure rejected => simp [openingResult] at result
        | ok opening afterOpening =>
            simp only [openingResult] at result
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at result
            | reject failure rejected => simp [indexResult] at result
            | ok index afterIndex =>
                simp only [indexResult] at result
                cases closingResult : symbol .rightBracket .expression
                    afterIndex with
                | invariant error => simp [closingResult] at result
                | reject failure rejected => simp [closingResult] at result
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    exact .index opening.span closing.span
                      (symbol_success_exactTokenParses .leftBracket
                        .expression openingResult)
                      (nestedSuccessSound indexResult)
                      (symbol_success_exactTokenParses .rightBracket
                        .expression closingResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span closing.span
                        value := .index base
                          (SourceSpan.cover opening.span closing.span) index
                      } afterClosing expression output result)
      · simp only [indexed, Bool.false_eq_true, if_false] at result
        have indexedFalse : isSymbol input .leftBracket = false := by
          simp_all
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false
          .leftBracket indexedFalse
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at result
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              exact .call indexAbsent
                (delimitedNoTrailing_allowEmpty_success_sound
                  .leftParen .rightParen nested nestedOrdinary .expression
                    .expression nestedSuccessSound nestedShape argumentsResult)
                (inductionHypothesis {
                  span := SourceSpan.cover base.span arguments.span
                  value := .call base arguments
                } afterArguments expression output result)
        · simp only [called, Bool.false_eq_true, if_false] at result
          have calledFalse : isSymbol input .leftParen = false := by
            simp_all
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false
            .leftParen calledFalse
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at result
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject failure rejected => simp [dotResult] at result
            | ok dot afterDot =>
                simp only [dotResult] at result
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at result
                | reject failure rejected => simp [nameResult] at result
                | ok name afterName =>
                    simp only [nameResult] at result
                    exact .field dot.span indexAbsent callAbsent
                      (symbol_success_exactTokenParses .dot .expression
                        dotResult)
                      (identifier_success_sound .expression nameResult)
                      (inductionHypothesis {
                        span := SourceSpan.cover base.span name.span
                        value := .field base dot.span name
                      } afterName expression output result)
          · simp only [field] at result
            cases result
            have fieldFalse : isSymbol input .dot = false := by
              simp_all
            exact .done ⟨indexAbsent, callAbsent,
              symbolAbsentAt_of_isSymbol_eq_false .dot fieldFalse⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- Every executable complete postfix success consists of one supplied
ordinary atom followed by its exact maximal ordinary suffix sequence. -/
theorem expressionPostfix_success_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomOrdinary nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomSuccessSound : ∀ {input output : State} {value : Expr},
      expressionAtom nested block input = .ok value output →
        atomOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (nestedSuccessSound : ∀ {input output : State} {value : Expr},
      nested input = .ok value output →
        nestedOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State} {expression : Expr}
    (result : expressionPostfix nested block input = .ok expression output) :
    DeclarativeGrammar.ExpressionPostfixOrdinaryParses atomOrdinary
      nestedOrdinary input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base afterAtom =>
      simp only [atomResult] at result
      exact ⟨base, afterAtom.declarativeRemainder,
        atomSuccessSound atomResult,
        ExpressionAtomInternals.postfixTail_success_ordinary_sound
          nested block nestedOrdinary nestedSuccessSound nestedShape
            (afterAtom.remainingCount + 1) base afterAtom expression output
              result⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionPostfixOrdinaryOutcomeSoundnessProperties
/-!
Composed executable ordinary outcomes for maximal Core postfix expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package both complete-postfix executable bridges over supplied atom and
recursive outcomes. -/
theorem expressionPostfix_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomOrdinary nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomRejects nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (atomSuccessSound : ∀ {input output : State} {expression : Expr},
      expressionAtom nested block input = .ok expression output →
        atomOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (atomRejectSound : ∀ {input rejected : State} {failure : Failure},
      expressionAtom nested block input = .reject failure rejected →
        atomRejects input.declarativeRemainder rejected.declarativeRemainder)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    (∀ {input output : State} {expression : Expr},
      expressionPostfix nested block input = .ok expression output →
        DeclarativeGrammar.ExpressionPostfixOrdinaryParses atomOrdinary
          nestedOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionPostfix nested block input = .reject failure rejected →
        DeclarativeGrammar.ExpressionPostfixRejects atomOrdinary
          nestedOrdinary atomRejects nestedRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨expressionPostfix_success_ordinary_sound nested block atomOrdinary
      nestedOrdinary atomSuccessSound nestedSuccessSound nestedShape,
    expressionPostfix_reject_ordinary_sound nested block atomOrdinary
      nestedOrdinary atomRejects nestedRejects atomSuccessSound atomRejectSound
        nestedSuccessSound nestedRejectSound nestedShape⟩

/-- Lift deterministic atom and recursive outcomes to the complete postfix
layer. -/
theorem expressionPostfix_ordinaryOutcomeSpec
    {atomOrdinary nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {atomRejects nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (atomOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec atomOrdinary
      atomRejects)
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ExpressionPostfixOrdinaryParses atomOrdinary
        nestedOrdinary)
      (DeclarativeGrammar.ExpressionPostfixRejects atomOrdinary nestedOrdinary
        atomRejects nestedRejects) :=
  DeclarativeGrammar.expressionPostfixDeterministicOutcomeSpec atomOutcomes
    nestedOutcomes

end Solcore.Syntax.Parser
end
