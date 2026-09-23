import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.DeclarativeTraitMethodOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.FunctionSignatureOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionSignatureOrdinarySuccessSoundnessProperties
import Solcore.Syntax.DeclarativeTraitMethodExactnessProperties
import Solcore.Syntax.DeclarativeTraitBodyOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.DeclarativeTraitBodyExactnessProperties
import Solcore.Syntax.DeclarativeTraitDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.DeclarativeTraitDeclarationExactnessProperties
import Solcore.Syntax.Parser.FunctionProperties
import Solcore.Syntax.CallableDeclarationValidity
import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.FunctionSignatureTotalityProperties
import Solcore.Syntax.Parser.GenericParametersTotalityProperties
import Solcore.Syntax.Parser.WhereClauseTotalityProperties
import Solcore.Syntax.Parser.FunctionSignatureDiagnosticReflectionProperties
import Solcore.Syntax.Parser.FunctionSignatureSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseSoundnessProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TraitInternals

/-- Parse one signature-only trait method. -/
def traitMethod : Parser TraitMethod := do
  let signature ← functionSignature .module
  let semicolon ← symbol .semicolon .topItem
  pure {
    span := SourceSpan.cover signature.span semicolon.span
    value := {
      leadingComments := []
      signature
      semicolon := semicolon.span
    }
  }

structure TraitBody where
  span : SourceSpan
  methods : List TraitMethod

def closeTraitBody (opening : Token)
    (methodsRev : List TraitMethod) : Parser TraitBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    methods := methodsRev.reverse
  }

def traitMethods (opening : Token) :
    Nat → List TraitMethod → State → Reply TraitBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, methodsRev, state =>
      if isSymbol state .rightBrace then
        closeTraitBody opening methodsRev state
      else if isKeyword state .functionKw then
        let before := state.cursor
        match traitMethod state with
        | .ok value next =>
            if next.cursor > before then
              traitMethods opening fuel (value :: methodsRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        rejectAt state {
          head := .keyword .functionKw
          tail := [.symbol .rightBrace]
        } .topItem

def traitBody : Parser TraitBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      traitMethods opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end TraitInternals

/-- Parse a canonical trait declaration and signature-only methods. -/
def traitDecl : Parser TraitDecl := do
  let marker ← contextual .trait .topItem
  let name ← identifier .topItem
  let genericParameters ← genericParameters
  let whereClause ← whereClause
  let body ← TraitInternals.traitBody
  pure {
    span := SourceSpan.cover marker.span body.span
    value := {
      name
      genericParameters
      whereClause
      bodySpan := body.span
      methods := body.methods
    }
  }

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitMethodOrdinaryRejectionSoundnessProperties`
-/

/-! Exact broad ordinary rejection for signature-only trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- Every executable trait-method rejection occurs in its broad signature or
at its exact, non-consuming missing-semicolon stage. -/
theorem traitMethod_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : traitMethod input = .reject failure rejected) :
    DeclarativeGrammar.TraitMethodRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold traitMethod at result
  cases signatureResult : functionSignature .module input with
  | invariant error => simp [bind, signatureResult] at result
  | reject signatureFailure signatureRejected =>
      simp only [bind, signatureResult] at result
      cases result
      exact .signatureRejected
        (functionSignature_reject_ordinaryOutcome_sound .module
          signatureResult)
  | ok signature afterSignature =>
      simp only [bind, signatureResult] at result
      have signatureParsed := functionSignature_success_ordinaryOutcome_sound
        .module signatureResult
      cases semicolonResult : symbol .semicolon .topItem afterSignature with
      | invariant error => simp [semicolonResult] at result
      | ok semicolon output => simp [semicolonResult, pure] at result
      | reject semicolonFailure semicolonRejected =>
          have semicolonRejectedEq := symbol_reject_state_eq .semicolon
            .topItem semicolonResult
          subst semicolonRejected
          simp only [semicolonResult] at result
          cases result
          exact .semicolonMissing signatureParsed
            (symbol_reject_tokenKindAbsentAt .semicolon .topItem
              semicolonResult)

end Solcore.Syntax.Parser.TraitInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitMethodOrdinarySuccessSoundnessProperties`
-/

/-! Broad ordinary-success soundness for signature-only trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem traitMethodOrdinarySuccess_bind_ok_components {alpha beta : Type}
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

namespace TraitInternals

/-- Every executable trait-method success records its broad module-location
signature, exact semicolon, AST cover span, empty trivia, and remainder. -/
theorem traitMethod_success_ordinaryOutcome_sound
    {input output : State} {method : TraitMethod}
    (result : traitMethod input = .ok method output) :
    DeclarativeGrammar.TraitMethodOrdinaryParses
      input.declarativeRemainder method output.declarativeRemainder := by
  unfold traitMethod at result
  rcases traitMethodOrdinarySuccess_bind_ok_components result with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases traitMethodOrdinarySuccess_bind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed semicolon.span
    (functionSignature_success_ordinaryOutcome_sound .module signatureResult)
    (symbol_success_exactTokenParses .semicolon .topItem semicolonResult)

end TraitInternals
end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitMethodOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable broad ordinary outcomes for trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- Package executable trait-method success and exact rejection. -/
theorem traitMethod_ordinaryOutcome_sound :
    (∀ {input output : State} {method : TraitMethod},
      traitMethod input = .ok method output →
        DeclarativeGrammar.TraitMethodOrdinaryParses
          input.declarativeRemainder method output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      traitMethod input = .reject failure rejected →
        DeclarativeGrammar.TraitMethodRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨traitMethod_success_ordinaryOutcome_sound,
    traitMethod_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad trait-method outcomes. -/
theorem traitMethod_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TraitMethodOrdinaryParses
      DeclarativeGrammar.TraitMethodRejects :=
  DeclarativeGrammar.traitMethodDeterministicOutcomeSpec

/-- Re-export unconditional exact trait-method outcomes. -/
theorem traitMethod_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TraitMethodOrdinaryParses
      DeclarativeGrammar.TraitMethodRejects :=
  DeclarativeGrammar.traitMethodExactOutcomeSpec

/-- Two successful trait methods have the same AST and declarative remainder. -/
theorem traitMethod_success_result_unique
    {input leftOutput rightOutput : State} {left right : TraitMethod}
    (leftResult : traitMethod input = .ok left leftOutput)
    (rightResult : traitMethod input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitMethodOrdinaryParses.result_unique
    (traitMethod_success_ordinaryOutcome_sound leftResult)
    (traitMethod_success_ordinaryOutcome_sound rightResult)

/-- Two trait-method rejections have the same declarative endpoint. -/
theorem traitMethod_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : traitMethod input = .reject leftFailure leftOutput)
    (rightResult : traitMethod input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitMethodRejects.output_unique
    (traitMethod_reject_ordinaryOutcome_sound leftResult)
    (traitMethod_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.TraitInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitBodyOrdinaryRejectionSoundnessProperties`
-/

/-! Exact broad ordinary rejection for the custom trait-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

private theorem traitBodyOrdinaryRejection_functionPresent_of_isKeyword_eq_true
    {input : State}
    (present : isKeyword input .functionKw = true) :
    DeclarativeGrammar.TraitMethodStartAt input.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses .functionKw .topItem result).1⟩

private theorem traitMethods_reject_ordinaryOutcome_sound
    (opening : Token) :
    ∀ fuel methodsRev input failure rejected,
      traitMethods opening fuel methodsRev input = .reject failure rejected →
      DeclarativeGrammar.TraitMethodTailRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input failure rejected result
      simp [traitMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input failure rejected result
      unfold traitMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .topItem
              closingPresent with ⟨closing, closingResult⟩
          unfold closeTraitBody at result
          simp [bind, closingResult, pure] at result
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases functionPresent : isKeyword input .functionKw with
          | false =>
              simp only [functionPresent, Bool.false_eq_true, if_false]
                at result
              unfold rejectAt at result
              cases result
              exact .unexpected
                (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                  closingPresent)
                (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                  functionPresent)
          | true =>
              simp only [functionPresent, if_true] at result
              cases methodResult : traitMethod input with
              | invariant error => simp [methodResult] at result
              | reject methodFailure methodRejected =>
                  simp only [methodResult] at result
                  cases result
                  exact .methodRejected
                    (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                      closingPresent)
                    (traitBodyOrdinaryRejection_functionPresent_of_isKeyword_eq_true
                      functionPresent)
                    (traitMethod_reject_ordinaryOutcome_sound methodResult)
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    exact .laterRejected
                      (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                        closingPresent)
                      (traitBodyOrdinaryRejection_functionPresent_of_isKeyword_eq_true
                        functionPresent)
                      (traitMethod_success_ordinaryOutcome_sound methodResult)
                      progress
                      (inductionHypothesis (method :: methodsRev) afterMethod
                        failure rejected result)
                  · simp [progress] at result

/-- Every executable trait-body rejection records opening failure or the exact
first rejection of its prioritized broad method tail. -/
theorem traitBody_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : traitBody input = .reject failure rejected) :
    DeclarativeGrammar.TraitBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold traitBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have rejectedEq := symbol_reject_state_eq .leftBrace .topItem
        openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .topItem openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      exact .tailRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        (traitMethods_reject_ordinaryOutcome_sound opening
          (afterOpening.remainingCount + 1) [] afterOpening failure rejected
            result)

end Solcore.Syntax.Parser.TraitInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitBodyOrdinarySuccessSoundnessProperties`
-/

/-! Broad ordinary-success soundness for the custom trait-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

private theorem traitBodyOrdinarySuccess_bind_ok_components {alpha beta : Type}
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

private theorem traitBodyOrdinarySuccess_functionPresent_of_isKeyword_eq_true
    {input : State}
    (present : isKeyword input .functionKw = true) :
    DeclarativeGrammar.TraitMethodStartAt input.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses .functionKw .topItem result).1⟩

private theorem closeTraitBody_success_ordinary_sound (opening : Token)
    (methodsRev : List TraitMethod) {input output : State} {body : TraitBody}
    (result : closeTraitBody opening methodsRev input = .ok body output) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        methods := methodsRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan output.declarativeRemainder := by
  unfold closeTraitBody at result
  rcases traitBodyOrdinarySuccess_bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult⟩

private theorem traitMethods_success_ordinary_sound_strong
    (opening : Token) :
    ∀ fuel methodsRev input body output,
      traitMethods opening fuel methodsRev input = .ok body output →
      ∃ methods closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          methods := methodsRev.reverse ++ methods
        } ∧
        DeclarativeGrammar.TraitMethodTailOrdinaryParses
          input.declarativeRemainder methods closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body output result
      simp [traitMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input body output result
      unfold traitMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeTraitBody_success_ordinary_sound opening methodsRev
              result with ⟨closingSpan, bodyEq, closingParsed⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingParsed⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases functionPresent : isKeyword input .functionKw with
          | false => simp [functionPresent, rejectAt] at result
          | true =>
              simp only [functionPresent, if_true] at result
              cases methodResult : traitMethod input with
              | invariant error => simp [methodResult] at result
              | reject failure rejected => simp [methodResult] at result
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (method :: methodsRev)
                        afterMethod body output result with
                      ⟨methods, closingSpan, bodyEq, tailParsed⟩
                    refine ⟨method :: methods, closingSpan, ?_,
                      .next
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        (traitBodyOrdinarySuccess_functionPresent_of_isKeyword_eq_true
                          functionPresent)
                        (traitMethod_success_ordinaryOutcome_sound
                          methodResult)
                        progress tailParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp [progress] at result

/-- Every executable trait-body success records the exact brace span, forward
ordinary methods, and final remainder without a diagnostic-free premise. -/
theorem traitBody_success_ordinaryOutcome_sound
    {input output : State} {body : TraitBody}
    (result : traitBody input = .ok body output) :
    DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
      input.declarativeRemainder (body.span, body.methods)
        output.declarativeRemainder := by
  unfold traitBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases traitMethods_success_ordinary_sound_strong opening
          (afterOpening.remainingCount + 1) [] afterOpening body output result
        with ⟨methods, closingSpan, bodyEq, methodsParsed⟩
      rw [bodyEq]
      exact .parsed opening.span closingSpan
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        methodsParsed

end Solcore.Syntax.Parser.TraitInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitBodyOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable broad ordinary outcomes for trait bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- Package executable trait-body success and exact rejection. -/
theorem traitBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : TraitBody},
      traitBody input = .ok body output →
        DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
          input.declarativeRemainder (body.span, body.methods)
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      traitBody input = .reject failure rejected →
        DeclarativeGrammar.TraitBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨traitBody_success_ordinaryOutcome_sound,
    traitBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad trait-body outcomes. -/
theorem traitBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
      DeclarativeGrammar.TraitBodyRejects :=
  DeclarativeGrammar.traitBodyDeterministicOutcomeSpec

/-- Re-export unconditional exact trait-body outcomes. -/
theorem traitBody_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
      DeclarativeGrammar.TraitBodyRejects :=
  DeclarativeGrammar.traitBodyExactOutcomeSpec

/-- Two successful trait bodies have the same span, methods, and declarative
remainder. -/
theorem traitBody_success_result_unique
    {input leftOutput rightOutput : State} {left right : TraitBody}
    (leftResult : traitBody input = .ok left leftOutput)
    (rightResult : traitBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases traitBody_exactOutcomeSpec.successResultUnique
      (traitBody_success_ordinaryOutcome_sound leftResult)
      (traitBody_success_ordinaryOutcome_sound rightResult) with
    ⟨bodyEq, outputEq⟩
  constructor
  · cases left
    cases right
    cases bodyEq
    rfl
  · exact outputEq

/-- Two trait-body rejections have the same declarative endpoint. -/
theorem traitBody_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : traitBody input = .reject leftFailure leftOutput)
    (rightResult : traitBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitBodyRejects.output_unique
    (traitBody_reject_ordinaryOutcome_sound leftResult)
    (traitBody_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.TraitInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitDeclarationOrdinaryRejectionSoundnessProperties`
-/

/-! Exact broad ordinary rejection for complete trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · rcases contextual_eq_ok_of_isContextual_eq_true value context present
      with ⟨token, parsed⟩
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

/-- Every executable trait-declaration rejection records its first rejecting
stage among marker, name, required generics, where clause, and broad body. -/
theorem traitDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : traitDecl input = .reject failure rejected) :
    DeclarativeGrammar.TraitDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold traitDecl at result
  cases markerResult : contextual .trait .topItem input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := contextual_reject_state_eq .trait .topItem
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (contextual_reject_tokenKindAbsentAt .trait .topItem markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := contextual_success_exactTokenParses .trait .topItem
        markerResult
      cases nameResult : identifier .topItem afterMarker with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected marker.span markerParsed
            (identifier_reject_sound .topItem nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .topItem nameResult
          cases genericsResult : genericParameters afterName with
          | invariant error => simp [genericsResult] at result
          | reject genericsFailure genericsRejected =>
              simp only [genericsResult] at result
              cases result
              exact .genericsRejected marker.span markerParsed nameParsed
                (genericParameters_ordinaryOutcome_sound.2 genericsResult)
          | ok genericParameters afterGenerics =>
              simp only [genericsResult] at result
              have genericsParsed := genericParameters_ordinaryOutcome_sound.1
                genericsResult
              cases whereResult : whereClause afterGenerics with
              | invariant error => simp [whereResult] at result
              | reject whereFailure whereRejected =>
                  simp only [whereResult] at result
                  cases result
                  exact .whereRejected marker.span markerParsed nameParsed
                    genericsParsed (whereClause_ordinaryOutcome_sound.2
                      whereResult)
              | ok parsedWhere afterWhere =>
                  simp only [whereResult] at result
                  have whereParsed := whereClause_ordinaryOutcome_sound.1
                    whereResult
                  cases bodyResult : TraitInternals.traitBody afterWhere with
                  | invariant error => simp [bodyResult] at result
                  | reject bodyFailure bodyRejected =>
                      simp only [bodyResult] at result
                      cases result
                      exact .bodyRejected marker.span markerParsed nameParsed
                        genericsParsed whereParsed
                        (TraitInternals.traitBody_reject_ordinaryOutcome_sound
                          bodyResult)
                  | ok body output => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitDeclarationOrdinarySuccessSoundnessProperties`
-/

/-! Broad ordinary-success soundness for complete trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem traitDeclarationOrdinarySuccess_bind_ok_components {alpha beta : Type}
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

/-- Every executable trait declaration records its exact marker, name,
required generic parameters, optional where clause, broad body, AST, and
remainder without a diagnostic-free premise. -/
theorem traitDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : TraitDecl}
    (result : traitDecl input = .ok declaration output) :
    DeclarativeGrammar.TraitDeclOrdinaryParses input.declarativeRemainder
      declaration output.declarativeRemainder := by
  unfold traitDecl at result
  rcases traitDeclarationOrdinarySuccess_bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases traitDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases traitDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases traitDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, rest⟩
  rcases traitDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (contextual_success_exactTokenParses .trait .topItem markerResult)
    (identifier_success_sound .topItem nameResult)
    (genericParameters_ordinaryOutcome_sound.1 genericsResult)
    (whereClause_ordinaryOutcome_sound.1 whereResult)
    (TraitInternals.traitBody_success_ordinaryOutcome_sound bodyResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitDeclarationOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable broad ordinary outcomes for trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable trait-declaration success and exact five-stage
rejection. -/
theorem traitDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : TraitDecl},
      traitDecl input = .ok declaration output →
        DeclarativeGrammar.TraitDeclOrdinaryParses input.declarativeRemainder
          declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      traitDecl input = .reject failure rejected →
        DeclarativeGrammar.TraitDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨traitDecl_success_ordinaryOutcome_sound,
    traitDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad trait-declaration outcomes. -/
theorem traitDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TraitDeclOrdinaryParses
      DeclarativeGrammar.TraitDeclRejects :=
  DeclarativeGrammar.traitDeclDeterministicOutcomeSpec

/-- Re-export unconditional exact trait-declaration outcomes. -/
theorem traitDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TraitDeclOrdinaryParses
      DeclarativeGrammar.TraitDeclRejects :=
  DeclarativeGrammar.traitDeclExactOutcomeSpec

/-- Two successful trait declarations have the same AST and declarative
remainder. -/
theorem traitDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : TraitDecl}
    (leftResult : traitDecl input = .ok left leftOutput)
    (rightResult : traitDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitDeclOrdinaryParses.result_unique
    (traitDecl_success_ordinaryOutcome_sound leftResult)
    (traitDecl_success_ordinaryOutcome_sound rightResult)

/-- Two trait-declaration rejections have the same declarative endpoint. -/
theorem traitDecl_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : traitDecl input = .reject leftFailure leftOutput)
    (rightResult : traitDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TraitDeclRejects.output_unique
    (traitDecl_reject_ordinaryOutcome_sound leftResult)
    (traitDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitProperties`
-/

/-! Ordinary-result contracts for canonical trait parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem traitBind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
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

namespace TraitInternals

namespace TraitBody

/-- Every trait-body range and retained method belongs to one source. -/
def ValidFor (file : SourceFile) (body : TraitBody) : Prop :=
  body.span.ValidFor file ∧
    List.ValidFor TraitMethod.ValidFor file body.methods

end TraitBody

/-- A signature-only trait method retains only ranges from its source. -/
theorem traitMethod_validFor :
    traitMethod.ValidFor TraitMethod.ValidFor := by
  intro input inputValid
  have weak : traitMethod.ValidFor (fun _ _ => True) := by
    unfold traitMethod
    apply Parser.bind_validFor (functionSignature_validFor .module)
    intro signature
    apply Parser.bind_validFor (symbol_validFor .semicolon .topItem)
    intro semicolon
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  have weakResult := weak input inputValid
  cases parsed : traitMethod input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok method final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold traitMethod at stages
      rcases traitBind_ok_components stages with
        ⟨signature, afterSignature, signatureResult, rest⟩
      rcases traitBind_ok_components rest with
        ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
      have signatureReply := functionSignature_validFor .module input inputValid
      rw [signatureResult] at signatureReply
      have semicolonReply := symbol_validFor .semicolon .topItem
        afterSignature signatureReply.2.1
      rw [semicolonResult] at semicolonReply
      have signatureValid : FunctionSignature.ValidFor input.file signature := by
        simpa [signatureReply.2.2] using signatureReply.1
      have semicolonValid : semicolon.span.ValidFor input.file := by
        simpa only [Located.ValidFor, semicolonReply.2.2,
          signatureReply.2.2] using semicolonReply.1
      rcases functionSignature_startsAtCurrentTokenOnSuccess .module
          input signature afterSignature signatureResult with
        ⟨first, firstFound, signatureStart⟩
      have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
      have semicolonShape := symbol_ok_state_shape .semicolon .topItem
        semicolonResult
      have signatureTokens := functionSignature_preservesTokensOnSuccess .module
        input signature afterSignature signatureResult
      have semicolonAt : input.tokens[afterSignature.cursor]? = some semicolon := by
        simpa [signatureTokens] using
          State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        firstAt semicolonAt
          (FunctionInternals.functionSignature_cursor_lt_onSuccess .module
            signatureResult)
      have firstValid := inputValid.peek?_span_validFor firstFound
      have ordered : signature.span.startByte ≤ semicolon.span.endByte := by
        calc
          signature.span.startByte = first.span.startByte := signatureStart.symm
          _ ≤ first.span.endByte := firstValid.2.1
          _ ≤ semicolon.span.startByte := separated
          _ ≤ semicolon.span.endByte := semicolonValid.2.1
      have outerValid := SourceSpan.cover_validFor signatureValid.1
        semicolonValid ordered
      cases finished
      exact ⟨⟨outerValid, by simp, signatureValid, semicolonValid⟩,
        weakResult.2.1, weakResult.2.2⟩

/-- Trait methods retain the signature parser's ordinary token window. -/
theorem traitMethod_preservesTokenWindow
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module)) :
    Parser.PreservesTokenWindow traitMethod := by
  unfold traitMethod
  apply Parser.bind_preservesTokenWindow signatureShape
  intro signature
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .topItem)
  intro semicolon
  exact Parser.pure_preservesTokenWindow _

/-- Closing a trait body retains its braces and accumulated methods. -/
private theorem closeTraitBody_validFor (opening : Token)
    (methodsRev : List TraitMethod) (input : State) (openingIndex : Nat)
    (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (methodsValid : List.ValidFor TraitMethod.ValidFor
      input.file methodsRev) :
    (closeTraitBody opening methodsRev input).ValidFor input
      TraitBody.ValidFor := by
  unfold closeTraitBody
  have closingReply := symbol_validFor .rightBrace .topItem input inputValid
  cases closingResult : symbol .rightBrace .topItem input with
  | invariant error =>
      simp only [bind, closingResult]
      trivial
  | reject failure rejected =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult]
      exact closingReply
  | ok closing next =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult, pure, Reply.ValidFor]
      have closingShape := symbol_ok_state_shape .rightBrace .topItem
        closingResult
      have closingAt := State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingValid :=
        inputValid.token_span_validFor_of_getElem?_eq_some openingFound
      have closingValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using closingReply.1
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        openingFound closingAt openingBefore
      have ordered : opening.span.startByte ≤ closing.span.endByte :=
        Nat.le_trans openingValid.2.1
          (Nat.le_trans separated closingValid.2.1)
      refine ⟨⟨SourceSpan.cover_validFor openingValid closingValid ordered, ?_⟩,
        closingReply.2.1, closingReply.2.2⟩
      intro method member
      exact methodsValid method (by simpa using member)

/-- The fuel-bounded trait loop retains every parsed method and body range. -/
theorem traitMethods_validFor (opening : Token) :
    ∀ fuel methodsRev input openingIndex,
      input.ValidFor →
      input.tokens[openingIndex]? = some opening →
      openingIndex < input.cursor →
      List.ValidFor TraitMethod.ValidFor input.file methodsRev →
      (traitMethods opening fuel methodsRev input).ValidFor input
        TraitBody.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro methodsRev input openingIndex inputValid openingFound
        openingBefore methodsValid
      unfold traitMethods
      split
      · exact closeTraitBody_validFor opening methodsRev input openingIndex
          inputValid openingFound openingBefore methodsValid
      · split
        · have methodReply := traitMethod_validFor input inputValid
          cases methodResult : traitMethod input with
          | invariant error => trivial
          | reject failure rejected =>
              rw [methodResult] at methodReply
              exact methodReply
          | ok method next =>
              rw [methodResult] at methodReply
              simp only
              split
              · have methodTokens := traitMethod_preservesTokenWindow
                  (functionSignature_preservesTokenWindow .module)
                  |>.preservesTokensOnSuccess
                have openingFoundNext : next.tokens[openingIndex]? =
                    some opening := by
                  simpa [methodTokens input method next methodResult] using
                    openingFound
                have accumulated : List.ValidFor TraitMethod.ValidFor
                    next.file (method :: methodsRev) := by
                  intro retained member
                  simp only [List.mem_cons] at member
                  rcases member with retainedEq | retainedMember
                  · subst retained
                    simpa [methodReply.2.2] using methodReply.1
                  · simpa [methodReply.2.2] using
                      methodsValid retained retainedMember
                have progress : input.cursor < next.cursor := by omega
                exact (inductionHypothesis (method :: methodsRev) next
                  openingIndex methodReply.2.1 openingFoundNext
                    (Nat.lt_trans openingBefore progress) accumulated
                      ).of_file_eq methodReply.2.2
              · trivial
        · unfold rejectAt Reply.ValidFor
          exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩

/-- A complete trait body retains both braces and every method. -/
theorem traitBody_validFor : traitBody.ValidFor TraitBody.ValidFor := by
  intro input inputValid
  unfold traitBody
  have openingReply := symbol_validFor .leftBrace .topItem input inputValid
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [openingResult] at openingReply
      exact openingReply
  | ok opening next =>
      rw [openingResult] at openingReply
      have openingShape := symbol_ok_state_shape .leftBrace .topItem
        openingResult
      have openingAtInput :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have openingAtNext : next.tokens[input.cursor]? = some opening := by
        simpa [openingShape.2] using openingAtInput
      exact (traitMethods_validFor opening (next.remainingCount + 1) [] next
        input.cursor openingReply.2.1 openingAtNext (by simp [openingShape.2])
          (by simp [List.ValidFor])).of_file_eq openingReply.2.2

/-- The method loop retains the opening brace as the body left edge. -/
private theorem traitMethods_preservesOpeningStartOnSuccess
    (opening : Token) : ∀ fuel methodsRev input body final,
    traitMethods opening fuel methodsRev input = .ok body final →
      body.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro methodsRev input body final parsed
      unfold traitMethods at parsed
      split at parsed
      · unfold closeTraitBody at parsed
        rcases traitBind_ok_components parsed with
          ⟨closing, afterClosing, closingResult, finished⟩
        cases finished
        rfl
      · split at parsed
        · cases methodResult : traitMethod input with
          | invariant error => simp [methodResult] at parsed
          | reject failure rejected => simp [methodResult] at parsed
          | ok method next =>
              simp only [methodResult] at parsed
              split at parsed
              · exact inductionHypothesis (method :: methodsRev) next body
                  final parsed
              · contradiction
        · simp [rejectAt] at parsed

/-- A complete trait body starts at its opening brace token. -/
theorem traitBody_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess traitBody (·.span) := by
  intro input body final parsed
  unfold traitBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening next =>
      simp only [openingResult] at parsed
      have openingShape := symbol_ok_state_shape .leftBrace .topItem
        openingResult
      have retained := traitMethods_preservesOpeningStartOnSuccess opening
        (next.remainingCount + 1) [] next body final parsed
      exact ⟨opening, openingShape.1, retained.symm⟩

private theorem closeTraitBody_preservesTokenWindow (opening : Token)
    (methodsRev : List TraitMethod) :
    Parser.PreservesTokenWindow (closeTraitBody opening methodsRev) := by
  unfold closeTraitBody
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .topItem)
  intro closing
  exact Parser.pure_preservesTokenWindow _

/-- The fuel-bounded trait-method loop preserves ordinary token windows. -/
theorem traitMethods_preservesTokenWindow
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module)) (opening : Token) :
    ∀ fuel methodsRev,
      Parser.PreservesTokenWindow (traitMethods opening fuel methodsRev) := by
  intro fuel
  induction fuel with
  | zero => intro methodsRev input; trivial
  | succ fuel inductionHypothesis =>
      intro methodsRev input
      unfold traitMethods
      split
      · exact closeTraitBody_preservesTokenWindow opening methodsRev input
      · split
        · have methodShape :=
            traitMethod_preservesTokenWindow signatureShape input
          cases methodResult : traitMethod input with
          | ok method next =>
              rw [methodResult] at methodShape
              change (if next.cursor > input.cursor then
                traitMethods opening fuel (method :: methodsRev) next
                else .invariant (.noProgress .topLevel next.currentSpan)
                ).PreservesTokenWindow input
              split
              · exact (inductionHypothesis (method :: methodsRev) next).trans
                  methodShape
              · trivial
          | reject failure rejected =>
              rw [methodResult] at methodShape
              exact methodShape
          | invariant error => trivial
        · exact rejectAt_preservesTokenWindow input _ _

/-- Trait bodies preserve every ordinary token window. -/
theorem traitBody_preservesTokenWindow
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module)) :
    Parser.PreservesTokenWindow traitBody := by
  intro input
  unfold traitBody
  have openingShape := symbol_preservesTokenWindow .leftBrace .topItem input
  cases openingResult : symbol .leftBrace .topItem input with
  | ok opening next =>
      rw [openingResult] at openingShape
      exact (traitMethods_preservesTokenWindow signatureShape opening
        (next.remainingCount + 1) [] next).trans openingShape
  | reject failure rejected =>
      rw [openingResult] at openingShape
      exact openingShape
  | invariant error => trivial

private theorem closeTraitBody_cursorMonotoneOnSuccess (opening : Token)
    (methodsRev : List TraitMethod) :
    Parser.CursorMonotoneOnSuccess (closeTraitBody opening methodsRev) := by
  unfold closeTraitBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightBrace .topItem)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- The fuel-bounded trait-method loop never rewinds on success. -/
theorem traitMethods_cursorMonotoneOnSuccess (opening : Token) :
    ∀ fuel methodsRev,
      Parser.CursorMonotoneOnSuccess (traitMethods opening fuel methodsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body next result
      unfold traitMethods at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next result
      unfold traitMethods at result
      split at result
      · exact closeTraitBody_cursorMonotoneOnSuccess opening methodsRev
          input body next result
      · split at result
        · cases methodResult : traitMethod input with
          | ok method afterMethod =>
              simp only [methodResult] at result
              split at result
              · exact Nat.le_trans (Nat.le_of_lt (by assumption))
                  (inductionHypothesis (method :: methodsRev) afterMethod
                    body next result)
              · contradiction
          | reject failure rejected => simp [methodResult] at result
          | invariant error => simp [methodResult] at result
        · unfold rejectAt at result
          contradiction

/-- Successful trait-body parsing never rewinds its caller. -/
theorem traitBody_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess traitBody := by
  intro input body final result
  unfold traitBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | ok opening next =>
      simp only [openingResult] at result
      exact Nat.le_trans
        (symbol_cursorMonotoneOnSuccess .leftBrace .topItem input opening next
          openingResult)
        (traitMethods_cursorMonotoneOnSuccess opening
          (next.remainingCount + 1) [] next body final result)
  | reject failure rejected => simp [openingResult] at result
  | invariant error => simp [openingResult] at result

end TraitInternals

/-- A complete trait declaration retains only ranges from its source. -/
theorem traitDecl_validFor : traitDecl.ValidFor TraitDecl.ValidFor := by
  intro input inputValid
  have weak : traitDecl.ValidFor (fun _ _ => True) := by
    unfold traitDecl
    apply Parser.bind_validFor (contextual_validFor .trait .topItem)
    intro marker
    apply Parser.bind_validFor (identifier_validFor .topItem)
    intro name
    apply Parser.bind_validFor genericParameters_validFor
    intro genericParameters
    apply Parser.bind_validFor whereClause_validFor
    intro parsedWhereClause
    apply Parser.bind_validFor TraitInternals.traitBody_validFor
    intro body
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  have weakResult := weak input inputValid
  cases parsed : traitDecl input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok declaration final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold traitDecl at stages
      rcases traitBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases traitBind_ok_components rest with
        ⟨name, afterName, nameResult, rest⟩
      rcases traitBind_ok_components rest with
        ⟨genericParameters, afterParameters, parametersResult, rest⟩
      rcases traitBind_ok_components rest with
        ⟨parsedWhereClause, afterWhere, whereResult, rest⟩
      rcases traitBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerReply := contextual_validFor .trait .topItem input inputValid
      rw [markerResult] at markerReply
      have nameReply := identifier_validFor .topItem afterMarker markerReply.2.1
      rw [nameResult] at nameReply
      have parametersReply := genericParameters_validFor afterName nameReply.2.1
      rw [parametersResult] at parametersReply
      have whereReply := whereClause_validFor afterParameters
        parametersReply.2.1
      rw [whereResult] at whereReply
      have bodyReply := TraitInternals.traitBody_validFor afterWhere
        whereReply.2.1
      rw [bodyResult] at bodyReply
      have markerValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerReply.1
      have nameValid : name.span.ValidFor input.file := by
        simpa only [Located.ValidFor, markerReply.2.2] using nameReply.1
      have parametersValid : NonemptyDelimitedList.ValidFor Located.ValidFor
          input.file genericParameters := by
        simpa [nameReply.2.2, markerReply.2.2] using parametersReply.1
      have whereValid : Option.ValidFor WhereClause.ValidFor input.file
          parsedWhereClause := by
        simpa [parametersReply.2.2, nameReply.2.2, markerReply.2.2] using
          whereReply.1
      have bodyValid : TraitInternals.TraitBody.ValidFor input.file body := by
        simpa [whereReply.2.2, parametersReply.2.2, nameReply.2.2,
          markerReply.2.2] using bodyReply.1
      rcases contextual_startsAtCurrentTokenOnSuccess .trait .topItem input
          marker afterMarker markerResult with
        ⟨markerToken, markerFound, markerStart⟩
      rcases TraitInternals.traitBody_startsAtCurrentTokenOnSuccess afterWhere
          body afterBody bodyResult with
        ⟨opening, openingFound, bodyStart⟩
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerFound
      have openingAtAfter :=
        State.getElem?_eq_some_of_peek?_eq_some openingFound
      have markerTokens := contextual_preservesTokensOnSuccess .trait .topItem
        input marker afterMarker markerResult
      have nameTokens := identifier_preservesTokensOnSuccess .topItem
        afterMarker name afterName nameResult
      have parametersTokens := genericParameters_preservesTokensOnSuccess
        afterName genericParameters afterParameters parametersResult
      have whereTokens := whereClause_preservesTokensOnSuccess afterParameters
        parsedWhereClause afterWhere whereResult
      have openingAt : input.tokens[afterWhere.cursor]? = some opening := by
        simpa [whereTokens, parametersTokens, nameTokens, markerTokens] using
          openingAtAfter
      have markerProgress : input.cursor < afterMarker.cursor := by
        exact acceptToken_cursor_lt_onSuccess (.contextual .trait) .topItem
          (·.isContextual .trait) markerResult
      have progress : input.cursor < afterWhere.cursor :=
        Nat.lt_of_lt_of_le markerProgress
          (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem
            afterMarker name afterName nameResult)
            (Nat.le_trans (genericParameters_cursorMonotoneOnSuccess afterName
              genericParameters afterParameters parametersResult)
              (whereClause_cursorMonotoneOnSuccess afterParameters
                parsedWhereClause afterWhere whereResult)))
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        markerAt openingAt progress
      have markerTokenValid := inputValid.peek?_span_validFor markerFound
      have ordered : marker.span.startByte ≤ body.span.endByte := by
        calc
          marker.span.startByte = markerToken.span.startByte := markerStart.symm
          _ ≤ markerToken.span.endByte := markerTokenValid.2.1
          _ ≤ opening.span.startByte := separated
          _ = body.span.startByte := bodyStart
          _ ≤ body.span.endByte := bodyValid.1.2.1
      have outerValid := SourceSpan.cover_validFor markerValid bodyValid.1 ordered
      cases finished
      refine ⟨⟨outerValid, nameValid, parametersValid.1,
        parametersValid.2, ?_, bodyValid.1, bodyValid.2⟩,
          weakResult.2.1, weakResult.2.2⟩
      intro clause member
      cases parsedWhereClause with
      | none => simp at member
      | some retained =>
          simp at member
          subst clause
          simpa [Option.ValidFor] using whereValid

/-- Complete trait declarations preserve ordinary token windows. -/
theorem traitDecl_preservesTokenWindow
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module))
    (whereShape : Parser.PreservesTokenWindow whereClause) :
    Parser.PreservesTokenWindow traitDecl := by
  unfold traitDecl
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .trait .topItem)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .topItem)
  intro name
  apply Parser.bind_preservesTokenWindow genericParameters_preservesTokenWindow
  intro genericParameters
  apply Parser.bind_preservesTokenWindow whereShape
  intro whereClause
  apply Parser.bind_preservesTokenWindow
    (TraitInternals.traitBody_preservesTokenWindow signatureShape)
  intro body
  exact Parser.pure_preservesTokenWindow _

theorem traitDecl_preservesTokensOnSuccess
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module))
    (whereShape : Parser.PreservesTokenWindow whereClause) :
    Parser.PreservesTokensOnSuccess traitDecl :=
  (traitDecl_preservesTokenWindow signatureShape whereShape
    ).preservesTokensOnSuccess

/-- Complete trait declarations never rewind their caller. -/
theorem traitDecl_cursorMonotoneOnSuccess
    (whereMonotone : Parser.CursorMonotoneOnSuccess whereClause) :
    Parser.CursorMonotoneOnSuccess traitDecl := by
  unfold traitDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .trait .topItem)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .topItem)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    genericParameters_cursorMonotoneOnSuccess
  intro genericParameters
  apply Parser.bind_cursorMonotoneOnSuccess whereMonotone
  intro whereClause
  apply Parser.bind_cursorMonotoneOnSuccess
    TraitInternals.traitBody_cursorMonotoneOnSuccess
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful trait declaration starts at its current `trait` token. -/
theorem traitDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess traitDecl (·.span) := by
  unfold traitDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (contextual_startsAtCurrentTokenOnSuccess .trait .topItem)
  intro marker input declaration final parsed
  rcases traitBind_ok_components parsed with
    ⟨name, afterName, _nameResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨genericParameters, afterParameters, _parametersResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨whereClause, afterWhere, _whereResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  rfl

/-- A successful signature-only trait method consumes its signature. -/
theorem TraitInternals.traitMethod_cursor_lt_onSuccess
    {input final : State} {method : TraitMethod}
    (parsed : traitMethod input = .ok method final) :
    input.cursor < final.cursor := by
  have stages := parsed
  unfold traitMethod at stages
  rcases traitBind_ok_components stages with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (FunctionInternals.functionSignature_cursor_lt_onSuccess .module
      signatureResult)
    (symbol_cursorMonotoneOnSuccess .semicolon .topItem afterSignature
      semicolon final semicolonResult)

/-- A successful trait body consumes its opening brace. -/
theorem TraitInternals.traitBody_cursor_lt_onSuccess
    {input final : State} {body : TraitBody}
    (parsed : traitBody input = .ok body final) :
    input.cursor < final.cursor := by
  unfold traitBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening next =>
      simp only [openingResult] at parsed
      exact Nat.lt_of_lt_of_le
        (acceptToken_cursor_lt_onSuccess (.symbol .leftBrace) .topItem
          (· == .symbol .leftBrace) openingResult)
        (traitMethods_cursorMonotoneOnSuccess opening
          (next.remainingCount + 1) [] next body final parsed)

/-- A successful trait declaration consumes its `trait` marker. -/
theorem traitDecl_cursor_lt_onSuccess
    {input final : State} {declaration : TraitDecl}
    (parsed : traitDecl input = .ok declaration final) :
    input.cursor < final.cursor := by
  have stages := parsed
  unfold traitDecl at stages
  rcases traitBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨genericParameters, afterParameters, parametersResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨parsedWhereClause, afterWhere, whereResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (acceptToken_cursor_lt_onSuccess (.contextual .trait) .topItem
      (·.isContextual .trait) markerResult)
    (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem afterMarker
      name afterName nameResult)
      (Nat.le_trans (genericParameters_cursorMonotoneOnSuccess afterName
        genericParameters afterParameters parametersResult)
        (Nat.le_trans (whereClause_cursorMonotoneOnSuccess afterParameters
          parsedWhereClause afterWhere whereResult)
          (TraitInternals.traitBody_cursorMonotoneOnSuccess afterWhere body
            final bodyResult))))

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitBodyTotalityProperties`
-/

/-! Valid-input totality for canonical trait methods and trait bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- A signature-only trait method has only ordinary outcomes on valid input. -/
theorem traitMethod_invariantFreeOnValid :
    Parser.InvariantFreeOnValid traitMethod := by
  unfold traitMethod
  apply Parser.bind_invariantFreeOnValid
    (functionSignature_validFor .module)
    (functionSignature_invariantFreeOnValid .module)
  intro signature
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .topItem)
    (symbol_ordinary .semicolon .topItem).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover signature.span semicolon.span
    value := {
      leadingComments := []
      signature
      semicolon := semicolon.span
    }
  } : TraitMethod)

theorem traitMethod_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ method next, traitMethod input = .ok method next) ∨
      (∃ failure next, traitMethod input = .reject failure next) :=
  traitMethod_invariantFreeOnValid input inputValid

theorem traitMethod_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    traitMethod input ≠ .invariant error :=
  traitMethod_invariantFreeOnValid.ne_invariant input inputValid error

/-- A trait method is a strict reusable parser element. -/
theorem traitMethod_elementTotalityContract :
    ElementTotalityContract traitMethod := {
  validFor := traitMethod_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := traitMethod_preservesTokenWindow
    (functionSignature_preservesTokenWindow .module)
  cursorLtOnSuccess := traitMethod_cursor_lt_onSuccess
  invariantFree := traitMethod_ne_invariant
}

private theorem closeTraitBody_ordinary (opening : Token)
    (methodsRev : List TraitMethod) :
    Parser.Ordinary (closeTraitBody opening methodsRev) := by
  intro input
  rcases (symbol_ordinary .rightBrace .topItem) input with
    ⟨closing, next, closingResult⟩ |
    ⟨failure, rejected, closingResult⟩
  · exact Or.inl ⟨{
      span := SourceSpan.cover opening.span closing.span
      methods := methodsRev.reverse
    }, next, by
      simp only [closeTraitBody, bind, closingResult, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [closeTraitBody, bind, closingResult]⟩

/--
Strict method progress spends one unit of the loop's explicit fuel bound.
Thus neither fuel exhaustion nor the no-progress invariant is reachable.
-/
theorem traitMethods_ordinary_of_remainingCount_lt (opening : Token) :
    ∀ fuel methodsRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ body next,
        traitMethods opening fuel methodsRev input = .ok body next) ∨
      (∃ failure next,
        traitMethods opening fuel methodsRev input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero => intros; omega
  | succ fuel inductionHypothesis =>
      intro methodsRev input inputValid adequate
      unfold traitMethods
      by_cases closes : isSymbol input .rightBrace
      · simpa only [closes, if_true] using
          closeTraitBody_ordinary opening methodsRev input
      · by_cases methodPresent : isKeyword input .functionKw
        · rcases traitMethod_ordinary input inputValid with
            ⟨method, next, methodResult⟩ |
            ⟨failure, rejected, methodResult⟩
          · have methodReply := traitMethod_validFor input inputValid
            rw [methodResult] at methodReply
            have methodWindow := traitMethod_preservesTokenWindow
              (functionSignature_preservesTokenWindow .module) input
            rw [methodResult] at methodWindow
            have progress := traitMethod_cursor_lt_onSuccess methodResult
            have nextAdequate : next.remainingCount < fuel :=
              remainingCount_lt_after_strict_progress methodReply.2.1
                methodWindow.2 progress adequate
            simpa only [closes, Bool.false_eq_true, if_false,
              methodPresent, if_true, methodResult, if_pos progress] using
                inductionHypothesis (method :: methodsRev) next
                  methodReply.2.1 nextAdequate
          · exact Or.inr ⟨failure, rejected, by
              simp only [closes, Bool.false_eq_true, if_false,
                methodPresent, if_true, methodResult]⟩
        · simpa only [closes, Bool.false_eq_true, if_false,
            methodPresent] using
              (Parser.rejectAt_invariantFreeOnValid
                (alpha := TraitBody)
                { head := .keyword .functionKw,
                  tail := [.symbol .rightBrace] }
                .topItem) input inputValid

/-- Production fuel is exactly one more than the remaining token count. -/
theorem traitMethods_production_ordinary
    (opening : Token) (methodsRev : List TraitMethod)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body next,
      traitMethods opening (input.remainingCount + 1) methodsRev input =
        .ok body next) ∨
      (∃ failure next,
        traitMethods opening (input.remainingCount + 1) methodsRev input =
          .reject failure next) :=
  traitMethods_ordinary_of_remainingCount_lt opening
    (input.remainingCount + 1) methodsRev input inputValid (by omega)

/-- The production loop parser is invariant-free on every valid input. -/
theorem traitMethods_production_invariantFreeOnValid
    (opening : Token) (methodsRev : List TraitMethod) :
    Parser.InvariantFreeOnValid (fun input =>
      traitMethods opening (input.remainingCount + 1) methodsRev input) :=
  traitMethods_production_ordinary opening methodsRev

theorem traitMethods_production_ne_invariant
    (opening : Token) (methodsRev : List TraitMethod)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    traitMethods opening (input.remainingCount + 1) methodsRev input ≠
      .invariant error :=
  (traitMethods_production_invariantFreeOnValid opening methodsRev
    ).ne_invariant input inputValid error

theorem traitMethods_ne_invariant_of_remainingCount_lt
    (opening : Token) (fuel : Nat) (methodsRev : List TraitMethod)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    traitMethods opening fuel methodsRev input ≠ .invariant error := by
  intro failed
  rcases traitMethods_ordinary_of_remainingCount_lt opening fuel methodsRev
      input inputValid adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- A canonical trait body has only ordinary outcomes on valid input. -/
theorem traitBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid traitBody := by
  intro input inputValid
  rcases (symbol_ordinary .leftBrace .topItem) input with
    ⟨opening, next, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .topItem input inputValid
    rw [openingResult] at openingReply
    simpa only [traitBody, openingResult] using
      traitMethods_production_ordinary opening [] next openingReply.2.1
  · exact Or.inr ⟨failure, rejected, by
      simp only [traitBody, openingResult]⟩

theorem traitBody_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ body next, traitBody input = .ok body next) ∨
      (∃ failure next, traitBody input = .reject failure next) :=
  traitBody_invariantFreeOnValid input inputValid

theorem traitBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    traitBody input ≠ .invariant error :=
  traitBody_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser.TraitInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitDeclarationTotalityProperties`
-/

/-! Valid-input totality for complete canonical trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every production stage of a trait declaration has an ordinary outcome. -/
theorem traitDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid traitDecl := by
  unfold traitDecl
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .trait .topItem)
    (contextual_ordinary .trait .topItem).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid genericParameters_validFor
    genericParameters_invariantFreeOnValid
  intro genericParameters
  apply Parser.bind_invariantFreeOnValid whereClause_validFor
    whereClause_invariantFreeOnValid
  intro parsedWhereClause
  apply Parser.bind_invariantFreeOnValid TraitInternals.traitBody_validFor
    TraitInternals.traitBody_invariantFreeOnValid
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := {
      name
      genericParameters
      whereClause := parsedWhereClause
      bodySpan := body.span
      methods := body.methods
    }
  } : TraitDecl)

theorem traitDecl_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, traitDecl input = .ok declaration next) ∨
      (∃ failure next, traitDecl input = .reject failure next) :=
  traitDecl_invariantFreeOnValid input inputValid

theorem traitDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    traitDecl input ≠ .invariant error :=
  traitDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitMethodSoundnessProperties`
-/

/-! Diagnostic-free success soundness for signature-only trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem traitMethodSoundness_bind_ok_components {alpha beta : Type}
    {first : Parser alpha}
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

namespace TraitInternals

/-- Trait-method parsing cannot erase an incoming diagnostic. -/
theorem traitMethod_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess traitMethod := by
  unfold traitMethod
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (functionSignature_reflectsDiagnosticFreeOnSuccess .module)
  intro signature
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .topItem)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every diagnostic-free trait method follows its signature and semicolon. -/
theorem traitMethod_success_sound {input next : State} {method : TraitMethod}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitMethod input = .ok method next) :
    DeclarativeGrammar.TraitMethodParses input.declarativeRemainder method
      next.declarativeRemainder := by
  unfold traitMethod at result
  rcases traitMethodSoundness_bind_ok_components result with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases traitMethodSoundness_bind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have afterSignatureFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .topItem afterSignature semicolon next semicolonResult
    diagnosticFree
  exact .parsed semicolon.span
    (functionSignature_module_success_sound afterSignatureFree
      signatureResult)
    (symbol_success_exactTokenParses .semicolon .topItem semicolonResult)

/-- Trait-method grammar soundness composes with source validity. -/
theorem traitMethod_success_sound_and_validFor {input next : State}
    {method : TraitMethod} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitMethod input = .ok method next) :
    DeclarativeGrammar.TraitMethodParses input.declarativeRemainder method
        next.declarativeRemainder ∧
      TraitMethod.ValidFor input.file method := by
  refine ⟨traitMethod_success_sound diagnosticFree result, ?_⟩
  have valid := traitMethod_validFor input inputValid
  rw [result] at valid
  exact valid.1

end TraitInternals

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitBodySoundnessProperties`
-/

/-! Diagnostic-free success soundness for the fuel-bounded trait body. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

private theorem traitBodySoundness_bind_ok_components {alpha beta : Type}
    {first : Parser alpha}
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

private theorem closeTraitBody_success_sound_and_reflects
    (opening : Token) (methodsRev : List TraitMethod)
    {input next : State} {body : TraitBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : closeTraitBody opening methodsRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        methods := methodsRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder ∧
      input.diagnosticsRev = [] := by
  unfold closeTraitBody at result
  rcases traitBodySoundness_bind_ok_components result with
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

private theorem traitMethods_success_sound_strong (opening : Token) :
    ∀ fuel methodsRev input body next,
      next.diagnosticsRev = [] →
      traitMethods opening fuel methodsRev input = .ok body next →
      ∃ methods closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          methods := methodsRev.reverse ++ methods
        } ∧
        DeclarativeGrammar.TraitMethodTailParses
          input.declarativeRemainder methods closingSpan
            next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body next diagnosticFree result
      simp [traitMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next diagnosticFree result
      unfold traitMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeTraitBody_success_sound_and_reflects opening methodsRev
              diagnosticFree result with
            ⟨closingSpan, bodyEq, closingGrammar, inputFree⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingGrammar, inputFree⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases methodPresent : isKeyword input .functionKw with
          | false => simp [methodPresent, rejectAt] at result
          | true =>
              simp only [methodPresent, if_true] at result
              cases methodResult : traitMethod input with
              | invariant error => simp [methodResult] at result
              | reject failure rejected => simp [methodResult] at result
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (method :: methodsRev)
                        afterMethod body next diagnosticFree result with
                      ⟨methods, closingSpan, bodyEq, tailGrammar,
                        afterMethodFree⟩
                    have methodGrammar := traitMethod_success_sound
                      afterMethodFree methodResult
                    have inputFree :=
                      traitMethod_reflectsDiagnosticFreeOnSuccess input method
                        afterMethod methodResult afterMethodFree
                    refine ⟨method :: methods, closingSpan, ?_,
                      .next
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        methodGrammar tailGrammar,
                      inputFree⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every diagnostic-free trait body follows its exact forward method grammar. -/
theorem traitBody_success_sound {input next : State} {body : TraitBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitBody input = .ok body next) :
    DeclarativeGrammar.TraitBodyParses input.declarativeRemainder body.span
      body.methods next.declarativeRemainder := by
  unfold traitBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases traitMethods_success_sound_strong opening
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨methods, closingSpan, bodyEq, tailGrammar, afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.TraitBodyParses.parsed opening.span
        closingSpan
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        tailGrammar

/-- Trait-body parsing cannot erase an incoming diagnostic. -/
theorem traitBody_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess traitBody := by
  intro input body next result diagnosticFree
  unfold traitBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases traitMethods_success_sound_strong opening
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨methods, closingSpan, bodyEq, tailGrammar, afterOpeningFree⟩
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .topItem input
        opening afterOpening openingResult afterOpeningFree

/-- Trait-body grammar soundness composes with retained-source validity. -/
theorem traitBody_success_sound_and_validFor {input next : State}
    {body : TraitBody} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitBody input = .ok body next) :
    DeclarativeGrammar.TraitBodyParses input.declarativeRemainder body.span
        body.methods next.declarativeRemainder ∧
      TraitBody.ValidFor input.file body := by
  refine ⟨traitBody_success_sound diagnosticFree result, ?_⟩
  have valid := traitBody_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.TraitInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.TraitDeclSoundnessProperties`
-/

/-! Diagnostic-free success soundness for complete trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem traitDeclSoundness_bind_ok_components {alpha beta : Type}
    {first : Parser alpha}
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

/-- Trait declaration parsing cannot erase an incoming diagnostic. -/
theorem traitDecl_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess traitDecl := by
  unfold traitDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .trait .topItem)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .topItem)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    genericParameters_reflectsDiagnosticFreeOnSuccess
  intro genericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    whereClause_reflectsDiagnosticFreeOnSuccess
  intro whereClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    TraitInternals.traitBody_reflectsDiagnosticFreeOnSuccess
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every diagnostic-free trait success follows its exact declaration grammar. -/
theorem traitDecl_success_sound {input next : State} {declaration : TraitDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitDecl input = .ok declaration next) :
    DeclarativeGrammar.TraitDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder := by
  unfold traitDecl at result
  rcases traitDeclSoundness_bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases traitDeclSoundness_bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases traitDeclSoundness_bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases traitDeclSoundness_bind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, rest⟩
  rcases traitDeclSoundness_bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (contextual_success_exactTokenParses .trait .topItem markerResult)
    (identifier_success_sound .topItem nameResult)
    (genericParameters_success_sound genericsResult)
    (whereClause_success_sound whereResult)
    (TraitInternals.traitBody_success_sound diagnosticFree bodyResult)

/-- Trait declaration grammar soundness composes with source validity. -/
theorem traitDecl_success_sound_and_validFor {input next : State}
    {declaration : TraitDecl} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitDecl input = .ok declaration next) :
    DeclarativeGrammar.TraitDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      TraitDecl.ValidFor input.file declaration := by
  refine ⟨traitDecl_success_sound diagnosticFree result, ?_⟩
  have valid := traitDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
