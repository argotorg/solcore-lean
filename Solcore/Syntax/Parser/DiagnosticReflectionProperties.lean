import Solcore.Syntax.Parser.Delimited

/-! Backward propagation of diagnostic-free parser success. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace Parser

/-- A successful diagnostic-free output implies a diagnostic-free input. -/
def ReflectsDiagnosticFreeOnSuccess {alpha : Type}
    (parser : Parser alpha) : Prop :=
  ∀ input value next, parser input = .ok value next →
    next.diagnosticsRev = [] → input.diagnosticsRev = []

/-- Pure parsing reflects diagnostic freedom exactly. -/
theorem pure_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (value : alpha) :
    ReflectsDiagnosticFreeOnSuccess (pure value : Parser alpha) := by
  intro input result next parsed diagnosticFree
  cases parsed
  exact diagnosticFree

/-- Sequential composition reflects through both successful stages. -/
theorem bind_reflectsDiagnosticFreeOnSuccess {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstReflects : ReflectsDiagnosticFreeOnSuccess first)
    (nextReflects : ∀ value, ReflectsDiagnosticFreeOnSuccess (next value)) :
    ReflectsDiagnosticFreeOnSuccess (first >>= next) := by
  intro input value final parsed diagnosticFree
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      have afterFree := nextReflects firstValue afterFirst value final parsed
        diagnosticFree
      exact firstReflects input firstValue afterFirst firstResult afterFree
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Transactional ordered choice reflects through its successful branch. -/
theorem orElse_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    {first second : Parser alpha}
    (firstReflects : ReflectsDiagnosticFreeOnSuccess first)
    (secondReflects : ReflectsDiagnosticFreeOnSuccess second) :
    ReflectsDiagnosticFreeOnSuccess (orElse first second) := by
  intro input value next parsed diagnosticFree
  unfold orElse at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      cases parsed
      exact firstReflects input value next firstResult diagnosticFree
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondReflects input value next parsed diagnosticFree
  | invariant error => simp [firstResult] at parsed

end Parser

/-- Reading state reflects diagnostic freedom. -/
theorem getState_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess getState := by
  intro input value next parsed diagnosticFree
  unfold getState at parsed
  cases parsed
  exact diagnosticFree

/-- Exact token acceptance never removes prior diagnostics. -/
theorem acceptToken_reflectsDiagnosticFreeOnSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (acceptToken expected context accepts) := by
  intro input value next parsed diagnosticFree
  unfold acceptToken at parsed
  cases found : input.peek? with
  | none => simp [found, rejectAt] at parsed
  | some token =>
      simp only [found] at parsed
      split at parsed
      · cases parsed
        exact diagnosticFree
      · unfold rejectAt at parsed
        contradiction

theorem keyword_reflectsDiagnosticFreeOnSuccess
    (value : HardKeyword) (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (keyword value context) :=
  acceptToken_reflectsDiagnosticFreeOnSuccess (.keyword value) context
    (fun kind => kind == .keyword value)

theorem symbol_reflectsDiagnosticFreeOnSuccess
    (value : Symbol) (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (symbol value context) :=
  acceptToken_reflectsDiagnosticFreeOnSuccess (.symbol value) context
    (fun kind => kind == .symbol value)

theorem contextual_reflectsDiagnosticFreeOnSuccess
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (contextual value context) :=
  acceptToken_reflectsDiagnosticFreeOnSuccess (.contextual value) context
    (fun kind => kind.isContextual value)

/-- Raw identifiers never remove prior diagnostics. -/
theorem rawIdentifier_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (rawIdentifier context) := by
  intro input value next parsed diagnosticFree
  rw [rawIdentifier_ok_state_shape context parsed] at diagnosticFree
  exact diagnosticFree

/-- Checked identifiers may add a diagnostic but never remove one. -/
theorem identifier_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (identifier context) := by
  intro input value next parsed diagnosticFree
  unfold identifier at parsed
  cases rawResult : rawIdentifier context input with
  | invariant error => simp [rawResult] at parsed
  | reject failure rejected => simp [rawResult] at parsed
  | ok name afterName =>
      simp only [rawResult] at parsed
      split at parsed
      · cases parsed
        simp [State.emit] at diagnosticFree
      · cases parsed
        exact rawIdentifier_reflectsDiagnosticFreeOnSuccess context input value
          next rawResult diagnosticFree

/-- Emitting a diagnostic cannot have a diagnostic-free success. -/
theorem emitDiagnostic_reflectsDiagnosticFreeOnSuccess
    (diagnostic : ParseDiagnostic) :
    Parser.ReflectsDiagnosticFreeOnSuccess (emitDiagnostic diagnostic) := by
  intro input value next parsed diagnosticFree
  unfold emitDiagnostic modifyState at parsed
  cases parsed
  simp [State.emit] at diagnosticFree

private theorem closeDelimited_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List alpha) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closeDelimited opening closing context elementsRev) := by
  intro input values next parsed diagnosticFree
  unfold closeDelimited at parsed
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at parsed
  | reject failure rejected => simp [closingResult] at parsed
  | ok token afterClosing =>
      simp only [closingResult] at parsed
      cases parsed
      exact symbol_reflectsDiagnosticFreeOnSuccess closing context input token
        next closingResult diagnosticFree

private theorem afterDelimitedElement_reflectsDiagnosticFreeOnSuccess
    {alpha : Type} (element : Parser alpha)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (closing : Symbol) (allowTrailing : Bool) (context : ParseContext)
    (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next parsed diagnosticFree
      simp [afterDelimitedElement] at parsed
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next parsed diagnosticFree
      unfold afterDelimitedElement at parsed
      split at parsed
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at parsed
        | reject failure rejected => simp [commaResult] at parsed
        | ok comma afterComma =>
            simp only [commaResult] at parsed
            split at parsed
            · have afterCommaFree :=
                  closeDelimited_reflectsDiagnosticFreeOnSuccess opening
                    closing context elementsRev afterComma values next parsed
                    diagnosticFree
              exact symbol_reflectsDiagnosticFreeOnSuccess .comma context
                input comma afterComma commaResult afterCommaFree
            · cases elementResult : element afterComma with
              | invariant error => simp [elementResult] at parsed
              | reject failure rejected => simp [elementResult] at parsed
              | ok elementValue afterElement =>
                  simp only [elementResult] at parsed
                  split at parsed
                  · have afterElementFree := inductionHypothesis
                        (elementValue :: elementsRev) afterElement values next
                        parsed diagnosticFree
                    have afterCommaFree := elementReflects afterComma
                      elementValue afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma context
                      input comma afterComma commaResult afterCommaFree
                  · contradiction
      · split at parsed
        · exact closeDelimited_reflectsDiagnosticFreeOnSuccess opening
            closing context elementsRev input values next parsed diagnosticFree
        · unfold rejectAt at parsed
          contradiction

/-- Generic delimiter policy never removes diagnostics from its input. -/
theorem delimitedWithPolicy_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser alpha) (context : ParseContext) (phase : ParserPhase)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase) := by
  intro input values next parsed diagnosticFree
  unfold delimitedWithPolicy at parsed
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok openingToken afterOpening =>
      simp only [openingResult] at parsed
      split at parsed
      · have afterOpeningFree :=
            closeDelimited_reflectsDiagnosticFreeOnSuccess openingToken
              closing context [] afterOpening values next parsed diagnosticFree
        exact symbol_reflectsDiagnosticFreeOnSuccess opening context input
          openingToken afterOpening openingResult afterOpeningFree
      · cases elementResult : element afterOpening with
        | invariant error => simp [elementResult] at parsed
        | reject failure rejected => simp [elementResult] at parsed
        | ok value afterElement =>
            simp only [elementResult] at parsed
            split at parsed
            · have afterElementFree :=
                  afterDelimitedElement_reflectsDiagnosticFreeOnSuccess
                    element elementReflects closing allowTrailing context phase
                    openingToken (afterOpening.remainingCount + 1) [value]
                    afterElement values next parsed diagnosticFree
              have afterOpeningFree := elementReflects afterOpening value
                afterElement elementResult afterElementFree
              exact symbol_reflectsDiagnosticFreeOnSuccess opening context
                input openingToken afterOpening openingResult afterOpeningFree
            · contradiction

theorem delimited_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser alpha)
    (context : ParseContext) (phase : ParserPhase)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (delimited opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_reflectsDiagnosticFreeOnSuccess opening closing
    allowEmpty true element context phase elementReflects

theorem delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser alpha)
    (context : ParseContext) (phase : ParserPhase)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (delimitedNoTrailing opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_reflectsDiagnosticFreeOnSuccess opening closing
    allowEmpty false element context phase elementReflects

end Solcore.Syntax.Parser
