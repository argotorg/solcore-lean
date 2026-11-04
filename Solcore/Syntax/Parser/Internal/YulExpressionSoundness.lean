import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Yul
import Solcore.Syntax.Grammar.Yul
import Solcore.Syntax.Parser.Internal.ParameterSoundness
import Solcore.Syntax.Yul
import Solcore.Syntax.Parser.Internal.DelimitedSoundness

/-!
Soundness of the parsers of Yul expressions: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties
/-! Exact ordinary rejection facts for required hard-keyword tokens. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Required-keyword rejection is exact absence of that keyword token. -/
theorem keyword_reject_tokenKindAbsentAt (value : HardKeyword)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) := by
  rintro ⟨span, inside, found⟩
  unfold keyword acceptToken at result
  unfold State.peek? at result
  simp only [inside, ↓reduceIte, found] at result
  change (if instBEqTokenKind.beq (.keyword value) (.keyword value) then
      Reply.ok _ _ else _) = _ at result
  simp only [instBEqTokenKind.beq] at result
  change (if instBEqHardKeyword.beq value value then Reply.ok _ _ else _) = _
    at result
  unfold instBEqHardKeyword.beq at result
  cases value <;> contradiction

/-- Required-keyword rejection retains the complete input state. -/
theorem keyword_reject_state_eq (value : HardKeyword)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.keyword value) context
    (· == .keyword value) result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionLookaheadProperties
/-!
Bridges between executable inline-Yul expression guards and declarative token
starter predicates.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem startsYulLiteral_eq_true_of_tokenAt_decimal {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .decimalLiteral spelling }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulLiteral_eq_true_of_tokenAt_hexadecimal {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .hexadecimalLiteral spelling }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulLiteral_eq_true_of_tokenAt_string {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .stringLiteral spelling }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulLiteral_eq_true_of_tokenAt_true {input : State}
    {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword .trueKw }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulLiteral_eq_true_of_tokenAt_false {input : State}
    {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword .falseKw }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

/-- Declarative Yul-literal presence makes the executable first guard true. -/
theorem startsYulLiteral_eq_true_of_yulLiteralStartsAt {input : State}
    (starts : DeclarativeGrammar.YulLiteralStartsAt
      input.declarativeRemainder) :
    startsYulLiteral input = true := by
  rcases starts with ⟨span, spelling, token⟩ |
      ⟨span, spelling, token⟩ | ⟨span, spelling, token⟩ |
      ⟨span, token⟩ | ⟨span, token⟩
  · exact startsYulLiteral_eq_true_of_tokenAt_decimal token
  · exact startsYulLiteral_eq_true_of_tokenAt_hexadecimal token
  · exact startsYulLiteral_eq_true_of_tokenAt_string token
  · exact startsYulLiteral_eq_true_of_tokenAt_true token
  · exact startsYulLiteral_eq_true_of_tokenAt_false token

/-- A false executable literal guard excludes every declarative Yul literal. -/
theorem not_yulLiteralStartsAt_of_startsYulLiteral_eq_false {input : State}
    (absent : startsYulLiteral input = false) :
    ¬ DeclarativeGrammar.YulLiteralStartsAt
      input.declarativeRemainder := by
  intro starts
  rw [startsYulLiteral_eq_true_of_yulLiteralStartsAt starts] at absent
  contradiction

private theorem startsYulName_eq_true_of_tokenAt_identifier {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .identifier spelling }) :
    startsYulName input = true := by
  unfold startsYulName State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulName_eq_true_of_tokenAt_marked {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .yulIdentifier spelling }) :
    startsYulName input = true := by
  unfold startsYulName State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulName_eq_true_of_tokenAt_underscore {input : State}
    {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .underscore }) :
    startsYulName input = true := by
  unfold startsYulName State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulName_eq_true_of_tokenAt_fallback {input : State}
    {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword .fallbackKw }) :
    startsYulName input = true := by
  unfold startsYulName State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

/-- Declarative Yul-name presence makes the executable second guard true. -/
theorem startsYulName_eq_true_of_yulNameStartsAt {input : State}
    (starts : DeclarativeGrammar.YulNameStartsAt input.declarativeRemainder) :
    startsYulName input = true := by
  rcases starts with ⟨span, spelling, token⟩ |
      ⟨span, spelling, token⟩ | ⟨span, token⟩ | ⟨span, token⟩
  · exact startsYulName_eq_true_of_tokenAt_identifier token
  · exact startsYulName_eq_true_of_tokenAt_marked token
  · exact startsYulName_eq_true_of_tokenAt_underscore token
  · exact startsYulName_eq_true_of_tokenAt_fallback token

/-- A false executable name guard excludes every declarative Yul name. -/
theorem not_yulNameStartsAt_of_startsYulName_eq_false {input : State}
    (absent : startsYulName input = false) :
    ¬ DeclarativeGrammar.YulNameStartsAt input.declarativeRemainder := by
  intro starts
  rw [startsYulName_eq_true_of_yulNameStartsAt starts] at absent
  contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionRecoveryDiagnosticProperties
/-!
Diagnostic commitments at inline-Yul expression rejection and recovery
boundaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Consuming forbidden source-level Yul meta syntax always emits its
constraint diagnostic. -/
theorem rejectedMeta_diagnostics_ne_nil_onSuccess
    {input next : State} {value : YulExpr}
    (result : rejectedMeta input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold rejectedMeta at result
  cases found : input.peek? with
  | none => simp [found, rejectAt] at result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals simp [State.emit]

/-- Forbidden Yul meta syntax cannot have a diagnostic-free success. -/
theorem rejectedMeta_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess rejectedMeta := by
  intro input value next result diagnosticFree
  exact False.elim
    (rejectedMeta_diagnostics_ne_nil_onSuccess result diagnosticFree)

namespace YulExpressionInternals

/-- Finishing a recovered Yul expression always commits its recovery
diagnostic. -/
theorem finishRecovered_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) {input next : State} {value : YulExpr}
    (result : finishRecovered first last input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold finishRecovered at result
  cases result
  simp [State.emit]

/-- Every successful auxiliary Yul-expression recovery retains a diagnostic,
including success at a recovery boundary or at the active window end. -/
theorem recoverAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : YulExpr},
      recoverAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverAux at recovered
      split at recovered
      · exact finishRecovered_diagnostics_ne_nil_onSuccess first last
          recovered
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            exact finishRecovered_diagnostics_ne_nil_onSuccess first last
              recovered
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- A diagnostic-free public Yul-layer success is exactly the unchanged
successful result of its non-recovering core parser. -/
theorem layer_core_of_diagnosticFree_success
    (nested : Parser YulExpr) {input next : State} {value : YulExpr}
    (result : layer nested input = .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    yulExpressionCore nested input = .ok value next := by
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isBoundary rewound then .reject failure rewound
        else
          match rewound.advance? with
          | some (token, afterToken) =>
              recoverAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic)
          | none => .reject failure rewound) = .ok value next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            exact False.elim
              (recoverAux_diagnostics_ne_nil_onSuccess token.span token.span
                (afterToken.remainingCount + 1) result diagnosticFree)
  | invariant error =>
      simp [coreResult] at result

/-- Diagnostic reflection for the recovering Yul layer reduces to diagnostic
reflection for its non-recovering core parser. -/
theorem layer_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulExpr)
    (coreReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (yulExpressionCore nested)) :
    Parser.ReflectsDiagnosticFreeOnSuccess (layer nested) := by
  intro input value next result diagnosticFree
  exact coreReflects input value next
    (layer_core_of_diagnosticFree_success nested result diagnosticFree)
    diagnosticFree

end YulExpressionInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.LeafProperties
/-! Provenance and cursor contracts for nonrecursive inline-Yul leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem advanceAfterYulPeek_validFor {state : State}
    {token : Token} (valid : state.ValidFor)
    (found : state.peek? = some token) :
    token.span.ValidFor state.file ∧
      ({ state with cursor := state.cursor + 1 } : State).ValidFor ∧
      ({ state with cursor := state.cursor + 1 } : State).file = state.file := by
  refine ⟨valid.peek?_span_validFor found, ?_, rfl⟩
  apply valid.advance?_validFor (token := token)
  unfold State.advance?
  rw [found]
  rfl

/-- Yul-name success consumes exactly one token and preserves its span. -/
theorem yulName_ok_state_shape {input next : State} {name : YulIdentifier}
    (result : yulName input = .ok name next) :
    ∃ token, input.peek? = some token ∧
      token.span = name.span ∧ next.tokens = input.tokens ∧
      next.cursor = input.cursor + 1 := by
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
        rcases identifier_ok_state_shape .yulExpression result with
          ⟨token, tokenFound, tokenSpan, tokensEq, cursorEq⟩
        exact ⟨token, by simpa [found] using tokenFound,
          tokenSpan, tokensEq, cursorEq⟩
      case yulIdentifier text =>
        cases result
        exact ⟨_, rfl, rfl, rfl, rfl⟩
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw =>
          cases result
          exact ⟨_, rfl, rfl, rfl, rfl⟩
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore =>
          cases result
          exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- Yul-literal success changes only the cursor by one token. -/
theorem yulLiteral_ok_state_shape {input next : State}
    {literal : YulLiteral}
    (result : yulLiteral input = .ok literal next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold yulLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals try { cases result; rfl }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals rfl

/-- A successful Yul name starts at the current input token. -/
theorem yulName_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulName (·.span) := by
  intro input name next result
  rcases yulName_ok_state_shape result with
    ⟨token, found, span, _tokens, _cursor⟩
  exact ⟨token, found, congrArg SourceSpan.startByte span⟩

/-- A successful Yul literal starts at the current input token. -/
theorem yulLiteral_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulLiteral (·.span) := by
  intro input literal next result
  unfold yulLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals try { cases result; exact ⟨_, rfl, rfl⟩ }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals exact ⟨_, rfl, rfl⟩

/-- Yul-name acceptance preserves its located range and parser-state validity. -/
theorem yulName_ok_validFor {state next : State} {name : YulIdentifier}
    (valid : state.ValidFor) (result : yulName state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulName at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        exact identifier_ok_validFor valid .yulExpression result
      case yulIdentifier text =>
        cases result
        exact advanceAfterYulPeek_validFor valid found
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw =>
          cases result
          exact advanceAfterYulPeek_validFor valid found
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore =>
          cases result
          exact advanceAfterYulPeek_validFor valid found

/-- Yul-name rejection preserves its source position and parser state. -/
theorem yulName_reject_validFor {state next : State} {failure : Failure}
    (valid : state.ValidFor)
    (result : yulName state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulName at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      case identifier text =>
        exact identifier_reject_validFor valid .yulExpression result
      case yulIdentifier text => contradiction
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_reject_validFor valid _ _ result }
        case fallbackKw => contradiction
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { exact rejectAt_reject_validFor valid _ _ result }
        case underscore => contradiction

/-- Yul-literal acceptance preserves its located range and parser state. -/
theorem yulLiteral_ok_validFor {state next : State} {literal : YulLiteral}
    (valid : state.ValidFor) (result : yulLiteral state = .ok literal next) :
    literal.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulLiteral at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals try { cases result; exact advanceAfterYulPeek_validFor valid found }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals exact advanceAfterYulPeek_validFor valid found

/-- Yul-literal rejection preserves its source position and parser state. -/
theorem yulLiteral_reject_validFor {state next : State} {failure : Failure}
    (valid : state.ValidFor)
    (result : yulLiteral state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulLiteral at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      all_goals try contradiction
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_reject_validFor valid _ _ result }
        all_goals contradiction

/-- Every accepted Yul name retains a source-valid token range. -/
theorem yulName_validFor : yulName.ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact yulName_ok_validFor inputValid result
  · intro input inputValid failure next result
    exact yulName_reject_validFor inputValid result

/-- Every accepted Yul literal retains a source-valid token range. -/
theorem yulLiteral_validFor : yulLiteral.ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact yulLiteral_ok_validFor inputValid result
  · intro input inputValid failure next result
    exact yulLiteral_reject_validFor inputValid result

/-- Yul names preserve the token window on every ordinary reply. -/
theorem yulName_preservesTokenWindow :
    Parser.PreservesTokenWindow yulName := by
  intro input
  unfold yulName
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      case identifier text =>
        exact identifier_preservesTokenWindow .yulExpression input
      case yulIdentifier text => exact ⟨rfl, rfl⟩
      case keyword keyword =>
        cases keyword
        all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
        exact ⟨rfl, rfl⟩
      case symbol symbol =>
        cases symbol
        all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
        exact ⟨rfl, rfl⟩

/-- Yul literals preserve the token window on every ordinary reply. -/
theorem yulLiteral_preservesTokenWindow :
    Parser.PreservesTokenWindow yulLiteral := by
  intro input
  unfold yulLiteral
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      all_goals try { exact ⟨rfl, rfl⟩ }
      case keyword keyword =>
        cases keyword
        all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
        all_goals exact ⟨rfl, rfl⟩

/-- Yul-name parsing preserves the immutable token carrier. -/
theorem yulName_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulName := by
  intro input name next result
  exact (yulName_ok_state_shape result).choose_spec.2.2.1

/-- Yul-literal parsing preserves the immutable token carrier. -/
theorem yulLiteral_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulLiteral := by
  intro input literal next result
  rw [yulLiteral_ok_state_shape result]

/-- Yul-name parsing advances by one token on success. -/
theorem yulName_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulName := by
  intro input name next result
  rw [(yulName_ok_state_shape result).choose_spec.2.2.2]
  simp

/-- Yul-literal parsing advances by one token on success. -/
theorem yulLiteral_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulLiteral := by
  intro input literal next result
  rw [yulLiteral_ok_state_shape result]
  simp

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.Common
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulParsedBlock

/-- A Yul block and every retained statement belong to one input file. -/
def ValidFor (statementValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) (block : YulParsedBlock) : Prop :=
  block.span.ValidFor file ∧
    ∀ statement ∈ block.body, statementValid file statement

end YulParsedBlock

private theorem closeYulBlock_validFor
    (statementValid : SourceFile → YulStmt → Prop)
    (opening : Token) (bodyRev : List YulStmt) (state : State)
    (openingIndex : Nat) (stateValid : state.ValidFor)
    (openingValid : opening.span.ValidFor state.file)
    (bodyValid : ∀ item ∈ bodyRev, statementValid state.file item)
    (openingFound : state.tokens[openingIndex]? = some opening)
    (openingBeforeCursor : openingIndex < state.cursor) :
    (closeYulBlock opening bodyRev state).ValidFor state
      (YulParsedBlock.ValidFor statementValid) := by
  unfold closeYulBlock
  cases closingResult : symbol .rightBrace .yulStatement state with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have valid := symbol_validFor .rightBrace .yulStatement state stateValid
      rw [closingResult] at valid
      simpa only [closingResult, Reply.ValidFor] using valid
  | ok closing next =>
      have closingValid :=
        symbol_validFor .rightBrace .yulStatement state stateValid
      rw [closingResult] at closingValid
      have closingShape :=
        symbol_ok_state_shape .rightBrace .yulStatement closingResult
      have closingFound :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingBeforeClosing :=
        stateValid.token_end_le_token_start_of_getElem?_lt
          openingFound closingFound openingBeforeCursor
      have closingSpanValid : closing.span.ValidFor state.file := by
        simpa only [Located.ValidFor] using closingValid.1
      unfold Reply.ValidFor YulParsedBlock.ValidFor
      refine ⟨⟨SourceSpan.cover_validFor openingValid closingSpanValid
        (Nat.le_trans openingValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1)), ?_⟩,
        closingValid.2.1, closingValid.2.2⟩
      intro item member
      exact bodyValid item (by simpa using member)

private theorem yulBlockItems_validFor
    (statementValid : SourceFile → YulStmt → Prop)
    (statement : Parser YulStmt)
    (statementContract : statement.ValidFor statementValid)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    (opening : Token) :
    ∀ fuel bodyRev state openingIndex,
      state.ValidFor →
      opening.span.ValidFor state.file →
      (∀ item ∈ bodyRev, statementValid state.file item) →
      state.tokens[openingIndex]? = some opening →
      openingIndex < state.cursor →
      (yulBlockItems statement opening fuel bodyRev state).ValidFor state
        (YulParsedBlock.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro bodyRev state openingIndex stateValid openingValid bodyValid
        openingFound openingBeforeCursor
      unfold yulBlockItems
      split
      · exact closeYulBlock_validFor statementValid opening bodyRev state
          openingIndex stateValid openingValid bodyValid openingFound
          openingBeforeCursor
      · split
        · cases closingResult : symbol .rightBrace .yulStatement state with
          | invariant error => trivial
          | reject failure rejected =>
              have valid :=
                symbol_validFor .rightBrace .yulStatement state stateValid
              rw [closingResult] at valid
              exact valid
          | ok closing next => simp only [Reply.ValidFor]
        · cases itemResult : statement state with
          | invariant error => trivial
          | reject failure rejected =>
              have valid := statementContract state stateValid
              rw [itemResult] at valid
              exact valid
          | ok item next =>
              have itemValid := statementContract state stateValid
              rw [itemResult] at itemValid
              simp only
              split
              · have tokensEq := statementShape state item next itemResult
                have recursive := inductionHypothesis (item :: bodyRev) next
                  openingIndex itemValid.2.1
                  (by simpa [itemValid.2.2] using openingValid)
                  (by
                    intro retained member
                    rcases List.mem_cons.mp member with rfl | member
                    · simpa [itemValid.2.2] using itemValid.1
                    · simpa [itemValid.2.2] using
                        bodyValid retained member)
                  (by simpa [tokensEq] using openingFound)
                  (Nat.lt_trans openingBeforeCursor (by assumption))
                exact recursive.of_file_eq itemValid.2.2
              · trivial

/-- A valid, token-preserving statement parser lifts through Yul braces. -/
theorem yulBlock_validFor
    (statementValid : SourceFile → YulStmt → Prop)
    (statement : Parser YulStmt)
    (statementContract : statement.ValidFor statementValid)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    (yulBlock statement).ValidFor
      (YulParsedBlock.ValidFor statementValid) := by
  intro input inputValid
  unfold yulBlock
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .leftBrace .yulStatement input inputValid
      rw [openingResult] at valid
      exact valid
  | ok opening afterOpening =>
      have openingValid :=
        symbol_validFor .leftBrace .yulStatement input inputValid
      rw [openingResult] at openingValid
      have openingShape :=
        symbol_ok_state_shape .leftBrace .yulStatement openingResult
      have openingFound :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have recursive := yulBlockItems_validFor statementValid statement
        statementContract statementShape opening
        (afterOpening.remainingCount + 1) [] afterOpening input.cursor
        openingValid.2.1
        (by simpa only [Located.ValidFor, openingValid.2.2] using
          openingValid.1)
        (by simp) (by simpa [openingShape.2] using openingFound)
        (by rw [openingShape.2]; simp)
      exact recursive.of_file_eq openingValid.2.2

private theorem closeYulBlock_preservesTokenWindow (opening : Token)
    (bodyRev : List YulStmt) :
    Parser.PreservesTokenWindow (closeYulBlock opening bodyRev) := by
  intro input
  unfold closeYulBlock
  have closingShape :=
    symbol_preservesTokenWindow .rightBrace .yulStatement input
  cases closingResult : symbol .rightBrace .yulStatement input with
  | ok closing next => rw [closingResult] at closingShape; exact closingShape
  | reject failure rejected =>
      rw [closingResult] at closingShape
      exact closingShape
  | invariant error => trivial

private theorem yulBlockItems_preservesTokenWindow
    (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement)
    (opening : Token) : ∀ fuel bodyRev,
      Parser.PreservesTokenWindow
        (yulBlockItems statement opening fuel bodyRev) := by
  intro fuel
  induction fuel with
  | zero => intro bodyRev input; trivial
  | succ fuel inductionHypothesis =>
      intro bodyRev input
      unfold yulBlockItems
      split
      · exact closeYulBlock_preservesTokenWindow opening bodyRev input
      · split
        · have closingShape :=
            symbol_preservesTokenWindow .rightBrace .yulStatement input
          cases closingResult : symbol .rightBrace .yulStatement input with
          | ok closing next => trivial
          | reject failure rejected =>
              rw [closingResult] at closingShape
              exact closingShape
          | invariant error => trivial
        · have itemShape := statementShape input
          cases itemResult : statement input with
          | ok item next =>
              rw [itemResult] at itemShape
              change (if next.cursor > input.cursor then
                yulBlockItems statement opening fuel (item :: bodyRev) next
                else .invariant (.noProgress .yul next.currentSpan)
                ).PreservesTokenWindow input
              split
              · exact (inductionHypothesis (item :: bodyRev) next).trans
                  itemShape
              · trivial
          | reject failure rejected =>
              rw [itemResult] at itemShape
              exact itemShape
          | invariant error => trivial

/-- Yul-block parsing preserves the nested parser's ordinary token window. -/
theorem yulBlock_preservesTokenWindow (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (yulBlock statement) := by
  intro input
  unfold yulBlock
  have openingShape :=
    symbol_preservesTokenWindow .leftBrace .yulStatement input
  cases openingResult : symbol .leftBrace .yulStatement input with
  | ok opening next =>
      rw [openingResult] at openingShape
      exact (yulBlockItems_preservesTokenWindow statement statementShape
        opening (next.remainingCount + 1) [] next).trans openingShape
  | reject failure rejected =>
      rw [openingResult] at openingShape
      exact openingShape
  | invariant error => trivial

private theorem closeYulBlock_ok_state_shape (opening : Token)
    (bodyRev : List YulStmt) {input next : State} {body : YulParsedBlock}
    (result : closeYulBlock opening bodyRev input = .ok body next) :
    next.tokens = input.tokens ∧ input.cursor < next.cursor ∧
      body.span.startByte = opening.span.startByte := by
  unfold closeYulBlock at result
  cases closingResult : symbol .rightBrace .yulStatement input with
  | ok closing afterClosing =>
      simp only [closingResult] at result
      cases result
      have shape :=
        symbol_ok_state_shape .rightBrace .yulStatement closingResult
      exact ⟨by rw [shape.2], by rw [shape.2]; simp, rfl⟩
  | reject failure rejected => simp [closingResult] at result
  | invariant error => simp [closingResult] at result

private theorem yulBlockItems_ok_state_shape (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    (opening : Token) :
    ∀ fuel bodyRev input body next,
      yulBlockItems statement opening fuel bodyRev input = .ok body next →
      next.tokens = input.tokens ∧ input.cursor < next.cursor ∧
        body.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next result
      unfold yulBlockItems at result
      split at result
      · exact closeYulBlock_ok_state_shape opening bodyRev result
      · split at result
        · cases closingResult : symbol .rightBrace .yulStatement input <;>
            simp [closingResult] at result
        · cases itemResult : statement input with
          | ok item afterItem =>
              simp only [itemResult] at result
              split at result
              · have recursive := inductionHypothesis (item :: bodyRev)
                    afterItem body next result
                exact ⟨recursive.1.trans
                    (statementShape input item afterItem itemResult),
                  Nat.lt_trans (by assumption) recursive.2.1,
                  recursive.2.2⟩
              · contradiction
          | reject failure rejected => simp [itemResult] at result
          | invariant error => simp [itemResult] at result

/-- Successful Yul-block parsing exposes its opening and total progress. -/
theorem yulBlock_ok_state_shape (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {body : YulParsedBlock}
    (result : yulBlock statement input = .ok body next) :
    ∃ opening, input.peek? = some opening ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor ∧
      opening.span.startByte = body.span.startByte := by
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have recursive := yulBlockItems_ok_state_shape statement statementShape
        opening (afterOpening.remainingCount + 1) [] afterOpening body next
          result
      have openingShape :=
        symbol_ok_state_shape .leftBrace .yulStatement openingResult
      exact ⟨opening, openingShape.1,
        recursive.1.trans (by rw [openingShape.2]),
        Nat.lt_trans (by rw [openingShape.2]; simp) recursive.2.1,
        recursive.2.2.symm⟩
  | reject failure rejected => simp [openingResult] at result
  | invariant error => simp [openingResult] at result

/-- Yul-block success preserves the immutable token carrier. -/
theorem yulBlock_preservesTokensOnSuccess (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulBlock statement) := by
  intro input body next result
  exact (yulBlock_ok_state_shape statement statementShape result).choose_spec.2.1

/-- Every successful Yul block consumes both braces. -/
theorem yulBlock_cursor_lt_onSuccess (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {body : YulParsedBlock}
    (result : yulBlock statement input = .ok body next) :
    input.cursor < next.cursor :=
  (yulBlock_ok_state_shape statement statementShape result).choose_spec.2.2.1

/-- Successful Yul-block parsing never rewinds the token cursor. -/
theorem yulBlock_cursorMonotoneOnSuccess (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulBlock statement) := by
  intro input body next result
  exact Nat.le_of_lt (yulBlock_cursor_lt_onSuccess statement statementShape result)

/-- A successful Yul block starts at its opening brace token. -/
theorem yulBlock_startsAtCurrentTokenOnSuccess (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.StartsAtCurrentTokenOnSuccess (yulBlock statement) (·.span) := by
  intro input body next result
  rcases yulBlock_ok_state_shape statement statementShape result with
    ⟨opening, found, _tokens, _progress, start⟩
  exact ⟨opening, found, start⟩

namespace YulNameSequence

/-- The sequence range and every retained Yul name belong to one input file. -/
def ValidFor (file : SourceFile) (values : YulNameSequence) : Prop :=
  values.span.ValidFor file ∧
    ∀ name ∈ values.names.toList, name.span.ValidFor file

end YulNameSequence

private theorem yulNamesTail_validFor (first : YulIdentifier) :
    ∀ fuel last tailRev state firstIndex firstToken,
      state.ValidFor →
      first.span.ValidFor state.file →
      last.span.ValidFor state.file →
      (∀ name ∈ tailRev, name.span.ValidFor state.file) →
      first.span.startByte ≤ last.span.endByte →
      state.tokens[firstIndex]? = some firstToken →
      firstToken.span = first.span →
      firstIndex < state.cursor →
      (yulNamesTail first fuel last tailRev state).ValidFor state
        YulNameSequence.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      unfold yulNamesTail
      split
      · cases commaResult : symbol .comma .yulStatement state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have valid := symbol_validFor .comma .yulStatement state stateValid
            rw [commaResult] at valid
            simpa only [Reply.ValidFor] using valid
        | ok comma afterComma =>
            have commaValid :=
              symbol_validFor .comma .yulStatement state stateValid
            rw [commaResult] at commaValid
            have commaShape :=
              symbol_ok_state_shape .comma .yulStatement commaResult
            simp only
            cases nameResult : yulName afterComma with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have valid := yulName_validFor afterComma commaValid.2.1
                rw [nameResult] at valid
                exact valid.of_file_eq commaValid.2.2
            | ok name next =>
                have nameValid := yulName_validFor afterComma commaValid.2.1
                rw [nameResult] at nameValid
                rcases yulName_ok_state_shape nameResult with
                  ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
                have nameFoundInState :
                    state.tokens[state.cursor + 1]? = some nameToken := by
                  have foundAtCursor :=
                    State.getElem?_eq_some_of_peek?_eq_some nameFound
                  simpa [commaShape.2] using foundAtCursor
                have firstEndBeforeNameStart :
                    first.span.endByte ≤ name.span.startByte := by
                  have ordered :=
                    stateValid.token_end_le_token_start_of_getElem?_lt
                      firstFound nameFoundInState
                      (Nat.lt_of_lt_of_le firstBeforeCursor
                        (Nat.le_add_right state.cursor 1))
                  simpa [firstSpan, nameSpan] using ordered
                have nameSpanValid : name.span.ValidFor next.file := by
                  have valid : name.span.ValidFor afterComma.file := by
                    simpa only [Located.ValidFor] using nameValid.1
                  simpa [nameValid.2.2] using valid
                apply (inductionHypothesis name (name :: tailRev) next
                  firstIndex firstToken nameValid.2.1
                  (by simpa [nameValid.2.2, commaValid.2.2] using firstValid)
                  nameSpanValid _ _ _ firstSpan _).of_file_eq
                  (nameValid.2.2.trans commaValid.2.2)
                · intro item member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact nameSpanValid
                  · simpa [nameValid.2.2, commaValid.2.2] using
                      tailValid item member
                · exact Nat.le_trans firstValid.2.1
                    (Nat.le_trans firstEndBeforeNameStart nameSpanValid.2.1)
                · simpa [nameTokens, commaShape.2] using firstFound
                · rw [nameCursor, commaShape.2]
                  exact Nat.lt_trans
                    (Nat.lt_trans firstBeforeCursor (Nat.lt_succ_self _))
                    (Nat.lt_succ_self _)
      · unfold finishYulNames Reply.ValidFor YulNameSequence.ValidFor
        refine ⟨⟨SourceSpan.cover_validFor firstValid lastValid
          firstBeforeLast, ?_⟩, stateValid, rfl⟩
        intro name member
        simp only [NonemptyList.toList, List.mem_cons,
          List.mem_reverse] at member
        rcases member with rfl | member
        · exact firstValid
        · exact tailValid name member

/-- Yul-name sequences preserve their covering and component provenance. -/
theorem yulNames_validFor :
    yulNames.ValidFor YulNameSequence.ValidFor := by
  intro input inputValid
  unfold yulNames
  cases firstResult : yulName input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have valid := yulName_validFor input inputValid
      rw [firstResult] at valid
      exact valid
  | ok first next =>
      have firstValid := yulName_validFor input inputValid
      rw [firstResult] at firstValid
      rcases yulName_ok_state_shape firstResult with
        ⟨firstToken, firstFound, firstSpan, firstTokens, firstCursor⟩
      have foundNext : next.tokens[input.cursor]? = some firstToken := by
        have found := State.getElem?_eq_some_of_peek?_eq_some firstFound
        simpa [firstTokens] using found
      have spanValid : first.span.ValidFor next.file := by
        have valid : first.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using firstValid.1
        simpa [firstValid.2.2] using valid
      exact (yulNamesTail_validFor first (next.remainingCount + 1) first []
        next input.cursor firstToken firstValid.2.1 spanValid spanValid
        (by simp) spanValid.2.1 foundNext firstSpan
        (by rw [firstCursor]; simp)).of_file_eq firstValid.2.2

private theorem yulNamesTail_ok_state_shape (first : YulIdentifier) :
    ∀ fuel last tailRev input names next,
      yulNamesTail first fuel last tailRev input = .ok names next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        names.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input names next result
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
                have recursive := inductionHypothesis name
                  (name :: tailRev) afterName names next result
                have commaShape :=
                  symbol_ok_state_shape .comma .yulStatement commaResult
                rcases yulName_ok_state_shape nameResult with
                  ⟨_token, _found, _span, nameTokens, nameCursor⟩
                refine ⟨recursive.1.trans
                    (nameTokens.trans (by rw [commaShape.2])), ?_,
                  recursive.2.2⟩
                apply Nat.le_trans _ recursive.2.1
                rw [nameCursor, commaShape.2]
                exact Nat.le_trans (Nat.le_add_right input.cursor 1)
                  (Nat.le_add_right (input.cursor + 1) 1)
      · unfold finishYulNames at result
        cases result
        exact ⟨rfl, Nat.le_refl _, rfl⟩

/-- Successful Yul-name parsing starts at the first token and makes progress. -/
theorem yulNames_ok_state_shape {input next : State}
    {names : YulNameSequence} (result : yulNames input = .ok names next) :
    ∃ firstToken, input.peek? = some firstToken ∧
      firstToken.span.startByte = names.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have tailShape := yulNamesTail_ok_state_shape first
        (afterFirst.remainingCount + 1) first [] afterFirst names next result
      rcases yulName_ok_state_shape firstResult with
        ⟨firstToken, found, span, tokens, cursor⟩
      refine ⟨firstToken, found, ?_, tailShape.1.trans tokens, ?_⟩
      · exact (congrArg (fun sourceSpan : SourceSpan =>
          sourceSpan.startByte) span).trans tailShape.2.2.symm
      · exact Nat.lt_of_lt_of_le (by rw [cursor]; simp) tailShape.2.1

/-- Yul-name sequence success preserves the immutable token carrier. -/
theorem yulNames_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulNames := by
  intro input names next result
  exact (yulNames_ok_state_shape result).choose_spec.2.2.1

private theorem yulNamesTail_preservesTokenWindow (first : YulIdentifier) :
    ∀ fuel last tailRev, Parser.PreservesTokenWindow
      (yulNamesTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; change True; trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold yulNamesTail
      split
      · have commaShape :=
          symbol_preservesTokenWindow .comma .yulStatement input
        cases commaResult : symbol .comma .yulStatement input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [commaResult] at commaShape
            exact commaShape
        | ok comma afterComma =>
            rw [commaResult] at commaShape
            have nameShape := yulName_preservesTokenWindow afterComma
            cases nameResult : yulName afterComma with
            | invariant error => simp only [nameResult,
                Reply.PreservesTokenWindow]
            | reject failure rejected =>
                rw [nameResult] at nameShape
                simpa only [commaResult, nameResult, Reply.PreservesTokenWindow]
                  using nameShape.trans commaShape
            | ok name next =>
                rw [nameResult] at nameShape
                simpa only [commaResult, nameResult, Reply.PreservesTokenWindow]
                  using (inductionHypothesis name (name :: tailRev) next).trans
                    (nameShape.trans commaShape)
      · exact ⟨rfl, rfl⟩

/-- Yul-name parsing preserves every ordinary token window. -/
theorem yulNames_preservesTokenWindow :
    Parser.PreservesTokenWindow yulNames := by
  intro input
  unfold yulNames
  have firstShape := yulName_preservesTokenWindow input
  cases firstResult : yulName input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [firstResult] at firstShape
      exact firstShape
  | ok first next =>
      rw [firstResult] at firstShape
      exact (yulNamesTail_preservesTokenWindow first
        (next.remainingCount + 1) first [] next).trans firstShape

/-- Yul-name sequence success never moves the cursor backwards. -/
theorem yulNames_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulNames := by
  intro input names next result
  exact Nat.le_of_lt (yulNames_ok_state_shape result).choose_spec.2.2.2

/-- A successful Yul-name sequence starts at its first name token. -/
theorem yulNames_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulNames (·.span) := by
  intro input names next result
  rcases yulNames_ok_state_shape result with
    ⟨first, found, start, _tokens, _progress⟩
  exact ⟨first, found, start⟩

/-- Yul parameter lists preserve their delimiter and element provenance. -/
theorem yulParameters_validFor :
    yulParameters.ValidFor (DelimitedList.ValidFor Located.ValidFor) := by
  exact delimited_validFor Located.ValidFor .leftParen .rightParen true
    yulName .yulStatement .yul yulName_validFor
      yulName_preservesTokensOnSuccess

/-- Yul parameter-list success preserves the immutable token carrier. -/
theorem yulParameters_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulParameters := by
  exact delimited_preservesTokensOnSuccess .leftParen .rightParen true
    yulName .yulStatement .yul yulName_preservesTokensOnSuccess

/-- Yul parameter lists preserve every ordinary token window. -/
theorem yulParameters_preservesTokenWindow :
    Parser.PreservesTokenWindow yulParameters := by
  exact delimited_preservesTokenWindow .leftParen .rightParen true
    yulName .yulStatement .yul yulName_preservesTokenWindow

/-- Every successful Yul parameter list consumes both delimiters. -/
theorem yulParameters_cursor_lt_onSuccess {input next : State}
    {parameters : DelimitedList YulIdentifier}
    (result : yulParameters input = .ok parameters next) :
    input.cursor < next.cursor := by
  exact delimitedWithPolicy_cursor_lt_onSuccess .leftParen .rightParen true
    true yulName .yulStatement .yul result

/-- Yul parameter-list success never moves the cursor backwards. -/
theorem yulParameters_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulParameters := by
  exact delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
    yulName .yulStatement .yul

/-- A successful Yul parameter list starts at its opening parenthesis. -/
theorem yulParameters_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulParameters (·.span) :=
  delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen true
    yulName .yulStatement .yul

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionLeafSoundnessProperties
/-!
Diagnostic reflection and exact declarative soundness for inline-Yul leaves.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Yul-name success never removes an earlier diagnostic. -/
theorem yulName_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulName := by
  intro input name next result diagnosticFree
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
        exact identifier_reflectsDiagnosticFreeOnSuccess .yulExpression input
          name next result diagnosticFree
      case yulIdentifier text =>
        cases result
        exact diagnosticFree
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw =>
          cases result
          exact diagnosticFree
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore =>
          cases result
          exact diagnosticFree

/-- Yul-literal success never removes an earlier diagnostic. -/
theorem yulLiteral_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulLiteral := by
  intro input literal next result diagnosticFree
  rw [yulLiteral_ok_state_shape result] at diagnosticFree
  exact diagnosticFree

/-- Every diagnostic-free successful Yul name follows the strict leaf grammar.

The diagnostic-free premise rules out the checked ordinary-identifier branch
whose spelling contains `-`.
-/
theorem yulName_success_sound_of_diagnosticFree {input next : State}
    {name : YulIdentifier} (diagnosticFree : next.diagnosticsRev = [])
    (result : yulName input = .ok name next) :
    DeclarativeGrammar.YulNameParses input.declarativeRemainder name
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
        have parsed := identifier_success_sound .yulExpression result
        unfold identifier at result
        cases rawResult : rawIdentifier .yulExpression input with
        | invariant error => simp [rawResult] at result
        | reject failure rejected => simp [rawResult] at result
        | ok parsedName afterName =>
            simp only [rawResult] at result
            split at result
            · cases result
              simp [State.emit] at diagnosticFree
            · have hyphenAbsent :
                  parsedName.value.toList.contains '-' = false :=
                Bool.eq_false_iff.mpr (by assumption)
              cases result
              exact .identifier hyphenAbsent parsed
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

/-- Every successful Yul literal is exactly its current literal token. -/
theorem yulLiteral_success_sound {input next : State}
    {literal : YulLiteral}
    (result : yulLiteral input = .ok literal next) :
    DeclarativeGrammar.YulLiteralParses input.declarativeRemainder literal
      next.declarativeRemainder := by
  unfold yulLiteral at result
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
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case trueKw =>
          cases result
          exact .trueKeyword (tokenAt_of_peek?_eq_some found)
        case falseKw =>
          cases result
          exact .falseKeyword (tokenAt_of_peek?_eq_some found)

/-- Strict Yul-name grammar soundness composes with source provenance. -/
theorem yulName_success_sound_and_validFor {input next : State}
    {name : YulIdentifier} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulName input = .ok name next) :
    DeclarativeGrammar.YulNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      Located.ValidFor input.file name := by
  refine ⟨yulName_success_sound_of_diagnosticFree diagnosticFree result, ?_⟩
  exact (yulName_ok_validFor inputValid result).1

/-- Yul-literal grammar soundness composes with source provenance. -/
theorem yulLiteral_success_sound_and_validFor {input next : State}
    {literal : YulLiteral} (inputValid : input.ValidFor)
    (result : yulLiteral input = .ok literal next) :
    DeclarativeGrammar.YulLiteralParses input.declarativeRemainder literal
        next.declarativeRemainder ∧
      Located.ValidFor input.file literal := by
  refine ⟨yulLiteral_success_sound result, ?_⟩
  exact (yulLiteral_ok_validFor inputValid result).1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ExpressionProperties
/-! Compositional carrier and cursor contracts for one inline-Yul expression layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem presentYulCallArguments_validFor
    (nested : Parser YulExpr) (valueValid : SourceFile → YulExpr → Prop)
    (nestedValid : nested.ValidFor valueValid)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (do
      pure (some (← delimited .leftParen .rightParen true nested
        .yulExpression .yul))).ValidFor
          (Option.ValidFor (DelimitedList.ValidFor valueValid)) := by
  apply Parser.bind_validFor_of_value
    (delimited_validFor valueValid .leftParen .rightParen true nested
      .yulExpression .yul nestedValid nestedPreserves)
  intro arguments input inputValid argumentsValid
  exact ⟨argumentsValid, inputValid, rfl⟩

private theorem presentYulCallArguments_preservesTokensOnSuccess
    (nested : Parser YulExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (do
      pure (some (← delimited .leftParen .rightParen true nested
        .yulExpression .yul))) := by
  apply Parser.bind_preservesTokensOnSuccess
  · exact delimited_preservesTokensOnSuccess .leftParen .rightParen true
      nested .yulExpression .yul nestedPreserves
  · intro arguments
    exact Parser.pure_preservesTokensOnSuccess (some arguments)

private theorem presentYulCallArguments_preservesTokenWindow
    (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (do
      pure (some (← delimited .leftParen .rightParen true nested
        .yulExpression .yul))) := by
  apply Parser.bind_preservesTokenWindow
  · exact delimited_preservesTokenWindow .leftParen .rightParen true nested
      .yulExpression .yul nestedShape
  · intro arguments
    exact Parser.pure_preservesTokenWindow (some arguments)

private theorem presentYulCallArguments_cursorMonotoneOnSuccess
    (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (do
      pure (some (← delimited .leftParen .rightParen true nested
        .yulExpression .yul))) := by
  apply Parser.bind_cursorMonotoneOnSuccess
  · exact delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
      nested .yulExpression .yul
  · intro arguments
    exact Parser.pure_cursorMonotoneOnSuccess (some arguments)

/-- Optional Yul-call arguments preserve delimiter and element provenance. -/
theorem optionalYulCallArguments_validFor
    (nested : Parser YulExpr) (valueValid : SourceFile → YulExpr → Prop)
    (nestedValid : nested.ValidFor valueValid)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (optionalYulCallArguments nested).ValidFor
      (Option.ValidFor (DelimitedList.ValidFor valueValid)) := by
  intro input inputValid
  unfold optionalYulCallArguments
  split
  · exact Parser.orElse_validFor
      (presentYulCallArguments_validFor nested valueValid nestedValid
        nestedPreserves)
      (Parser.pure_validFor none _ (fun _ => trivial)) input inputValid
  · exact ⟨trivial, inputValid, rfl⟩

/-- Optional call arguments preserve every ordinary token window. -/
theorem optionalYulCallArguments_preservesTokenWindow
    (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (optionalYulCallArguments nested) := by
  intro input
  unfold optionalYulCallArguments
  split
  · exact Parser.orElse_preservesTokenWindow
      (presentYulCallArguments_preservesTokenWindow nested nestedShape)
      (Parser.pure_preservesTokenWindow none) input
  · exact ⟨rfl, rfl⟩

/-- Optional Yul-call arguments preserve the immutable lexer token carrier. -/
theorem optionalYulCallArguments_preservesTokensOnSuccess
    (nested : Parser YulExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (optionalYulCallArguments nested) := by
  intro input arguments next result
  unfold optionalYulCallArguments at result
  split at result
  · exact (Parser.orElse_preservesTokensOnSuccess
      (presentYulCallArguments_preservesTokensOnSuccess nested
        nestedPreserves)
      (Parser.pure_preservesTokensOnSuccess none)) input arguments next result
  · cases result
    rfl

/-- Optional Yul-call arguments never rewind the parser cursor. -/
theorem optionalYulCallArguments_cursorMonotoneOnSuccess
    (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (optionalYulCallArguments nested) := by
  intro input arguments next result
  unfold optionalYulCallArguments at result
  split at result
  · exact (Parser.orElse_cursorMonotoneOnSuccess
      (presentYulCallArguments_cursorMonotoneOnSuccess nested)
      (Parser.pure_cursorMonotoneOnSuccess none)) input arguments next result
  · cases result
    exact Nat.le_refl _

/-- Present call arguments start at their opening parenthesis token. -/
theorem optionalYulCallArguments_some_startsAtCurrentTokenOnSuccess
    (nested : Parser YulExpr) {input next : State}
    {arguments : DelimitedList YulExpr}
    (result : optionalYulCallArguments nested input = .ok (some arguments) next) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = arguments.span.startByte := by
  unfold optionalYulCallArguments at result
  split at result
  · unfold orElse at result
    cases presentResult : (do
        pure (some (← delimited .leftParen .rightParen true nested
          .yulExpression .yul))) input with
    | invariant error => simp [presentResult] at result
    | reject failure rejected =>
        simp only [presentResult] at result
        change Reply.ok none input = Reply.ok (some arguments) next at result
        cases result
    | ok value afterPresent =>
        simp only [presentResult] at result
        cases result
        change (do
          pure (some (← delimited .leftParen .rightParen true nested
            .yulExpression .yul))) input = .ok (some arguments) next at presentResult
        cases argumentsResult : delimited .leftParen .rightParen true nested
            .yulExpression .yul input with
        | invariant error =>
            simp only [bind, argumentsResult] at presentResult
            contradiction
        | reject failure rejected =>
            simp only [bind, argumentsResult] at presentResult
            contradiction
        | ok parsed afterArguments =>
            simp only [bind, argumentsResult] at presentResult
            cases presentResult
            exact delimited_startsAtCurrentTokenOnSuccess .leftParen
              .rightParen true nested .yulExpression .yul input arguments
              next argumentsResult
  · cases result

/-- Rejected source-level Yul meta syntax produces a valid error expression. -/
theorem rejectedMeta_yulExpr_validFor :
    rejectedMeta.ValidFor YulExpr.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid expression next result
    unfold rejectedMeta at result
    cases found : input.peek? with
    | none =>
        simp only [found] at result
        unfold rejectAt at result
        contradiction
    | some token =>
        rcases token with ⟨span, kind⟩
        have spanValid := inputValid.peek?_span_validFor found
        have advancedValid :
            ({ input with cursor := input.cursor + 1 } : State).ValidFor := by
          apply inputValid.advance?_validFor
          unfold State.advance?
          rw [found]
          rfl
        cases kind <;> simp only [found] at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals exact ⟨YulExpr.ValidFor.error spanValid,
          advancedValid.emit_validFor _ spanValid, rfl⟩
  · intro input inputValid failure next result
    unfold rejectedMeta at result
    cases found : input.peek? with
    | none =>
        simp only [found] at result
        exact rejectAt_reject_validFor inputValid _ _ result
    | some token =>
        rcases token with ⟨span, kind⟩
        cases kind <;> simp only [found] at result
        all_goals try { exact rejectAt_reject_validFor inputValid _ _ result }
        all_goals contradiction

/-- Meta-syntax rejection preserves every ordinary token window. -/
theorem rejectedMeta_preservesTokenWindow :
    Parser.PreservesTokenWindow rejectedMeta := by
  intro input
  unfold rejectedMeta
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      all_goals exact ⟨rfl, rfl⟩

/-- The outer range of rejected meta syntax remains source-valid. -/
theorem rejectedMeta_validFor :
    rejectedMeta.ValidFor Located.ValidFor :=
  rejectedMeta_yulExpr_validFor.mono (by
    intro file expression valid
    cases valid <;> assumption)

/-- Rejected source-level Yul meta syntax preserves the token carrier. -/
theorem rejectedMeta_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess rejectedMeta := by
  intro input expression next result
  unfold rejectedMeta at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals rfl

/-- Rejected meta syntax starts at the diagnosed input token. -/
theorem rejectedMeta_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess rejectedMeta (·.span) := by
  intro input expression next result
  unfold rejectedMeta at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals exact ⟨_, rfl, rfl⟩

/-- Rejected source-level Yul meta syntax advances by one token. -/
theorem rejectedMeta_cursor_lt_onSuccess {input next : State}
    {expression : YulExpr} (result : rejectedMeta input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold rejectedMeta at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals simp [State.emit]

/-- Rejected source-level Yul meta syntax never rewinds the parser cursor. -/
theorem rejectedMeta_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess rejectedMeta := by
  intro input expression next result
  exact Nat.le_of_lt (rejectedMeta_cursor_lt_onSuccess result)

/-- One recursive Yul-expression layer preserves all retained source ranges. -/
theorem yulExpressionCore_validFor
    (nested : Parser YulExpr)
    (nestedValid : nested.ValidFor YulExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulExpressionCore nested).ValidFor YulExpr.ValidFor := by
  intro input inputValid
  unfold yulExpressionCore
  split
  · cases literalResult : yulLiteral input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have valid := yulLiteral_validFor input inputValid
        rw [literalResult] at valid
        simpa only [Reply.ValidFor] using valid
    | ok literal afterLiteral =>
        have valid := yulLiteral_validFor input inputValid
        rw [literalResult] at valid
        exact ⟨YulExpr.ValidFor.literal valid.1 valid.1,
          valid.2.1, valid.2.2⟩
  · split
    · cases nameResult : yulName input with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have valid := yulName_validFor input inputValid
          rw [nameResult] at valid
          simpa only [Reply.ValidFor] using valid
      | ok name afterName =>
          have nameValid := yulName_validFor input inputValid
          rw [nameResult] at nameValid
          simp only
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              have valid := optionalYulCallArguments_validFor nested
                YulExpr.ValidFor nestedValid nestedPreserves afterName
                nameValid.2.1
              rw [argumentsResult] at valid
              exact valid.of_file_eq nameValid.2.2
          | ok arguments afterArguments =>
              have argumentsValid := optionalYulCallArguments_validFor nested
                YulExpr.ValidFor nestedValid nestedPreserves afterName
                nameValid.2.1
              rw [argumentsResult] at argumentsValid
              cases arguments with
              | none =>
                  exact ⟨YulExpr.ValidFor.identifier nameValid.1 nameValid.1,
                    argumentsValid.2.1,
                    argumentsValid.2.2.trans nameValid.2.2⟩
              | some arguments =>
                  have nameSpanValid : name.span.ValidFor input.file := by
                    simpa only [Located.ValidFor] using nameValid.1
                  have argumentsSpanValid :
                      arguments.span.ValidFor input.file := by
                    simpa only [Option.ValidFor, DelimitedList.ValidFor,
                      nameValid.2.2] using argumentsValid.1.1
                  have retainedValid : ∀ argument ∈ arguments.elements,
                      YulExpr.ValidFor input.file argument := by
                    intro argument member
                    simpa only [Option.ValidFor, DelimitedList.ValidFor,
                      nameValid.2.2] using argumentsValid.1.2 argument member
                  rcases yulName_ok_state_shape nameResult with
                    ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
                  rcases optionalYulCallArguments_some_startsAtCurrentTokenOnSuccess
                      nested argumentsResult with
                    ⟨openingToken, openingFound, openingStart⟩
                  have nameAt :=
                    State.getElem?_eq_some_of_peek?_eq_some nameFound
                  have openingAt :
                      input.tokens[afterName.cursor]? = some openingToken := by
                    have found :=
                      State.getElem?_eq_some_of_peek?_eq_some openingFound
                    simpa [nameTokens] using found
                  have nameEndBeforeArgumentsStart :
                      name.span.endByte ≤ arguments.span.startByte := by
                    have ordered :=
                      inputValid.token_end_le_token_start_of_getElem?_lt
                        nameAt openingAt (by rw [nameCursor]; simp)
                    simpa [nameSpan, openingStart] using ordered
                  have coverValid := SourceSpan.cover_validFor nameSpanValid
                    argumentsSpanValid (Nat.le_trans nameSpanValid.2.1
                      (Nat.le_trans nameEndBeforeArgumentsStart
                        argumentsSpanValid.2.1))
                  exact ⟨YulExpr.ValidFor.call coverValid nameSpanValid
                      argumentsSpanValid retainedValid,
                    argumentsValid.2.1,
                    argumentsValid.2.2.trans nameValid.2.2⟩
    · split <;> try { exact
          rejectedMeta_yulExpr_validFor input inputValid }
      unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩

/-- A successful Yul-expression layer starts at its leading token. -/
theorem yulExpressionCore_startsAtCurrentTokenOnSuccess
    (nested : Parser YulExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulExpressionCore nested) (·.span) := by
  intro input expression next result
  unfold yulExpressionCore at result
  split at result
  · cases literalResult : yulLiteral input with
    | invariant error => simp [literalResult] at result
    | reject failure rejected => simp [literalResult] at result
    | ok literal afterLiteral =>
        simp only [literalResult] at result
        have starts := yulLiteral_startsAtCurrentTokenOnSuccess input literal
          afterLiteral literalResult
        cases result
        exact starts
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
              rcases yulName_startsAtCurrentTokenOnSuccess input name afterName
                  nameResult with ⟨token, found, start⟩
              cases arguments <;> cases result
              · exact ⟨token, found, start⟩
              · exact ⟨token, found, start⟩
    · split at result <;> try { exact
          rejectedMeta_startsAtCurrentTokenOnSuccess input expression next result }
      unfold rejectAt at result
      contradiction

/-- One Yul-expression layer preserves tokens when its recursive parser does. -/
theorem yulExpressionCore_preservesTokensOnSuccess
    (nested : Parser YulExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulExpressionCore nested) := by
  intro input expression next result
  unfold yulExpressionCore at result
  split at result
  · cases literalResult : yulLiteral input with
    | ok literal afterLiteral =>
        simp only [literalResult] at result
        have preserved := yulLiteral_preservesTokensOnSuccess input literal
          afterLiteral literalResult
        cases result
        exact preserved
    | reject failure rejected => simp [literalResult] at result
    | invariant error => simp [literalResult] at result
  · split at result
    · cases nameResult : yulName input with
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              have argumentsPreserved :=
                optionalYulCallArguments_preservesTokensOnSuccess nested
                  nestedPreserves afterName arguments afterArguments
                    argumentsResult
              have namePreserved := yulName_preservesTokensOnSuccess input name
                afterName nameResult
              cases arguments <;> cases result
              all_goals exact argumentsPreserved.trans namePreserved
          | reject failure rejected => simp [argumentsResult] at result
          | invariant error => simp [argumentsResult] at result
      | reject failure rejected => simp [nameResult] at result
      | invariant error => simp [nameResult] at result
    · split at result <;> try { exact
          rejectedMeta_preservesTokensOnSuccess input expression next result }
      unfold rejectAt at result
      contradiction

/-- One Yul-expression layer preserves every ordinary token window. -/
theorem yulExpressionCore_preservesTokenWindow
    (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (yulExpressionCore nested) := by
  intro input
  unfold yulExpressionCore
  split
  · have literalShape := yulLiteral_preservesTokenWindow input
    cases literalResult : yulLiteral input with
    | ok literal next => rw [literalResult] at literalShape; exact literalShape
    | reject failure next =>
        rw [literalResult] at literalShape
        exact literalShape
    | invariant error => trivial
  · split
    · have nameShape := yulName_preservesTokenWindow input
      cases nameResult : yulName input with
      | ok name afterName =>
          rw [nameResult] at nameShape
          have argumentsShape :=
            optionalYulCallArguments_preservesTokenWindow nested nestedShape
              afterName
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | ok arguments next =>
              rw [argumentsResult] at argumentsShape
              cases arguments <;>
                simp only [argumentsResult, Reply.PreservesTokenWindow] <;>
                exact argumentsShape.trans nameShape
          | reject failure next =>
              rw [argumentsResult] at argumentsShape
              simp only [argumentsResult, Reply.PreservesTokenWindow]
              exact argumentsShape.trans nameShape
          | invariant error =>
              simp only [argumentsResult, Reply.PreservesTokenWindow]
      | reject failure next =>
          rw [nameResult] at nameShape
          exact nameShape
      | invariant error => trivial
    · split
      all_goals try { exact rejectedMeta_preservesTokenWindow input }
      exact rejectAt_preservesTokenWindow input _ _

/-- Core Yul rejection retains the caller's immutable token window. -/
theorem yulExpressionCore_reject_preservesTokenWindow
    (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input failedState : State} {failure : Failure}
    (result : yulExpressionCore nested input =
      .reject failure failedState) :
    failedState.tokens = input.tokens ∧
      failedState.window = input.window := by
  have preserved := yulExpressionCore_preservesTokenWindow nested nestedShape input
  rw [result] at preserved
  exact preserved

/-- Every successful Yul-expression layer consumes at least its leading token. -/
theorem yulExpressionCore_cursor_lt_onSuccess
    (nested : Parser YulExpr) {input next : State} {expression : YulExpr}
    (result : yulExpressionCore nested input = .ok expression next) :
    input.cursor < next.cursor := by
  unfold yulExpressionCore at result
  split at result
  · cases literalResult : yulLiteral input with
    | ok literal afterLiteral =>
        simp only [literalResult] at result
        have shape := yulLiteral_ok_state_shape literalResult
        cases result
        rw [shape]
        simp
    | reject failure rejected => simp [literalResult] at result
    | invariant error => simp [literalResult] at result
  · split at result
    · cases nameResult : yulName input with
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalYulCallArguments nested afterName with
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              have nameProgress : input.cursor < afterName.cursor := by
                rw [(yulName_ok_state_shape nameResult).choose_spec.2.2.2]
                simp
              have argumentsMonotone :=
                optionalYulCallArguments_cursorMonotoneOnSuccess nested
                  afterName arguments afterArguments argumentsResult
              cases arguments <;> cases result
              all_goals exact Nat.lt_of_lt_of_le nameProgress argumentsMonotone
          | reject failure rejected => simp [argumentsResult] at result
          | invariant error => simp [argumentsResult] at result
      | reject failure rejected => simp [nameResult] at result
      | invariant error => simp [nameResult] at result
    · split at result <;> try { exact
          rejectedMeta_cursor_lt_onSuccess result }
      unfold rejectAt at result
      contradiction

/-- One Yul-expression layer never rewinds the parser cursor. -/
theorem yulExpressionCore_cursorMonotoneOnSuccess
    (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (yulExpressionCore nested) := by
  intro input expression next result
  exact Nat.le_of_lt (yulExpressionCore_cursor_lt_onSuccess nested result)

namespace YulExpressionInternals

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

/-- Finishing Yul-expression recovery retains a source-valid error range. -/
theorem finishRecovered_validFor (first last : SourceSpan) (state : State)
    (stateValid : state.ValidFor) (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecovered first last state).ValidFor state YulExpr.ValidFor := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecovered Reply.ValidFor
  exact ⟨YulExpr.ValidFor.error spanValid,
    stateValid.emit_validFor _ spanValid, rfl⟩

/--
Recovery preserves recursive expression provenance.  The final hypotheses
record the already-consumed token whose span is `last`; they make the source
ordering needed by the next recovery step explicit.
-/
theorem recoverAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverAux first last fuel state).ValidFor state YulExpr.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverAux
      split
      · exact finishRecovered_validFor first last state stateValid firstValid
          lastValid ordered
      · cases advanced : state.advance? with
        | some pair =>
            rcases pair with ⟨token, next⟩
            have nextValid := stateValid.advance?_validFor advanced
            unfold State.advance? at advanced
            cases found : state.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have tokenValid := stateValid.peek?_span_validFor found
                have currentFound :=
                  State.getElem?_eq_some_of_peek?_eq_some found
                have lastBeforeCurrent :=
                  stateValid.token_end_le_token_start_of_getElem?_lt
                    lastFound currentFound lastBefore
                have recursive := inductionHypothesis token.span
                  { state with cursor := state.cursor + 1 } state.cursor token
                  nextValid (by simpa using firstValid)
                  (by simpa using tokenValid)
                  (Nat.le_trans ordered (Nat.le_trans
                    (by simpa [lastSpan] using lastBeforeCurrent)
                    tokenValid.2.1))
                  currentFound rfl (by simp)
                exact recursive.of_file_eq rfl
        | none =>
            exact finishRecovered_validFor first last state stateValid
              firstValid lastValid ordered

/-- Successful recovery preserves tokens, cursor order, and its first byte. -/
theorem recoverAux_ok_state_shape (first : SourceSpan) :
    ∀ fuel last input expression next,
      recoverAux first last fuel input = .ok expression next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        expression.span.startByte = first.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last input expression next result
      unfold recoverAux at result
      split at result
      · unfold finishRecovered at result
        cases result
        exact ⟨rfl, Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recursive := inductionHypothesis token.span afterToken
              expression next result
            unfold State.advance? at advanced
            cases found : input.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                exact ⟨recursive.1,
                  Nat.le_trans (Nat.le_add_right input.cursor 1)
                    recursive.2.1,
                  recursive.2.2⟩
        | none =>
            simp only [advanced] at result
            unfold finishRecovered at result
            cases result
            exact ⟨rfl, Nat.le_refl _, rfl⟩

/-- Yul recovery preserves the immutable lexer token carrier on success. -/
theorem recoverAux_preservesTokensOnSuccess (first last : SourceSpan)
    (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (recoverAux first last fuel) := by
  intro input expression next result
  exact (recoverAux_ok_state_shape first fuel last input expression next
    result).1

/-- Yul recovery never rewinds the cursor on success. -/
theorem recoverAux_cursorMonotoneOnSuccess (first last : SourceSpan)
    (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess (recoverAux first last fuel) := by
  intro input expression next result
  exact (recoverAux_ok_state_shape first fuel last input expression next
    result).2.1

/-- Yul recovery preserves the complete immutable token window. -/
theorem recoverAux_preservesTokenWindow (first last : SourceSpan)
    (fuel : Nat) :
    Parser.PreservesTokenWindow (recoverAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverAux
      split
      · unfold finishRecovered Reply.PreservesTokenWindow
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecovered Reply.PreservesTokenWindow
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            have recursive := inductionHypothesis token.span afterToken
            have advanceShape := advance?_state_shape advanced
            exact recursive.trans (by
              simp [advanceShape.2])

/-- One recovering Yul-expression layer preserves recursive provenance. -/
theorem layer_validFor (nested : Parser YulExpr)
    (nestedValid : nested.ValidFor YulExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreRejectShape : ∀ input failure failedState,
      yulExpressionCore nested input = .reject failure failedState →
      failedState.tokens = input.tokens ∧ failedState.window = input.window) :
    (layer nested).ValidFor YulExpr.ValidFor := by
  intro input inputValid
  unfold layer
  cases coreResult : yulExpressionCore nested input with
  | ok expression next =>
      have valid := yulExpressionCore_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [coreResult] at valid
      exact valid
  | invariant error => trivial
  | reject failure failedState =>
      have coreValid := yulExpressionCore_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [coreResult] at coreValid
      have rejectedShape := coreRejectShape input failure failedState coreResult
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := coreValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, rejectedShape.2] using inputValid.cursor_le_endIndex
        endIndex_le_size := coreValid.2.1.endIndex_le_size
        endByte_le_source := coreValid.2.1.endByte_le_source
        endByte_boundary := coreValid.2.1.endByte_boundary
        diagnosticsRev := coreValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using coreValid.2.2
      have failureValid : failure.span.ValidFor rewound.file := by
        simpa [rewound, coreValid.2.2] using coreValid.1
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, next) =>
            recoverAux token.span token.span (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).ValidFor input YulExpr.ValidFor
      split
      · exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
      · cases advanced : rewound.advance? with
        | none => exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            have advanceShape := advance?_state_shape advanced
            have nextValid := rewoundValid.advance?_validFor advanced
            have tokenValid : token.span.ValidFor next.file := by
              rw [advanceShape.2]
              exact rewoundValid.peek?_span_validFor advanceShape.1
            have emittedValid := nextValid.emit_validFor failure.toDiagnostic
              (by simpa [advanceShape.2] using
                failure.toDiagnostic_span_validFor failureValid)
            have currentFound :
                (next.emit failure.toDiagnostic).tokens[rewound.cursor]? =
                  some token := by
              simpa [advanceShape.2, State.emit] using
                State.getElem?_eq_some_of_peek?_eq_some advanceShape.1
            have recovered := recoverAux_validFor token.span
              (next.remainingCount + 1) token.span
              (next.emit failure.toDiagnostic) rewound.cursor token emittedValid
              (by simpa [State.emit] using tokenValid)
              (by simpa [State.emit] using tokenValid)
              tokenValid.2.1 currentFound rfl (by
                simp [advanceShape.2, State.emit])
            exact recovered.of_file_eq (by
              simpa [advanceShape.2, State.emit] using rewoundFile)

/-- A recovering Yul layer preserves tokens when rejection does as well. -/
theorem layer_preservesTokensOnSuccess (nested : Parser YulExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreRejectPreserves : ∀ input failure failedState,
      yulExpressionCore nested input = .reject failure failedState →
      failedState.tokens = input.tokens) :
    Parser.PreservesTokensOnSuccess (layer nested) := by
  intro input expression next result
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | ok value afterCore =>
      simp only [coreResult] at result
      have preserved := yulExpressionCore_preservesTokensOnSuccess nested
        nestedPreserves input value afterCore coreResult
      cases result
      exact preserved
  | invariant error => simp [coreResult] at result
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok expression next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recovered := recoverAux_ok_state_shape token.span
              (afterToken.remainingCount + 1) token.span
              (afterToken.emit failure.toDiagnostic) expression next result
            have advanceShape := advance?_state_shape advanced
            exact recovered.1.trans (by
              simpa [advanceShape.2, State.emit, rewound] using
                coreRejectPreserves input failure failedState coreResult)

/-- A recovering Yul layer preserves every ordinary token window. -/
theorem layer_preservesTokenWindow (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (layer nested) := by
  intro input
  unfold layer
  cases coreResult : yulExpressionCore nested input with
  | invariant error => trivial
  | ok expression next =>
      have coreShape := yulExpressionCore_preservesTokenWindow nested
        nestedShape input
      rw [coreResult] at coreShape
      exact coreShape
  | reject failure failedState =>
      have coreShape := yulExpressionCore_preservesTokenWindow nested
        nestedShape input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using coreShape
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := by
        simpa [rewound] using failedShape
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).PreservesTokenWindow input
      split
      · exact rewoundShape
      · cases advanced : rewound.advance? with
        | none => exact rewoundShape
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            have recovered := recoverAux_preservesTokenWindow token.span
              token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
            have advanceShape := advance?_state_shape advanced
            exact recovered.trans (by
              simpa [State.emit, advanceShape.2] using rewoundShape)

/-- A recovering Yul layer never rewinds its caller's cursor. -/
theorem layer_cursorMonotoneOnSuccess (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (layer nested) := by
  intro input expression next result
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | invariant error => simp [coreResult] at result
  | ok value afterCore =>
      simp only [coreResult] at result
      have monotone := yulExpressionCore_cursorMonotoneOnSuccess nested
        input value afterCore coreResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok expression next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recovered := recoverAux_cursorMonotoneOnSuccess token.span
              token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic) expression next result
            have advanceShape := advance?_state_shape advanced
            exact Nat.le_trans (by simp [advanceShape.2, State.emit, rewound])
              recovered

/-- A successful recovering layer starts at its caller's current token. -/
theorem layer_startsAtCurrentTokenOnSuccess (nested : Parser YulExpr)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.StartsAtCurrentTokenOnSuccess (layer nested) (·.span) := by
  intro input expression next result
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | invariant error => simp [coreResult] at result
  | ok value afterCore =>
      simp only [coreResult] at result
      have starts := yulExpressionCore_startsAtCurrentTokenOnSuccess nested
        input value afterCore coreResult
      cases result
      simpa using starts
  | reject failure failedState =>
      simp only [coreResult] at result
      have coreShape := yulExpressionCore_reject_preservesTokenWindow nested
        nestedShape coreResult
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isBoundary rewound then Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok expression next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have advanceShape := advance?_state_shape advanced
            have found : input.peek? = some token := by
              have rewoundFound := advanceShape.1
              unfold State.peek? at rewoundFound ⊢
              simpa [rewound, coreShape.1, coreShape.2] using rewoundFound
            have recovered := recoverAux_ok_state_shape token.span
              (afterToken.remainingCount + 1) token.span
              (afterToken.emit failure.toDiagnostic) expression next result
            exact ⟨token, found, recovered.2.2.symm⟩

/-- Every fuel-bounded recursive Yul parser preserves token windows. -/
theorem withFuel_preservesTokenWindow : ∀ fuel,
    Parser.PreservesTokenWindow (withFuel fuel) := by
  intro fuel
  induction fuel with
  | zero => intro input; trivial
  | succ fuel inductionHypothesis =>
      exact layer_preservesTokenWindow (withFuel fuel) inductionHypothesis

/-- Every fuel-bounded recursive Yul parser preserves source provenance. -/
theorem withFuel_validFor : ∀ fuel,
    (withFuel fuel).ValidFor YulExpr.ValidFor := by
  intro fuel
  induction fuel with
  | zero =>
      intro input inputValid
      change True
      trivial
  | succ fuel inductionHypothesis =>
      have nestedShape := withFuel_preservesTokenWindow fuel
      exact layer_validFor (withFuel fuel) inductionHypothesis
        nestedShape.preservesTokensOnSuccess (by
          intro input failure failedState result
          exact yulExpressionCore_reject_preservesTokenWindow
            (withFuel fuel) nestedShape result)

/-- Every fuel-bounded recursive Yul parser preserves its token carrier. -/
theorem withFuel_preservesTokensOnSuccess (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (withFuel fuel) :=
  (withFuel_preservesTokenWindow fuel).preservesTokensOnSuccess

/-- Every fuel-bounded recursive Yul parser keeps cursor order. -/
theorem withFuel_cursorMonotoneOnSuccess : ∀ fuel,
    Parser.CursorMonotoneOnSuccess (withFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input expression next result
      unfold withFuel at result
      contradiction
  | succ fuel inductionHypothesis =>
      exact layer_cursorMonotoneOnSuccess (withFuel fuel)

/-- Every successful fuel-bounded Yul parser starts at its input token. -/
theorem withFuel_startsAtCurrentTokenOnSuccess : ∀ fuel,
    Parser.StartsAtCurrentTokenOnSuccess (withFuel fuel) (·.span) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input expression next result
      unfold withFuel at result
      contradiction
  | succ fuel inductionHypothesis =>
      exact layer_startsAtCurrentTokenOnSuccess (withFuel fuel)
        (withFuel_preservesTokenWindow fuel)

end YulExpressionInternals

/-- The public recursive Yul parser preserves all retained source ranges. -/
theorem yulExpression_validFor :
    yulExpression.ValidFor YulExpr.ValidFor := by
  intro input inputValid
  unfold yulExpression
  exact YulExpressionInternals.withFuel_validFor
    (input.remainingCount + 1) input inputValid

/-- The public recursive Yul parser preserves every ordinary token window. -/
theorem yulExpression_preservesTokenWindow :
    Parser.PreservesTokenWindow yulExpression := by
  intro input
  unfold yulExpression
  exact YulExpressionInternals.withFuel_preservesTokenWindow
    (input.remainingCount + 1) input

/-- The public recursive Yul parser preserves its immutable token carrier. -/
theorem yulExpression_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulExpression :=
  yulExpression_preservesTokenWindow.preservesTokensOnSuccess

/-- The public recursive Yul parser never rewinds its cursor. -/
theorem yulExpression_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulExpression := by
  intro input expression next result
  unfold yulExpression at result
  exact YulExpressionInternals.withFuel_cursorMonotoneOnSuccess
    (input.remainingCount + 1) input expression next result

/-- A successful public Yul expression starts at its current input token. -/
theorem yulExpression_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulExpression (·.span) := by
  intro input expression next result
  unfold yulExpression at result
  exact YulExpressionInternals.withFuel_startsAtCurrentTokenOnSuccess
    (input.remainingCount + 1) input expression next result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulCallArgumentsSoundnessProperties
/-!
Diagnostic reflection and exact ordered soundness for transactional inline-Yul
call arguments.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulLeftParenTokenAtOfIsSymbol
    {input : State} (present : isSymbol input .leftParen = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .leftParen } := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol .leftParen) = true at present
      have parsed : symbol .leftParen .yulExpression input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold symbol acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span,
        (symbol_ok_tokenAt .leftParen .yulExpression parsed).1⟩

/-- Optional Yul call arguments reflect diagnostics through either successful
transactional branch. -/
theorem optionalYulCallArguments_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalYulCallArguments nested) := by
  intro input arguments next result diagnosticFree
  unfold optionalYulCallArguments at result
  split at result
  · exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
      (Parser.bind_reflectsDiagnosticFreeOnSuccess
        (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
          nested .yulExpression .yul nestedReflects)
        (fun values => Parser.pure_reflectsDiagnosticFreeOnSuccess
          (some values)))
      (Parser.pure_reflectsDiagnosticFreeOnSuccess none)
      input arguments next result diagnosticFree
  · cases result
    exact diagnosticFree

/-- Every diagnostic-free optional-call success records absence, a disjoint
ordinary-rejection fallback, or the exact preferred argument-list grammar. -/
theorem optionalYulCallArguments_success_sound
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
    {input next : State}
    {arguments : Option (DelimitedList YulExpr)}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalYulCallArguments nested input = .ok arguments next) :
    DeclarativeGrammar.OptionalYulCallArgumentsParses nestedParses fallback
      input.declarativeRemainder arguments next.declarativeRemainder := by
  unfold optionalYulCallArguments at result
  by_cases present : isSymbol input .leftParen = true
  · simp only [present, if_true] at result
    unfold orElse at result
    cases argumentsResult : delimited .leftParen .rightParen true nested
        .yulExpression .yul input with
    | invariant error =>
        simp [bind, argumentsResult] at result
    | reject failure failed =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        rcases yulLeftParenTokenAtOfIsSymbol present with
          ⟨openingSpan, openingToken⟩
        exact .rewound openingSpan openingToken
          (rejectSound argumentsResult)
    | ok values afterArguments =>
        simp only [bind, argumentsResult, pure] at result
        cases result
        exact .present
          (delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
            .leftParen .rightParen nested nestedParses .yulExpression .yul
            nestedSound nestedReflects nestedShape diagnosticFree
            argumentsResult)
  · have absentBool : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absentBool, Bool.false_eq_true, if_false] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen absentBool)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionCoreSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulExpressionLayerSoundnessProperties
/-!
Public diagnostic-free declarative bridge for the recoverable inline-Yul
expression layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The public recoverable Yul layer reflects diagnostic freedom whenever its
recursive expression parser does. -/
theorem yulExpressionLayer_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (YulExpressionInternals.layer nested) :=
  YulExpressionInternals.layer_reflectsDiagnosticFreeOnSuccess nested
    (yulExpressionCore_reflectsDiagnosticFreeOnSuccess nested nestedReflects)

/-- Every diagnostic-free public-layer success is the unchanged core success
and follows the exact literal-before-name inline-Yul grammar. -/
theorem yulExpressionLayer_success_sound
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
    (result : YulExpressionInternals.layer nested input =
      .ok expression next) :
    DeclarativeGrammar.YulExpressionCoreParses nestedParses fallback
      input.declarativeRemainder expression next.declarativeRemainder :=
  yulExpressionCore_success_sound nested nestedParses fallback nestedReflects
    nestedSound nestedShape rejectSound diagnosticFree
      (YulExpressionInternals.layer_core_of_diagnosticFree_success nested
        result diagnosticFree)

end Solcore.Syntax.Parser
end
