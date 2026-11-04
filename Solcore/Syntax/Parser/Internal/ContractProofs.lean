import Solcore.Syntax.Parser.Internal.ContractEntryProofs
import Solcore.Syntax.Parser.Internal.ImplProofs
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Syntax.Parser.Declarations
import Solcore.Syntax.Parser.Internal.DeriveSoundness
import Solcore.Syntax.Parser.Internal.EnumProofs
import Solcore.Syntax.Parser.Internal.TypeAliasProofs
import Solcore.Syntax.Parser.Internal.TypeBasics
import Solcore.Syntax.Validity
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Grammar.Declarations
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Internal.DeclarationExactness
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.Internal.TermSoundness

/-!
Proofs about the parsers of contracts: token-window and cursor laws, source validity,
soundness against the declarative grammar, and exact outcomes.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.DeclarationCanonicalProperties
/-! Canonical recursive-validity instances for body-bearing declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public functions retain canonical Core statements in their bodies. -/
theorem functionDecl_canonical_validFor (location : FunctionLocation) :
    (functionDecl location).ValidFor
      (FunctionDecl.ValidFor CoreStatement.ValidFor) :=
  functionDecl_validFor CoreStatement.ValidFor location
    (block_canonical_validFor .allow)

/-- Constructors retain canonical Core statements in their bodies. -/
theorem constructorDecl_canonical_validFor :
    constructorDecl.ValidFor
      (ConstructorDecl.ValidFor CoreStatement.ValidFor) :=
  constructorDecl_validFor CoreStatement.ValidFor
    (block_canonical_validFor .require)

/-- Fallback declarations retain canonical Core statements in their bodies. -/
theorem fallbackDecl_canonical_validFor :
    fallbackDecl.ValidFor
      (FallbackDecl.ValidFor CoreStatement.ValidFor) :=
  fallbackDecl_validFor CoreStatement.ValidFor
    (block_canonical_validFor .require)

/-- Implementations retain canonical Core statements in every method body. -/
theorem implDecl_canonical_validFor :
    implDecl.ValidFor (ImplDecl.ValidFor CoreStatement.ValidFor) :=
  implDecl_validFor CoreStatement.ValidFor
    (block_canonical_validFor .allow)
    (block_canonical_preservesTokenWindow .allow)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractProperties
/-! Contracts for canonical contract declaration parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

private theorem contractBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
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
theorem optionalFieldInitializer_validFor (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid) :
    (optionalFieldInitializer expression).ValidFor
      (Option.ValidFor expressionValueValid) := by
  unfold optionalFieldInitializer
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .equal
  · simp only [present, if_true]
    apply Parser.bind_validFor (symbol_validFor .equal .contractMember)
    intro equal
    apply Parser.bind_validFor_of_value expressionValid
    intro value input inputValid valueValid
    exact ⟨by simpa only [Option.ValidFor] using valueValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)
theorem optionalFieldInitializer_preservesTokenWindow
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow
      (optionalFieldInitializer expression) := by
  unfold optionalFieldInitializer
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isSymbol observed .equal
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .equal .contractMember)
    intro equal
    apply Parser.bind_preservesTokenWindow expressionWindow
    intro value
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none
theorem optionalFieldInitializer_preservesTokensOnSuccess
    (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess
      (optionalFieldInitializer expression) :=
  (optionalFieldInitializer_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess
theorem optionalFieldInitializer_cursorMonotoneOnSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess
      (optionalFieldInitializer expression) := by
  unfold optionalFieldInitializer
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .equal
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .equal .contractMember)
    intro equal
    apply Parser.bind_cursorMonotoneOnSuccess expressionCursor
    intro value
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none
theorem contractField_preservesTokenWindow (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (contractField expression) := by
  unfold contractField
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .contractMember); intro name
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .colon .contractMember); intro colon
  apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
  intro type
  apply Parser.bind_preservesTokenWindow
    (optionalFieldInitializer_preservesTokenWindow expression
      expressionWindow); intro initializer
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .contractMember); intro semicolon
  exact Parser.pure_preservesTokenWindow _
theorem contractField_preservesTokensOnSuccess (expression : Parser Expr)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (contractField expression) :=
  (contractField_preservesTokenWindow expression
    expressionWindow).preservesTokensOnSuccess
theorem contractField_cursorMonotoneOnSuccess (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (contractField expression) := by
  unfold contractField
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .contractMember); intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .colon .contractMember); intro colon
  apply Parser.bind_cursorMonotoneOnSuccess
    typeExpr_cursorMonotoneOnSuccess; intro type
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalFieldInitializer_cursorMonotoneOnSuccess expression
      expressionCursor); intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .contractMember); intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _
theorem contractField_startsAtCurrentTokenOnSuccess
    (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (contractField expression) (·.span) := by
  intro input field final parsed
  have stages := parsed
  unfold contractField at stages
  rcases contractBind_ok_components stages with
    ⟨name, afterName, nameResult, rest⟩
  rcases contractBind_ok_components rest with ⟨_, _, _, rest⟩
  rcases contractBind_ok_components rest with ⟨_, _, _, rest⟩
  rcases contractBind_ok_components rest with ⟨_, _, _, rest⟩
  rcases contractBind_ok_components rest with ⟨semicolon, _, _, finished⟩
  rcases identifier_ok_state_shape .contractMember nameResult with
    ⟨token, found, tokenSpan, _tokens, _cursor⟩
  cases finished
  exact ⟨token, found, by simp [SourceSpan.cover, tokenSpan]⟩
theorem contractField_value_validForOnSuccess
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {field : ContractField}
    (inputValid : input.ValidFor)
    (parsed : contractField expression input = .ok field final) :
    ContractField.ValidFor expressionValueValid input.file field := by
  have stages := parsed
  unfold contractField at stages
  rcases contractBind_ok_components stages with
    ⟨name, afterName, nameResult, rest⟩
  rcases contractBind_ok_components rest with
    ⟨colon, afterColon, colonResult, rest⟩
  rcases contractBind_ok_components rest with
    ⟨type, afterType, typeResult, rest⟩
  rcases contractBind_ok_components rest with
    ⟨initializer, afterInitializer, initializerResult, rest⟩
  rcases contractBind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  have nameContract := identifier_validFor .contractMember input inputValid
  rw [nameResult] at nameContract
  have colonContract := symbol_validFor .colon .contractMember afterName
    nameContract.2.1
  rw [colonResult] at colonContract
  have typeContract := typeExpr_validFor afterColon colonContract.2.1
  rw [typeResult] at typeContract
  have initializerContract := optionalFieldInitializer_validFor expression
    expressionValueValid expressionValid afterType typeContract.2.1
  rw [initializerResult] at initializerContract
  have semicolonContract := symbol_validFor .semicolon .contractMember
    afterInitializer initializerContract.2.1
  rw [semicolonResult] at semicolonContract
  have nameValid : name.span.ValidFor input.file := by
    simpa only [Located.ValidFor] using nameContract.1
  have typeValid : TypeExpr.ValidFor input.file type := by
    simpa [colonContract.2.2, nameContract.2.2] using typeContract.1
  have initializerValid : Option.ValidFor expressionValueValid input.file
      initializer := by
    simpa [typeContract.2.2, colonContract.2.2, nameContract.2.2] using
      initializerContract.1
  have semicolonValid : semicolon.span.ValidFor input.file := by
    simpa only [Located.ValidFor, initializerContract.2.2,
      typeContract.2.2, colonContract.2.2, nameContract.2.2] using
      semicolonContract.1
  rcases identifier_ok_state_shape .contractMember nameResult with
    ⟨nameToken, nameFound, nameTokenSpan, _nameTokens, nameCursor⟩
  have nameAt := State.getElem?_eq_some_of_peek?_eq_some nameFound
  have semicolonAtAfter := State.getElem?_eq_some_of_peek?_eq_some
    (symbol_ok_state_shape .semicolon .contractMember semicolonResult).1
  have semicolonAt : input.tokens[afterInitializer.cursor]? = some semicolon := by
    simpa [optionalFieldInitializer_preservesTokensOnSuccess expression
        expressionWindow afterType initializer afterInitializer initializerResult,
      typeExpr_preservesTokensOnSuccess afterColon type afterType typeResult,
      symbol_preservesTokensOnSuccess .colon .contractMember afterName colon
        afterColon colonResult,
      identifier_preservesTokensOnSuccess .contractMember input name afterName
        nameResult] using semicolonAtAfter
  have nameStrict : input.cursor < afterName.cursor := by
    rw [nameCursor]
    simp
  have cursorOrder : input.cursor < afterInitializer.cursor :=
    Nat.lt_of_lt_of_le nameStrict (Nat.le_trans
      (symbol_cursorMonotoneOnSuccess .colon .contractMember afterName colon
        afterColon colonResult) (Nat.le_trans
      (typeExpr_cursorMonotoneOnSuccess afterColon type afterType typeResult)
      (optionalFieldInitializer_cursorMonotoneOnSuccess expression
        expressionCursor afterType initializer afterInitializer
          initializerResult)))
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt
    nameAt semicolonAt cursorOrder
  have outerValid := SourceSpan.cover_validFor nameValid semicolonValid
    (Nat.le_trans nameValid.2.1
      (Nat.le_trans (by simpa [nameTokenSpan] using separated)
        semicolonValid.2.1))
  cases finished
  exact ⟨outerValid, nameValid, typeValid, by
    intro value member
    cases initializer with
    | none => simp at member
    | some retained =>
        have valueEq : value = retained := by simpa using member.symm
        subst value
        simpa only [Option.ValidFor] using initializerValid⟩
theorem contractField_validFor (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    (contractField expression).ValidFor
      (ContractField.ValidFor expressionValueValid) := by
  have weak : (contractField expression).ValidFor (fun _ _ => True) := by
    unfold contractField
    apply Parser.bind_validFor (identifier_validFor .contractMember); intro name
    apply Parser.bind_validFor (symbol_validFor .colon .contractMember)
    intro colon
    apply Parser.bind_validFor typeExpr_validFor; intro type
    apply Parser.bind_validFor
      (optionalFieldInitializer_validFor expression expressionValueValid
        expressionValid); intro initializer
    apply Parser.bind_validFor
      (symbol_validFor .semicolon .contractMember); intro semicolon
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : contractField expression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok field final =>
      rw [parsed] at weakResult
      exact ⟨contractField_value_validForOnSuccess expression
        expressionValueValid expressionValid expressionWindow expressionCursor
        inputValid parsed, weakResult.2.1, weakResult.2.2⟩

abbrev CanonicalContractMemberValid : SourceFile → ContractMember → Prop :=
  ContractMember.ValidFor CoreStatement.ValidFor
    (Expr.ValidFor CoreStatement.ValidFor)

def ContractMemberSpanAligned (member : ContractMember) : Prop :=
  match member.value with
  | .field declaration => member.span = declaration.span
  | .function declaration => member.span = declaration.span
  | .constructor declaration => member.span = declaration.span
  | .fallback declaration => member.span = declaration.span
  | .typeAlias declaration => member.span = declaration.span
  | .enum declaration => member.span = declaration.span
  | .error => True

/-- Canonical validity plus the alignment needed by attribute attachment. -/
structure CanonicalContractMemberContract (file : SourceFile)
    (member : ContractMember) : Prop where
  validFor : CanonicalContractMemberValid file member
  spanAligned : ContractMemberSpanAligned member

private theorem contractMember_span_valid {file : SourceFile} {member : ContractMember}
    (valid : CanonicalContractMemberValid file member) :
    member.span.ValidFor file := by cases valid <;> assumption

/-- Prefix extension preserves member provenance and outer-span alignment. -/
theorem extendContractMemberStart_contract {file : SourceFile}
    (prefixSpan : SourceSpan) (member : ContractMember)
    (prefixValid : prefixSpan.ValidFor file)
    (memberContract : CanonicalContractMemberContract file member)
    (ordered : prefixSpan.startByte ≤ member.span.endByte) :
    CanonicalContractMemberContract file (extendContractMemberStart prefixSpan member) := by
  have coveredValid := SourceSpan.cover_validFor prefixValid
    (contractMember_span_valid memberContract.validFor) ordered
  constructor
  · cases memberContract.validFor with
    | field _ commentsValid declarationValid =>
        exact .field coveredValid commentsValid ⟨coveredValid, declarationValid.2⟩
    | function _ commentsValid declarationValid =>
        exact .function coveredValid commentsValid ⟨coveredValid, declarationValid.2⟩
    | constructor _ commentsValid declarationValid =>
        exact .constructor coveredValid commentsValid ⟨coveredValid, declarationValid.2⟩
    | fallback _ commentsValid declarationValid =>
        exact .fallback coveredValid commentsValid ⟨coveredValid, declarationValid.2⟩
    | typeAlias _ commentsValid declarationValid =>
        exact .typeAlias coveredValid commentsValid ⟨coveredValid, declarationValid.2⟩
    | enum _ commentsValid declarationValid =>
        exact .enum coveredValid commentsValid ⟨coveredValid, declarationValid.2⟩
    | error _ commentsValid => exact .error coveredValid commentsValid
  · rcases member with ⟨span, comments, value⟩
    cases value <;> simp [extendContractMemberStart, ContractMemberSpanAligned]

/-- Attaching a valid derive attribute preserves the canonical member contract. -/
theorem attachContractDerive_reply_validFor
    (derive : DeriveAttribute) (member : ContractMember) (input : State)
    (inputValid : input.ValidFor)
    (deriveValid : DeriveAttribute.ValidFor input.file derive)
    (memberContract : CanonicalContractMemberContract input.file member)
    (ordered : derive.span.startByte ≤ member.span.endByte) :
    (attachContractDerive derive member input).ValidFor input
      CanonicalContractMemberContract := by
  rcases member with ⟨memberSpan, comments, value⟩
  cases value
  all_goals first
  | have extended := extendContractMemberStart_contract derive.span _ deriveValid.1 memberContract ordered
    unfold attachContractDerive bind emitDiagnostic modifyState pure Reply.ValidFor
    exact ⟨extended, inputValid.emit_validFor _ deriveValid.1, rfl⟩
  | rename_i declaration
    have aligned : memberSpan = declaration.span := by
      simpa only [ContractMemberSpanAligned] using memberContract.spanAligned
    have declarationValid := by cases memberContract.validFor; assumption
    have coveredValid := SourceSpan.cover_validFor deriveValid.1
      declarationValid.1 (by simpa [aligned] using ordered)
    have retainedDerive : ∀ retained ∈ (some derive : Option DeriveAttribute), DeriveAttribute.ValidFor input.file retained := by
      intro retained retainedMember
      simp only [Option.mem_def] at retainedMember
      cases Option.some.inj retainedMember
      exact deriveValid
    unfold attachContractDerive Reply.ValidFor
    exact ⟨{
      validFor := .enum coveredValid (by
        cases memberContract.validFor
        assumption) ⟨coveredValid, retainedDerive, declarationValid.2.2⟩
      spanAligned := rfl
    }, inputValid, rfl⟩

private theorem emitThenPure_preservesTokenWindow
    (diagnostic : ParseDiagnostic) (value : ContractMember) :
    Parser.PreservesTokenWindow (do
      let _ ← emitDiagnostic diagnostic
      pure value) := by
  apply Parser.bind_preservesTokenWindow
    (emitDiagnostic_preservesTokenWindow diagnostic)
  intro _
  exact Parser.pure_preservesTokenWindow value

theorem attachContractDerive_preservesTokenWindow
    (derive : DeriveAttribute) (member : ContractMember) :
    Parser.PreservesTokenWindow (attachContractDerive derive member) := by
  rcases member with ⟨span, comments, value⟩
  cases value <;> first
  | exact Parser.pure_preservesTokenWindow _
  | exact emitThenPure_preservesTokenWindow _ _

theorem attachContractDerive_preservesTokensOnSuccess
    (derive : DeriveAttribute) (member : ContractMember) :
    Parser.PreservesTokensOnSuccess (attachContractDerive derive member) :=
  (attachContractDerive_preservesTokenWindow derive member).preservesTokensOnSuccess

private theorem emitThenPure_cursorMonotoneOnSuccess
    (diagnostic : ParseDiagnostic) (value : ContractMember) :
    Parser.CursorMonotoneOnSuccess (do
      let _ ← emitDiagnostic diagnostic
      pure value) := by
  apply Parser.bind_cursorMonotoneOnSuccess
    (emitDiagnostic_cursorMonotoneOnSuccess diagnostic)
  intro _
  exact Parser.pure_cursorMonotoneOnSuccess value

theorem attachContractDerive_cursorMonotoneOnSuccess
    (derive : DeriveAttribute) (member : ContractMember) :
    Parser.CursorMonotoneOnSuccess (attachContractDerive derive member) := by
  rcases member with ⟨span, comments, value⟩
  cases value <;> first
  | exact Parser.pure_cursorMonotoneOnSuccess _
  | exact emitThenPure_cursorMonotoneOnSuccess _ _

theorem attachContractDerive_preservesDeriveStartOnSuccess
    (derive : DeriveAttribute) (member : ContractMember)
    {input final : State} {result : ContractMember}
    (parsed : attachContractDerive derive member input = .ok result final) :
    derive.span.startByte = result.span.startByte := by
  rcases member with ⟨span, comments, value⟩
  cases value <;>
    unfold attachContractDerive bind emitDiagnostic modifyState pure at parsed
  all_goals cases parsed; rfl

theorem attachContractDerive_spanAlignedOnSuccess
    (derive : DeriveAttribute) (member : ContractMember)
    {input final : State} {result : ContractMember}
    (parsed : attachContractDerive derive member input = .ok result final) :
    ContractMemberSpanAligned result := by
  rcases member with ⟨span, comments, value⟩
  cases value <;>
    unfold attachContractDerive bind emitDiagnostic modifyState pure at parsed
  all_goals cases parsed <;>
    simp [ContractMemberSpanAligned, extendContractMemberStart]

/-- Source and state guarantees shared by every contract-member branch. -/
structure ContractMemberParserContract
    (parser : Parser ContractMember) : Prop where
  validFor : parser.ValidFor CanonicalContractMemberValid
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess parser (·.span)
  spanAlignedOnSuccess : ∀ input member next,
    parser input = .ok member next → ContractMemberSpanAligned member

namespace ContractMemberParserContract

theorem preservesTokensOnSuccess {parser : Parser ContractMember}
    (contract : ContractMemberParserContract parser) :
    Parser.PreservesTokensOnSuccess parser :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

end ContractMemberParserContract

theorem mapMember_contract {alpha : Type} (parser : Parser alpha)
    (wrap : alpha → ContractMember)
    (valueValid : SourceFile → alpha → Prop) (span : alpha → SourceSpan)
    (parserValid : parser.ValidFor valueValid)
    (parserWindow : Parser.PreservesTokenWindow parser)
    (parserCursor : Parser.CursorMonotoneOnSuccess parser)
    (parserStarts : Parser.StartsAtCurrentTokenOnSuccess parser span)
    (wrapValid : ∀ file value, valueValid file value →
      CanonicalContractMemberValid file (wrap value))
    (wrapSpan : ∀ value, (wrap value).span = span value)
    (wrapAligned : ∀ value, ContractMemberSpanAligned (wrap value)) :
    ContractMemberParserContract (mapMember parser wrap) := {
  validFor := by
    unfold mapMember
    apply Parser.bind_validFor_of_value parserValid
    intro value input inputValid valueIsValid
    exact ⟨wrapValid input.file value valueIsValid, inputValid, rfl⟩
  preservesTokenWindow := by
    unfold mapMember
    apply Parser.bind_preservesTokenWindow parserWindow
    intro value
    exact Parser.pure_preservesTokenWindow _
  cursorMonotoneOnSuccess := by
    unfold mapMember
    apply Parser.bind_cursorMonotoneOnSuccess parserCursor
    intro value
    exact Parser.pure_cursorMonotoneOnSuccess _
  startsAtCurrentTokenOnSuccess := by
    unfold mapMember
    apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first parserStarts
    intro value input member final parsed
    cases parsed
    exact (congrArg SourceSpan.startByte (wrapSpan value)).symm
  spanAlignedOnSuccess := by
    intro input member next parsed
    rcases contractBind_ok_components parsed with ⟨value, _, _, finished⟩
    cases finished
    exact wrapAligned value
}

theorem contractField_canonical_contract : ContractMemberParserContract
    (mapMember (contractField expression) wrapField) :=
  mapMember_contract (contractField expression) wrapField
    (ContractField.ValidFor (Expr.ValidFor CoreStatement.ValidFor)) (·.span)
    (contractField_validFor expression (Expr.ValidFor CoreStatement.ValidFor)
      expression_canonical_contract.validFor
      expression_canonical_contract.preservesTokenWindow
      expression_canonical_contract.cursorMonotoneOnSuccess)
    (contractField_preservesTokenWindow expression
      expression_canonical_contract.preservesTokenWindow)
    (contractField_cursorMonotoneOnSuccess expression
      expression_canonical_contract.cursorMonotoneOnSuccess)
    (contractField_startsAtCurrentTokenOnSuccess expression)
    (fun _ _ valid => .field valid.1 (by simp) valid) (fun _ => rfl)
    (fun _ => rfl)

theorem contractFunction_canonical_contract : ContractMemberParserContract
    (mapMember (functionDecl .contract) wrapContractFunction) :=
  mapMember_contract (functionDecl .contract) wrapContractFunction
    (FunctionDecl.ValidFor CoreStatement.ValidFor) (·.span)
    (functionDecl_canonical_validFor .contract)
    (functionDecl_preservesTokenWindow_of_block .contract
      (block_canonical_preservesTokenWindow .allow))
    (functionDecl_cursorMonotoneOnSuccess_of_block .contract
      (block_canonical_cursorMonotoneOnSuccess .allow))
    (functionDecl_startsAtCurrentTokenOnSuccess .contract)
    (fun _ _ valid => .function valid.1 (by simp) valid) (fun _ => rfl)
    (fun _ => rfl)

theorem contractConstructor_canonical_contract : ContractMemberParserContract
    (mapMember constructorDecl wrapConstructor) :=
  mapMember_contract constructorDecl wrapConstructor
    (ConstructorDecl.ValidFor CoreStatement.ValidFor) (·.span)
    constructorDecl_canonical_validFor
    (constructorDecl_preservesTokenWindow
      (block_canonical_preservesTokenWindow .require))
    (constructorDecl_cursorMonotoneOnSuccess
      (block_canonical_cursorMonotoneOnSuccess .require))
    constructorDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ valid => .constructor valid.1 (by simp) valid) (fun _ => rfl)
    (fun _ => rfl)

theorem contractFallback_canonical_contract : ContractMemberParserContract
    (mapMember fallbackDecl wrapFallback) :=
  mapMember_contract fallbackDecl wrapFallback
    (FallbackDecl.ValidFor CoreStatement.ValidFor) (·.span)
    fallbackDecl_canonical_validFor
    (fallbackDecl_preservesTokenWindow
      (block_canonical_preservesTokenWindow .require))
    (fallbackDecl_cursorMonotoneOnSuccess
      (block_canonical_cursorMonotoneOnSuccess .require))
    fallbackDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ valid => .fallback valid.1 (by simp) valid) (fun _ => rfl)
    (fun _ => rfl)

theorem contractTypeAlias_canonical_contract : ContractMemberParserContract
    (mapMember typeAlias wrapContractTypeAlias) :=
  mapMember_contract typeAlias wrapContractTypeAlias TypeAliasDecl.ValidFor
    (·.span) typeAlias_validFor typeAlias_preservesTokenWindow
    typeAlias_cursorMonotoneOnSuccess
    typeAlias_startsAtCurrentTokenOnSuccess
    (fun _ _ valid => .typeAlias valid.1 (by simp) valid) (fun _ => rfl)
    (fun _ => rfl)

theorem contractEnum_canonical_contract : ContractMemberParserContract
    (mapMember (enumDecl none) wrapContractEnum) :=
  mapMember_contract (enumDecl none) wrapContractEnum EnumDecl.ValidFor
    (·.span) enumDecl_none_validFor (enumDecl_preservesTokenWindow none)
    (enumDecl_cursorMonotoneOnSuccess none)
    enumDecl_none_startsAtCurrentTokenOnSuccess
    (fun _ _ valid => .enum valid.1 (by simp) valid) (fun _ => rfl)
    (fun _ => rfl)

theorem rejectedContractMember_canonical_contract :
    ContractMemberParserContract rejectedContractMember := {
  validFor := by
    intro input inputValid
    unfold rejectedContractMember rejectAt Reply.ValidFor
    exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  preservesTokenWindow := by
    intro input
    exact rejectAt_preservesTokenWindow input _ _
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    simp [rejectedContractMember, rejectAt] at parsed
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    simp [rejectedContractMember, rejectAt] at parsed
  spanAlignedOnSuccess := by
    intro input value next parsed
    simp [rejectedContractMember, rejectAt] at parsed
}

theorem contractMemberParser_canonical_contract (state : State) :
    ContractMemberParserContract (contractMemberParser state) := by
  unfold contractMemberParser
  split
  · exact contractField_canonical_contract
  split
  · exact contractFunction_canonical_contract
  split
  · exact contractConstructor_canonical_contract
  split
  · exact contractFallback_canonical_contract
  split
  · exact contractTypeAlias_canonical_contract
  split
  · exact contractEnum_canonical_contract
  · exact rejectedContractMember_canonical_contract

theorem contractMemberCore_canonical_contract :
    ContractMemberParserContract contractMemberCore := {
  validFor := by
    intro input inputValid
    exact (contractMemberParser_canonical_contract input).validFor
      input inputValid
  preservesTokenWindow := by
    intro input
    exact (contractMemberParser_canonical_contract input).preservesTokenWindow
      input
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    exact (contractMemberParser_canonical_contract input).cursorMonotoneOnSuccess
      input value next parsed
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    exact (contractMemberParser_canonical_contract input).startsAtCurrentTokenOnSuccess
      input value next parsed
  spanAlignedOnSuccess := by
    intro input value next parsed
    exact (contractMemberParser_canonical_contract input).spanAlignedOnSuccess
      input value next parsed
}

private theorem derive_start_le_member_end {input afterDerive next : State}
    {derive : DeriveAttribute} {member : ContractMember}
    (inputValid : input.ValidFor)
    (deriveResult : deriveAttribute input = .ok derive afterDerive)
    (memberResult : contractMemberCore afterDerive = .ok member next)
    (memberSpanValid : member.span.ValidFor input.file) :
    derive.span.startByte ≤ member.span.endByte := by
  rcases deriveAttribute_startsAtCurrentTokenOnSuccess _ _ _ deriveResult with
    ⟨first, firstFound, firstStart⟩
  rcases contractMemberCore_canonical_contract.startsAtCurrentTokenOnSuccess
      _ _ _ memberResult with ⟨last, lastFound, lastStart⟩
  have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
  have lastAt := State.getElem?_eq_some_of_peek?_eq_some lastFound
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt firstAt
    (by simpa [deriveAttribute_preservesTokensOnSuccess _ _ _ deriveResult]
      using lastAt) (deriveAttribute_cursor_lt_onSuccess deriveResult)
  exact calc
    derive.span.startByte = first.span.startByte := firstStart.symm
    _ ≤ first.span.endByte := (inputValid.peek?_span_validFor firstFound).2.1
    _ ≤ last.span.startByte := separated
    _ = member.span.startByte := lastStart
    _ ≤ member.span.endByte := memberSpanValid.2.1

/-- The derive-aware member parser satisfies the canonical member contract. -/
theorem contractMemberWithAttribute_canonical_contract :
    ContractMemberParserContract contractMemberWithAttribute := {
  validFor := by
    intro input inputValid
    unfold contractMemberWithAttribute
    by_cases attributed : isSymbol input .hash
    · simp only [attributed, if_true]
      have deriveReply := deriveAttribute_validFor input inputValid
      cases deriveResult : deriveAttribute input with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          simp only
          rw [deriveResult] at deriveReply
          simpa only [Reply.ValidFor] using deriveReply
      | ok derive afterDerive =>
          simp only
          rw [deriveResult] at deriveReply
          have memberReply := contractMemberCore_canonical_contract.validFor
            afterDerive deriveReply.2.1
          cases memberResult : contractMemberCore afterDerive with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              simp only
              rw [memberResult] at memberReply
              exact memberReply.of_file_eq deriveReply.2.2
          | ok member next =>
              simp only
              rw [memberResult] at memberReply
              have fileEq := memberReply.2.2.trans deriveReply.2.2
              have attached := attachContractDerive_reply_validFor derive member
                next memberReply.2.1 (by simpa [fileEq] using deriveReply.1)
                ⟨by simpa [memberReply.2.2] using memberReply.1,
                  contractMemberCore_canonical_contract.spanAlignedOnSuccess
                    _ _ _ memberResult⟩
                (derive_start_le_member_end inputValid deriveResult memberResult
                  (by simpa [deriveReply.2.2] using
                    contractMember_span_valid memberReply.1))
              exact (attached.mono (fun _ _ contract => contract.validFor)).of_file_eq
                fileEq
    · simp only [attributed]
      exact contractMemberCore_canonical_contract.validFor input inputValid
  preservesTokenWindow := by
    intro input
    unfold contractMemberWithAttribute
    split
    · have deriveWindow := deriveAttribute_preservesTokenWindow input
      cases deriveResult : deriveAttribute input with
      | invariant error => simp only [Reply.PreservesTokenWindow]
      | reject failure rejected =>
          simp only
          rw [deriveResult] at deriveWindow
          simpa only [Reply.PreservesTokenWindow] using deriveWindow
      | ok derive afterDerive =>
          simp only
          rw [deriveResult] at deriveWindow
          have memberWindow :=
            contractMemberCore_canonical_contract.preservesTokenWindow afterDerive
          cases memberResult : contractMemberCore afterDerive with
          | invariant error => simp only [Reply.PreservesTokenWindow]
          | reject failure rejected =>
              simp only
              rw [memberResult] at memberWindow
              exact memberWindow.trans deriveWindow
          | ok member next =>
              simp only
              rw [memberResult] at memberWindow
              exact (attachContractDerive_preservesTokenWindow derive member next).trans
                (memberWindow.trans deriveWindow)
    · exact contractMemberCore_canonical_contract.preservesTokenWindow input
  cursorMonotoneOnSuccess := by
    intro input result final parsed
    unfold contractMemberWithAttribute at parsed
    split at parsed
    · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
      rename_i derive afterDerive
      cases memberResult : contractMemberCore afterDerive <;>
        simp [memberResult] at parsed
      rename_i member next
      exact Nat.le_trans (deriveAttribute_cursorMonotoneOnSuccess _ _ _ deriveResult)
        (Nat.le_trans (contractMemberCore_canonical_contract.cursorMonotoneOnSuccess
          _ _ _ memberResult)
          (attachContractDerive_cursorMonotoneOnSuccess _ _ _ _ _ parsed))
    · exact contractMemberCore_canonical_contract.cursorMonotoneOnSuccess
        _ _ _ parsed
  startsAtCurrentTokenOnSuccess := by
    intro input result final parsed
    unfold contractMemberWithAttribute at parsed
    split at parsed
    · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
      rename_i derive afterDerive
      cases memberResult : contractMemberCore afterDerive <;>
        simp [memberResult] at parsed
      rcases deriveAttribute_startsAtCurrentTokenOnSuccess _ _ _ deriveResult with
        ⟨token, found, start⟩
      exact ⟨token, found, start.trans
        (attachContractDerive_preservesDeriveStartOnSuccess _ _ parsed)⟩
    · exact contractMemberCore_canonical_contract.startsAtCurrentTokenOnSuccess
        _ _ _ parsed
  spanAlignedOnSuccess := by
    intro input result final parsed
    unfold contractMemberWithAttribute at parsed
    split at parsed
    · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
      rename_i derive afterDerive
      cases memberResult : contractMemberCore afterDerive <;>
        simp [memberResult] at parsed
      exact attachContractDerive_spanAlignedOnSuccess _ _ parsed
    · exact contractMemberCore_canonical_contract.spanAlignedOnSuccess
        _ _ _ parsed
}
end ContractInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractFieldSoundnessProperties
/-! Parametric diagnostic-free soundness for contract storage fields. -/

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

namespace ContractInternals

/-- Optional initializer parsing reflects diagnostic freedom through its
abstract expression parser. -/
theorem optionalFieldInitializer_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalFieldInitializer expression) := by
  unfold optionalFieldInitializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .equal .contractMember)
    intro equal
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess expressionReflects
    intro value
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- Every diagnostic-free optional initializer success preserves the `=`
priority decision and follows the supplied expression grammar. -/
theorem optionalFieldInitializer_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    {input next : State} {initializer : Option Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalFieldInitializer expression input =
      .ok initializer next) :
    DeclarativeGrammar.OptionalContractFieldInitializerParses
      expressionParses input.declarativeRemainder initializer
        next.declarativeRemainder := by
  unfold optionalFieldInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal
  · simp only [present, if_true] at result
    cases equalResult : symbol .equal .contractMember input with
    | invariant error => simp [equalResult] at result
    | reject failure rejected => simp [equalResult] at result
    | ok equal afterEqual =>
        simp only [equalResult] at result
        cases valueResult : expression afterEqual with
        | invariant error => simp [valueResult] at result
        | reject failure rejected => simp [valueResult] at result
        | ok value afterValue =>
            simp only [valueResult, pure] at result
            cases result
            exact .present equal.span
              (symbol_success_exactTokenParses .equal .contractMember
                equalResult)
              (expressionSound diagnosticFree valueResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .equal absent)

/-- Optional-initializer grammar soundness composes with source validity. -/
theorem optionalFieldInitializer_success_sound_and_validFor
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    {input next : State} {initializer : Option Expr}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalFieldInitializer expression input =
      .ok initializer next) :
    DeclarativeGrammar.OptionalContractFieldInitializerParses
        expressionParses input.declarativeRemainder initializer
          next.declarativeRemainder ∧
      Option.ValidFor expressionValueValid input.file initializer := by
  refine ⟨optionalFieldInitializer_success_sound expression
    expressionParses expressionSound diagnosticFree result,
    ?_⟩
  have valid := optionalFieldInitializer_validFor expression
    expressionValueValid expressionValid input inputValid
  rw [result] at valid
  exact valid.1

/-- Contract-field parsing reflects diagnostic freedom whenever initializer
expressions do. -/
theorem contractField_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (contractField expression) := by
  unfold contractField
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .contractMember)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .colon .contractMember)
  intro colon
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    typeExpr_reflectsDiagnosticFreeOnSuccess
  intro type
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalFieldInitializer_reflectsDiagnosticFreeOnSuccess expression
      expressionReflects)
  intro initializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .contractMember)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every diagnostic-free field success follows the exact name, type,
initializer, and semicolon grammar. -/
theorem contractField_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    {input next : State} {field : ContractField}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractField expression input = .ok field next) :
    DeclarativeGrammar.ContractFieldParses expressionParses
      input.declarativeRemainder field next.declarativeRemainder := by
  unfold contractField at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨colon, afterColon, colonResult, rest⟩
  rcases bind_ok_components rest with
    ⟨type, afterType, typeResult, rest⟩
  rcases bind_ok_components rest with
    ⟨initializer, afterInitializer, initializerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have afterInitializerFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .contractMember afterInitializer semicolon next
      semicolonResult diagnosticFree
  exact .parsed colon.span semicolon.span
    (identifier_success_sound .contractMember nameResult)
    (symbol_success_exactTokenParses .colon .contractMember colonResult)
    (typeExpr_success_sound typeResult)
    (optionalFieldInitializer_success_sound expression expressionParses
      expressionSound afterInitializerFree initializerResult)
    (symbol_success_exactTokenParses .semicolon .contractMember
      semicolonResult)

/-- Parametric field grammar soundness composes with source validity. -/
theorem contractField_success_sound_and_validFor
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    {input next : State} {field : ContractField}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractField expression input = .ok field next) :
    DeclarativeGrammar.ContractFieldParses expressionParses
        input.declarativeRemainder field next.declarativeRemainder ∧
      ContractField.ValidFor expressionValueValid input.file field := by
  refine ⟨contractField_success_sound expression expressionParses
    expressionSound diagnosticFree result, ?_⟩
  have valid := contractField_validFor expression expressionValueValid
    expressionValid expressionWindow expressionCursor input inputValid
  rw [result] at valid
  exact valid.1

end ContractInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberCoreSoundnessProperties
/-! Parametric strict soundness for attribute-free contract-member dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ContractInternals

private theorem tokenKind_eq_colon_of_beq_true {actual : TokenKind}
    (accepted : (actual == .symbol .colon) = true) :
    actual = .symbol .colon := by
  change instBEqTokenKind.beq actual (.symbol .colon) = true at accepted
  cases actual <;> simp only [instBEqTokenKind.beq] at accepted
  all_goals try contradiction
  case symbol actual =>
    change instBEqSymbol.beq actual .colon = true at accepted
    unfold instBEqSymbol.beq at accepted
    cases actual <;> first | rfl | cases accepted

/-- Executable positive field lookahead is exactly the two-token grammar. -/
theorem contractFieldStartsAt_of_startsContractField_eq_true
    {input : State} (starts : startsContractField input = true) :
    DeclarativeGrammar.ContractFieldStartsAt input.declarativeRemainder := by
  unfold startsContractField at starts
  have parts := Bool.and_eq_true_iff.mp starts
  cases currentFound : input.peek? with
  | none =>
      simp [isIdentifier, State.peekKind?, currentFound] at parts
  | some current =>
      rcases current with ⟨nameSpan, currentKind⟩
      cases currentKind <;>
        simp [isIdentifier, State.peekKind?, currentFound] at parts
      case identifier spelling =>
        unfold State.peekOffsetKind? at parts
        cases followingFound : input.peekOffset? 1 with
        | none => simp [followingFound] at parts
        | some following =>
            rcases following with ⟨colonSpan, followingKind⟩
            simp only [followingFound, Option.map_some] at parts
            have followingKindEq := tokenKind_eq_colon_of_beq_true parts
            subst followingKind
            exact ⟨spelling, nameSpan, colonSpan,
              tokenAt_of_peek?_eq_some currentFound,
              State.cursor_add_lt_endIndex_of_peekOffset?_eq_some
                followingFound,
              State.getElem?_eq_some_of_peekOffset?_eq_some followingFound⟩

/-- The independent two-token field grammar makes executable lookahead true. -/
theorem startsContractField_eq_true_of_contractFieldStartsAt
    {input : State}
    (starts : DeclarativeGrammar.ContractFieldStartsAt
      input.declarativeRemainder) :
    startsContractField input = true := by
  rcases starts with ⟨spelling, nameSpan, colonSpan, nameToken, colonToken⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span := nameSpan, value := .identifier spelling }
    at nameToken
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    (input.cursor + 1) { span := colonSpan, value := .symbol .colon }
    at colonToken
  have namePresent : isIdentifier input = true := by
    unfold isIdentifier State.peekKind? State.peek?
    simp only [nameToken.1, ↓reduceIte, nameToken.2, Option.map_some]
  have colonPresent : input.peekOffsetKind? 1 =
      some (.symbol .colon) := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [colonToken.1, ↓reduceIte, colonToken.2, Option.map_some]
  unfold startsContractField
  rw [namePresent, colonPresent]
  decide

/-- Executable negative field lookahead excludes the exact field prefix. -/
theorem not_contractFieldStartsAt_of_startsContractField_eq_false
    {input : State} (stops : startsContractField input = false) :
    ¬ DeclarativeGrammar.ContractFieldStartsAt input.declarativeRemainder := by
  intro starts
  rw [startsContractField_eq_true_of_contractFieldStartsAt starts] at stops
  contradiction

private theorem mapMember_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → ContractMember)
    (reflects : Parser.ReflectsDiagnosticFreeOnSuccess parser) :
    Parser.ReflectsDiagnosticFreeOnSuccess (mapMember parser wrap) := by
  unfold mapMember
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess reflects
  intro value
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Core dispatch cannot erase diagnostics when its abstract leaves cannot. -/
theorem contractMemberCore_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess contractMemberCore := by
  intro input member next result diagnosticFree
  unfold contractMemberCore contractMemberParser at result
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      (contractField expression) wrapField
      (contractField_reflectsDiagnosticFreeOnSuccess expression
        expressionReflects) input member next result diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      (functionDecl .contract) wrapContractFunction
      (functionDecl_reflectsDiagnosticFreeOnSuccess .contract
        allowBodyReflects) input member next result diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      constructorDecl wrapConstructor
      (constructorDecl_reflectsDiagnosticFreeOnSuccess requiredBodyReflects)
        input member next result diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      fallbackDecl wrapFallback
      (fallbackDecl_reflectsDiagnosticFreeOnSuccess requiredBodyReflects)
        input member next result diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      typeAlias wrapContractTypeAlias
      typeAlias_reflectsDiagnosticFreeOnSuccess input member next result
        diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      (enumDecl none) wrapContractEnum
      (enumDecl_reflectsDiagnosticFreeOnSuccess none) input member next result
        diagnosticFree
  · simp [rejectedContractMember, rejectAt] at result

/-- Every diagnostic-free core success follows the exact six-way priority. -/
theorem contractMemberCore_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {member : ContractMember}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractMemberCore input = .ok member next) :
    DeclarativeGrammar.ContractMemberCoreParses expressionParses
      allowBodyParses requiredBodyParses input.declarativeRemainder member
        next.declarativeRemainder := by
  unfold contractMemberCore contractMemberParser at result
  split at result
  next startsField =>
    unfold mapMember at result
    rcases bind_ok_components result with
      ⟨declaration, afterDeclaration, declarationResult, finished⟩
    cases finished
    exact .field
      (contractFieldStartsAt_of_startsContractField_eq_true startsField)
      (contractField_success_sound expression expressionParses
        expressionSound diagnosticFree declarationResult)
  next fieldAbsent =>
    have fieldAbsentEq : startsContractField input = false :=
      Bool.eq_false_iff.mpr fieldAbsent
    split at result
    next startsFunction =>
      unfold mapMember at result
      rcases bind_ok_components result with
        ⟨declaration, afterDeclaration, declarationResult, finished⟩
      cases finished
      exact .function
        (not_contractFieldStartsAt_of_startsContractField_eq_false
          fieldAbsentEq)
        (functionDecl_success_sound .contract allowBodyParses
          allowBodyReflects allowBodySound diagnosticFree declarationResult)
    next functionAbsent =>
      have functionAbsentEq : isKeyword input .functionKw = false :=
        Bool.eq_false_iff.mpr functionAbsent
      split at result
      next startsConstructor =>
        unfold mapMember at result
        rcases bind_ok_components result with
          ⟨declaration, afterDeclaration, declarationResult, finished⟩
        cases finished
        exact .constructor
          (not_contractFieldStartsAt_of_startsContractField_eq_false
            fieldAbsentEq)
          (keywordAbsentAt_of_isKeyword_eq_false .functionKw
            functionAbsentEq)
          (constructorDecl_success_sound requiredBodyParses
            requiredBodyReflects requiredBodySound diagnosticFree
              declarationResult)
      next constructorAbsent =>
        have constructorAbsentEq : isKeyword input .constructorKw = false :=
          Bool.eq_false_iff.mpr constructorAbsent
        split at result
        next startsFallback =>
          unfold mapMember at result
          rcases bind_ok_components result with
            ⟨declaration, afterDeclaration, declarationResult, finished⟩
          cases finished
          exact .fallback
            (not_contractFieldStartsAt_of_startsContractField_eq_false
              fieldAbsentEq)
            (keywordAbsentAt_of_isKeyword_eq_false .functionKw
              functionAbsentEq)
            (keywordAbsentAt_of_isKeyword_eq_false .constructorKw
              constructorAbsentEq)
            (fallbackDecl_success_sound requiredBodyParses
              requiredBodyReflects requiredBodySound diagnosticFree
                declarationResult)
        next fallbackAbsent =>
          have fallbackAbsentEq : isKeyword input .fallbackKw = false :=
            Bool.eq_false_iff.mpr fallbackAbsent
          split at result
          next startsType =>
            unfold mapMember at result
            rcases bind_ok_components result with
              ⟨declaration, afterDeclaration, declarationResult, finished⟩
            cases finished
            exact .typeAlias
              (not_contractFieldStartsAt_of_startsContractField_eq_false
                fieldAbsentEq)
              (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                functionAbsentEq)
              (keywordAbsentAt_of_isKeyword_eq_false .constructorKw
                constructorAbsentEq)
              (keywordAbsentAt_of_isKeyword_eq_false .fallbackKw
                fallbackAbsentEq)
              (typeAlias_success_sound diagnosticFree declarationResult)
          next typeAbsent =>
            have typeAbsentEq : isKeyword input .typeKw = false :=
              Bool.eq_false_iff.mpr typeAbsent
            split at result
            next startsEnum =>
              unfold mapMember at result
              rcases bind_ok_components result with
                ⟨declaration, afterDeclaration, declarationResult, finished⟩
              cases finished
              exact .enum
                (not_contractFieldStartsAt_of_startsContractField_eq_false
                  fieldAbsentEq)
                (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                  functionAbsentEq)
                (keywordAbsentAt_of_isKeyword_eq_false .constructorKw
                  constructorAbsentEq)
                (keywordAbsentAt_of_isKeyword_eq_false .fallbackKw
                  fallbackAbsentEq)
                (keywordAbsentAt_of_isKeyword_eq_false .typeKw typeAbsentEq)
                (enumDecl_success_sound none declarationResult)
            next enumAbsent =>
              simp [rejectedContractMember, rejectAt] at result

end ContractInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberStrictProperties
/-! Strict cursor progress for every canonical contract-member branch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem bind_cursor_lt_of_first {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstStrict : ∀ {input after : State} {value : alpha},
      first input = .ok value after → input.cursor < after.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok firstValue after => next firstValue after
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue after =>
      simp only [firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue after value final parsed)
  | reject failure rejected => simp [firstResult] at parsed
  | invariant error => simp [firstResult] at parsed

private theorem mapMember_cursor_lt_onSuccess {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → ContractMember)
    (strict : ∀ {input final : State} {value : alpha},
      parser input = .ok value final → input.cursor < final.cursor)
    {input final : State} {member : ContractMember}
    (parsed : mapMember parser wrap input = .ok member final) :
    input.cursor < final.cursor := by
  unfold mapMember at parsed
  change (match parser input with
    | .ok value next => Reply.ok (wrap value) next
    | .reject failure rejected => Reply.reject failure rejected
    | .invariant error => Reply.invariant error) =
      Reply.ok member final at parsed
  cases result : parser input with
  | reject failure rejected => simp [result] at parsed
  | invariant error => simp [result] at parsed
  | ok value next =>
      simp only [result] at parsed
      cases parsed
      exact strict result

theorem contractFieldMember_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : mapMember (contractField expression) wrapField input =
      .ok member final) :
    input.cursor < final.cursor := by
  apply mapMember_cursor_lt_onSuccess (contractField expression) wrapField
    _ parsed
  intro fieldInput fieldFinal field parsedField
  unfold contractField at parsedField
  refine bind_cursor_lt_of_first (parsed := parsedField) ?_ ?_
  · intro before after name nameResult
    rcases identifier_ok_state_shape .contractMember nameResult with
      ⟨token, found, span, tokens, cursor⟩
    omega
  · intro name
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .colon .contractMember); intro _
    apply Parser.bind_cursorMonotoneOnSuccess typeExpr_cursorMonotoneOnSuccess
      ; intro _
    apply Parser.bind_cursorMonotoneOnSuccess
      (optionalFieldInitializer_cursorMonotoneOnSuccess expression
        expression_canonical_contract.cursorMonotoneOnSuccess); intro _
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .semicolon .contractMember); intro _
    exact Parser.pure_cursorMonotoneOnSuccess _

theorem contractFunctionMember_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : mapMember (functionDecl .contract) wrapContractFunction input =
      .ok member final) : input.cursor < final.cursor := by
  apply mapMember_cursor_lt_onSuccess (functionDecl .contract)
    wrapContractFunction _ parsed
  intro functionInput functionFinal declaration parsedFunction
  unfold functionDecl at parsedFunction
  refine bind_cursor_lt_of_first (parsed := parsedFunction)
    (FunctionInternals.functionSignature_cursor_lt_onSuccess .contract) ?_
  intro signature
  apply Parser.bind_cursorMonotoneOnSuccess
    (isolateBlock_cursorMonotoneOnSuccess (block .allow)
      (block_canonical_cursorMonotoneOnSuccess .allow)); intro _
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem contractConstructorMember_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : mapMember constructorDecl wrapConstructor input =
      .ok member final) : input.cursor < final.cursor := by
  apply mapMember_cursor_lt_onSuccess constructorDecl wrapConstructor _ parsed
  intro constructorInput constructorFinal declaration parsedConstructor
  unfold constructorDecl at parsedConstructor
  apply bind_cursor_lt_of_first
    (acceptToken_cursor_lt_onSuccess (.keyword .constructorKw)
      .contractMember (fun kind => kind == .keyword .constructorKw))
    (fun _ => ?_) parsedConstructor
  apply Parser.bind_cursorMonotoneOnSuccess
    ContractEntryInternals.entryParameters_cursorMonotoneOnSuccess; intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
      .constructorKw); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (isolateBlock_cursorMonotoneOnSuccess (block .require)
      (block_canonical_cursorMonotoneOnSuccess .require)); intro _
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem contractFallbackMember_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : mapMember fallbackDecl wrapFallback input = .ok member final) :
    input.cursor < final.cursor := by
  apply mapMember_cursor_lt_onSuccess fallbackDecl wrapFallback _ parsed
  intro fallbackInput fallbackFinal declaration parsedFallback
  unfold fallbackDecl at parsedFallback
  apply bind_cursor_lt_of_first
    (acceptToken_cursor_lt_onSuccess (.keyword .fallbackKw)
      .contractMember (fun kind => kind == .keyword .fallbackKw))
    (fun _ => ?_) parsedFallback
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    ContractEntryInternals.entryParameters_cursorMonotoneOnSuccess
  intro _
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      (ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
        .fallbackKw); intro _
    apply Parser.bind_cursorMonotoneOnSuccess
      (isolateBlock_cursorMonotoneOnSuccess (block .require)
        (block_canonical_cursorMonotoneOnSuccess .require)); intro _
    exact Parser.pure_cursorMonotoneOnSuccess _
  · apply Parser.bind_cursorMonotoneOnSuccess
      (emitDiagnostic_cursorMonotoneOnSuccess _); intro _
    apply Parser.bind_cursorMonotoneOnSuccess
      (ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
        .fallbackKw); intro _
    apply Parser.bind_cursorMonotoneOnSuccess
      (isolateBlock_cursorMonotoneOnSuccess (block .require)
        (block_canonical_cursorMonotoneOnSuccess .require)); intro _
    exact Parser.pure_cursorMonotoneOnSuccess _

theorem contractTypeAliasMember_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : mapMember typeAlias wrapContractTypeAlias input =
      .ok member final) : input.cursor < final.cursor := by
  apply mapMember_cursor_lt_onSuccess typeAlias wrapContractTypeAlias _ parsed
  intro aliasInput aliasFinal declaration parsedAlias
  unfold typeAlias at parsedAlias
  apply bind_cursor_lt_of_first
    (acceptToken_cursor_lt_onSuccess (.keyword .typeKw) .typeAlias
      (fun kind => kind == .keyword .typeKw)) (fun _ => ?_) parsedAlias
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .typeAlias); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    parseTypeAliasParameters_cursorMonotoneOnSuccess; intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .equal .typeAlias); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    TypeAliasInternals.parseAliasValue_cursorMonotoneOnSuccess; intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .typeAlias); intro _
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem contractEnumMember_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : mapMember (enumDecl none) wrapContractEnum input =
      .ok member final) : input.cursor < final.cursor := by
  apply mapMember_cursor_lt_onSuccess (enumDecl none) wrapContractEnum _ parsed
  intro enumInput enumFinal declaration parsedEnum
  unfold enumDecl at parsedEnum
  apply bind_cursor_lt_of_first
    (acceptToken_cursor_lt_onSuccess (.contextual .enum) .topItem
      (fun kind => kind.isContextual .enum)) (fun _ => ?_) parsedEnum
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .topItem); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalGenericParameters_cursorMonotoneOnSuccess; intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    EnumInternals.enumBody_cursorMonotoneOnSuccess; intro _
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem contractMemberCore_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : contractMemberCore input = .ok member final) :
    input.cursor < final.cursor := by
  unfold contractMemberCore contractMemberParser at parsed
  split at parsed
  · exact contractFieldMember_cursor_lt_onSuccess parsed
  split at parsed
  · exact contractFunctionMember_cursor_lt_onSuccess parsed
  split at parsed
  · exact contractConstructorMember_cursor_lt_onSuccess parsed
  split at parsed
  · exact contractFallbackMember_cursor_lt_onSuccess parsed
  split at parsed
  · exact contractTypeAliasMember_cursor_lt_onSuccess parsed
  split at parsed
  · exact contractEnumMember_cursor_lt_onSuccess parsed
  · simp [rejectedContractMember, rejectAt] at parsed

theorem contractMemberWithAttribute_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : contractMemberWithAttribute input = .ok member final) :
    input.cursor < final.cursor := by
  unfold contractMemberWithAttribute at parsed
  split at parsed
  · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
    rename_i derive afterDerive
    cases memberResult : contractMemberCore afterDerive <;>
      simp [memberResult] at parsed
    rename_i coreMember afterMember
    exact Nat.lt_of_lt_of_le (deriveAttribute_cursor_lt_onSuccess deriveResult)
      (Nat.le_trans
        (contractMemberCore_canonical_contract.cursorMonotoneOnSuccess
          _ _ _ memberResult)
        (attachContractDerive_cursorMonotoneOnSuccess
          _ _ _ _ _ parsed))
  · exact contractMemberCore_cursor_lt_onSuccess parsed

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractRecoveryDiagnosticProperties
/-! Diagnostic commitments of contract-member recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Finishing a recovered contract member always emits its recovery diagnostic. -/
theorem finishRecoveredMember_success_hasDiagnostic
    (first last : SourceSpan) {input next : State} {member : ContractMember}
    (result : finishRecoveredMember first last input = .ok member next) :
    next.diagnosticsRev ≠ [] := by
  unfold finishRecoveredMember at result
  cases result
  simp [State.emit]

/-- Every successful auxiliary contract-member recovery retains a diagnostic. -/
theorem recoverContractMemberAux_success_hasDiagnostic
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {member : ContractMember},
      recoverContractMemberAux first last fuel input = .ok member next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverContractMemberAux]
  | succ fuel inductionHypothesis =>
      intro input next member recovered
      unfold recoverContractMemberAux at recovered
      split at recovered
      · exact finishRecoveredMember_success_hasDiagnostic first last recovered
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            exact finishRecoveredMember_success_hasDiagnostic first last recovered
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- Every successful public contract-member recovery retains a diagnostic. -/
theorem recoverContractMember_success_hasDiagnostic
    {input next : State} {member : ContractMember}
    (recovered : recoverContractMember input = .ok member next) :
    next.diagnosticsRev ≠ [] := by
  unfold recoverContractMember at recovered
  cases advanced : input.advance? with
  | none =>
      simp [advanced, rejectAt] at recovered
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at recovered
      exact recoverContractMemberAux_success_hasDiagnostic token.span token.span
        (afterToken.remainingCount + 1) recovered

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractRecoveryProperties
/-! Contracts for canonical contract-member error recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

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

abbrev RecoveredContractMemberValid :=
  ContractMember.ValidFor CoreStatement.ValidFor
    (Expr.ValidFor CoreStatement.ValidFor)

theorem finishRecoveredMember_validFor
    (first last : SourceSpan) (state : State)
    (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredMember first last state).ValidFor state
      RecoveredContractMemberValid := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredMember Reply.ValidFor
  exact ⟨.error spanValid (by simp),
    stateValid.emit_validFor _ spanValid, rfl⟩

theorem recoverContractMemberAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverContractMemberAux first last fuel state).ValidFor state
        RecoveredContractMemberValid := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverContractMemberAux
      split
      · exact finishRecoveredMember_validFor first last state stateValid
          firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredMember_validFor first last state stateValid
              firstValid lastValid ordered
        | some pair =>
            rcases pair with ⟨token, next⟩
            have shape := advance?_state_shape advanced
            have nextValid := stateValid.advance?_validFor advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                currentFound lastBefore
            exact (inductionHypothesis token.span next state.cursor token
              nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl
              (by simp [shape.2])).of_file_eq (by simp [shape.2])

theorem recoverContractMember_validFor :
    Parser.ValidFor recoverContractMember RecoveredContractMemberValid := by
  intro input inputValid
  unfold recoverContractMember
  cases advanced : input.advance? with
  | none =>
      unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      have shape := advance?_state_shape advanced
      have nextValid := inputValid.advance?_validFor advanced
      have tokenValid := inputValid.peek?_span_validFor shape.1
      have currentFound := State.getElem?_eq_some_of_peek?_eq_some shape.1
      exact (recoverContractMemberAux_validFor token.span
        (next.remainingCount + 1) token.span next input.cursor token nextValid
        (by simpa [shape.2] using tokenValid)
        (by simpa [shape.2] using tokenValid) tokenValid.2.1
        (by simpa [shape.2] using currentFound) rfl
        (by simp [shape.2])).of_file_eq (by simp [shape.2])

theorem finishRecoveredMember_preservesTokenWindow
    (first last : SourceSpan) :
    Parser.PreservesTokenWindow (finishRecoveredMember first last) := by
  intro input
  unfold finishRecoveredMember Reply.PreservesTokenWindow State.emit
  exact ⟨rfl, rfl⟩

theorem recoverContractMemberAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow
      (recoverContractMemberAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverContractMemberAux
      split
      · exact finishRecoveredMember_preservesTokenWindow first last input
      · cases advanced : input.advance? with
        | none =>
            exact finishRecoveredMember_preservesTokenWindow first last input
        | some pair =>
            rcases pair with ⟨token, next⟩
            exact (inductionHypothesis token.span next).trans (by
              simp [(advance?_state_shape advanced).2])

theorem recoverContractMemberAux_preservesTokensOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokensOnSuccess
      (recoverContractMemberAux first last fuel) :=
  (recoverContractMemberAux_preservesTokenWindow first last fuel).preservesTokensOnSuccess

theorem recoverContractMemberAux_ok_state_shape (first last : SourceSpan) :
    ∀ fuel, ∀ {input final : State} {member : ContractMember},
      recoverContractMemberAux first last fuel input = .ok member final →
      input.cursor ≤ final.cursor ∧
        first.startByte = member.span.startByte := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverContractMemberAux]
  | succ fuel inductionHypothesis =>
      intro input final member parsed
      unfold recoverContractMemberAux at parsed
      split at parsed
      · unfold finishRecoveredMember at parsed
        cases parsed
        exact ⟨Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredMember at parsed
            cases parsed
            exact ⟨Nat.le_refl _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at parsed
            have recursive := inductionHypothesis token.span parsed
            exact ⟨Nat.le_trans (by
              simp [(advance?_state_shape advanced).2]) recursive.1,
              recursive.2⟩

theorem recoverContractMemberAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess
      (recoverContractMemberAux first last fuel) :=
  fun _ _ _ parsed =>
    (recoverContractMemberAux_ok_state_shape first last fuel parsed).1

theorem recoverContractMember_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverContractMember := by
  intro input
  unfold recoverContractMember
  cases advanced : input.advance? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some pair =>
      rcases pair with ⟨token, next⟩
      exact (recoverContractMemberAux_preservesTokenWindow token.span token.span
        (next.remainingCount + 1) next).trans (by
          simp [(advance?_state_shape advanced).2])

theorem recoverContractMember_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess recoverContractMember :=
  recoverContractMember_preservesTokenWindow.preservesTokensOnSuccess

theorem recoverContractMember_ok_state_shape
    {input final : State} {member : ContractMember}
    (parsed : recoverContractMember input = .ok member final) :
    input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = member.span.startByte := by
  unfold recoverContractMember at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      have recovered := recoverContractMemberAux_ok_state_shape token.span
        token.span (next.remainingCount + 1) parsed
      exact ⟨Nat.le_trans (by simp [(advance?_state_shape advanced).2])
        recovered.1, token, (advance?_state_shape advanced).1, recovered.2⟩

theorem recoverContractMember_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : recoverContractMember input = .ok member final) :
    input.cursor < final.cursor := by
  unfold recoverContractMember at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      exact Nat.lt_of_lt_of_le (by simp [(advance?_state_shape advanced).2])
        (recoverContractMemberAux_ok_state_shape token.span token.span
          (next.remainingCount + 1) parsed).1

theorem recoverContractMember_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess recoverContractMember :=
  fun _ _ _ parsed =>
    Nat.le_of_lt (recoverContractMember_cursor_lt_onSuccess parsed)

theorem recoverContractMember_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess recoverContractMember (·.span) :=
  fun _ _ _ parsed => (recoverContractMember_ok_state_shape parsed).2

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodyProperties
/-! Contracts for canonical contract-body accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

namespace ContractBody

def ValidFor (file : SourceFile) (body : ContractBody) : Prop :=
  body.span.ValidFor file ∧
    List.ValidFor CanonicalContractMemberValid file body.members

end ContractBody

private theorem rewindAfterMemberReject_validFor {input failedState : State}
    (inputValid : input.ValidFor) (failedValid : failedState.ValidFor)
    (windowEq : failedState.window = input.window) :
    ({ failedState with cursor := input.cursor } : State).ValidFor := {
  tokens := failedValid.tokens
  cursor_le_endIndex := by simpa [windowEq] using inputValid.cursor_le_endIndex
  endIndex_le_size := failedValid.endIndex_le_size
  endByte_le_source := failedValid.endByte_le_source
  endByte_boundary := failedValid.endByte_boundary
  diagnosticsRev := failedValid.diagnosticsRev
}

theorem closeContractBody_validFor (opening : Token)
    (membersRev : List ContractMember) (input : State) (openingIndex : Nat)
    (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (membersValid : List.ValidFor CanonicalContractMemberValid
      input.file membersRev) :
    (closeContractBody opening membersRev input).ValidFor input
      ContractBody.ValidFor := by
  unfold closeContractBody
  have closingReply := symbol_validFor .rightBrace .topItem input inputValid
  cases closingResult : symbol .rightBrace .topItem input with
  | invariant error => simp only [bind, closingResult]; trivial
  | reject failure rejected =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult]
      exact closingReply
  | ok closing next =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult, pure, Reply.ValidFor]
      have closingShape := symbol_ok_state_shape .rightBrace .topItem closingResult
      have closingAt := State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingValid :=
        inputValid.token_span_validFor_of_getElem?_eq_some openingFound
      have closingValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using closingReply.1
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        openingFound closingAt openingBefore
      have bodyValid := SourceSpan.cover_validFor openingValid closingValid
        (Nat.le_trans openingValid.2.1
          (Nat.le_trans separated closingValid.2.1))
      refine ⟨⟨bodyValid, ?_⟩, closingReply.2.1, closingReply.2.2⟩
      intro member memberOf
      exact membersValid member (by simpa using memberOf)

theorem contractMembers_validFor (opening : Token) :
    ∀ fuel membersRev input openingIndex,
      input.ValidFor → input.tokens[openingIndex]? = some opening →
      openingIndex < input.cursor →
      List.ValidFor CanonicalContractMemberValid input.file membersRev →
      (contractMembers opening fuel membersRev input).ValidFor input
        ContractBody.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro membersRev input openingIndex inputValid openingFound openingBefore
        membersValid
      unfold contractMembers
      split
      · exact closeContractBody_validFor opening membersRev input openingIndex
          inputValid openingFound openingBefore membersValid
      · split
        · have closingReply := symbol_validFor .rightBrace .topItem input inputValid
          cases closingResult : symbol .rightBrace .topItem input with
          | invariant error => trivial
          | ok closing next => trivial
          | reject failure rejected =>
              rw [closingResult] at closingReply
              exact closingReply
        · have memberReply :=
            contractMemberWithAttribute_canonical_contract.validFor input inputValid
          have memberWindow :=
            contractMemberWithAttribute_canonical_contract.preservesTokenWindow input
          cases memberResult : contractMemberWithAttribute input with
          | invariant error => trivial
          | ok member next =>
              rw [memberResult] at memberReply memberWindow
              simp only
              split
              · have accumulated : List.ValidFor CanonicalContractMemberValid
                    next.file (member :: membersRev) := by
                  intro retained memberOf
                  rcases List.mem_cons.mp memberOf with rfl | prior
                  · simpa [memberReply.2.2] using memberReply.1
                  · simpa [memberReply.2.2] using membersValid retained prior
                have openingFoundNext : next.tokens[openingIndex]? = some opening := by
                  simpa [memberWindow.1] using openingFound
                exact (inductionHypothesis (member :: membersRev) next
                  openingIndex memberReply.2.1 openingFoundNext
                  (Nat.lt_trans openingBefore (by omega)) accumulated).of_file_eq
                    memberReply.2.2
              · trivial
          | reject failure failedState =>
              rw [memberResult] at memberReply memberWindow
              dsimp only
              let rewound : State := { failedState with cursor := input.cursor }
              have rewoundValid := rewindAfterMemberReject_validFor inputValid
                memberReply.2.1 memberWindow.2
              have rewoundFile : rewound.file = input.file := by
                simpa [rewound] using memberReply.2.2
              split
              · exact ⟨by simpa [rewound, memberReply.2.2] using memberReply.1,
                  rewoundValid, rewoundFile⟩
              · have recoveryReply := recoverContractMember_validFor
                  rewound rewoundValid
                cases recoveryResult : recoverContractMember rewound with
                | invariant error => trivial
                | reject recoveryFailure rejected =>
                    rw [recoveryResult] at recoveryReply
                    exact recoveryReply.of_file_eq rewoundFile
                | ok member next =>
                    rw [recoveryResult] at recoveryReply
                    have openingFoundNext : next.tokens[openingIndex]? =
                        some opening := by
                      simpa [recoverContractMember_preservesTokensOnSuccess
                        rewound member next recoveryResult, rewound,
                        memberWindow.1]
                        using openingFound
                    have accumulated : List.ValidFor
                        CanonicalContractMemberValid next.file
                        (member :: membersRev) := by
                      intro retained memberOf
                      rcases List.mem_cons.mp memberOf with rfl | prior
                      · simpa [recoveryReply.2.2] using recoveryReply.1
                      · simpa [recoveryReply.2.2, rewoundFile] using
                          membersValid retained prior
                    have progress : input.cursor < next.cursor := by
                      simpa [rewound] using
                        recoverContractMember_cursor_lt_onSuccess recoveryResult
                    exact (inductionHypothesis (member :: membersRev) next
                      openingIndex recoveryReply.2.1 openingFoundNext
                      (Nat.lt_trans openingBefore progress) accumulated
                        ).of_file_eq (recoveryReply.2.2.trans rewoundFile)

theorem contractBody_validFor : contractBody.ValidFor ContractBody.ValidFor := by
  intro input inputValid
  unfold contractBody
  have openingReply := symbol_validFor .leftBrace .topItem input inputValid
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected => rw [openingResult] at openingReply; exact openingReply
  | ok opening next =>
      rw [openingResult] at openingReply
      have shape := symbol_ok_state_shape .leftBrace .topItem openingResult
      have openingAt := State.getElem?_eq_some_of_peek?_eq_some shape.1
      exact (contractMembers_validFor opening (next.remainingCount + 1) [] next
        input.cursor openingReply.2.1 (by simpa [shape.2] using openingAt)
        (by simp [shape.2]) (by simp [List.ValidFor])).of_file_eq
          openingReply.2.2

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractDeclarationProperties
/-! Conditional contracts for the outer canonical contract declaration. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- The body-parser boundary required by the outer declaration proof. -/
structure ContractBodyParserInputs : Prop where
  validFor : contractBody.ValidFor ContractBody.ValidFor
  preservesTokenWindow : Parser.PreservesTokenWindow contractBody
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess contractBody
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractBody (·.span)

/-- The complete outer declaration contract produced from a body boundary. -/
structure ContractDeclParserContract : Prop where
  validFor : contractDecl.ValidFor
    (ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor)
  preservesTokenWindow : Parser.PreservesTokenWindow contractDecl
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess contractDecl
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractDecl (·.span)
  cursorLtOnSuccess : ∀ {input final : State} {declaration : ContractDecl},
    contractDecl input = .ok declaration final → input.cursor < final.cursor

theorem ContractDeclParserContract.preservesTokensOnSuccess
    (contract : ContractDeclParserContract) :
    Parser.PreservesTokensOnSuccess contractDecl :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

/-- The outer contract declaration composes entirely from its body boundary. -/
theorem contractDecl_contract (bodyInputs : ContractBodyParserInputs) :
    ContractDeclParserContract := {
  validFor := by
    have weak : contractDecl.ValidFor (fun _ _ => True) := by
      unfold contractDecl
      apply Parser.bind_validFor (keyword_validFor .contractKw .topItem)
      intro marker
      apply Parser.bind_validFor (identifier_validFor .topItem)
      intro name
      apply Parser.bind_validFor optionalGenericParameters_validFor
      intro genericParameters
      apply Parser.bind_validFor bodyInputs.validFor
      intro body
      exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
    intro input inputValid
    have weakResult := weak input inputValid
    cases parsed : contractDecl input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [parsed] at weakResult
        exact weakResult
    | ok declaration final =>
        rw [parsed] at weakResult
        have stages := parsed
        unfold contractDecl at stages
        rcases contractBind_ok_components stages with
          ⟨marker, afterMarker, markerResult, rest⟩
        rcases contractBind_ok_components rest with
          ⟨name, afterName, nameResult, rest⟩
        rcases contractBind_ok_components rest with
          ⟨parameters, afterParameters, parametersResult, rest⟩
        rcases contractBind_ok_components rest with
          ⟨body, afterBody, bodyResult, finished⟩
        have markerReply := keyword_validFor .contractKw .topItem input inputValid
        rw [markerResult] at markerReply
        have nameReply := identifier_validFor .topItem afterMarker markerReply.2.1
        rw [nameResult] at nameReply
        have parametersReply := optionalGenericParameters_validFor afterName
          nameReply.2.1
        rw [parametersResult] at parametersReply
        have bodyReply := bodyInputs.validFor afterParameters
          parametersReply.2.1
        rw [bodyResult] at bodyReply
        have markerValid : marker.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using markerReply.1
        have nameValid : name.span.ValidFor input.file := by
          simpa only [Located.ValidFor, markerReply.2.2] using nameReply.1
        have parametersValid : Option.ValidFor
            (NonemptyDelimitedList.ValidFor Located.ValidFor) input.file
            parameters := by
          simpa [nameReply.2.2, markerReply.2.2] using parametersReply.1
        have bodyValid : ContractBody.ValidFor input.file body := by
          simpa [parametersReply.2.2, nameReply.2.2, markerReply.2.2] using
            bodyReply.1
        have markerShape := acceptToken_ok_state_shape (.keyword .contractKw)
          .topItem (· == .keyword .contractKw) markerResult
        have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerShape.1
        rcases bodyInputs.startsAtCurrentTokenOnSuccess
            afterParameters body afterBody bodyResult with
          ⟨opening, openingFound, bodyStart⟩
        have openingAtAfter :=
          State.getElem?_eq_some_of_peek?_eq_some openingFound
        have openingAt : input.tokens[afterParameters.cursor]? = some opening := by
          simpa [optionalGenericParameters_preservesTokensOnSuccess afterName
              parameters afterParameters parametersResult,
            identifier_preservesTokensOnSuccess .topItem afterMarker name
              afterName nameResult,
            keyword_preservesTokensOnSuccess .contractKw .topItem input marker
              afterMarker markerResult] using openingAtAfter
        have progress : input.cursor < afterParameters.cursor :=
          Nat.lt_of_lt_of_le (acceptToken_cursor_lt_onSuccess
            (.keyword .contractKw) .topItem (· == .keyword .contractKw)
            markerResult)
            (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem
              afterMarker name afterName nameResult)
              (optionalGenericParameters_cursorMonotoneOnSuccess afterName
                parameters afterParameters parametersResult))
        have separated := inputValid.token_end_le_token_start_of_getElem?_lt
          markerAt openingAt progress
        have ordered : marker.span.startByte ≤ body.span.endByte := by
          exact Nat.le_trans markerValid.2.1 (Nat.le_trans separated (by
            rw [bodyStart]
            exact bodyValid.1.2.1))
        have outerValid := SourceSpan.cover_validFor markerValid bodyValid.1 ordered
        cases finished
        refine ⟨⟨outerValid, nameValid, ?_, ?_, bodyValid.1, bodyValid.2⟩,
          weakResult.2.1, weakResult.2.2⟩
        · cases parameters with
          | none => simp
          | some values => simpa [Option.ValidFor] using parametersValid.1
        · cases parameters with
          | none => simp
          | some values =>
              intro retained member parameter parameterMember
              have retainedEq : retained = values := by simpa using member.symm
              subst retained
              exact parametersValid.2 parameter parameterMember
  preservesTokenWindow := by
    unfold contractDecl
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .contractKw .topItem)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (identifier_preservesTokenWindow .topItem)
    intro name
    apply Parser.bind_preservesTokenWindow
      optionalGenericParameters_preservesTokenWindow
    intro parameters
    apply Parser.bind_preservesTokenWindow bodyInputs.preservesTokenWindow
    intro body
    exact Parser.pure_preservesTokenWindow _
  cursorMonotoneOnSuccess := by
    intro input declaration final parsed
    have stages := parsed
    unfold contractDecl at stages
    rcases contractBind_ok_components stages with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨name, afterName, nameResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact Nat.le_trans (keyword_cursorMonotoneOnSuccess .contractKw .topItem
      input marker afterMarker markerResult)
      (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem afterMarker
        name afterName nameResult)
        (Nat.le_trans (optionalGenericParameters_cursorMonotoneOnSuccess
          afterName parameters afterParameters parametersResult)
          (bodyInputs.cursorMonotoneOnSuccess afterParameters body final
            bodyResult)))
  startsAtCurrentTokenOnSuccess := by
    unfold contractDecl
    apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
      (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .contractKw)
        .topItem (· == .keyword .contractKw))
    intro marker input declaration final parsed
    rcases contractBind_ok_components parsed with
      ⟨name, afterName, nameResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    rfl
  cursorLtOnSuccess := by
    intro input final declaration parsed
    have stages := parsed
    unfold contractDecl at stages
    rcases contractBind_ok_components stages with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨name, afterName, nameResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact Nat.lt_of_lt_of_le (acceptToken_cursor_lt_onSuccess
      (.keyword .contractKw) .topItem (· == .keyword .contractKw) markerResult)
      (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem afterMarker
        name afterName nameResult)
        (Nat.le_trans (optionalGenericParameters_cursorMonotoneOnSuccess
          afterName parameters afterParameters parametersResult)
          (bodyInputs.cursorMonotoneOnSuccess afterParameters body final
            bodyResult)))
}

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodyStateProperties
/-! Token-window and cursor contracts for canonical contract bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

theorem closeContractBody_preservesTokenWindow (opening : Token)
    (membersRev : List ContractMember) :
    Parser.PreservesTokenWindow (closeContractBody opening membersRev) := by
  unfold closeContractBody
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .topItem)
  intro closing
  exact Parser.pure_preservesTokenWindow _

theorem contractMembers_preservesTokenWindow (opening : Token) :
    ∀ fuel membersRev,
      Parser.PreservesTokenWindow (contractMembers opening fuel membersRev) := by
  intro fuel
  induction fuel with
  | zero => intros membersRev input; trivial
  | succ fuel inductionHypothesis =>
      intro membersRev input
      unfold contractMembers
      split
      · exact closeContractBody_preservesTokenWindow opening membersRev input
      · split
        · have shape := symbol_preservesTokenWindow .rightBrace .topItem input
          cases result : symbol .rightBrace .topItem input with
          | invariant error => trivial
          | ok closing next => trivial
          | reject failure rejected => rw [result] at shape; exact shape
        · have memberShape :=
            contractMemberWithAttribute_canonical_contract.preservesTokenWindow input
          cases memberResult : contractMemberWithAttribute input with
          | invariant error => trivial
          | ok member next =>
              rw [memberResult] at memberShape
              simp only
              split
              · exact (inductionHypothesis (member :: membersRev) next).trans
                  memberShape
              · trivial
          | reject failure failedState =>
              rw [memberResult] at memberShape
              dsimp only
              let rewound : State := { failedState with cursor := input.cursor }
              have rewoundShape : rewound.tokens = input.tokens ∧
                  rewound.window = input.window := by
                simpa [rewound, Reply.PreservesTokenWindow] using memberShape
              split
              · exact rewoundShape
              · have recoveryShape :=
                  recoverContractMember_preservesTokenWindow rewound
                cases recoveryResult : recoverContractMember rewound with
                | invariant error => trivial
                | reject failure rejected =>
                    rw [recoveryResult] at recoveryShape
                    exact recoveryShape.trans rewoundShape
                | ok member next =>
                    rw [recoveryResult] at recoveryShape
                    exact (inductionHypothesis (member :: membersRev) next).trans
                      (recoveryShape.trans rewoundShape)

theorem contractMembers_ok_state_shape (opening : Token) :
    ∀ fuel membersRev {input final : State} {body : ContractBody},
      contractMembers opening fuel membersRev input = .ok body final →
      input.cursor ≤ final.cursor ∧
        body.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro membersRev input final body parsed
      unfold contractMembers at parsed
      split at parsed
      · unfold closeContractBody at parsed
        cases closingResult : symbol .rightBrace .topItem input with
        | invariant error =>
            simp only [bind, closingResult] at parsed
            contradiction
        | reject failure rejected =>
            simp only [bind, closingResult] at parsed
            contradiction
        | ok closing next =>
            have monotone := symbol_cursorMonotoneOnSuccess .rightBrace .topItem
              input closing next closingResult
            simp only [bind, closingResult, pure] at parsed
            cases parsed
            exact ⟨monotone, rfl⟩
      · split at parsed
        · cases closingResult : symbol .rightBrace .topItem input <;>
            simp [closingResult] at parsed
        · cases memberResult : contractMemberWithAttribute input with
          | invariant error => simp [memberResult] at parsed
          | ok member next =>
              simp only [memberResult] at parsed
              split at parsed
              · have recursive := inductionHypothesis (member :: membersRev) parsed
                exact ⟨Nat.le_trans (Nat.le_of_lt (by assumption)) recursive.1,
                  recursive.2⟩
              · contradiction
          | reject failure failedState =>
              simp only [memberResult] at parsed
              let rewound : State := { failedState with cursor := input.cursor }
              change (if atContractRecoveryBoundary input then
                  .reject failure rewound
                else match recoverContractMember rewound with
                  | .ok member next =>
                      contractMembers opening fuel (member :: membersRev) next
                  | .reject recoveryFailure next => .reject recoveryFailure next
                  | .invariant error => .invariant error) = .ok body final at parsed
              split at parsed
              · contradiction
              · cases recoveryResult : recoverContractMember rewound with
                | invariant error => simp [recoveryResult] at parsed
                | reject failure rejected => simp [recoveryResult] at parsed
                | ok member next =>
                    simp only [recoveryResult] at parsed
                    have recursive := inductionHypothesis (member :: membersRev) parsed
                    have progress : input.cursor < next.cursor := by
                      simpa [rewound] using
                        recoverContractMember_cursor_lt_onSuccess recoveryResult
                    exact ⟨Nat.le_trans (Nat.le_of_lt progress) recursive.1,
                      recursive.2⟩

theorem contractBody_preservesTokenWindow :
    Parser.PreservesTokenWindow contractBody := by
  intro input
  unfold contractBody
  have openingShape := symbol_preservesTokenWindow .leftBrace .topItem input
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected => rw [openingResult] at openingShape; exact openingShape
  | ok opening next =>
      rw [openingResult] at openingShape
      exact (contractMembers_preservesTokenWindow opening
        (next.remainingCount + 1) [] next).trans openingShape

theorem contractBody_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess contractBody :=
  contractBody_preservesTokenWindow.preservesTokensOnSuccess

theorem contractBody_ok_state_shape {input final : State} {body : ContractBody}
    (parsed : contractBody input = .ok body final) :
    input.cursor < final.cursor ∧
      ∃ opening, input.peek? = some opening ∧
        opening.span.startByte = body.span.startByte := by
  unfold contractBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening next =>
      simp only [openingResult] at parsed
      have shape := symbol_ok_state_shape .leftBrace .topItem openingResult
      have bodyShape := contractMembers_ok_state_shape opening
        (next.remainingCount + 1) [] parsed
      exact ⟨Nat.lt_of_lt_of_le (by simp [shape.2]) bodyShape.1,
        opening, shape.1, bodyShape.2.symm⟩

theorem contractBody_cursor_lt_onSuccess {input final : State}
    {body : ContractBody} (parsed : contractBody input = .ok body final) :
    input.cursor < final.cursor := (contractBody_ok_state_shape parsed).1

theorem contractBody_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess contractBody :=
  fun _ _ _ parsed => Nat.le_of_lt (contractBody_cursor_lt_onSuccess parsed)

theorem contractBody_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractBody (·.span) :=
  fun _ _ _ parsed => (contractBody_ok_state_shape parsed).2

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractCanonicalProperties
/-! Unconditional canonical contracts for complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The completed body proofs discharge every conditional outer input. -/
theorem contractBody_canonical_inputs :
    ContractInternals.ContractBodyParserInputs := {
  validFor := ContractInternals.contractBody_validFor
  preservesTokenWindow := ContractInternals.contractBody_preservesTokenWindow
  cursorMonotoneOnSuccess :=
    ContractInternals.contractBody_cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    ContractInternals.contractBody_startsAtCurrentTokenOnSuccess
}

/-- Complete contract declarations satisfy the full canonical parser contract. -/
theorem contractDecl_canonical_contract :
    ContractInternals.ContractDeclParserContract :=
  ContractInternals.contractDecl_contract contractBody_canonical_inputs

theorem contractDecl_canonical_validFor :
    contractDecl.ValidFor
      (ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor) :=
  contractDecl_canonical_contract.validFor

theorem contractDecl_canonical_preservesTokenWindow :
    Parser.PreservesTokenWindow contractDecl :=
  contractDecl_canonical_contract.preservesTokenWindow

theorem contractDecl_canonical_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess contractDecl :=
  contractDecl_canonical_contract.preservesTokensOnSuccess

theorem contractDecl_canonical_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess contractDecl :=
  contractDecl_canonical_contract.cursorMonotoneOnSuccess

theorem contractDecl_canonical_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractDecl (·.span) :=
  contractDecl_canonical_contract.startsAtCurrentTokenOnSuccess

theorem contractDecl_canonical_cursor_lt_onSuccess
    {input final : State} {declaration : ContractDecl}
    (parsed : contractDecl input = .ok declaration final) :
    input.cursor < final.cursor :=
  contractDecl_canonical_contract.cursorLtOnSuccess parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberRecoveryBoundaryProperties
/-! Executable-to-declarative boundary bridges for contract-member recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem symbolPresent_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .topItem result).1⟩

private theorem keywordPresent_of_isKeyword_eq_true (value : HardKeyword)
    {input : State} (present : isKeyword input value = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .topItem result).1⟩

private theorem enumPresent_of_isContextual_eq_true {input : State}
    (present : isContextual input .enum = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder
        (.identifier ContextualKeyword.enum.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true .enum .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses .enum .topItem result).1⟩

private theorem isSymbol_eq_true_of_present (value : Symbol)
    {input : State}
    (present : DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.symbol value)) :
    isSymbol input value = true := by
  rcases present with ⟨span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := .symbol value } at token
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem isKeyword_eq_true_of_present (value : HardKeyword)
    {input : State}
    (present : DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.keyword value)) :
    isKeyword input value = true := by
  rcases present with ⟨span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := .keyword value } at token
  unfold isKeyword State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  change instBEqTokenKind.beq (.keyword value) (.keyword value) = true
  simp only [instBEqTokenKind.beq]
  change instBEqHardKeyword.beq value value = true
  unfold instBEqHardKeyword.beq
  cases value <;> rfl

private theorem isEnum_eq_true_of_present {input : State}
    (present : DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder
        (.identifier ContextualKeyword.enum.spelling)) :
    isContextual input .enum = true := by
  rcases present with ⟨span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor {
      span
      value := .identifier ContextualKeyword.enum.spelling
    } at token
  unfold isContextual State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some,
    TokenKind.isContextual]
  exact beq_iff_eq.mpr rfl

/-- A true executable boundary guard exposes one exact declarative boundary. -/
theorem recoveryBoundaryStartsAt_of_atContractRecoveryBoundary_eq_true
    {input : State} (present : atContractRecoveryBoundary input = true) :
    DeclarativeGrammar.ContractMemberRecoveryBoundaryStartsAt
      input.declarativeRemainder := by
  unfold atContractRecoveryBoundary at present
  by_cases hash : isSymbol input .hash = true
  · exact .hash (symbolPresent_of_isSymbol_eq_true .hash hash)
  · have hashFalse : isSymbol input .hash = false := Bool.eq_false_iff.mpr hash
    by_cases function : isKeyword input .functionKw = true
    · exact .function
        (keywordPresent_of_isKeyword_eq_true .functionKw function)
    · have functionFalse : isKeyword input .functionKw = false :=
        Bool.eq_false_iff.mpr function
      by_cases constructor : isKeyword input .constructorKw = true
      · exact .constructor
          (keywordPresent_of_isKeyword_eq_true .constructorKw constructor)
      · have constructorFalse : isKeyword input .constructorKw = false :=
          Bool.eq_false_iff.mpr constructor
        by_cases fallback : isKeyword input .fallbackKw = true
        · exact .fallback
            (keywordPresent_of_isKeyword_eq_true .fallbackKw fallback)
        · have fallbackFalse : isKeyword input .fallbackKw = false :=
            Bool.eq_false_iff.mpr fallback
          by_cases typeAlias : isKeyword input .typeKw = true
          · exact .typeAlias
              (keywordPresent_of_isKeyword_eq_true .typeKw typeAlias)
          · have typeFalse : isKeyword input .typeKw = false :=
              Bool.eq_false_iff.mpr typeAlias
            by_cases closing : isSymbol input .rightBrace = true
            · exact .rightBrace
                (symbolPresent_of_isSymbol_eq_true .rightBrace closing)
            · have closingFalse : isSymbol input .rightBrace = false :=
                Bool.eq_false_iff.mpr closing
              have enum : isContextual input .enum = true := by
                simpa [hashFalse, functionFalse, constructorFalse,
                  fallbackFalse, typeFalse, closingFalse] using present
              exact .enum (enumPresent_of_isContextual_eq_true enum)

/-- Every exact declarative boundary makes the executable guard true. -/
theorem atContractRecoveryBoundary_eq_true_of_recoveryBoundaryStartsAt
    {input : State}
    (starts : DeclarativeGrammar.ContractMemberRecoveryBoundaryStartsAt
      input.declarativeRemainder) :
    atContractRecoveryBoundary input = true := by
  cases starts with
  | hash present =>
      simp [atContractRecoveryBoundary,
        isSymbol_eq_true_of_present .hash present]
  | function present =>
      simp [atContractRecoveryBoundary,
        isKeyword_eq_true_of_present .functionKw present]
  | constructor present =>
      simp [atContractRecoveryBoundary,
        isKeyword_eq_true_of_present .constructorKw present]
  | fallback present =>
      simp [atContractRecoveryBoundary,
        isKeyword_eq_true_of_present .fallbackKw present]
  | typeAlias present =>
      simp [atContractRecoveryBoundary,
        isKeyword_eq_true_of_present .typeKw present]
  | rightBrace present =>
      simp [atContractRecoveryBoundary,
        isSymbol_eq_true_of_present .rightBrace present]
  | enum present =>
      simp [atContractRecoveryBoundary, isEnum_eq_true_of_present present]

/-- A true auxiliary guard gives an exact nonconsuming recovery stop. -/
theorem contractMemberRecoveryStops_of_guard_eq_true (input : State)
    (stops : (input.atEnd || atContractRecoveryBoundary input) = true) :
    DeclarativeGrammar.ContractMemberRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have boundary : atContractRecoveryBoundary input = true := by
      simpa [atEndFalse] using stops
    exact .boundary
      (recoveryBoundaryStartsAt_of_atContractRecoveryBoundary_eq_true
        boundary)

/-- Under a false auxiliary guard, failed advancement is an exact missing
carrier slot inside the active window. -/
theorem contractMemberRecoveryStops_of_advance?_eq_none (input : State)
    (guard : (input.atEnd || atContractRecoveryBoundary input) = false)
    (advanced : input.advance? = none) :
    DeclarativeGrammar.ContractMemberRecoveryStops
      input.declarativeRemainder := by
  have notAtEnd : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    have atEndTrue : input.atEnd = true := by
      unfold State.atEnd
      exact decide_eq_true atEnd
    simp [atEndTrue] at guard
  have inside : input.cursor < input.window.endIndex := by omega
  apply DeclarativeGrammar.ContractMemberRecoveryStops.missingToken inside
  unfold State.advance? State.peek? at advanced
  simpa [State.declarativeRemainder, inside] using advanced

/-- A current token under a false auxiliary guard excludes every exact stop. -/
theorem no_contractMemberRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (guard : (input.atEnd || atContractRecoveryBoundary input) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.ContractMemberRecoveryStops
      input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | boundary starts =>
      have boundary :=
        atContractRecoveryBoundary_eq_true_of_recoveryBoundaryStartsAt starts
      simp [boundary] at guard
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractFieldInitializerOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for optional contract-field initializers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- Every successful optional initializer preserves the exact `=` lookahead
priority and the supplied expression success relation. -/
theorem optionalFieldInitializer_success_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {initializer : Option Expr}
    (result : optionalFieldInitializer expression input =
      .ok initializer output) :
    DeclarativeGrammar.OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input.declarativeRemainder initializer
        output.declarativeRemainder := by
  unfold optionalFieldInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal
  · rcases Solcore.Syntax.Parser.symbol_eq_ok_of_isSymbol_eq_true
      .equal .contractMember present
      with ⟨equal, equalResult⟩
    simp only [present, if_true, equalResult] at result
    cases expressionResult : expression
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [expressionResult] at result
    | reject failure rejected => simp [expressionResult] at result
    | ok value afterValue =>
        simp only [expressionResult, pure] at result
        cases result
        exact .present equal.span
          (symbol_success_exactTokenParses .equal .contractMember equalResult)
          (expressionSuccessSound expressionResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .equal absent)

/-- Every optional-initializer rejection follows a present exact `=` and the
supplied expression rejection; the absent branch cannot reject. -/
theorem optionalFieldInitializer_reject_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalFieldInitializer expression input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalContractFieldInitializerRejects
      expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalFieldInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal
  · rcases Solcore.Syntax.Parser.symbol_eq_ok_of_isSymbol_eq_true
      .equal .contractMember present
      with ⟨equal, equalResult⟩
    simp only [present, if_true, equalResult] at result
    cases expressionResult : expression
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [expressionResult] at result
    | ok value afterValue => simp [expressionResult, pure] at result
    | reject expressionFailure expressionRejected =>
        simp only [expressionResult] at result
        cases result
        exact .expressionRejected equal.span
          (symbol_success_exactTokenParses .equal .contractMember equalResult)
          (expressionRejectSound expressionResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package exact executable optional-initializer success and rejection. -/
theorem optionalFieldInitializer_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {initializer : Option Expr},
      optionalFieldInitializer expression input = .ok initializer output →
        DeclarativeGrammar.OptionalContractFieldInitializerOrdinaryParses
          expressionOrdinary input.declarativeRemainder initializer
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalFieldInitializer expression input = .reject failure rejected →
        DeclarativeGrammar.OptionalContractFieldInitializerRejects
          expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨optionalFieldInitializer_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound,
    optionalFieldInitializer_reject_ordinaryOutcome_sound expression
      expressionRejects expressionRejectSound⟩

/-- Re-export the parameterized deterministic optional-initializer contract. -/
theorem optionalFieldInitializer_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalContractFieldInitializerOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.OptionalContractFieldInitializerRejects
        expressionRejects) :=
  DeclarativeGrammar.optionalContractFieldInitializerDeterministicOutcomeSpec
    expressionOutcomes

/-- Re-export exact optional-initializer outcomes from an exact expression
contract. -/
theorem optionalFieldInitializer_exactOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalContractFieldInitializerOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.OptionalContractFieldInitializerRejects
        expressionRejects) :=
  DeclarativeGrammar.optionalContractFieldInitializerExactOutcomeSpec
    expressionOutcomes

/-- Under an exact expression contract, two executable initializer successes
have the same value and declarative remainder. -/
theorem optionalFieldInitializer_success_result_unique
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input leftOutput rightOutput : State}
    {left right : Option Expr}
    (leftResult : optionalFieldInitializer expression input =
      .ok left leftOutput)
    (rightResult : optionalFieldInitializer expression input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (optionalFieldInitializer_exactOutcomeSpec expressionOutcomes)
    |>.successResultUnique
      (optionalFieldInitializer_success_ordinaryOutcome_sound expression
        expressionOrdinary expressionSuccessSound leftResult)
      (optionalFieldInitializer_success_ordinaryOutcome_sound expression
        expressionOrdinary expressionSuccessSound rightResult)

/-- Under an exact expression contract, two executable initializer
rejections have the same declarative endpoint. -/
theorem optionalFieldInitializer_reject_output_unique
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : optionalFieldInitializer expression input =
      .reject leftFailure leftOutput)
    (rightResult : optionalFieldInitializer expression input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (optionalFieldInitializer_exactOutcomeSpec expressionOutcomes)
    |>.rejectOutputUnique
      (optionalFieldInitializer_reject_ordinaryOutcome_sound expression
        expressionRejects expressionRejectSound leftResult)
      (optionalFieldInitializer_reject_ordinaryOutcome_sound expression
        expressionRejects expressionRejectSound rightResult)

end ContractInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractFieldOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection for contract storage fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- Every executable field rejection records the first rejecting stage and its
exact remainder. -/
theorem contractField_reject_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : contractField expression input = .reject failure rejected) :
    DeclarativeGrammar.ContractFieldRejects expressionOrdinary
      expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold contractField at result
  cases nameResult : identifier .contractMember input with
  | invariant error => simp [bind, nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [bind, nameResult] at result
      cases result
      exact .nameRejected (identifier_reject_sound .contractMember nameResult)
  | ok name afterName =>
      simp only [bind, nameResult] at result
      have nameParsed := identifier_success_sound .contractMember nameResult
      cases colonResult : symbol .colon .contractMember afterName with
      | invariant error => simp [colonResult] at result
      | reject colonFailure colonRejected =>
          have colonRejectedEq := symbol_reject_state_eq .colon
            .contractMember colonResult
          subst colonRejected
          simp only [colonResult] at result
          cases result
          exact .colonMissing nameParsed
            (symbol_reject_tokenKindAbsentAt .colon .contractMember
              colonResult)
      | ok colon afterColon =>
          simp only [colonResult] at result
          have colonParsed := symbol_success_exactTokenParses .colon
            .contractMember colonResult
          cases typeResult : typeExpr afterColon with
          | invariant error => simp [typeResult] at result
          | reject typeFailure typeRejected =>
              simp only [typeResult] at result
              cases result
              exact .typeRejected colon.span nameParsed colonParsed
                (typeExpr_ordinaryOutcome_sound.2 typeResult)
          | ok type afterType =>
              simp only [typeResult] at result
              have typeParsed := typeExpr_ordinaryOutcome_sound.1 typeResult
              cases initializerResult : optionalFieldInitializer expression
                  afterType with
              | invariant error => simp [initializerResult] at result
              | reject initializerFailure initializerRejected =>
                  simp only [initializerResult] at result
                  cases result
                  exact .initializerRejected colon.span nameParsed colonParsed
                    typeParsed
                    (optionalFieldInitializer_reject_ordinaryOutcome_sound
                      expression expressionRejects expressionRejectSound
                        initializerResult)
              | ok initializer afterInitializer =>
                  simp only [initializerResult] at result
                  have initializerParsed :=
                    optionalFieldInitializer_success_ordinaryOutcome_sound
                      expression expressionOrdinary expressionSuccessSound
                        initializerResult
                  cases semicolonResult : symbol .semicolon .contractMember
                      afterInitializer with
                  | invariant error => simp [semicolonResult] at result
                  | ok semicolon output =>
                      simp [semicolonResult, pure] at result
                  | reject semicolonFailure semicolonRejected =>
                      have semicolonRejectedEq := symbol_reject_state_eq
                        .semicolon .contractMember semicolonResult
                      subst semicolonRejected
                      simp only [semicolonResult] at result
                      cases result
                      exact .semicolonMissing colon.span nameParsed colonParsed
                        typeParsed initializerParsed
                        (symbol_reject_tokenKindAbsentAt .semicolon
                          .contractMember semicolonResult)

end ContractInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractFieldOrdinarySuccessSoundnessProperties
/-! Executable ordinary success for contract storage fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components_variant {alpha beta : Type}
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

namespace ContractInternals

/-- Every executable field success records its exact name, colon, public Core
type, prioritized optional initializer, semicolon, AST, span, and remainder. -/
theorem contractField_success_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {field : ContractField}
    (result : contractField expression input = .ok field output) :
    DeclarativeGrammar.ContractFieldOrdinaryParses expressionOrdinary
      input.declarativeRemainder field output.declarativeRemainder := by
  unfold contractField at result
  rcases bind_ok_components_variant result with
    ⟨name, afterName, nameResult, colonStage⟩
  rcases bind_ok_components_variant colonStage with
    ⟨colon, afterColon, colonResult, typeStage⟩
  rcases bind_ok_components_variant typeStage with
    ⟨type, afterType, typeResult, initializerStage⟩
  rcases bind_ok_components_variant initializerStage with
    ⟨initializer, afterInitializer, initializerResult, semicolonStage⟩
  rcases bind_ok_components_variant semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed colon.span semicolon.span
    (identifier_success_sound .contractMember nameResult)
    (symbol_success_exactTokenParses .colon .contractMember colonResult)
    (typeExpr_ordinaryOutcome_sound.1 typeResult)
    (optionalFieldInitializer_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound initializerResult)
    (symbol_success_exactTokenParses .semicolon .contractMember
      semicolonResult)

end ContractInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberCoreOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for attribute-free contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

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

private theorem keywordPresentAt_of_isKeyword_eq_true
    (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .contractMember present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .contractMember result).1⟩

private theorem enumPresentAt_of_isContextual_eq_true {input : State}
    (present : isContextual input .enum = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder
        (.identifier ContextualKeyword.enum.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true .enum .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses .enum .topItem result).1⟩

/-- Every successful executable core member follows its exact broad ordinary
branch, including all positive and earlier-negative dispatch guards. -/
theorem contractMemberCore_success_ordinaryOutcome_sound
    {input output : State} {member : ContractMember}
    (result : contractMemberCore input = .ok member output) :
    DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      input.declarativeRemainder member output.declarativeRemainder := by
  unfold contractMemberCore contractMemberParser at result
  split at result
  next startsField =>
    unfold mapMember at result
    rcases bind_ok_components result with
      ⟨declaration, afterDeclaration, declarationResult, finished⟩
    cases finished
    exact .field
      (contractFieldStartsAt_of_startsContractField_eq_true startsField)
      (contractField_success_ordinaryOutcome_sound expression
        DeclarativeGrammar.CoreExpressionOrdinaryParses
        expression_success_ordinary_sound declarationResult)
  next fieldAbsent =>
    have fieldAbsentEq : startsContractField input = false :=
      Bool.eq_false_iff.mpr fieldAbsent
    have noField :=
      not_contractFieldStartsAt_of_startsContractField_eq_false fieldAbsentEq
    split at result
    next startsFunction =>
      unfold mapMember at result
      rcases bind_ok_components result with
        ⟨declaration, afterDeclaration, declarationResult, finished⟩
      cases finished
      exact .function noField
        (keywordPresentAt_of_isKeyword_eq_true .functionKw startsFunction)
        (functionDecl_success_ordinaryOutcome_sound .contract
          declarationResult)
    next functionAbsent =>
      have functionAbsentEq : isKeyword input .functionKw = false :=
        Bool.eq_false_iff.mpr functionAbsent
      have noFunction := keywordAbsentAt_of_isKeyword_eq_false .functionKw
        functionAbsentEq
      split at result
      next startsConstructor =>
        unfold mapMember at result
        rcases bind_ok_components result with
          ⟨declaration, afterDeclaration, declarationResult, finished⟩
        cases finished
        exact .constructor noField noFunction
          (keywordPresentAt_of_isKeyword_eq_true .constructorKw
            startsConstructor)
          (constructorDecl_success_ordinaryOutcome_sound declarationResult)
      next constructorAbsent =>
        have constructorAbsentEq : isKeyword input .constructorKw = false :=
          Bool.eq_false_iff.mpr constructorAbsent
        have noConstructor := keywordAbsentAt_of_isKeyword_eq_false
          .constructorKw constructorAbsentEq
        split at result
        next startsFallback =>
          unfold mapMember at result
          rcases bind_ok_components result with
            ⟨declaration, afterDeclaration, declarationResult, finished⟩
          cases finished
          exact .fallback noField noFunction noConstructor
            (keywordPresentAt_of_isKeyword_eq_true .fallbackKw startsFallback)
            (fallbackDecl_success_ordinaryOutcome_sound declarationResult)
        next fallbackAbsent =>
          have fallbackAbsentEq : isKeyword input .fallbackKw = false :=
            Bool.eq_false_iff.mpr fallbackAbsent
          have noFallback := keywordAbsentAt_of_isKeyword_eq_false .fallbackKw
            fallbackAbsentEq
          split at result
          next startsType =>
            unfold mapMember at result
            rcases bind_ok_components result with
              ⟨declaration, afterDeclaration, declarationResult, finished⟩
            cases finished
            exact .typeAlias noField noFunction noConstructor noFallback
              (keywordPresentAt_of_isKeyword_eq_true .typeKw startsType)
              (typeAlias_success_ordinaryOutcome_sound declarationResult)
          next typeAbsent =>
            have typeAbsentEq : isKeyword input .typeKw = false :=
              Bool.eq_false_iff.mpr typeAbsent
            have noType := keywordAbsentAt_of_isKeyword_eq_false .typeKw
              typeAbsentEq
            split at result
            next startsEnum =>
              unfold mapMember at result
              rcases bind_ok_components result with
                ⟨declaration, afterDeclaration, declarationResult, finished⟩
              cases finished
              exact .enum noField noFunction noConstructor noFallback noType
                (enumPresentAt_of_isContextual_eq_true startsEnum)
                (enumDecl_success_ordinaryOutcome_sound none declarationResult)
            next enumAbsent =>
              simp [rejectedContractMember, rejectAt] at result

end ContractInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractFieldOrdinaryOutcomeSoundnessProperties
/-! Complete executable ordinary outcomes for contract storage fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- Package executable contract-field success and exact rejection. -/
theorem contractField_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {field : ContractField},
      contractField expression input = .ok field output →
        DeclarativeGrammar.ContractFieldOrdinaryParses expressionOrdinary
          input.declarativeRemainder field output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractField expression input = .reject failure rejected →
        DeclarativeGrammar.ContractFieldRejects expressionOrdinary
          expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨contractField_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound,
    contractField_reject_ordinaryOutcome_sound expression expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic contract-field outcomes with the fixed public Core
type outcome. -/
theorem contractField_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ContractFieldOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ContractFieldRejects expressionOrdinary
        expressionRejects) :=
  DeclarativeGrammar.contractFieldDeterministicOutcomeSpec
    expressionOutcomes

/-- Re-export exact field outcomes from an exact initializer-expression
contract. -/
theorem contractField_exactOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.ContractFieldOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ContractFieldRejects expressionOrdinary
        expressionRejects) :=
  DeclarativeGrammar.contractFieldExactOutcomeSpec expressionOutcomes

/-- Under an exact expression contract, two executable field successes have
the same AST and declarative remainder. -/
theorem contractField_success_result_unique
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input leftOutput rightOutput : State}
    {left right : ContractField}
    (leftResult : contractField expression input = .ok left leftOutput)
    (rightResult : contractField expression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractField_exactOutcomeSpec expressionOutcomes).successResultUnique
    (contractField_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound leftResult)
    (contractField_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound rightResult)

/-- Under an exact expression contract, two executable field rejections have
the same declarative endpoint. -/
theorem contractField_reject_output_unique
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractField expression input =
      .reject leftFailure leftOutput)
    (rightResult : contractField expression input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractField_exactOutcomeSpec expressionOutcomes).rejectOutputUnique
    (contractField_reject_ordinaryOutcome_sound expression
      expressionOrdinary expressionRejects expressionSuccessSound
        expressionRejectSound leftResult)
    (contractField_reject_ordinaryOutcome_sound expression
      expressionOrdinary expressionRejects expressionSuccessSound
        expressionRejectSound rightResult)

end ContractInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberCoreOrdinaryRejectionSoundnessProperties
/-! Exact broad rejection reflection for attribute-free contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

private theorem mapMember_reject_result {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → ContractMember)
    {input rejected : State} {failure : Failure}
    (result : mapMember parser wrap input = .reject failure rejected) :
    parser input = .reject failure rejected := by
  unfold mapMember at result
  cases parserResult : parser input with
  | ok value output => simp [bind, parserResult, pure] at result
  | reject innerFailure innerRejected =>
      simp only [bind, parserResult] at result
      cases result
      rfl
  | invariant error => simp [bind, parserResult] at result

private theorem keywordPresent_of_isKeyword_eq_true_variant (value : HardKeyword)
    {input : State} (present : isKeyword input value = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .contractMember present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .contractMember parsed).1⟩

private theorem enumPresent_of_isContextual_eq_true_variant {input : State}
    (present : isContextual input .enum = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder
        (.identifier ContextualKeyword.enum.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true .enum .topItem present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses .enum .topItem parsed).1⟩

/-- Every executable core-member rejection records the selected committed
branch and that branch's exact final rejection remainder. -/
theorem contractMemberCore_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : contractMemberCore input = .reject failure rejected) :
    DeclarativeGrammar.ContractMemberCoreRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold contractMemberCore contractMemberParser at result
  split at result
  next startsField =>
    exact .fieldRejected
      (contractFieldStartsAt_of_startsContractField_eq_true startsField)
      (contractField_reject_ordinaryOutcome_sound expression
        DeclarativeGrammar.CoreExpressionOrdinaryParses
        DeclarativeGrammar.CoreExpressionPublicRejects
        expression_success_ordinary_sound expression_reject_ordinary_sound
        (mapMember_reject_result (contractField expression) wrapField result))
  next fieldAbsent =>
    have fieldAbsentEq : startsContractField input = false :=
      Bool.eq_false_iff.mpr fieldAbsent
    have fieldAbsentGrammar :=
      not_contractFieldStartsAt_of_startsContractField_eq_false fieldAbsentEq
    split at result
    next startsFunction =>
      exact .functionRejected fieldAbsentGrammar
        (keywordPresent_of_isKeyword_eq_true_variant .functionKw startsFunction)
        (functionDecl_reject_ordinaryOutcome_sound .contract
          (mapMember_reject_result (functionDecl .contract)
            wrapContractFunction result))
    next functionAbsent =>
      have functionAbsentEq : isKeyword input .functionKw = false :=
        Bool.eq_false_iff.mpr functionAbsent
      have functionAbsentGrammar :=
        keywordAbsentAt_of_isKeyword_eq_false .functionKw functionAbsentEq
      split at result
      next startsConstructor =>
        exact .constructorRejected fieldAbsentGrammar functionAbsentGrammar
          (keywordPresent_of_isKeyword_eq_true_variant .constructorKw
            startsConstructor)
          (constructorDecl_reject_ordinaryOutcome_sound
            (mapMember_reject_result constructorDecl wrapConstructor result))
      next constructorAbsent =>
        have constructorAbsentEq : isKeyword input .constructorKw = false :=
          Bool.eq_false_iff.mpr constructorAbsent
        have constructorAbsentGrammar :=
          keywordAbsentAt_of_isKeyword_eq_false .constructorKw
            constructorAbsentEq
        split at result
        next startsFallback =>
          exact .fallbackRejected fieldAbsentGrammar functionAbsentGrammar
            constructorAbsentGrammar
            (keywordPresent_of_isKeyword_eq_true_variant .fallbackKw startsFallback)
            (fallbackDecl_reject_ordinaryOutcome_sound
              (mapMember_reject_result fallbackDecl wrapFallback result))
        next fallbackAbsent =>
          have fallbackAbsentEq : isKeyword input .fallbackKw = false :=
            Bool.eq_false_iff.mpr fallbackAbsent
          have fallbackAbsentGrammar :=
            keywordAbsentAt_of_isKeyword_eq_false .fallbackKw fallbackAbsentEq
          split at result
          next startsType =>
            exact .typeAliasRejected fieldAbsentGrammar functionAbsentGrammar
              constructorAbsentGrammar fallbackAbsentGrammar
              (keywordPresent_of_isKeyword_eq_true_variant .typeKw startsType)
              (typeAlias_reject_ordinaryOutcome_sound
                (mapMember_reject_result typeAlias wrapContractTypeAlias
                  result))
          next typeAbsent =>
            have typeAbsentEq : isKeyword input .typeKw = false :=
              Bool.eq_false_iff.mpr typeAbsent
            have typeAbsentGrammar :=
              keywordAbsentAt_of_isKeyword_eq_false .typeKw typeAbsentEq
            split at result
            next startsEnum =>
              exact .enumRejected fieldAbsentGrammar functionAbsentGrammar
                constructorAbsentGrammar fallbackAbsentGrammar
                typeAbsentGrammar
                (enumPresent_of_isContextual_eq_true_variant startsEnum)
                (enumDecl_reject_ordinaryOutcome_sound none
                  (mapMember_reject_result (enumDecl none) wrapContractEnum
                    result))
            next enumAbsent =>
              have enumAbsentEq : isContextual input .enum = false :=
                Bool.eq_false_iff.mpr enumAbsent
              have enumAbsentGrammar :=
                contextualAbsentAt_of_isContextual_eq_false .enum enumAbsentEq
              unfold rejectedContractMember rejectAt at result
              cases result
              exact .unrecognized fieldAbsentGrammar functionAbsentGrammar
                constructorAbsentGrammar fallbackAbsentGrammar
                typeAbsentGrammar enumAbsentGrammar

end ContractInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberCoreOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for attribute-free contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Package unconditional executable success and exact selected-branch
rejection for attribute-free contract members. -/
theorem contractMemberCore_ordinaryOutcome_sound :
    (∀ {input output : State} {member : ContractMember},
      contractMemberCore input = .ok member output →
        DeclarativeGrammar.ContractMemberCoreOrdinaryParses
          input.declarativeRemainder member output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractMemberCore input = .reject failure rejected →
        DeclarativeGrammar.ContractMemberCoreRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨contractMemberCore_success_ordinaryOutcome_sound,
    contractMemberCore_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive attribute-free member outcomes. -/
theorem contractMemberCore_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreDeterministicOutcomeSpec

/-- Exact public expressions, isolated bodies, and enums supply exact
attribute-free member outcomes. -/
theorem contractMemberCore_exactOutcomeSpec_of_leaves
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects)
    (allowBodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    (requireBodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require))
    (enumOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.EnumDeclOrdinaryParses none)
      DeclarativeGrammar.EnumDeclRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfLeaves
    expressionOutcomes allowBodyOutcomes requireBodyOutcomes enumOutcomes

/-- Fixed-fuel Core exactness leaves only enum exactness as a premise. -/
theorem contractMemberCore_exactOutcomeSpec_of_termFuel
    (expressionOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (enumOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.EnumDeclOrdinaryParses none)
      DeclarativeGrammar.EnumDeclRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfTermFuel
    expressionOutcomes statementOutcomes enumOutcomes

/-- Fixed-fuel Core expression and statement exactness alone supplies the
attribute-free member contract; enum outcomes are unconditional. -/
theorem contractMemberCore_exactOutcomeSpec_of_coreTermFuel
    (expressionOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfCoreTermFuel
    expressionOutcomes statementOutcomes

/-- Any exact core contract fixes two executable success ASTs and endpoints. -/
theorem contractMemberCore_success_result_unique
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects)
    {input leftOutput rightOutput : State} {left right : ContractMember}
    (leftResult : contractMemberCore input = .ok left leftOutput)
    (rightResult : contractMemberCore input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  coreOutcomes.successResultUnique
    (contractMemberCore_success_ordinaryOutcome_sound leftResult)
    (contractMemberCore_success_ordinaryOutcome_sound rightResult)

/-- Any exact core contract fixes two executable rejection endpoints. -/
theorem contractMemberCore_reject_output_unique
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractMemberCore input = .reject leftFailure leftOutput)
    (rightResult : contractMemberCore input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  coreOutcomes.rejectOutputUnique
    (contractMemberCore_reject_ordinaryOutcome_sound leftResult)
    (contractMemberCore_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ContractInternals
end
