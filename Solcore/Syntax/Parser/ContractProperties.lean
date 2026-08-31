import Solcore.Syntax.Parser.Contract
import Solcore.Syntax.Parser.DeclarationCanonicalProperties
import Solcore.Syntax.Parser.DeriveCarrierProperties
import Solcore.Syntax.Parser.EnumProperties
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.Parser.TypeAliasProperties
import Solcore.Syntax.ContractDeclarationValidity

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
