import Solcore.Syntax.Parser.ContractProperties

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
