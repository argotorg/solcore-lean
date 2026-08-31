import Solcore.Syntax.Parser.FileCompleteProperties

/-! Strict cursor progress for complete top-level item parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_cursor_lt_onSuccess_of_first {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstStrict : ∀ {input middle : State} {value : alpha},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {result : beta}
    (parsed : (first >>= next) input = .ok result final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok value middle => next value middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok result final at parsed
  cases firstResult : first input with
  | ok value middle =>
      simp only [firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone value middle result final parsed)
  | reject failure rejected => simp [firstResult] at parsed
  | invariant error => simp [firstResult] at parsed

/-- A complete import consumes its leading keyword. -/
theorem importDecl_cursor_lt_onSuccess {input final : State}
    {declaration : ImportDecl}
    (parsed : importDecl input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold importDecl at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.keyword .importKw) .importDecl (· == .keyword .importKw) result) ?_ parsed
  intro importKeyword
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases star : isSymbol observed .star
  · simp only [star, if_true]
    by_cases namespaceAlias :
        observed.peekOffsetKind? 1 == some (.keyword .asKw)
    · simp only [namespaceAlias, if_true]
      exact namespaceImport_cursorMonotoneOnSuccess importKeyword.span
    · simp only [namespaceAlias]
      exact wildcardImport_cursorMonotoneOnSuccess importKeyword.span
  · simp only [star]
    by_cases selected : isSymbol observed .leftBrace
    · simp only [selected, if_true]
      exact selectiveImport_cursorMonotoneOnSuccess importKeyword.span
    · simp only [selected]
      exact plainImport_cursorMonotoneOnSuccess importKeyword.span

/-- A complete export consumes its leading keyword. -/
theorem exportDecl_cursor_lt_onSuccess {input final : State}
    {declaration : ExportDecl}
    (parsed : exportDecl input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold exportDecl at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.keyword .exportKw) .exportDecl (· == .keyword .exportKw) result) ?_ parsed
  intro exportKeyword
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  split
  · exact localExport_cursorMonotoneOnSuccess exportKeyword.span
  · exact pathExport_cursorMonotoneOnSuccess exportKeyword.span

/-- A complete type alias consumes its leading keyword. -/
theorem typeAlias_cursor_lt_onSuccess {input final : State}
    {declaration : TypeAliasDecl}
    (parsed : typeAlias input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold typeAlias at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.keyword .typeKw) .typeAlias (· == .keyword .typeKw) result) ?_ parsed
  intro typeKeyword
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .typeAlias)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    parseTypeAliasParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .equal .typeAlias)
  intro equal
  apply Parser.bind_cursorMonotoneOnSuccess
    TypeAliasInternals.parseAliasValue_cursorMonotoneOnSuccess
  intro value
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .typeAlias)
  intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Every complete function consumes its signature's leading keyword. -/
theorem functionDecl_cursor_lt_onSuccess (location : FunctionLocation)
    {input final : State} {declaration : FunctionDecl}
    (parsed : functionDecl location input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold functionDecl at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (FunctionInternals.functionSignature_cursor_lt_onSuccess location) ?_ parsed
  intro signature
  apply Parser.bind_cursorMonotoneOnSuccess
    (isolateBlock_cursorMonotoneOnSuccess (block .allow)
      (block_canonical_cursorMonotoneOnSuccess .allow))
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Every complete enum consumes its contextual marker. -/
theorem enumDecl_cursor_lt_onSuccess (derive : Option DeriveAttribute)
    {input final : State} {declaration : EnumDecl}
    (parsed : enumDecl derive input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold enumDecl at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.contextual .enum) .topItem (·.isContextual .enum) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .topItem)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalGenericParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    EnumInternals.enumBody_cursorMonotoneOnSuccess
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

namespace FileInternals

private theorem mapTopItem_cursor_lt_onSuccess {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → TopItem)
    (parserStrict : ∀ {input final : State} {value : alpha},
      parser input = .ok value final → input.cursor < final.cursor)
    {input final : State} {item : TopItem}
    (parsed : mapTopItem parser wrap input = .ok item final) :
    input.cursor < final.cursor := by
  unfold mapTopItem at parsed
  cases result : parser input with
  | invariant error => simp [result] at parsed
  | reject failure rejected => simp [result] at parsed
  | ok value next =>
      simp only [result] at parsed
      cases parsed
      exact parserStrict result

/-- Every successful plain top-level declaration consumes its leading token. -/
theorem plainTopItem_cursor_lt_onSuccess {input final : State} {item : TopItem}
    (parsed : plainTopItem input = .ok item final) :
    input.cursor < final.cursor := by
  unfold plainTopItem at parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess importDecl wrapImport
      importDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess exportDecl wrapExport
      exportDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess pragmaDecl wrapPragma
      pragmaDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess typeAlias wrapTypeAlias
      typeAlias_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess (functionDecl .module) wrapFunction
      (functionDecl_cursor_lt_onSuccess .module) parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess (enumDecl none) wrapEnum
      (enumDecl_cursor_lt_onSuccess none) parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess traitDecl wrapTrait
      traitDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess implDecl wrapImpl
      implDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess contractDecl wrapContract
      contractDecl_canonical_cursor_lt_onSuccess parsed
  · unfold rejectAt at parsed
    contradiction

/-- The derive-aware item boundary always advances on ordinary success. -/
theorem parseItemsItem_cursor_lt_onSuccess {input final : State}
    {item : TopItem} (parsed : parseItemsItem input = .ok item final) :
    input.cursor < final.cursor := by
  unfold parseItemsItem topItem at parsed
  split at parsed
  · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
    rename_i derive afterDerive
    cases itemResult : plainTopItem afterDerive <;> simp [itemResult] at parsed
    rename_i inner next
    exact Nat.lt_of_lt_of_le (deriveAttribute_cursor_lt_onSuccess deriveResult)
      (Nat.le_trans
        ((plainTopItem_contract contractDecl_canonical_inputs
          ).cursorMonotoneOnSuccess
          afterDerive inner next itemResult)
        (attachDeriveAttribute_cursorMonotoneOnSuccess derive inner
          next item final parsed))
  · exact plainTopItem_cursor_lt_onSuccess parsed

end FileInternals
end Solcore.Syntax.Parser
