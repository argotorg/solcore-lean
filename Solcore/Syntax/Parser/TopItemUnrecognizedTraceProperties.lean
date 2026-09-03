import Solcore.Syntax.Parser.PlainTopItemOutcomePrimitiveProperties
import Solcore.Syntax.Parser.TopItemRecoveryBoundaryProperties

/-! Independent absence of every top-item start selects an unchanged,
uncommitted rejection before file-level recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- The independent absent-start condition includes hard keywords, contextual
declarations, and the leading derive hash. -/
theorem atTopItemStart_eq_false_of_topItemStartAbsent
    {input : State}
    (absent : DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds) :
    atTopItemStart input = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rcases importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true present with
    ⟨kind, member, span, token⟩
  exact absent kind member ⟨span, token⟩

/-- No recognized declaration or derive attribute is attempted when every
independent start token is absent. The rejection leaves diagnostics unchanged. -/
theorem parseItemsItem_eq_rejectAt_of_topItemStartAbsent
    {input : State}
    (absent : DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds) :
    parseItemsItem input =
      rejectAt input { head := .topItem, tail := [] } .topItem := by
  have keywordAbsent (value : HardKeyword)
      (member : TokenKind.keyword value ∈
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds) :
      isKeyword input value = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    exact absent (.keyword value) member
      (plainTopItemTokenPresentAt_of_isKeyword_eq_true value present)
  have contextualAbsent (value : ContextualKeyword)
      (member : TokenKind.identifier value.spelling ∈
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds) :
      isContextual input value = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    exact absent (.identifier value.spelling) member
      (plainTopItemTokenPresentAt_of_isContextual_eq_true value present)
  have hashAbsent : isSymbol input .hash = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    rcases symbol_eq_ok_of_isSymbol_eq_true .hash .topItem present with
      ⟨token, result⟩
    exact absent (.symbol .hash)
      (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds])
      ⟨token.span, (symbol_success_exactTokenParses .hash .topItem result).1⟩
  simp [parseItemsItem, topItem, plainTopItem, hashAbsent,
    keywordAbsent .importKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .exportKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .pragmaKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .typeKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .functionKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .defaultKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .contractKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    contextualAbsent .enum (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    contextualAbsent .trait (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    contextualAbsent .impl (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds])]

end Solcore.Syntax.Parser.FileInternals
