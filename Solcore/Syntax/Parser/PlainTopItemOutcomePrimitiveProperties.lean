import Solcore.Syntax.DeclarativePlainTopItemOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.File

/-! Shared executable primitives for broad attribute-free top-item outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Successful top-item mapping exposes the unchanged child endpoint and exact
wrapper value. -/
theorem mapTopItem_success_components {alpha : Type}
    {parser : Parser alpha} {wrap : alpha → TopItem}
    {input output : State} {item : TopItem}
    (result : mapTopItem parser wrap input = .ok item output) :
    ∃ value, parser input = .ok value output ∧ item = wrap value := by
  unfold mapTopItem at result
  cases childResult : parser input with
  | ok value afterValue =>
      simp only [childResult] at result
      cases result
      exact ⟨value, rfl, rfl⟩
  | reject failure rejected => simp [childResult] at result
  | invariant error => simp [childResult] at result

/-- Rejecting top-item mapping is an exact child-rejection passthrough. -/
theorem mapTopItem_reject_result {alpha : Type}
    {parser : Parser alpha} {wrap : alpha → TopItem}
    {input rejected : State} {failure : Failure}
    (result : mapTopItem parser wrap input = .reject failure rejected) :
    parser input = .reject failure rejected := by
  unfold mapTopItem at result
  cases childResult : parser input with
  | ok value output => simp [childResult] at result
  | invariant error => simp [childResult] at result
  | reject childFailure childRejected =>
      simp only [childResult] at result
      cases result
      rfl

/-- A positive hard-keyword guard is exact current-token evidence. -/
theorem plainTopItemTokenPresentAt_of_isKeyword_eq_true
    (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.PlainTopItemTokenPresentAt input.declarativeRemainder
      (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .topItem result).1⟩

/-- A positive contextual-word guard is exact current-token evidence. -/
theorem plainTopItemTokenPresentAt_of_isContextual_eq_true
    (value : ContextualKeyword) {input : State}
    (present : isContextual input value = true) :
    DeclarativeGrammar.PlainTopItemTokenPresentAt input.declarativeRemainder
      (.identifier value.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true value .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses value .topItem result).1⟩

/-- A false hard-keyword guard is exact current-token absence. -/
theorem plainTopItemTokenAbsentAt_of_isKeyword_eq_false
    (value : HardKeyword) {input : State}
    (absent : isKeyword input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) :=
  keywordAbsentAt_of_isKeyword_eq_false value absent

/-- A false contextual-word guard is exact current-token absence. -/
theorem plainTopItemTokenAbsentAt_of_isContextual_eq_false
    (value : ContextualKeyword) {input : State}
    (absent : isContextual input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) :=
  contextualAbsentAt_of_isContextual_eq_false value absent

/-- The first positive guard selects the import branch. -/
theorem plainTopItemImportBranchSelected {input : State}
    (importPresent : isKeyword input .importKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .importDecl :=
  .importDecl
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .importKw importPresent)

/-- A negative import guard followed by export selects export. -/
theorem plainTopItemExportBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportPresent : isKeyword input .exportKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .exportDecl :=
  .exportDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .exportKw exportPresent)

/-- The first three hard-keyword guards select pragma in priority order. -/
theorem plainTopItemPragmaBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaPresent : isKeyword input .pragmaKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .pragmaDecl :=
  .pragmaDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .pragmaKw pragmaPresent)

/-- The prioritized hard-keyword prefix selects a type alias. -/
theorem plainTopItemTypeAliasBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typePresent : isKeyword input .typeKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .typeAlias :=
  .typeAlias
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .typeKw typePresent)

/-- The prioritized hard-keyword prefix selects a module function. -/
theorem plainTopItemFunctionBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionPresent : isKeyword input .functionKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .functionDecl :=
  .functionDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .functionKw
      functionPresent)

/-- After the hard-keyword prefix, contextual enum selects enum. -/
theorem plainTopItemEnumBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumPresent : isContextual input .enum = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .enumDecl :=
  .enumDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenPresentAt_of_isContextual_eq_true .enum enumPresent)

/-- Contextual trait is selected only after enum is absent. -/
theorem plainTopItemTraitBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitPresent : isContextual input .trait = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .traitDecl :=
  .traitDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .enum enumAbsent)
    (plainTopItemTokenPresentAt_of_isContextual_eq_true .trait traitPresent)

/-- Either positive half of the executable impl/default disjunction selects
the implementation branch. -/
theorem plainTopItemImplBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false)
    (implOrDefaultPresent :
      (isContextual input .impl || isKeyword input .defaultKw) = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .implDecl := by
  apply DeclarativeGrammar.PlainTopItemBranchSelected.implDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .enum enumAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .trait traitAbsent)
  rcases Bool.or_eq_true_iff.mp implOrDefaultPresent with
    implPresent | defaultPresent
  · exact Or.inl
      (plainTopItemTokenPresentAt_of_isContextual_eq_true .impl implPresent)
  · exact Or.inr
      (plainTopItemTokenPresentAt_of_isKeyword_eq_true .defaultKw
        defaultPresent)

/-- A false impl/default disjunction is split before selecting contract. -/
theorem plainTopItemContractBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false)
    (implOrDefaultAbsent :
      (isContextual input .impl || isKeyword input .defaultKw) = false)
    (contractPresent : isKeyword input .contractKw = true) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .contractDecl := by
  rcases Bool.or_eq_false_iff.mp implOrDefaultAbsent with
    ⟨implAbsent, defaultAbsent⟩
  exact .contractDecl
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .enum enumAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .trait traitAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .impl implAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .defaultKw defaultAbsent)
    (plainTopItemTokenPresentAt_of_isKeyword_eq_true .contractKw
      contractPresent)

/-- If every declaration guard is false, the final unrecognized branch is
selected. -/
theorem plainTopItemUnrecognizedBranchSelected {input : State}
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false)
    (implOrDefaultAbsent :
      (isContextual input .impl || isKeyword input .defaultKw) = false)
    (contractAbsent : isKeyword input .contractKw = false) :
    DeclarativeGrammar.PlainTopItemBranchSelected input.declarativeRemainder
      .unrecognized := by
  rcases Bool.or_eq_false_iff.mp implOrDefaultAbsent with
    ⟨implAbsent, defaultAbsent⟩
  exact .unrecognized
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .importKw importAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .exportKw exportAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .pragmaKw pragmaAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .typeKw typeAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .functionKw
      functionAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .enum enumAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .trait traitAbsent)
    (plainTopItemTokenAbsentAt_of_isContextual_eq_false .impl implAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .defaultKw defaultAbsent)
    (plainTopItemTokenAbsentAt_of_isKeyword_eq_false .contractKw
      contractAbsent)

/-- `rejectAt` always retains the exact input state. -/
theorem plainTopItemRejectAt_rejected_state_eq {alpha : Type}
    {input rejected : State} {failure : Failure}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    (result : (rejectAt input expected context : Reply alpha) =
      .reject failure rejected) : rejected = input := by
  unfold rejectAt at result
  cases result
  rfl

end Solcore.Syntax.Parser.FileInternals
