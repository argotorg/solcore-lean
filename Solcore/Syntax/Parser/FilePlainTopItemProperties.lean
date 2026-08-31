import Solcore.Syntax.Parser.DeclarationCanonicalProperties
import Solcore.Syntax.Parser.EnumProperties
import Solcore.Syntax.Parser.ExportProperties
import Solcore.Syntax.Parser.FileTopItemProperties
import Solcore.Syntax.Parser.ImportProperties
import Solcore.Syntax.Parser.Pragma
import Solcore.Syntax.Parser.TraitProperties
import Solcore.Syntax.Parser.TypeAliasProperties

/-! Compositional contracts for top-level declaration dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- The complete contract retained by top-level declaration dispatch. -/
structure TopItemParserContract (parser : Parser TopItem) : Prop where
  validFor : parser.ValidFor TopItemContract
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess parser (·.span)

theorem TopItemParserContract.preservesTokensOnSuccess
    {parser : Parser TopItem}
    (contract : TopItemParserContract parser) :
    Parser.PreservesTokensOnSuccess parser :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

/-- The still-open outer contract declaration boundary is an explicit input. -/
structure ContractDeclInputs : Prop where
  validFor : contractDecl.ValidFor
    (ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor)
  preservesTokenWindow : Parser.PreservesTokenWindow contractDecl
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess contractDecl
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractDecl (·.span)

private theorem mapTopItem_contract {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → TopItem)
    (valueValid : SourceFile → alpha → Prop) (span : alpha → SourceSpan)
    (parserValid : parser.ValidFor valueValid)
    (parserWindow : Parser.PreservesTokenWindow parser)
    (parserCursor : Parser.CursorMonotoneOnSuccess parser)
    (parserStarts : Parser.StartsAtCurrentTokenOnSuccess parser span)
    (wrapValid : ∀ file value, valueValid file value →
      TopItemContract file (wrap value))
    (wrapSpan : ∀ value, (wrap value).span = span value) :
    TopItemParserContract (mapTopItem parser wrap) := {
  validFor := by
    intro input inputValid
    have valid := parserValid input inputValid
    unfold mapTopItem
    cases result : parser input with
    | invariant error => trivial
    | reject failure next =>
        rw [result] at valid
        exact ⟨valid.1, valid.2.1, valid.2.2⟩
    | ok value next =>
        rw [result] at valid
        simp only [Reply.ValidFor]
        exact ⟨wrapValid input.file value valid.1, valid.2.1, valid.2.2⟩
  preservesTokenWindow := by
    intro input
    have preserved := parserWindow input
    unfold mapTopItem
    cases result : parser input with
    | invariant error => trivial
    | reject failure next =>
        rw [result] at preserved
        exact ⟨preserved.1, preserved.2⟩
    | ok value next =>
        rw [result] at preserved
        exact ⟨preserved.1, preserved.2⟩
  cursorMonotoneOnSuccess := by
    intro input item next parsed
    unfold mapTopItem at parsed
    cases result : parser input with
    | invariant error => simp [result] at parsed
    | reject failure rejected => simp [result] at parsed
    | ok value final =>
        simp only [result] at parsed
        have monotone := parserCursor input value final result
        cases parsed
        exact monotone
  startsAtCurrentTokenOnSuccess := by
    intro input item next parsed
    unfold mapTopItem at parsed
    cases result : parser input with
    | invariant error => simp [result] at parsed
    | reject failure rejected => simp [result] at parsed
    | ok value final =>
        simp only [result] at parsed
        have starts := parserStarts input value final result
        cases parsed
        simpa only [wrapSpan value] using starts
}

private theorem stateChoice_contract (condition : State → Bool)
    {first second : Parser TopItem}
    (firstContract : TopItemParserContract first)
    (secondContract : TopItemParserContract second) :
    TopItemParserContract (fun input =>
      if condition input then first input else second input) := {
  validFor := by
    intro input inputValid
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.validFor input inputValid
    · simpa [selected] using secondContract.validFor input inputValid
  preservesTokenWindow := by
    intro input
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.preservesTokenWindow input
    · simpa [selected] using secondContract.preservesTokenWindow input
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    by_cases selected : condition input = true
    · exact firstContract.cursorMonotoneOnSuccess input value next
        (by simpa [selected] using parsed)
    · exact secondContract.cursorMonotoneOnSuccess input value next
        (by simpa [selected] using parsed)
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    by_cases selected : condition input = true
    · exact firstContract.startsAtCurrentTokenOnSuccess input value next
        (by simpa [selected] using parsed)
    · exact secondContract.startsAtCurrentTokenOnSuccess input value next
        (by simpa [selected] using parsed)
}

private theorem rejectedTopItem_contract : TopItemParserContract (fun input =>
    rejectAt input { head := .topItem, tail := [] } .topItem) := {
  validFor := by
    intro input inputValid
    unfold rejectAt Reply.ValidFor
    exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  preservesTokenWindow := fun input =>
    rejectAt_preservesTokenWindow input _ _
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    unfold rejectAt at parsed
    contradiction
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    unfold rejectAt at parsed
    contradiction
}

/-- All nine declaration branches and the terminal rejection compose in
implementation order.  Only the unfinished outer contract parser remains an
explicit dependency. -/
theorem plainTopItem_contract (contract : ContractDeclInputs) :
    TopItemParserContract plainTopItem := by
  have importBranch := mapTopItem_contract importDecl wrapImport
    ImportDecl.ValidFor (·.span) importDecl_validFor
    importDecl_preservesTokenWindow importDecl_cursorMonotoneOnSuccess
    importDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapImport_contract) (fun _ => rfl)
  have exportBranch := mapTopItem_contract exportDecl wrapExport
    ExportDecl.ValidFor (·.span) exportDecl_validFor
    exportDecl_preservesTokenWindow exportDecl_cursorMonotoneOnSuccess
    exportDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapExport_contract) (fun _ => rfl)
  have pragmaBranch := mapTopItem_contract pragmaDecl wrapPragma
    PragmaDecl.ValidFor (·.span) pragmaDecl_validFor
    pragmaDecl_preservesTokenWindow pragmaDecl_cursorMonotoneOnSuccess
    pragmaDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapPragma_contract) (fun _ => rfl)
  have aliasBranch := mapTopItem_contract typeAlias wrapTypeAlias
    TypeAliasDecl.ValidFor (·.span) typeAlias_validFor
    typeAlias_preservesTokenWindow typeAlias_cursorMonotoneOnSuccess
    typeAlias_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapTypeAlias_contract) (fun _ => rfl)
  have functionBranch := mapTopItem_contract (functionDecl .module) wrapFunction
    (FunctionDecl.ValidFor CoreStatement.ValidFor) (·.span)
    (functionDecl_canonical_validFor .module)
    (functionDecl_preservesTokenWindow_of_block .module
      (block_canonical_preservesTokenWindow .allow))
    (functionDecl_cursorMonotoneOnSuccess_of_block .module
      (block_canonical_cursorMonotoneOnSuccess .allow))
    (functionDecl_startsAtCurrentTokenOnSuccess .module)
    (fun _ _ => wrapFunction_contract) (fun _ => rfl)
  have enumBranch := mapTopItem_contract (enumDecl none) wrapEnum
    EnumDecl.ValidFor (·.span) enumDecl_none_validFor
    (enumDecl_preservesTokenWindow none)
    (enumDecl_cursorMonotoneOnSuccess none)
    enumDecl_none_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapEnum_contract) (fun _ => rfl)
  have traitBranch := mapTopItem_contract traitDecl wrapTrait
    TraitDecl.ValidFor (·.span) traitDecl_validFor
    (traitDecl_preservesTokenWindow
      (functionSignature_preservesTokenWindow .module)
      whereClause_preservesTokenWindow)
    (traitDecl_cursorMonotoneOnSuccess whereClause_cursorMonotoneOnSuccess)
    traitDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapTrait_contract) (fun _ => rfl)
  have implBranch := mapTopItem_contract implDecl wrapImpl
    (ImplDecl.ValidFor CoreStatement.ValidFor) (·.span)
    implDecl_canonical_validFor
    (implDecl_preservesTokenWindow_of_block
      (block_canonical_preservesTokenWindow .allow))
    implDecl_cursorMonotoneOnSuccess implDecl_startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapImpl_contract) (fun _ => rfl)
  have contractBranch := mapTopItem_contract contractDecl wrapContract
    (ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor) (·.span)
    contract.validFor contract.preservesTokenWindow
    contract.cursorMonotoneOnSuccess contract.startsAtCurrentTokenOnSuccess
    (fun _ _ => wrapContract_contract) (fun _ => rfl)
  have dispatch := stateChoice_contract (fun state => isKeyword state .importKw)
    importBranch (stateChoice_contract (fun state => isKeyword state .exportKw)
      exportBranch (stateChoice_contract (fun state => isKeyword state .pragmaKw)
        pragmaBranch (stateChoice_contract (fun state => isKeyword state .typeKw)
          aliasBranch (stateChoice_contract
            (fun state => isKeyword state .functionKw) functionBranch
            (stateChoice_contract (fun state => isContextual state .enum)
              enumBranch (stateChoice_contract
                (fun state => isContextual state .trait) traitBranch
                (stateChoice_contract (fun state =>
                  isContextual state .impl || isKeyword state .defaultKw)
                  implBranch (stateChoice_contract
                    (fun state => isKeyword state .contractKw)
                    contractBranch rejectedTopItem_contract))))))))
  unfold plainTopItem
  exact dispatch

end Solcore.Syntax.Parser.FileInternals
