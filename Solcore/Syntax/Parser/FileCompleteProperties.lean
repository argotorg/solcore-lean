import Solcore.Syntax.Parser.ContractCanonicalProperties
import Solcore.Syntax.Parser.FileCanonicalProperties
import Solcore.Syntax.Parser.FileCanonicalStateProperties

/-! Unconditional canonical contracts for complete-file parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FileInternals

/-- The completed contract parser discharges the final file-parser input. -/
theorem contractDecl_canonical_inputs : ContractDeclInputs := {
  validFor := contractDecl_canonical_contract.validFor
  preservesTokenWindow := contractDecl_canonical_contract.preservesTokenWindow
  cursorMonotoneOnSuccess :=
    contractDecl_canonical_contract.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    contractDecl_canonical_contract.startsAtCurrentTokenOnSuccess
}

theorem parseItemsItem_complete_contract :
    TopItemParserContract parseItemsItem :=
  parseItemsItem_contract contractDecl_canonical_inputs

theorem parseItemsItem_complete_validFor :
    parseItemsItem.ValidFor RecoveredTopItemValid :=
  parseItemsItem_canonical_validFor contractDecl_canonical_inputs

theorem sourceFile_complete_reply_validFor
    {comments : List Comment} {input : State}
    (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file) :
    (sourceFile comments input).ValidFor input CanonicalParsedFileValid :=
  sourceFile_canonical_reply_validFor contractDecl_canonical_inputs
    inputValid commentsValid

theorem parseItems_complete_preservesTokenWindow
    (fuel : Nat) (itemsRev : List TopItem) :
    Parser.PreservesTokenWindow (parseItems fuel itemsRev) :=
  parseItems_canonical_preservesTokenWindow contractDecl_canonical_inputs
    fuel itemsRev

theorem parseItems_complete_preservesTokensOnSuccess
    (fuel : Nat) (itemsRev : List TopItem) :
    Parser.PreservesTokensOnSuccess (parseItems fuel itemsRev) :=
  parseItems_canonical_preservesTokensOnSuccess contractDecl_canonical_inputs
    fuel itemsRev

theorem parseItems_complete_cursorMonotoneOnSuccess
    (fuel : Nat) (itemsRev : List TopItem) :
    Parser.CursorMonotoneOnSuccess (parseItems fuel itemsRev) :=
  parseItems_canonical_cursorMonotoneOnSuccess contractDecl_canonical_inputs
    fuel itemsRev

theorem sourceFile_complete_preservesTokenWindow (comments : List Comment) :
    Parser.PreservesTokenWindow (sourceFile comments) :=
  sourceFile_canonical_preservesTokenWindow contractDecl_canonical_inputs
    comments

theorem sourceFile_complete_preservesTokensOnSuccess
    (comments : List Comment) :
    Parser.PreservesTokensOnSuccess (sourceFile comments) :=
  sourceFile_canonical_preservesTokensOnSuccess contractDecl_canonical_inputs
    comments

theorem sourceFile_complete_cursorMonotoneOnSuccess
    (comments : List Comment) :
    Parser.CursorMonotoneOnSuccess (sourceFile comments) :=
  sourceFile_canonical_cursorMonotoneOnSuccess contractDecl_canonical_inputs
    comments

end FileInternals

theorem parseLexed_ok_complete_validFor
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (lexedValid : lexed.ValidFor file)
    (result : parseLexed file lexed = .ok output) :
    CanonicalParsedFileValid file output.parsed :=
  parseLexed_ok_canonical_validFor FileInternals.contractDecl_canonical_inputs
    file lexed output lexedValid result

theorem parse_ok_complete_validFor
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    CanonicalParsedFileValid file output.parsed :=
  parse_ok_canonical_validFor FileInternals.contractDecl_canonical_inputs
    file output result

end Solcore.Syntax.Parser
