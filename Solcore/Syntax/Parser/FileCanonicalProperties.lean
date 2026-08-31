import Solcore.Syntax.Parser.FileItemProperties
import Solcore.Syntax.Parser.PublicValidityProperties

/-! Canonical file validity from the completed derive-aware item boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FileInternals

/-- The derive-aware item contract supplies the canonical predicate expected by
the complete-file loop. -/
theorem parseItemsItem_canonical_validFor (contract : ContractDeclInputs) :
    parseItemsItem.ValidFor RecoveredTopItemValid :=
  (parseItemsItem_contract contract).validFor.mono
    (fun _ _ itemContract => itemContract.validFor)

/-- Complete-file replies retain canonical parsed-file provenance. -/
theorem sourceFile_canonical_reply_validFor
    (contract : ContractDeclInputs) {comments : List Comment} {input : State}
    (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file) :
    (sourceFile comments input).ValidFor input CanonicalParsedFileValid :=
  sourceFile_reply_validFor (parseItemsItem_canonical_validFor contract)
    (parseItemsItem_contract contract).preservesTokenWindow inputValid
    commentsValid

end FileInternals

/-- Preflighted parsing needs only the explicit outer contract-declaration
boundary to return a canonically valid parsed file. -/
theorem parseLexed_ok_canonical_validFor
    (contract : FileInternals.ContractDeclInputs)
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (lexedValid : lexed.ValidFor file)
    (result : parseLexed file lexed = .ok output) :
    CanonicalParsedFileValid file output.parsed :=
  parseLexed_ok_parsed_validFor
    (FileInternals.parseItemsItem_canonical_validFor contract)
    (FileInternals.parseItemsItem_contract contract).preservesTokenWindow
    file lexed output lexedValid result

/-- Public source parsing exposes canonical parsed-file validity under the same
single explicit declaration boundary. -/
theorem parse_ok_canonical_validFor
    (contract : FileInternals.ContractDeclInputs)
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    CanonicalParsedFileValid file output.parsed :=
  parse_ok_parsed_validFor
    (FileInternals.parseItemsItem_canonical_validFor contract)
    (FileInternals.parseItemsItem_contract contract).preservesTokenWindow
    file output result

end Solcore.Syntax.Parser
