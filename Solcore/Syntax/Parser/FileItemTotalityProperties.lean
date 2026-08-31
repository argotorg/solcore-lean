import Solcore.Syntax.Parser.DeriveAttributeTotalityProperties
import Solcore.Syntax.Parser.FileCompleteProperties
import Solcore.Syntax.Parser.FilePlainTopItemTotalityProperties
import Solcore.Syntax.Parser.PublicTotalityProperties

/-! Conditional totality from derive-aware items through public parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Attaching a parsed derive attribute cannot introduce an invariant reply. -/
theorem attachDeriveAttribute_invariantFreeOnValid
    (derive : DeriveAttribute) (item : TopItem) :
    Parser.InvariantFreeOnValid (attachDeriveAttribute derive item) := by
  intro input _inputValid
  rcases item with ⟨span, comments, value⟩
  cases value <;> left <;>
    simp [attachDeriveAttribute, emitDiagnostic, modifyState, bind, pure]

/-- The derive-aware top-item parser inherits the seven plain branch inputs. -/
theorem topItem_invariantFreeOnValid
    (contract : PlainTopItemTotalityContract) :
    Parser.InvariantFreeOnValid topItem := by
  intro input inputValid
  unfold topItem
  by_cases attributed : isSymbol input .hash
  · simp only [attributed, if_true]
    have deriveReply := deriveAttribute_validFor input inputValid
    rcases deriveAttribute_ordinary input inputValid with
      ⟨derive, afterDerive, deriveResult⟩ |
      ⟨failure, rejected, deriveResult⟩
    · rw [deriveResult] at deriveReply
      have plainValid :=
        (plainTopItem_contract contractDecl_canonical_inputs).validFor
          afterDerive deriveReply.2.1
      rcases plainTopItem_invariantFreeOnValid contract afterDerive
          deriveReply.2.1 with
        ⟨item, next, itemResult⟩ | ⟨failure, rejected, itemResult⟩
      · rw [itemResult] at plainValid
        rcases attachDeriveAttribute_invariantFreeOnValid derive item next
            plainValid.2.1 with
          ⟨attached, final, attachedResult⟩ |
          ⟨failure, rejected, attachedResult⟩
        · left
          exact ⟨attached, final, by
            simp only [deriveResult, itemResult, attachedResult]⟩
        · right
          exact ⟨failure, rejected, by
            simp only [deriveResult, itemResult, attachedResult]⟩
      · right
        exact ⟨failure, rejected, by
          simp only [deriveResult, itemResult]⟩
    · right
      exact ⟨failure, rejected, by simp only [deriveResult]⟩
  · simpa [attributed] using
      plainTopItem_invariantFreeOnValid contract input inputValid

/-- The file-loop item boundary has the same conditional totality contract. -/
theorem parseItemsItem_invariantFreeOnValid
    (contract : PlainTopItemTotalityContract) :
    Parser.InvariantFreeOnValid parseItemsItem := by
  simpa only [parseItemsItem] using topItem_invariantFreeOnValid contract

/-- Convert the compositional parser contract to the file-loop premise. -/
theorem parseItemsItemInvariantFree_of_plainTopItemContract
    (contract : PlainTopItemTotalityContract) :
    ParseItemsItemInvariantFree := by
  intro input inputValid error
  exact (parseItemsItem_invariantFreeOnValid contract).ne_invariant
    input inputValid error

/-- Complete-file parsing succeeds under exactly the seven plain branch inputs. -/
theorem sourceFile_exists_ok_of_plainTopItemContract
    (contract : PlainTopItemTotalityContract)
    (comments : List Comment) (input : State) (inputValid : input.ValidFor) :
    ∃ parsed final, sourceFile comments input = .ok parsed final :=
  sourceFile_exists_ok
    (parseItemsItemInvariantFree_of_plainTopItemContract contract)
    comments input inputValid

end Solcore.Syntax.Parser.FileInternals

namespace Solcore.Syntax.Parser

/-- Valid tokenized input produces output under the seven branch inputs. -/
theorem parseLexed_exists_ok_of_plainTopItemContract
    (contract : FileInternals.PlainTopItemTotalityContract)
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file) :
    ∃ output, parseLexed file lexed = .ok output :=
  parseLexed_exists_ok_of_validFor
    (FileInternals.parseItemsItemInvariantFree_of_plainTopItemContract contract)
    file lexed lexedValid

/-- No parser error escapes valid tokenized input under those same inputs. -/
theorem parseLexed_ne_error_of_plainTopItemContract
    (contract : FileInternals.PlainTopItemTotalityContract)
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file)
    (error : ParserInvariantError) :
    parseLexed file lexed ≠ .error error :=
  parseLexed_ne_error_of_validFor
    (FileInternals.parseItemsItemInvariantFree_of_plainTopItemContract contract)
    file lexed lexedValid error

/-- Public source parsing succeeds under exactly the seven branch inputs. -/
theorem parse_exists_ok_of_plainTopItemContract
    (contract : FileInternals.PlainTopItemTotalityContract)
    (file : SourceFile) :
    ∃ output, parse file = .ok output :=
  parse_exists_ok
    (FileInternals.parseItemsItemInvariantFree_of_plainTopItemContract contract)
    file

/-- Public source parsing exposes no invariant error under those inputs. -/
theorem parse_ne_error_of_plainTopItemContract
    (contract : FileInternals.PlainTopItemTotalityContract)
    (file : SourceFile) (error : SyntaxInvariantError) :
    parse file ≠ .error error :=
  parse_ne_error
    (FileInternals.parseItemsItemInvariantFree_of_plainTopItemContract contract)
    file error

end Solcore.Syntax.Parser
