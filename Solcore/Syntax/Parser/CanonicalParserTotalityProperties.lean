import Solcore.Syntax.Parser.ContractDeclarationTotalityProperties
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.FileItemTotalityProperties
import Solcore.Syntax.Parser.FunctionDeclarationTotalityProperties
import Solcore.Syntax.Parser.Impl
import Solcore.Syntax.Parser.Trait

/-! Unconditional totality from canonical top-item dispatch to public parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every production declaration branch is invariant-free on valid input. -/
theorem productionPlainTopItemTotalityContract :
    PlainTopItemTotalityContract := {
  moduleFunction := functionDecl_invariantFreeOnValid .module
  enumDecl := enumDecl_invariantFreeOnValid none
  traitDecl := traitDecl_invariantFreeOnValid
  implDecl := implDecl_invariantFreeOnValid
  contractDecl := contractDecl_invariantFreeOnValid
}

/-- Plain canonical top-item dispatch has only ordinary outcomes. -/
theorem productionPlainTopItem_invariantFreeOnValid :
    Parser.InvariantFreeOnValid plainTopItem :=
  plainTopItem_invariantFreeOnValid productionPlainTopItemTotalityContract

theorem productionPlainTopItem_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ item next, plainTopItem input = .ok item next) ∨
      (∃ failure next, plainTopItem input = .reject failure next) :=
  productionPlainTopItem_invariantFreeOnValid input inputValid

theorem productionPlainTopItem_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    plainTopItem input ≠ .invariant error :=
  productionPlainTopItem_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- Derive-aware canonical top-item dispatch has only ordinary outcomes. -/
theorem productionTopItem_invariantFreeOnValid :
    Parser.InvariantFreeOnValid topItem :=
  topItem_invariantFreeOnValid productionPlainTopItemTotalityContract

theorem productionTopItem_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ item next, topItem input = .ok item next) ∨
      (∃ failure next, topItem input = .reject failure next) :=
  productionTopItem_invariantFreeOnValid input inputValid

theorem productionTopItem_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    topItem input ≠ .invariant error :=
  productionTopItem_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- The concrete file-loop item parser is invariant-free on valid input. -/
theorem productionParseItemsItem_invariantFreeOnValid :
    Parser.InvariantFreeOnValid parseItemsItem :=
  parseItemsItem_invariantFreeOnValid productionPlainTopItemTotalityContract

theorem productionParseItemsItem_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ item next, parseItemsItem input = .ok item next) ∨
      (∃ failure next, parseItemsItem input = .reject failure next) :=
  productionParseItemsItem_invariantFreeOnValid input inputValid

theorem productionParseItemsItem_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseItemsItem input ≠ .invariant error :=
  productionParseItemsItem_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- The concrete item theorem discharges the complete-file loop premise. -/
theorem productionParseItemsItemInvariantFree :
    ParseItemsItemInvariantFree :=
  parseItemsItemInvariantFree_of_plainTopItemContract
    productionPlainTopItemTotalityContract

/-- A complete canonical source-file parser always succeeds on valid state. -/
theorem productionSourceFile_exists_ok
    (comments : List Comment) (input : State) (inputValid : input.ValidFor) :
    ∃ parsed final, sourceFile comments input = .ok parsed final :=
  sourceFile_exists_ok_of_plainTopItemContract
    productionPlainTopItemTotalityContract comments input inputValid

theorem productionSourceFile_invariantFreeOnValid
    (comments : List Comment) :
    Parser.InvariantFreeOnValid (sourceFile comments) := by
  intro input inputValid
  exact Or.inl
    (productionSourceFile_exists_ok comments input inputValid)

theorem productionSourceFile_ordinary
    (comments : List Comment) (input : State) (inputValid : input.ValidFor) :
    (∃ parsed final, sourceFile comments input = .ok parsed final) ∨
      (∃ failure final,
        sourceFile comments input = .reject failure final) :=
  productionSourceFile_invariantFreeOnValid comments input inputValid

theorem productionSourceFile_ne_invariant
    (comments : List Comment) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    sourceFile comments input ≠ .invariant error :=
  (productionSourceFile_invariantFreeOnValid comments).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.FileInternals

namespace Solcore.Syntax.Parser

/-- Valid already-tokenized input always produces a parse output. -/
theorem productionParseLexed_exists_ok
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file) :
    ∃ output, parseLexed file lexed = .ok output :=
  parseLexed_exists_ok_of_plainTopItemContract
    FileInternals.productionPlainTopItemTotalityContract
    file lexed lexedValid

/-- No parser invariant escapes valid already-tokenized input. -/
theorem productionParseLexed_ne_error
    (file : SourceFile) (lexed : LexedFile) (lexedValid : lexed.ValidFor file)
    (error : ParserInvariantError) :
    parseLexed file lexed ≠ .error error :=
  parseLexed_ne_error_of_plainTopItemContract
    FileInternals.productionPlainTopItemTotalityContract
    file lexed lexedValid error

/-- Public parsing returns a parse output for every source file. -/
theorem productionParse_exists_ok (file : SourceFile) :
    ∃ output, parse file = .ok output :=
  parse_exists_ok_of_plainTopItemContract
    FileInternals.productionPlainTopItemTotalityContract file

/-- Public parsing cannot expose an internal syntax invariant error. -/
theorem productionParse_ne_error
    (file : SourceFile) (error : SyntaxInvariantError) :
    parse file ≠ .error error :=
  parse_ne_error_of_plainTopItemContract
    FileInternals.productionPlainTopItemTotalityContract file error

end Solcore.Syntax.Parser
