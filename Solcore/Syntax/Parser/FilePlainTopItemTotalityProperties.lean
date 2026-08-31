import Solcore.Syntax.Parser.FilePlainTopItemProperties
import Solcore.Syntax.Parser.ExportCanonicalTotalityProperties
import Solcore.Syntax.Parser.ImportTotalityProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PragmaTotalityProperties
import Solcore.Syntax.Parser.TypeAliasTotalityProperties

/-! Conditional invariant freedom for top-level declaration dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Mapping a successful value cannot introduce an invariant reply. -/
theorem mapTopItem_invariantFreeOnValid {alpha : Type}
    {parser : Parser alpha} (wrap : alpha → TopItem)
    (invariantFree : Parser.InvariantFreeOnValid parser) :
    Parser.InvariantFreeOnValid (mapTopItem parser wrap) := by
  intro input inputValid
  rcases invariantFree input inputValid with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨wrap value, next, by
      unfold mapTopItem
      simp only [result]⟩
  · exact Or.inr ⟨failure, next, by
      unfold mapTopItem
      simp only [result]⟩

/-- The five declaration parsers whose totality remains an explicit input. -/
structure PlainTopItemTotalityContract : Prop where
  moduleFunction : Parser.InvariantFreeOnValid (functionDecl .module)
  enumDecl : Parser.InvariantFreeOnValid (enumDecl none)
  traitDecl : Parser.InvariantFreeOnValid traitDecl
  implDecl : Parser.InvariantFreeOnValid implDecl
  contractDecl : Parser.InvariantFreeOnValid contractDecl

/--
All declaration branches compose in implementation order. Pragma totality and
the terminal top-item rejection are discharged internally.
-/
theorem plainTopItem_invariantFreeOnValid
    (contract : PlainTopItemTotalityContract) :
    Parser.InvariantFreeOnValid plainTopItem := by
  intro input inputValid
  unfold plainTopItem
  split
  · exact (mapTopItem_invariantFreeOnValid wrapImport
      importDecl_invariantFreeOnValid) input inputValid
  · split
    · exact (mapTopItem_invariantFreeOnValid wrapExport
        exportDecl_invariantFreeOnValid) input inputValid
    · split
      · exact (mapTopItem_invariantFreeOnValid wrapPragma
          (fun state _stateValid => pragmaDecl_ordinary state))
          input inputValid
      · split
        · exact (mapTopItem_invariantFreeOnValid wrapTypeAlias
            typeAlias_invariantFreeOnValid) input inputValid
        · split
          · exact (mapTopItem_invariantFreeOnValid wrapFunction
              contract.moduleFunction) input inputValid
          · split
            · exact (mapTopItem_invariantFreeOnValid wrapEnum
                contract.enumDecl) input inputValid
            · split
              · exact (mapTopItem_invariantFreeOnValid wrapTrait
                  contract.traitDecl) input inputValid
              · split
                · exact (mapTopItem_invariantFreeOnValid wrapImpl
                    contract.implDecl) input inputValid
                · split
                  · exact (mapTopItem_invariantFreeOnValid wrapContract
                      contract.contractDecl) input inputValid
                  · exact (Parser.rejectAt_invariantFreeOnValid
                      (alpha := TopItem)
                      { head := .topItem, tail := [] } .topItem)
                      input inputValid

/-- Conditional plain dispatch cannot expose an invariant on valid input. -/
theorem plainTopItem_ne_invariant
    (contract : PlainTopItemTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    plainTopItem input ≠ .invariant error :=
  (plainTopItem_invariantFreeOnValid contract).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.FileInternals
