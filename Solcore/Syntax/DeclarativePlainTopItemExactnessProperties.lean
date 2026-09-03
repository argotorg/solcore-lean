import Solcore.Syntax.DeclarativeCoreDeclarationExactnessProperties
import Solcore.Syntax.DeclarativeEnumDeclarationExactnessProperties
import Solcore.Syntax.DeclarativePlainTopItemOutcomeProperties
import Solcore.Syntax.DeclarativePragmaExactnessProperties
import Solcore.Syntax.DeclarativeTraitDeclarationExactnessProperties

/-! Exact prioritized top-item dispatch from its remaining module declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact import/export declarations close the remaining plain-item AST cases. -/
theorem PlainTopItemOrdinaryParses.value_unique_of_moduleDeclarations
    (importOutcomes : ExactDeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects)
    (exportOutcomes : ExactDeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects)
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : PlainTopItemOrdinaryParses input left afterLeft)
    (rightParsed : PlainTopItemOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed
  all_goals
    rename_i leftDeclaration leftSelected leftChild rightDeclaration rightSelected rightChild
    cases leftSelected.unique rightSelected
  all_goals first
    | have valueEq := importOutcomes.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := exportOutcomes.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := pragmaDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := typeAliasDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := functionDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := (enumDeclExactOutcomeSpec none).successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := traitDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := implDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl
    | have valueEq := contractDeclExactOutcomeSpec.successValueUnique leftChild rightChild
      cases valueEq
      rfl

/-- Selected leaf failure fixes its endpoint; an unrecognized item rewinds. -/
theorem PlainTopItemRejects.output_unique_of_moduleDeclarations
    (importOutcomes : ExactDeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects)
    (exportOutcomes : ExactDeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects)
    {input left right : Remainder}
    (leftRejected : PlainTopItemRejects input left)
    (rightRejected : PlainTopItemRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected
  all_goals first
    | rename_i leftSelected leftChild rightSelected rightChild
      cases leftSelected.unique rightSelected
    | rename_i leftSelected leftChild rightSelected
      cases leftSelected.unique rightSelected
    | rename_i leftSelected rightSelected rightChild
      cases leftSelected.unique rightSelected
    | rfl
  all_goals first
    | exact importOutcomes.rejectOutputUnique (by assumption) (by assumption)
    | exact exportOutcomes.rejectOutputUnique (by assumption) (by assumption)
    | exact pragmaDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact typeAliasDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact functionDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact (enumDeclExactOutcomeSpec none).rejectOutputUnique (by assumption) (by assumption)
    | exact traitDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact implDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)
    | exact contractDeclExactOutcomeSpec.rejectOutputUnique (by assumption) (by assumption)

/-- The exact plain dispatcher needs only the two remaining module contracts. -/
theorem plainTopItemExactOutcomeSpecOfModuleDeclarations
    (importOutcomes : ExactDeterministicOutcomeSpec ImportDeclOrdinaryParses ImportDeclRejects)
    (exportOutcomes : ExactDeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects) :
    ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects where
  toDeterministicOutcomeSpec := plainTopItemDeterministicOutcomeSpec
  successValueUnique :=
    PlainTopItemOrdinaryParses.value_unique_of_moduleDeclarations importOutcomes exportOutcomes
  rejectOutputUnique :=
    PlainTopItemRejects.output_unique_of_moduleDeclarations importOutcomes exportOutcomes

end Solcore.Syntax.DeclarativeGrammar
