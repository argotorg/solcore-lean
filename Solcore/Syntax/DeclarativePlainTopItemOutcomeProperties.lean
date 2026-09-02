import Solcore.Syntax.DeclarativeContractDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeExportDeclOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeImplDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeImportDeclOutcomeProperties
import Solcore.Syntax.DeclarativePlainTopItemOutcomeGrammar
import Solcore.Syntax.DeclarativePragmaOutcomeProperties
import Solcore.Syntax.DeclarativeTraitDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeTypeAliasOutcomeProperties

/-! Deterministic exact broad outcomes for plain top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive and prior-negative guards select at most one dispatcher
branch. -/
theorem PlainTopItemBranchSelected.unique
    {input : Remainder} {left right : PlainTopItemBranch}
    (leftSelected : PlainTopItemBranchSelected input left)
    (rightSelected : PlainTopItemBranchSelected input right) :
    left = right := by
  cases leftSelected <;> cases rightSelected <;>
    simp_all [PlainTopItemTokenPresentAt, TokenKindAbsentAt]

/-- Broad plain-top-item success has one final remainder. -/
theorem PlainTopItemOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : PlainTopItemOrdinaryParses input left afterLeft)
    (rightParsed : PlainTopItemOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed <;> cases rightParsed
  all_goals
    rename_i leftDeclaration leftSelected leftChild rightDeclaration
      rightSelected rightChild
    cases leftSelected.unique rightSelected
  all_goals first
    | exact ImportDeclOrdinaryParses.output_unique (by assumption)
        (by assumption)
    | exact ExportDeclOrdinaryParses.output_unique (by assumption)
        (by assumption)
    | exact PragmaDeclOrdinaryParses.output_unique (by assumption)
        (by assumption)
    | exact TypeAliasDeclOrdinaryParses.output_unique (by assumption)
        (by assumption)
    | exact FunctionDeclOrdinaryParses.output_unique (by assumption)
        (by assumption)
    | exact EnumDeclOrdinaryParses.output_unique none (by assumption)
        (by assumption)
    | exact TraitDeclOrdinaryParses.output_unique (by assumption)
        (by assumption)
    | exact ImplDeclOrdinaryParses.output_unique (by assumption)
        (by assumption)
    | exact ContractDeclOrdinaryParses.output_unique (by assumption)
        (by assumption)

/-- Exact selected-branch rejection excludes every broad plain success. -/
theorem PlainTopItemRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : PlainTopItemRejects input rejected) :
    ¬ ∃ item output, PlainTopItemOrdinaryParses input item output := by
  rintro ⟨item, output, successful⟩
  cases rejection <;> cases successful
  all_goals first
    | rename_i rejectedSelected rejectedChild declaration successfulSelected
        successfulChild
      cases rejectedSelected.unique successfulSelected
    | rename_i rejectedSelected declaration successfulSelected successfulChild
      cases rejectedSelected.unique successfulSelected
  all_goals first
    | exact importDeclDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact exportDeclDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact pragmaDeclDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact typeAliasDeclDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact functionDeclDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact (enumDeclDeterministicOutcomeSpec none).successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact traitDeclDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact implDeclDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact contractDeclDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩

/-- Plain top-item dispatch has deterministic and exclusive broad outcomes. -/
theorem plainTopItemDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PlainTopItemOrdinaryParses
      PlainTopItemRejects where
  successOutputUnique := PlainTopItemOrdinaryParses.output_unique
  successRejectDisjoint := PlainTopItemRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
