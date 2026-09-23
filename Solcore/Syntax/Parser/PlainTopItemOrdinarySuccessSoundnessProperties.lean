import Solcore.Syntax.Parser.ContractDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.ExportDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Impl
import Solcore.Syntax.Parser.ImportDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PlainTopItemOutcomePrimitiveProperties
import Solcore.Syntax.Parser.PragmaDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Trait
import Solcore.Syntax.Parser.TypeAlias

/-! Broad executable success reflection for the plain top-item dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every executable plain-top-item success follows the exact selected broad
declaration outcome. -/
theorem plainTopItem_success_ordinaryOutcome_sound
    {input output : State} {item : TopItem}
    (result : plainTopItem input = .ok item output) :
    DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold plainTopItem at result
  split at result
  next startsImport =>
    rcases mapTopItem_success_components result with
      ⟨declaration, declarationResult, rfl⟩
    exact .importDecl
      (plainTopItemImportBranchSelected startsImport)
      (importDecl_ordinaryOutcome_sound.1 declarationResult)
  next importAbsent =>
    have importAbsentEq := Bool.eq_false_iff.mpr importAbsent
    split at result
    next startsExport =>
      rcases mapTopItem_success_components result with
        ⟨declaration, declarationResult, rfl⟩
      exact .exportDecl
        (plainTopItemExportBranchSelected importAbsentEq startsExport)
        (exportDecl_ordinaryOutcome_sound.1 declarationResult)
    next exportAbsent =>
      have exportAbsentEq := Bool.eq_false_iff.mpr exportAbsent
      split at result
      next startsPragma =>
        rcases mapTopItem_success_components result with
          ⟨declaration, declarationResult, rfl⟩
        exact .pragmaDecl
          (plainTopItemPragmaBranchSelected importAbsentEq exportAbsentEq
            startsPragma)
          (pragmaDecl_ordinaryOutcome_sound.1 declarationResult)
      next pragmaAbsent =>
        have pragmaAbsentEq := Bool.eq_false_iff.mpr pragmaAbsent
        split at result
        next startsType =>
          rcases mapTopItem_success_components result with
            ⟨declaration, declarationResult, rfl⟩
          exact .typeAlias
            (plainTopItemTypeAliasBranchSelected importAbsentEq exportAbsentEq
              pragmaAbsentEq startsType)
            (typeAlias_ordinaryOutcome_sound.1 declarationResult)
        next typeAbsent =>
          have typeAbsentEq := Bool.eq_false_iff.mpr typeAbsent
          split at result
          next startsFunction =>
            rcases mapTopItem_success_components result with
              ⟨declaration, declarationResult, rfl⟩
            exact .functionDecl
              (plainTopItemFunctionBranchSelected importAbsentEq
                exportAbsentEq pragmaAbsentEq typeAbsentEq startsFunction)
              ((functionDecl_ordinaryOutcome_sound .module).1
                declarationResult)
          next functionAbsent =>
            have functionAbsentEq := Bool.eq_false_iff.mpr functionAbsent
            split at result
            next startsEnum =>
              rcases mapTopItem_success_components result with
                ⟨declaration, declarationResult, rfl⟩
              exact .enumDecl
                (plainTopItemEnumBranchSelected importAbsentEq exportAbsentEq
                  pragmaAbsentEq typeAbsentEq functionAbsentEq startsEnum)
                ((enumDecl_ordinaryOutcome_sound none).1 declarationResult)
            next enumAbsent =>
              have enumAbsentEq := Bool.eq_false_iff.mpr enumAbsent
              split at result
              next startsTrait =>
                rcases mapTopItem_success_components result with
                  ⟨declaration, declarationResult, rfl⟩
                exact .traitDecl
                  (plainTopItemTraitBranchSelected importAbsentEq
                    exportAbsentEq pragmaAbsentEq typeAbsentEq
                    functionAbsentEq enumAbsentEq startsTrait)
                  (traitDecl_ordinaryOutcome_sound.1 declarationResult)
              next traitAbsent =>
                have traitAbsentEq := Bool.eq_false_iff.mpr traitAbsent
                split at result
                next startsImpl =>
                  rcases mapTopItem_success_components result with
                    ⟨declaration, declarationResult, rfl⟩
                  exact .implDecl
                    (plainTopItemImplBranchSelected importAbsentEq
                      exportAbsentEq pragmaAbsentEq typeAbsentEq
                      functionAbsentEq enumAbsentEq traitAbsentEq startsImpl)
                    (implDecl_ordinaryOutcome_sound.1 declarationResult)
                next implAbsent =>
                  have implAbsentEq := Bool.eq_false_iff.mpr implAbsent
                  split at result
                  next startsContract =>
                    rcases mapTopItem_success_components result with
                      ⟨declaration, declarationResult, rfl⟩
                    exact .contractDecl
                      (plainTopItemContractBranchSelected importAbsentEq
                        exportAbsentEq pragmaAbsentEq typeAbsentEq
                        functionAbsentEq enumAbsentEq traitAbsentEq
                        implAbsentEq startsContract)
                      (contractDecl_ordinaryOutcome_sound.1 declarationResult)
                  next contractAbsent =>
                    simp [rejectAt] at result

end Solcore.Syntax.Parser.FileInternals
