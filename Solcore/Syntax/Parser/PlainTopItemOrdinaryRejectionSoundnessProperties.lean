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

/-! Exact rejection reflection for broad attribute-free top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every executable plain-top-item rejection records the exact selected child
rejection, or the final nonconsuming unrecognized branch. -/
theorem plainTopItem_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : plainTopItem input = .reject failure rejected) :
    DeclarativeGrammar.PlainTopItemRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold plainTopItem at result
  split at result
  next startsImport =>
    exact .importRejected
      (plainTopItemImportBranchSelected startsImport)
      (importDecl_ordinaryOutcome_sound.2
        (mapTopItem_reject_result result))
  next importAbsent =>
    have importAbsentEq : isKeyword input .importKw = false :=
      Bool.eq_false_iff.mpr importAbsent
    split at result
    next startsExport =>
      exact .exportRejected
        (plainTopItemExportBranchSelected importAbsentEq startsExport)
        (exportDecl_ordinaryOutcome_sound.2
          (mapTopItem_reject_result result))
    next exportAbsent =>
      have exportAbsentEq : isKeyword input .exportKw = false :=
        Bool.eq_false_iff.mpr exportAbsent
      split at result
      next startsPragma =>
        exact .pragmaRejected
          (plainTopItemPragmaBranchSelected importAbsentEq exportAbsentEq
            startsPragma)
          (pragmaDecl_ordinaryOutcome_sound.2
            (mapTopItem_reject_result result))
      next pragmaAbsent =>
        have pragmaAbsentEq : isKeyword input .pragmaKw = false :=
          Bool.eq_false_iff.mpr pragmaAbsent
        split at result
        next startsType =>
          exact .typeAliasRejected
            (plainTopItemTypeAliasBranchSelected importAbsentEq exportAbsentEq
              pragmaAbsentEq startsType)
            (typeAlias_ordinaryOutcome_sound.2
              (mapTopItem_reject_result result))
        next typeAbsent =>
          have typeAbsentEq : isKeyword input .typeKw = false :=
            Bool.eq_false_iff.mpr typeAbsent
          split at result
          next startsFunction =>
            exact .functionRejected
              (plainTopItemFunctionBranchSelected importAbsentEq exportAbsentEq
                pragmaAbsentEq typeAbsentEq startsFunction)
              ((functionDecl_ordinaryOutcome_sound .module).2
                (mapTopItem_reject_result result))
          next functionAbsent =>
            have functionAbsentEq : isKeyword input .functionKw = false :=
              Bool.eq_false_iff.mpr functionAbsent
            split at result
            next startsEnum =>
              exact .enumRejected
                (plainTopItemEnumBranchSelected importAbsentEq exportAbsentEq
                  pragmaAbsentEq typeAbsentEq functionAbsentEq startsEnum)
                ((enumDecl_ordinaryOutcome_sound none).2
                  (mapTopItem_reject_result result))
            next enumAbsent =>
              have enumAbsentEq : isContextual input .enum = false :=
                Bool.eq_false_iff.mpr enumAbsent
              split at result
              next startsTrait =>
                exact .traitRejected
                  (plainTopItemTraitBranchSelected importAbsentEq exportAbsentEq
                    pragmaAbsentEq typeAbsentEq functionAbsentEq enumAbsentEq
                    startsTrait)
                  (traitDecl_ordinaryOutcome_sound.2
                    (mapTopItem_reject_result result))
              next traitAbsent =>
                have traitAbsentEq : isContextual input .trait = false :=
                  Bool.eq_false_iff.mpr traitAbsent
                split at result
                next startsImpl =>
                  exact .implRejected
                    (plainTopItemImplBranchSelected importAbsentEq exportAbsentEq
                      pragmaAbsentEq typeAbsentEq functionAbsentEq enumAbsentEq
                      traitAbsentEq startsImpl)
                    (implDecl_ordinaryOutcome_sound.2
                      (mapTopItem_reject_result result))
                next implAbsent =>
                  have implAbsentEq :
                      (isContextual input .impl ||
                        isKeyword input .defaultKw) = false :=
                    Bool.eq_false_iff.mpr implAbsent
                  split at result
                  next startsContract =>
                    exact .contractRejected
                      (plainTopItemContractBranchSelected importAbsentEq
                        exportAbsentEq pragmaAbsentEq typeAbsentEq
                        functionAbsentEq enumAbsentEq traitAbsentEq implAbsentEq
                        startsContract)
                      (contractDecl_ordinaryOutcome_sound.2
                        (mapTopItem_reject_result result))
                  next contractAbsent =>
                    have contractAbsentEq :
                        isKeyword input .contractKw = false :=
                      Bool.eq_false_iff.mpr contractAbsent
                    rw [plainTopItemRejectAt_rejected_state_eq result]
                    exact .unrecognized
                      (plainTopItemUnrecognizedBranchSelected importAbsentEq
                        exportAbsentEq pragmaAbsentEq typeAbsentEq
                        functionAbsentEq enumAbsentEq traitAbsentEq implAbsentEq
                        contractAbsentEq)

end Solcore.Syntax.Parser.FileInternals
