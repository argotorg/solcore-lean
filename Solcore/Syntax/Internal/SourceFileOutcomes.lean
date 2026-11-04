import Solcore.Syntax.Internal.ContractBodyOutcomes
import Solcore.Syntax.Internal.ContractMemberOutcomes
import Solcore.Syntax.Internal.ExportOutcomes
import Solcore.Syntax.Internal.ImportOutcomes
import Solcore.Syntax.Grammar.SourceFile
import Solcore.Syntax.Internal.DeriveOutcomes
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.DelimitedOutcomes

/-!
Properties of the declarative grammar of top items, file items, nesting and lexed
validation: outcomes are deterministic, and successful values and rejection points are
unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativePlainTopItemOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTopItemDeriveAttachmentProperties
/-! Functional and total laws for pure top-item derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Attaching one derive attribute to one top-level item has one exact AST
result. -/
theorem TopItemDeriveAttaches.output_unique
    {derive : Syntax.DeriveAttribute} {item left right : Syntax.TopItem}
    (leftAttached : TopItemDeriveAttaches derive item left)
    (rightAttached : TopItemDeriveAttaches derive item right) :
    left = right := by
  cases leftAttached <;> cases rightAttached <;> rfl

/-- Every top-level item variant has an exact derive-attachment result. -/
theorem TopItemDeriveAttaches.exists
    (derive : Syntax.DeriveAttribute) (item : Syntax.TopItem) :
    ∃ output, TopItemDeriveAttaches derive item output := by
  rcases item with ⟨itemSpan, leadingComments, value⟩
  cases value with
  | importDecl declaration => exact ⟨_, .importDecl⟩
  | exportDecl declaration => exact ⟨_, .exportDecl⟩
  | pragmaDecl declaration => exact ⟨_, .pragmaDecl⟩
  | typeAlias declaration => exact ⟨_, .typeAlias⟩
  | enum declaration => exact ⟨_, .enum⟩
  | trait declaration => exact ⟨_, .trait⟩
  | impl declaration => exact ⟨_, .impl⟩
  | contract declaration => exact ⟨_, .contract⟩
  | function declaration => exact ⟨_, .function⟩
  | error => exact ⟨_, .error⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTopItemOutcomeProperties
/-! Deterministic broad ordinary outcomes for public top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {input : Remainder} {kind : TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : PlainTopItemTokenPresentAt input kind) : False := by
  unfold PlainTopItemTokenPresentAt at present
  exact absent present

/-- Public top-item success has one final remainder. -/
theorem TopItemOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemOrdinaryParses input left afterLeft)
    (rightParsed : TopItemOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | plain leftHashAbsent leftPlainParsed =>
      cases rightParsed with
      | plain rightHashAbsent rightPlainParsed =>
          exact plainTopItemDeterministicOutcomeSpec.successOutputUnique
            leftPlainParsed rightPlainParsed
      | derived rightHashPresent rightDeriveParsed rightPlainParsed
          rightAttached =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHashPresent)
  | derived leftHashPresent leftDeriveParsed leftPlainParsed leftAttached =>
      cases rightParsed with
      | plain rightHashAbsent rightPlainParsed =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHashPresent)
      | derived rightHashPresent rightDeriveParsed rightPlainParsed
          rightAttached =>
          have afterDeriveEq :=
            deriveAttributeDeterministicOutcomeSpec.successOutputUnique
              leftDeriveParsed rightDeriveParsed
          cases afterDeriveEq
          exact plainTopItemDeterministicOutcomeSpec.successOutputUnique
            leftPlainParsed rightPlainParsed

/-- Every exact public top-item rejection excludes plain and derive-prefixed
success. -/
theorem TopItemRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : TopItemRejects input rejected) :
    ¬ ∃ item output, TopItemOrdinaryParses input item output := by
  rintro ⟨item, output, successful⟩
  cases rejection with
  | plainRejected rejectedHashAbsent plainRejected =>
      cases successful with
      | plain successfulHashAbsent plainParsed =>
          exact plainTopItemDeterministicOutcomeSpec.successRejectDisjoint
            plainRejected ⟨_, _, plainParsed⟩
      | derived successfulHashPresent deriveParsed plainParsed attached =>
          exact absent_conflicts_token rejectedHashAbsent
            successfulHashPresent
  | deriveRejected rejectedHashPresent deriveRejected =>
      cases successful with
      | plain successfulHashAbsent plainParsed =>
          exact absent_conflicts_token successfulHashAbsent
            rejectedHashPresent
      | derived successfulHashPresent deriveParsed plainParsed attached =>
          exact deriveAttributeDeterministicOutcomeSpec.successRejectDisjoint
            deriveRejected ⟨_, _, deriveParsed⟩
  | derivedPlainRejected rejectedHashPresent rejectedDeriveParsed
      plainRejected =>
      cases successful with
      | plain successfulHashAbsent plainParsed =>
          exact absent_conflicts_token successfulHashAbsent
            rejectedHashPresent
      | derived successfulHashPresent successfulDeriveParsed plainParsed
          attached =>
          have afterDeriveEq :=
            deriveAttributeDeterministicOutcomeSpec.successOutputUnique
              rejectedDeriveParsed successfulDeriveParsed
          cases afterDeriveEq
          exact plainTopItemDeterministicOutcomeSpec.successRejectDisjoint
            plainRejected ⟨_, _, plainParsed⟩

/-- Public top-item outcomes have deterministic successful remainders and
exact rejection/success exclusion. -/
theorem topItemDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TopItemOrdinaryParses TopItemRejects where
  successOutputUnique := TopItemOrdinaryParses.output_unique
  successRejectDisjoint := TopItemRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTopItemExactnessProperties
/-! Exact top-item outcomes transported through leading derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact plain items and derive attributes fix the complete attached item AST. -/
theorem TopItemOrdinaryParses.value_unique_of_plain
    (plainOutcomes : ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects)
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemOrdinaryParses input left afterLeft)
    (rightParsed : TopItemOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | plain absent leftPlain =>
      cases rightParsed with
      | plain _ rightPlain => exact plainOutcomes.successValueUnique leftPlain rightPlain
      | derived present _ _ _ => exact False.elim (absent present)
  | derived present leftDerive leftPlain leftAttached =>
      cases rightParsed with
      | plain absent _ => exact False.elim (absent present)
      | derived _ rightDerive rightPlain rightAttached =>
          rcases deriveAttributeExactOutcomeSpec.successResultUnique leftDerive rightDerive with
            ⟨deriveEq, inputEq⟩
          subst deriveEq
          subst inputEq
          have valueEq := plainOutcomes.successValueUnique leftPlain rightPlain
          subst valueEq
          exact leftAttached.output_unique rightAttached

/-- The committed derive/plain branch determines the first rejecting endpoint. -/
theorem TopItemRejects.output_unique_of_plain
    (plainOutcomes : ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects)
    {input left right : Remainder}
    (leftRejected : TopItemRejects input left)
    (rightRejected : TopItemRejects input right) : left = right := by
  cases leftRejected with
  | plainRejected absent leftPlain =>
      cases rightRejected with
      | plainRejected _ rightPlain => exact plainOutcomes.rejectOutputUnique leftPlain rightPlain
      | deriveRejected present _ => exact False.elim (absent present)
      | derivedPlainRejected present _ _ => exact False.elim (absent present)
  | deriveRejected present leftDerive =>
      cases rightRejected with
      | plainRejected absent _ => exact False.elim (absent present)
      | deriveRejected _ rightDerive =>
          exact deriveAttributeExactOutcomeSpec.rejectOutputUnique leftDerive rightDerive
      | derivedPlainRejected _ rightDerive _ =>
          exact False.elim (deriveAttributeExactOutcomeSpec.successRejectDisjoint
            leftDerive ⟨_, _, rightDerive⟩)
  | derivedPlainRejected present leftDerive leftPlain =>
      cases rightRejected with
      | plainRejected absent _ => exact False.elim (absent present)
      | deriveRejected _ rightDerive =>
          exact False.elim (deriveAttributeExactOutcomeSpec.successRejectDisjoint
            rightDerive ⟨_, _, leftDerive⟩)
      | derivedPlainRejected _ rightDerive rightPlain =>
          have inputEq := deriveAttributeExactOutcomeSpec.successOutputUnique
            leftDerive rightDerive
          subst inputEq
          exact plainOutcomes.rejectOutputUnique leftPlain rightPlain

/-- Exact plain top-items lift through derive priority and pure attachment. -/
theorem topItemExactOutcomeSpecOfPlain
    (plainOutcomes : ExactDeterministicOutcomeSpec PlainTopItemOrdinaryParses PlainTopItemRejects) :
    ExactDeterministicOutcomeSpec TopItemOrdinaryParses TopItemRejects where
  toDeterministicOutcomeSpec := topItemDeterministicOutcomeSpec
  successValueUnique := TopItemOrdinaryParses.value_unique_of_plain plainOutcomes
  rejectOutputUnique := TopItemRejects.output_unique_of_plain plainOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTopItemRecoveryOutcomeProperties
/-! Functionality and outcome exclusion for top-item recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- A top-item recovery scan has one final remainder. -/
theorem TopItemRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.TopItem} {afterLeft afterRight : Remainder},
      TopItemRecoveryScanParses first leftLast input left afterLeft →
      TopItemRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- Complete ordinary top-item recovery has one final remainder. -/
theorem TopItemRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryParses input left afterLeft)
    (rightParsed : TopItemRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every top-item recovery rejection is non-consuming. -/
theorem TopItemRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : TopItemRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- An unavailable mandatory first token excludes every recovery success. -/
theorem TopItemRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : TopItemRecoveryRejects input rejected) :
    ¬ ∃ item output, TopItemRecoveryParses input item output := by
  rintro ⟨item, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd => exact Nat.not_lt_of_ge atEnd current.1
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Deterministic ordinary outcome contract for top-item recovery. -/
theorem topItemRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TopItemRecoveryParses
      TopItemRecoveryRejects where
  successOutputUnique := TopItemRecoveryParses.output_unique
  successRejectDisjoint := TopItemRecoveryRejects.disjointParses

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTopItemRecoveryExactnessProperties
/-! Exact recovery values and endpoints for top-level source-file items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- With the same first and last consumed spans, a recovery scan fixes its
error item and final remainder. -/
theorem TopItemRecoveryScanParses.result_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.TopItem} {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryScanParses first last input left afterLeft)
    (rightParsed : TopItemRecoveryScanParses first last input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      cases rightParsed with
      | stop => exact ⟨rfl, rfl⟩
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail ih =>
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have tokenEq := leftCurrent.token_unique rightCurrent
          cases tokenEq
          exact ih rightTail

/-- A recovery scan at fixed span history has one exact error-item AST. -/
theorem TopItemRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.TopItem} {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryScanParses first last input left afterLeft)
    (rightParsed : TopItemRecoveryScanParses first last input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- The mandatory first token fixes the initial spans; complete recovery fixes
both its exact error item and final remainder. -/
theorem TopItemRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryParses input left afterLeft)
    (rightParsed : TopItemRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have tokenEq := leftCurrent.token_unique rightCurrent
          cases tokenEq
          exact leftScan.result_unique rightScan

/-- Complete top-item recovery fixes its full error-item AST. -/
theorem TopItemRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryParses input left afterLeft)
    (rightParsed : TopItemRecoveryParses input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- Every recovery rejection selects the same original input endpoint. -/
theorem TopItemRecoveryRejects.output_unique {input left right : Remainder}
    (leftRejected : TopItemRecoveryRejects input left)
    (rightRejected : TopItemRecoveryRejects input right) : left = right :=
  leftRejected.output_eq.trans rightRejected.output_eq.symm

/-- Top-item recovery has unconditional exact ordinary outcomes. -/
theorem topItemRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TopItemRecoveryParses TopItemRecoveryRejects where
  toDeterministicOutcomeSpec := topItemRecoveryDeterministicOutcomeSpec
  successValueUnique := TopItemRecoveryParses.value_unique
  rejectOutputUnique := TopItemRecoveryRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFileItemsOutcomeProperties
/-! Deterministic broad outcomes for the recovery-aware file-item loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Preserved carrier and window evidence makes the file-loop rewind exact. -/
theorem TopItemRejectsWithPreservedWindow.exists_rewind_eq
    {input : Remainder}
    (rejected : TopItemRejectsWithPreservedWindow input) :
    ∃ failed, TopItemRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- A window-preserving top-item rejection excludes every broad top-item
success from the same input. -/
theorem TopItemRejectsWithPreservedWindow.disjointOrdinary
    {input : Remainder}
    (rejected : TopItemRejectsWithPreservedWindow input) :
    ¬ ∃ item output, TopItemOrdinaryParses input item output := by
  rintro ⟨item, output, parsed⟩
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  exact topItemDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨_, _, parsed⟩

/-- A forward file-item suffix has one final remainder. -/
theorem FileItemsOrdinaryParses.output_unique
    {input : Remainder} {leftItems rightItems : List Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : FileItemsOrdinaryParses input leftItems afterLeft)
    (rightParsed : FileItemsOrdinaryParses input rightItems afterRight) :
    afterLeft = afterRight := by
  induction leftParsed generalizing rightItems afterRight with
  | done leftAtEnd =>
      cases rightParsed with
      | done => rfl
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim
            (Nat.not_lt_of_ge leftAtEnd rightInside)
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim
            (Nat.not_lt_of_ge leftAtEnd rightInside)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim
            (Nat.not_lt_of_ge leftAtEnd rightInside)
  | direct leftInside leftItem leftProgress leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim
            (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          have afterItemEq :=
            topItemDeterministicOutcomeSpec.successOutputUnique
              leftItem rightItem
          cases afterItemEq
          exact inductionHypothesis rightTail
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim
            (rightRejected.disjointOrdinary ⟨_, _, leftItem⟩)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim
            (rightRejected.disjointOrdinary ⟨_, _, leftItem⟩)
  | boundaryStop leftInside leftRejected leftBoundary =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim
            (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim
            (leftRejected.disjointOrdinary ⟨_, _, rightItem⟩)
      | boundaryStop => rfl
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim (rightBoundaryAbsent leftBoundary)
  | recovered leftInside leftRejected leftBoundaryAbsent leftRecovery
        leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim
            (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim
            (leftRejected.disjointOrdinary ⟨_, _, rightItem⟩)
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim (leftBoundaryAbsent rightBoundary)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          have afterRecoveryEq :=
            topItemRecoveryDeterministicOutcomeSpec.successOutputUnique
              leftRecovery rightRecovery
          cases afterRecoveryEq
          exact inductionHypothesis rightTail

/-- Exact file-loop rejection excludes every successful forward suffix. -/
theorem FileItemsRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FileItemsRejects input rejected) :
    ¬ ∃ items output, FileItemsOrdinaryParses input items output := by
  induction rejection with
  | recoveryRejected rejectedInside rejectedItem rejectedBoundaryAbsent
        rejectedRecovery =>
      rintro ⟨items, output, parsed⟩
      cases parsed with
      | done successfulAtEnd =>
          exact Nat.not_lt_of_ge successfulAtEnd rejectedInside
      | direct successfulInside successfulItem successfulProgress
            successfulTail =>
          exact rejectedItem.disjointOrdinary ⟨_, _, successfulItem⟩
      | boundaryStop successfulInside successfulRejected
            successfulBoundary =>
          exact rejectedBoundaryAbsent successfulBoundary
      | recovered successfulInside successfulRejected
            successfulBoundaryAbsent successfulRecovery successfulTail =>
          exact topItemRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint rejectedRecovery
              ⟨_, _, successfulRecovery⟩
  | laterDirect rejectedInside rejectedItem rejectedProgress tailRejected
        inductionHypothesis =>
      rintro ⟨items, output, parsed⟩
      cases parsed with
      | done successfulAtEnd =>
          exact Nat.not_lt_of_ge successfulAtEnd rejectedInside
      | direct successfulInside successfulItem successfulProgress
            successfulTail =>
          have afterItemEq :=
            topItemDeterministicOutcomeSpec.successOutputUnique
              rejectedItem successfulItem
          cases afterItemEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩
      | boundaryStop successfulInside successfulRejected
            successfulBoundary =>
          exact successfulRejected.disjointOrdinary ⟨_, _, rejectedItem⟩
      | recovered successfulInside successfulRejected
            successfulBoundaryAbsent successfulRecovery successfulTail =>
          exact successfulRejected.disjointOrdinary ⟨_, _, rejectedItem⟩
  | laterRecovered rejectedInside rejectedItem rejectedBoundaryAbsent
        rejectedRecovery tailRejected inductionHypothesis =>
      rintro ⟨items, output, parsed⟩
      cases parsed with
      | done successfulAtEnd =>
          exact Nat.not_lt_of_ge successfulAtEnd rejectedInside
      | direct successfulInside successfulItem successfulProgress
            successfulTail =>
          exact rejectedItem.disjointOrdinary ⟨_, _, successfulItem⟩
      | boundaryStop successfulInside successfulRejected
            successfulBoundary =>
          exact rejectedBoundaryAbsent successfulBoundary
      | recovered successfulInside successfulRejected
            successfulBoundaryAbsent successfulRecovery successfulTail =>
          have afterRecoveryEq :=
            topItemRecoveryDeterministicOutcomeSpec.successOutputUnique
              rejectedRecovery successfulRecovery
          cases afterRecoveryEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- File-item suffixes have deterministic and exclusive broad outcomes. -/
theorem fileItemsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FileItemsOrdinaryParses FileItemsRejects where
  successOutputUnique := FileItemsOrdinaryParses.output_unique
  successRejectDisjoint := FileItemsRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSourceFileOutcomeProperties
/-! Deterministic broad ordinary outcomes for complete syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recovery-aware complete-file success has one final remainder. -/
theorem SourceFileOrdinaryParses.output_unique
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input : Remainder} {left right : Syntax.ParsedFile}
    {afterLeft afterRight : Remainder}
    (leftParsed : SourceFileOrdinaryParses file comments input left afterLeft)
    (rightParsed : SourceFileOrdinaryParses file comments input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftItems =>
      cases rightParsed with
      | parsed rightItems => exact leftItems.output_unique rightItems

/-- Exact complete-file rejection excludes every broad ordinary success. -/
theorem SourceFileRejects.disjointOrdinary
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input rejected : Remainder} (rejection : SourceFileRejects input rejected) :
    ¬ ∃ parsedFile output,
      SourceFileOrdinaryParses file comments input parsedFile output := by
  rintro ⟨parsedFile, output, parsed⟩
  cases rejection with
  | itemsRejected itemsRejected =>
      cases parsed with
      | parsed itemsParsed =>
          exact itemsRejected.disjointOrdinary ⟨_, _, itemsParsed⟩

/-- Complete source files have deterministic and exclusive broad outcomes. -/
theorem sourceFileDeterministicOutcomeSpec
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    DeterministicOutcomeSpec (SourceFileOrdinaryParses file comments)
      SourceFileRejects where
  successOutputUnique := SourceFileOrdinaryParses.output_unique
  successRejectDisjoint := SourceFileRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFileItemsExactnessProperties
/-! Exact recovery-aware file-item outcomes from successful top-item values. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The file loop's rejecting endpoint is unconditional: raw top-item failures
are rewound, and recovery rejection always retains its original input. -/
theorem FileItemsRejects.output_unique {input left right : Remainder}
    (leftRejected : FileItemsRejects input left)
    (rightRejected : FileItemsRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | recoveryRejected leftInside leftItem leftBoundary leftRecovery =>
      cases rightRejected with
      | recoveryRejected rightInside rightItem rightBoundary rightRecovery =>
          exact leftRecovery.output_unique rightRecovery
      | laterDirect rightInside rightItem rightProgress rightTail =>
          exact False.elim (leftItem.disjointOrdinary ⟨_, _, rightItem⟩)
      | laterRecovered rightInside rightItem rightBoundary rightRecovery
            rightTail =>
          exact False.elim
            (leftRecovery.disjointParses ⟨_, _, rightRecovery⟩)
  | laterDirect leftInside leftItem leftProgress leftTail ih =>
      cases rightRejected with
      | recoveryRejected rightInside rightItem rightBoundary rightRecovery =>
          exact False.elim (rightItem.disjointOrdinary ⟨_, _, leftItem⟩)
      | laterDirect rightInside rightItem rightProgress rightTail =>
          have inputEq := topItemDeterministicOutcomeSpec.successOutputUnique
            leftItem rightItem
          subst inputEq
          exact ih rightTail
      | laterRecovered rightInside rightItem rightBoundary rightRecovery
            rightTail =>
          exact False.elim (rightItem.disjointOrdinary ⟨_, _, leftItem⟩)
  | laterRecovered leftInside leftItem leftBoundary leftRecovery leftTail ih =>
      cases rightRejected with
      | recoveryRejected rightInside rightItem rightBoundary rightRecovery =>
          exact False.elim
            (rightRecovery.disjointParses ⟨_, _, leftRecovery⟩)
      | laterDirect rightInside rightItem rightProgress rightTail =>
          exact False.elim (leftItem.disjointOrdinary ⟨_, _, rightItem⟩)
      | laterRecovered rightInside rightItem rightBoundary rightRecovery
            rightTail =>
          have inputEq := leftRecovery.output_unique rightRecovery
          subst inputEq
          exact ih rightTail

/-- Unique successful top-item ASTs make the recovery-aware file loop fix its
complete forward item list, preserving boundary-stop priority. -/
theorem FileItemsOrdinaryParses.value_unique_of_topItem
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right)
    {input : Remainder} {leftItems rightItems : List Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : FileItemsOrdinaryParses input leftItems afterLeft)
    (rightParsed : FileItemsOrdinaryParses input rightItems afterRight) :
    leftItems = rightItems := by
  induction leftParsed generalizing rightItems afterRight with
  | done leftAtEnd =>
      cases rightParsed with
      | done => rfl
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim (Nat.not_lt_of_ge leftAtEnd rightInside)
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim (Nat.not_lt_of_ge leftAtEnd rightInside)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim (Nat.not_lt_of_ge leftAtEnd rightInside)
  | direct leftInside leftItem leftProgress leftTail ih =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          have itemEq := itemValues leftItem rightItem
          subst itemEq
          have inputEq := topItemDeterministicOutcomeSpec.successOutputUnique
            leftItem rightItem
          subst inputEq
          have tailEq := ih rightTail
          subst tailEq
          rfl
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim (rightRejected.disjointOrdinary ⟨_, _, leftItem⟩)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim (rightRejected.disjointOrdinary ⟨_, _, leftItem⟩)
  | boundaryStop leftInside leftRejected leftBoundary =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim (leftRejected.disjointOrdinary ⟨_, _, rightItem⟩)
      | boundaryStop => rfl
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          exact False.elim (rightBoundaryAbsent leftBoundary)
  | recovered leftInside leftRejected leftBoundaryAbsent leftRecovery
        leftTail ih =>
      cases rightParsed with
      | done rightAtEnd =>
          exact False.elim (Nat.not_lt_of_ge rightAtEnd leftInside)
      | direct rightInside rightItem rightProgress rightTail =>
          exact False.elim (leftRejected.disjointOrdinary ⟨_, _, rightItem⟩)
      | boundaryStop rightInside rightRejected rightBoundary =>
          exact False.elim (leftBoundaryAbsent rightBoundary)
      | recovered rightInside rightRejected rightBoundaryAbsent
            rightRecovery rightTail =>
          rcases leftRecovery.result_unique rightRecovery with
            ⟨itemEq, inputEq⟩
          subst itemEq
          subst inputEq
          have tailEq := ih rightTail
          subst tailEq
          rfl

/-- Unique successful top items fix the whole file-item list and remainder. -/
theorem FileItemsOrdinaryParses.result_unique_of_topItem
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right)
    {input : Remainder} {leftItems rightItems : List Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : FileItemsOrdinaryParses input leftItems afterLeft)
    (rightParsed : FileItemsOrdinaryParses input rightItems afterRight) :
    leftItems = rightItems ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_topItem itemValues rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Top-item success-value uniqueness alone supplies exact file-loop outcomes;
raw top-item rejection endpoint uniqueness is not required. -/
theorem fileItemsExactOutcomeSpecOfTopItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right) :
    ExactDeterministicOutcomeSpec FileItemsOrdinaryParses FileItemsRejects where
  toDeterministicOutcomeSpec := fileItemsDeterministicOutcomeSpec
  successValueUnique := FileItemsOrdinaryParses.value_unique_of_topItem itemValues
  rejectOutputUnique := FileItemsRejects.output_unique

/-- An exact top-item contract supplies complete exact file-loop outcomes. -/
theorem fileItemsExactOutcomeSpecOfTopItem
    (itemOutcomes : ExactDeterministicOutcomeSpec TopItemOrdinaryParses
      TopItemRejects) :
    ExactDeterministicOutcomeSpec FileItemsOrdinaryParses FileItemsRejects :=
  fileItemsExactOutcomeSpecOfTopItemValues itemOutcomes.successValueUnique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSourceFileExactnessProperties
/-! Exact source-file outcomes through deterministic source-order trivia attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact raw items fix the complete source-file AST after pure comment attachment. -/
theorem SourceFileOrdinaryParses.value_unique_of_fileItems
    (itemsOutcomes : ExactDeterministicOutcomeSpec FileItemsOrdinaryParses
      FileItemsRejects)
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input : Remainder} {left right : Syntax.ParsedFile}
    {afterLeft afterRight : Remainder}
    (leftParsed : SourceFileOrdinaryParses file comments input left afterLeft)
    (rightParsed : SourceFileOrdinaryParses file comments input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftItems =>
      cases rightParsed with
      | parsed rightItems =>
          have itemsEq := itemsOutcomes.successValueUnique leftItems rightItems
          subst itemsEq
          rfl

/-- Exact raw items fix both the source-file AST and the grammar's final remainder. -/
theorem SourceFileOrdinaryParses.result_unique_of_fileItems
    (itemsOutcomes : ExactDeterministicOutcomeSpec FileItemsOrdinaryParses
      FileItemsRejects)
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input : Remainder} {left right : Syntax.ParsedFile}
    {afterLeft afterRight : Remainder}
    (leftParsed : SourceFileOrdinaryParses file comments input left afterLeft)
    (rightParsed : SourceFileOrdinaryParses file comments input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_fileItems itemsOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Source-file rejection has one endpoint without any exact top-item premise. -/
theorem SourceFileRejects.output_unique {input left right : Remainder}
    (leftRejected : SourceFileRejects input left)
    (rightRejected : SourceFileRejects input right) : left = right := by
  cases leftRejected with
  | itemsRejected leftItems =>
      cases rightRejected with
      | itemsRejected rightItems => exact leftItems.output_unique rightItems

/-- Exact raw-item outcomes lift through fixed file provenance and comments. -/
theorem sourceFileExactOutcomeSpecOfFileItems
    (itemsOutcomes : ExactDeterministicOutcomeSpec FileItemsOrdinaryParses
      FileItemsRejects)
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    ExactDeterministicOutcomeSpec (SourceFileOrdinaryParses file comments)
      SourceFileRejects where
  toDeterministicOutcomeSpec := sourceFileDeterministicOutcomeSpec file comments
  successValueUnique :=
    SourceFileOrdinaryParses.value_unique_of_fileItems itemsOutcomes
  rejectOutputUnique := SourceFileRejects.output_unique

/-- Unique top-item success values suffice for complete source-file exactness. -/
theorem sourceFileExactOutcomeSpecOfTopItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right)
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    ExactDeterministicOutcomeSpec (SourceFileOrdinaryParses file comments)
      SourceFileRejects :=
  sourceFileExactOutcomeSpecOfFileItems
    (fileItemsExactOutcomeSpecOfTopItemValues itemValues) file comments

/-- An exact top-item contract supplies exact recovery-aware source-file outcomes. -/
theorem sourceFileExactOutcomeSpecOfTopItem
    (itemOutcomes : ExactDeterministicOutcomeSpec TopItemOrdinaryParses
      TopItemRejects)
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    ExactDeterministicOutcomeSpec (SourceFileOrdinaryParses file comments)
      SourceFileRejects :=
  sourceFileExactOutcomeSpecOfTopItemValues itemOutcomes.successValueUnique
    file comments

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNestingOutcomeProperties
/-! Functionality and outcome exclusion for bounded nesting scans. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A bounded nesting scan has exactly one ordinary result. -/
theorem NestingScans.result_unique
    {limit : Nat} {context : NestingContext} {tokens : List Token}
    {left right : Option NestingOverflow}
    (leftScan : NestingScans limit context tokens left)
    (rightScan : NestingScans limit context tokens right) :
    left = right := by
  induction leftScan generalizing right with
  | done =>
      cases rightScan
      rfl
  | conditionalExceeded leftAction leftExceeds =>
      cases rightScan <;> simp_all <;> omega
  | conditionalContinues leftAction leftWithin leftTail
        inductionHypothesis =>
      cases rightScan <;> simp_all <;> try omega
      exact inductionHypothesis (by assumption)
  | groupExceeded leftAction leftExceeds =>
      cases rightScan <;> simp_all <;> omega
  | groupContinues leftAction leftWithin leftTail inductionHypothesis =>
      cases rightScan <;> simp_all <;> try omega
      exact inductionHypothesis (by assumption)
  | blockExceeded leftAction leftExceeds =>
      cases rightScan <;> simp_all <;> omega
  | blockContinues leftAction leftWithin leftTail inductionHypothesis =>
      cases rightScan <;> simp_all <;> try omega
      exact inductionHypothesis (by assumption)
  | close leftAction leftTail inductionHypothesis =>
      cases rightScan <;> simp_all
      exact inductionHypothesis (by assumption)
  | reset leftAction leftTail inductionHypothesis =>
      cases rightScan <;> simp_all
      exact inductionHypothesis (by assumption)
  | preserve leftAction leftTail inductionHypothesis =>
      cases rightScan <;> simp_all
      exact inductionHypothesis (by assumption)

/-- Every finite token sequence has a declarative bounded-nesting result. -/
theorem NestingScans.exists_result (limit : Nat) :
    ∀ (context : NestingContext) (tokens : List Token),
      ∃ result, NestingScans limit context tokens result := by
  intro context tokens
  induction tokens generalizing context with
  | nil => exact ⟨none, .done⟩
  | cons token rest inductionHypothesis =>
      cases action : nestingAction token.value with
      | conditional =>
          by_cases exceeds : limit < context.conditionalDepth + 1
          · exact ⟨_, .conditionalExceeded action exceeds⟩
          · have within : context.conditionalDepth + 1 ≤ limit := by omega
            rcases inductionHypothesis
                { context with
                  conditionalDepth := context.conditionalDepth + 1 } with
              ⟨result, tail⟩
            exact ⟨result, .conditionalContinues action within tail⟩
      | groupOpen =>
          by_cases exceeds : limit < context.delimiterDepth + 1
          · exact ⟨_, .groupExceeded action exceeds⟩
          · have within : context.delimiterDepth + 1 ≤ limit := by omega
            rcases inductionHypothesis {
              delimiterDepth := context.delimiterDepth + 1
              conditionalDepth := context.conditionalDepth
              conditionalBases := context.conditionalDepth ::
                context.conditionalBases
            } with ⟨result, tail⟩
            exact ⟨result, .groupContinues action within tail⟩
      | blockOpen =>
          by_cases exceeds : limit < context.delimiterDepth + 1
          · exact ⟨_, .blockExceeded action exceeds⟩
          · have within : context.delimiterDepth + 1 ≤ limit := by omega
            rcases inductionHypothesis {
              delimiterDepth := context.delimiterDepth + 1
              conditionalDepth := 0
              conditionalBases := 0 :: context.conditionalBases
            } with ⟨result, tail⟩
            exact ⟨result, .blockContinues action within tail⟩
      | close =>
          rcases inductionHypothesis context.closeDelimiter with
            ⟨result, tail⟩
          exact ⟨result, .close action tail⟩
      | reset =>
          rcases inductionHypothesis context.resetConditional with
            ⟨result, tail⟩
          exact ⟨result, .reset action tail⟩
      | preserve =>
          rcases inductionHypothesis context with ⟨result, tail⟩
          exact ⟨result, .preserve action tail⟩

/-- A canonical overflow diagnostic excludes a clear nesting scan. -/
theorem NestingExceeds.disjointClears
    {tokens : List Token} {overflow : NestingOverflow}
    (exceeds : NestingExceeds tokens overflow) :
    ¬ NestingClears tokens := by
  intro clears
  have unique := exceeds.result_unique clears
  contradiction

/-- The first canonical overflow is unique. -/
theorem NestingExceeds.overflow_unique
    {tokens : List Token} {left right : NestingOverflow}
    (leftExceeds : NestingExceeds tokens left)
    (rightExceeds : NestingExceeds tokens right) :
    left = right := by
  have unique := leftExceeds.result_unique rightExceeds
  exact Option.some.inj unique

/-- Canonical nesting either clears or reports one exact first overflow. -/
theorem nestingOutcome_total (tokens : List Token) :
    NestingClears tokens ∨
      ∃ overflow, NestingExceeds tokens overflow := by
  rcases NestingScans.exists_result canonicalNestingLimit
      ({} : NestingContext) tokens with ⟨result, scan⟩
  cases result with
  | none => exact Or.inl scan
  | some overflow => exact Or.inr ⟨overflow, scan⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePublicSourceFileOutcomeProperties
/-! Branch exclusion and exact shapes of broad public syntax outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The nesting-overflow and recovery-aware source-file branches are
exclusive before either syntax shape is inspected. -/
theorem publicSourceFileBranches_disjoint
    {tokens : List Syntax.Token} {overflow : NestingOverflow}
    (exceeds : NestingExceeds tokens overflow)
    (clears : NestingClears tokens) : False :=
  exceeds.disjointClears clears

/-- Exact inversion of the two public syntax branches. -/
theorem publicSourceFileOrdinaryParses_iff
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {parsedFile : Syntax.ParsedFile} :
    PublicSourceFileOrdinaryParses file tokens comments parsedFile ↔
      (∃ overflow,
        NestingExceeds tokens overflow ∧
          parsedFile = nestingExceededParsedFile file comments) ∨
      (NestingClears tokens ∧
        ∃ final, SourceFileOrdinaryParses file comments
          (sourceFileRootRemainder tokens) parsedFile final) := by
  constructor
  · intro parsed
    cases parsed with
    | nestingExceeded nesting =>
        exact Or.inl ⟨_, nesting, rfl⟩
    | sourceFile nesting sourceParsed =>
        exact Or.inr ⟨nesting, _, sourceParsed⟩
  · rintro (⟨overflow, nesting, rfl⟩ | ⟨nesting, final, parsed⟩)
    · exact .nestingExceeded nesting
    · exact .sourceFile nesting parsed

/-- Every public syntax outcome retains exact file provenance and comments. -/
theorem PublicSourceFileOrdinaryParses.shape
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {parsedFile : Syntax.ParsedFile}
    (parsed : PublicSourceFileOrdinaryParses file tokens comments parsedFile) :
    parsedFile.source = file.id ∧
      parsedFile.span = SourceSpan.fullFile file ∧
      parsedFile.comments = comments := by
  cases parsed with
  | nestingExceeded =>
      exact ⟨rfl, rfl, rfl⟩
  | sourceFile _ sourceParsed =>
      cases sourceParsed
      exact ⟨rfl, rfl, rfl⟩

/-- If nesting exceeded, any public syntax derivation is the canonical empty
file; a clear source-file derivation is excluded. -/
theorem PublicSourceFileOrdinaryParses.eq_nestingExceededParsedFile
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {parsedFile : Syntax.ParsedFile}
    {overflow : NestingOverflow}
    (parsed : PublicSourceFileOrdinaryParses file tokens comments parsedFile)
    (exceeds : NestingExceeds tokens overflow) :
    parsedFile = nestingExceededParsedFile file comments := by
  cases parsed with
  | nestingExceeded => rfl
  | sourceFile clears _ =>
      exact False.elim (publicSourceFileBranches_disjoint exceeds clears)

/-- If nesting clears, any public syntax derivation exposes an exact broad
source-file derivation while keeping its final remainder existential. -/
theorem PublicSourceFileOrdinaryParses.sourceFile_of_clears
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {parsedFile : Syntax.ParsedFile}
    (parsed : PublicSourceFileOrdinaryParses file tokens comments parsedFile)
    (clears : NestingClears tokens) :
    ∃ final, SourceFileOrdinaryParses file comments
      (sourceFileRootRemainder tokens) parsedFile final := by
  cases parsed with
  | nestingExceeded exceeds =>
      exact False.elim (publicSourceFileBranches_disjoint exceeds clears)
  | sourceFile _ sourceParsed =>
      exact ⟨_, sourceParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePublicSourceFileValueProperties
/-! Exact public syntax values without inventing a public remainder or rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Nesting-branch exclusion and unique top-item values fix the public parsed
file. The hidden raw-grammar remainder is not part of this public conclusion. -/
theorem PublicSourceFileOrdinaryParses.value_unique_of_topItem
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right)
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {left right : Syntax.ParsedFile}
    (leftParsed : PublicSourceFileOrdinaryParses file tokens comments left)
    (rightParsed : PublicSourceFileOrdinaryParses file tokens comments right) :
    left = right := by
  cases leftParsed with
  | nestingExceeded leftNesting =>
      cases rightParsed with
      | nestingExceeded => rfl
      | sourceFile rightNesting rightSource =>
          exact False.elim
            (publicSourceFileBranches_disjoint leftNesting rightNesting)
  | sourceFile leftNesting leftSource =>
      cases rightParsed with
      | nestingExceeded rightNesting =>
          exact False.elim
            (publicSourceFileBranches_disjoint rightNesting leftNesting)
      | sourceFile rightNesting rightSource =>
          exact (sourceFileExactOutcomeSpecOfTopItemValues itemValues file
            comments).successValueUnique leftSource rightSource

/-- An exact top-item contract supplies public parsed-file value uniqueness. -/
theorem PublicSourceFileOrdinaryParses.value_unique_of_exact_topItem
    (itemOutcomes : ExactDeterministicOutcomeSpec TopItemOrdinaryParses
      TopItemRejects)
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {left right : Syntax.ParsedFile}
    (leftParsed : PublicSourceFileOrdinaryParses file tokens comments left)
    (rightParsed : PublicSourceFileOrdinaryParses file tokens comments right) :
    left = right :=
  leftParsed.value_unique_of_topItem itemOutcomes.successValueUnique rightParsed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLexedValidationOutcomeProperties
/-! Totality, functionality, and acceptance laws for lexical validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An ordered-span validation scan has at most one result. -/
theorem OrderedSpanValidationScans.result_unique
    {α : Type} {file : SourceFile} {spanOf : α → SourceSpan}
    {index previousEnd : Nat} {items : List α}
    {left right : Option IndexedSpan}
    (leftScan : OrderedSpanValidationScans file spanOf index previousEnd
      items left)
    (rightScan : OrderedSpanValidationScans file spanOf index previousEnd
      items right) :
    left = right := by
  induction leftScan generalizing right with
  | done =>
      cases rightScan
      rfl
  | rejected leftInvalid =>
      cases rightScan with
      | rejected => rfl
      | continues rightAccepted => contradiction
  | continues leftAccepted leftTail inductionHypothesis =>
      cases rightScan with
      | rejected rightInvalid => contradiction
      | continues _ rightTail =>
          exact inductionHypothesis rightTail

/-- Every finite ordered-span sequence has a validation result. -/
theorem OrderedSpanValidationScans.exists_result
    {α : Type} (file : SourceFile) (spanOf : α → SourceSpan) :
    ∀ (index previousEnd : Nat) (items : List α),
      ∃ result, OrderedSpanValidationScans file spanOf index previousEnd
        items result := by
  intro index previousEnd items
  induction items generalizing index previousEnd with
  | nil => exact ⟨none, .done⟩
  | cons item rest inductionHypothesis =>
      by_cases accepted : OrderedSpanAccepted file previousEnd (spanOf item)
      · rcases inductionHypothesis (index + 1) (spanOf item).endByte with
          ⟨result, tail⟩
        exact ⟨result, .continues accepted tail⟩
      · exact ⟨some { index := index, span := spanOf item },
          .rejected accepted⟩

/-- A clear ordered-span scan is exactly a valid source span sequence. -/
theorem OrderedSpanValidationScans.none_iff_spanSequenceValidFor
    {α : Type} {file : SourceFile} {spanOf : α → SourceSpan}
    {index previousEnd : Nat} {items : List α} :
    OrderedSpanValidationScans file spanOf index previousEnd items none ↔
      SpanSequence.ValidFor file spanOf previousEnd items := by
  constructor
  · intro scan
    induction items generalizing index previousEnd with
    | nil => trivial
    | cons item rest inductionHypothesis =>
        cases scan with
        | continues accepted tail =>
            exact ⟨accepted.1, accepted.2.1, accepted.2.2,
              inductionHypothesis tail⟩
  · intro valid
    induction items generalizing index previousEnd with
    | nil => exact .done
    | cons item rest inductionHypothesis =>
        simp only [SpanSequence.ValidFor] at valid
        rcases valid with
          ⟨spanValid, afterPrevious, nonempty, tailValid⟩
        exact .continues
          ⟨spanValid, afterPrevious, nonempty⟩
          (inductionHypothesis tailValid)

/-- A pointwise span-validation scan has at most one result. -/
theorem SpanValidationScans.result_unique
    {α : Type} {file : SourceFile} {spanOf : α → SourceSpan}
    {index : Nat} {items : List α} {left right : Option IndexedSpan}
    (leftScan : SpanValidationScans file spanOf index items left)
    (rightScan : SpanValidationScans file spanOf index items right) :
    left = right := by
  induction leftScan generalizing right with
  | done =>
      cases rightScan
      rfl
  | rejected leftInvalid =>
      cases rightScan with
      | rejected => rfl
      | continues rightAccepted => contradiction
  | continues leftAccepted leftTail inductionHypothesis =>
      cases rightScan with
      | rejected rightInvalid => contradiction
      | continues _ rightTail =>
          exact inductionHypothesis rightTail

/-- Every finite pointwise span sequence has a validation result. -/
theorem SpanValidationScans.exists_result
    {α : Type} (file : SourceFile) (spanOf : α → SourceSpan) :
    ∀ (index : Nat) (items : List α),
      ∃ result, SpanValidationScans file spanOf index items result := by
  intro index items
  induction items generalizing index with
  | nil => exact ⟨none, .done⟩
  | cons item rest inductionHypothesis =>
      by_cases accepted : (spanOf item).ValidFor file
      · rcases inductionHypothesis (index + 1) with ⟨result, tail⟩
        exact ⟨result, .continues accepted tail⟩
      · exact ⟨some { index := index, span := spanOf item },
          .rejected accepted⟩

/-- A clear pointwise span scan accepts exactly every list member. -/
theorem SpanValidationScans.none_iff_forall_validFor
    {α : Type} {file : SourceFile} {spanOf : α → SourceSpan}
    {index : Nat} {items : List α} :
    SpanValidationScans file spanOf index items none ↔
      ∀ item ∈ items, (spanOf item).ValidFor file := by
  constructor
  · intro scan
    induction items generalizing index with
    | nil => simp
    | cons head tail inductionHypothesis =>
        cases scan with
        | continues accepted tailScan =>
            intro item member
            rcases List.mem_cons.mp member with rfl | member
            · exact accepted
            · exact inductionHypothesis tailScan item member
  · intro valid
    induction items generalizing index with
    | nil => exact .done
    | cons item rest inductionHypothesis =>
        apply SpanValidationScans.continues (valid item (by simp))
        apply inductionHypothesis
        intro tailItem member
        exact valid tailItem (List.mem_cons_of_mem item member)

/-- Whole-file validation has at least one priority-ordered outcome. -/
theorem LexedFileValidationOutcome.exists_result
    (file : SourceFile) (lexed : LexedFile) :
    ∃ result, LexedFileValidationOutcome file lexed result := by
  by_cases mismatch : lexed.source ≠ file.id
  · exact ⟨_, .sourceRejected mismatch⟩
  · have sourceAccepted : lexed.source = file.id :=
      Decidable.of_not_not mismatch
    rcases OrderedSpanValidationScans.exists_result file
        (fun token : Token => token.span) 0 0 lexed.tokens with
      ⟨tokenResult, tokens⟩
    cases tokenResult with
    | some invalid => exact ⟨_, .tokenRejected sourceAccepted tokens⟩
    | none =>
        rcases OrderedSpanValidationScans.exists_result file
            (fun comment : Comment => comment.span) 0 0 lexed.comments with
          ⟨commentResult, comments⟩
        cases commentResult with
        | some invalid =>
            exact ⟨_, .commentRejected sourceAccepted tokens comments⟩
        | none =>
            rcases SpanValidationScans.exists_result file
                (fun diagnostic : LexicalDiagnostic => diagnostic.span)
                0 lexed.diagnostics with
              ⟨diagnosticResult, diagnostics⟩
            cases diagnosticResult with
            | some invalid =>
                exact ⟨_, .diagnosticRejected sourceAccepted tokens comments
                  diagnostics⟩
            | none =>
                exact ⟨none, .accepted sourceAccepted tokens comments
                  diagnostics⟩

/-- Whole-file validation has at most one priority-ordered result. -/
theorem LexedFileValidationOutcome.result_unique
    {file : SourceFile} {lexed : LexedFile}
    {left right : Option LexedValidationFailure}
    (leftOutcome : LexedFileValidationOutcome file lexed left)
    (rightOutcome : LexedFileValidationOutcome file lexed right) :
    left = right := by
  cases leftOutcome with
  | sourceRejected leftMismatch =>
      cases rightOutcome with
      | sourceRejected => rfl
      | tokenRejected rightSource => exact (leftMismatch rightSource).elim
      | commentRejected rightSource => exact (leftMismatch rightSource).elim
      | diagnosticRejected rightSource => exact (leftMismatch rightSource).elim
      | accepted rightSource => exact (leftMismatch rightSource).elim
  | tokenRejected leftSource leftTokens =>
      cases rightOutcome with
      | sourceRejected rightMismatch => exact (rightMismatch leftSource).elim
      | tokenRejected _ rightTokens =>
          cases leftTokens.result_unique rightTokens
          rfl
      | commentRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | diagnosticRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | accepted _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
  | commentRejected leftSource leftTokens leftComments =>
      cases rightOutcome with
      | sourceRejected rightMismatch => exact (rightMismatch leftSource).elim
      | tokenRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | commentRejected _ _ rightComments =>
          cases leftComments.result_unique rightComments
          rfl
      | diagnosticRejected _ _ rightComments =>
          have impossible := leftComments.result_unique rightComments
          contradiction
      | accepted _ _ rightComments =>
          have impossible := leftComments.result_unique rightComments
          contradiction
  | diagnosticRejected leftSource leftTokens leftComments leftDiagnostics =>
      cases rightOutcome with
      | sourceRejected rightMismatch => exact (rightMismatch leftSource).elim
      | tokenRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | commentRejected _ _ rightComments =>
          have impossible := leftComments.result_unique rightComments
          contradiction
      | diagnosticRejected _ _ _ rightDiagnostics =>
          cases leftDiagnostics.result_unique rightDiagnostics
          rfl
      | accepted _ _ _ rightDiagnostics =>
          have impossible := leftDiagnostics.result_unique rightDiagnostics
          contradiction
  | accepted leftSource leftTokens leftComments leftDiagnostics =>
      cases rightOutcome with
      | sourceRejected rightMismatch => exact (rightMismatch leftSource).elim
      | tokenRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | commentRejected _ _ rightComments =>
          have impossible := leftComments.result_unique rightComments
          contradiction
      | diagnosticRejected _ _ _ rightDiagnostics =>
          have impossible := leftDiagnostics.result_unique rightDiagnostics
          contradiction
      | accepted => rfl

/-- Whole-file validation either accepts or returns one exact failure. -/
theorem lexedFileValidationOutcome_total
    (file : SourceFile) (lexed : LexedFile) :
    LexedFileValidationAccepts file lexed ∨
      ∃ failure, LexedFileValidationRejects file lexed failure := by
  rcases LexedFileValidationOutcome.exists_result file lexed with
    ⟨result, outcome⟩
  cases result with
  | none => exact Or.inl outcome
  | some failure => exact Or.inr ⟨failure, outcome⟩

/-- An exact validation failure excludes acceptance. -/
theorem LexedFileValidationRejects.disjointAccepts
    {file : SourceFile} {lexed : LexedFile}
    {failure : LexedValidationFailure}
    (rejects : LexedFileValidationRejects file lexed failure) :
    ¬ LexedFileValidationAccepts file lexed := by
  intro accepts
  have impossible := rejects.result_unique accepts
  contradiction

/-- The exact first whole-file validation failure is unique. -/
theorem LexedFileValidationRejects.failure_unique
    {file : SourceFile} {lexed : LexedFile}
    {left right : LexedValidationFailure}
    (leftRejects : LexedFileValidationRejects file lexed left)
    (rightRejects : LexedFileValidationRejects file lexed right) :
    left = right := by
  exact Option.some.inj (leftRejects.result_unique rightRejects)

/-- Whole-file validation accepts exactly the lexical provenance contract. -/
theorem lexedFileValidationAccepts_iff_validFor
    (file : SourceFile) (lexed : LexedFile) :
    LexedFileValidationAccepts file lexed ↔ lexed.ValidFor file := by
  constructor
  · intro accepted
    cases accepted with
    | accepted source tokens comments diagnostics =>
        exact {
          source_eq := source
          tokens :=
            OrderedSpanValidationScans.none_iff_spanSequenceValidFor.mp tokens
          comments :=
            OrderedSpanValidationScans.none_iff_spanSequenceValidFor.mp comments
          diagnostics :=
            SpanValidationScans.none_iff_forall_validFor.mp diagnostics
        }
  · intro valid
    exact .accepted valid.source_eq
      (OrderedSpanValidationScans.none_iff_spanSequenceValidFor.mpr valid.tokens)
      (OrderedSpanValidationScans.none_iff_spanSequenceValidFor.mpr
        valid.comments)
      (SpanValidationScans.none_iff_forall_validFor.mpr valid.diagnostics)

end Solcore.Syntax.DeclarativeGrammar
end
