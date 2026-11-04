import Solcore.Core.Renaming
import Solcore.Core.Eval
import Solcore.Core.LocalLoop

/-!
# Core evaluation and renaming

Sizes of Core evaluation and continuations, closed renaming, helper inversion, continuation agreement, and agreement of typing contexts.

This file stays below the module that defines the Source `Context`. `Context` here is the Core one, found through `open Core`, and once that module is imported the `Context` of the enclosing namespace would win.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CoreClosedRenaming
/-! Static syntactic renaming of typed closed helper code. This concerns the
expression syntax only. It makes no claim that closures created in different
ambient environments are the same runtime value. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CoreProof
open Core

private theorem same_lift {context : Context} {left right : Renaming}
    (same : ∀ index, index < context.length → left index = right index) (type : Ty) :
    ∀ index, index < (type :: context).length → left.lift index = right.lift index := by
  intro index bound
  cases index with
  | zero => rfl
  | succ index => exact congrArg Nat.succ (same index (by simpa using bound))

/-- Renamings agreeing on every typed free slot produce identical syntax. -/
theorem typed_rename_agree {context : Context} {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType context expression type definitions) {left right : Renaming}
    (same : ∀ index, index < context.length → left index = right index) :
    expression.rename left = expression.rename right := by
  induction typed using HasType.rec
      (motive_2 := fun context _ _ branches _ _ => ∀ {left right : Renaming},
        (∀ index, index < context.length → left index = right index) →
        Expr.renameList branches left.lift = Expr.renameList branches right.lift)
      generalizing left right with
  | unit | bool | word | integer => rfl
  | var found => exact congrArg Expr.var (same _ (List.getElem?_eq_some_iff.mp found).1)
  | pair _ _ a b => simp only [Expr.rename, a same, b same]
  | first _ ih => exact congrArg Expr.first (ih same)
  | second _ ih => exact congrArg Expr.second (ih same)
  | lambda _ _ _ ih => simp only [Expr.rename, ih (same_lift same _)]
  | apply _ _ a b => simp only [Expr.rename, a same, b same]
  | inLeft _ _ ih => simp only [Expr.rename, ih same]
  | inRight _ _ ih => simp only [Expr.rename, ih same]
  | caseE _ _ _ a b c => simp only [Expr.rename, a same, b (same_lift same _), c (same_lift same _)]
  | newCell _ ih => simp only [Expr.rename, ih same]
  | loadCell _ ih => simp only [Expr.rename, ih same]
  | storeCell _ _ a b => simp only [Expr.rename, a same, b same]
  | construct _ _ ih => simp only [Expr.rename, ih same]
  | matchData _ _ _ _ a b => simp only [Expr.rename, a same, b same]
  | unary _ ih => simp only [Expr.rename, ih same]
  | binary _ _ a b => simp only [Expr.rename, a same, b same]
  | ternary _ _ _ a b c => simp only [Expr.rename, a same, b same, c same]
  | letE _ _ a b => simp only [Expr.rename, a same, b (same_lift same _)]
  | ifE _ _ _ a b c => simp only [Expr.rename, a same, b same, c same]
  | nil => rfl
  | cons _ _ a b =>
    rename_i left right same
    simp only [Expr.renameList, a (same_lift same _), b same]

theorem closed_rename {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (embedding : Renaming) : expression.rename embedding = expression := by
  have same := typed_rename_agree typed (left := embedding) (right := Renaming.id) (by intro index bound; simp at bound)
  simpa using same

end Solcore.SourceSemantics.CoreLowering.CoreProof
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize
/-! A natural-number size certificate for the existing Core big-step relation.
The size counts rule nodes and strictly decreases at every premise. This is a
mathematical induction device; it adds neither an evaluator nor a machine rule.
Every existing finite evaluation has a size certificate, and erasing that
certificate recovers exactly the original relation. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CoreProof

open Core

inductive EvaluationSize : Nat → Environment → Store → Expr → Value → Store → Prop where
  | unit {environment : Environment} {store : Store} :
      EvaluationSize 1 environment store .unit .unit store
  | bool {environment : Environment} {store : Store} {value : Bool} :
      EvaluationSize 1 environment store (.bool value) (.bool value) store
  | word {environment : Environment} {store : Store} {value : Word} :
      EvaluationSize 1 environment store (.word value) (.word value) store
  | integer {environment : Environment} {store : Store} {value : Int} :
      EvaluationSize 1 environment store (.integer value) (.integer value) store
  | pair {cost1 cost2 : Nat}
      {environment : Environment} {initialStore middleStore finalStore : Store}
      {left right : Expr} {leftValue rightValue : Value} :
      EvaluationSize cost1 environment initialStore left leftValue middleStore →
      EvaluationSize cost2 environment middleStore right rightValue finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore (.pair left right)
        (.pair leftValue rightValue) finalStore
  | first {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {operand : Expr} {leftValue rightValue : Value} :
      EvaluationSize cost1 environment initialStore operand
        (.pair leftValue rightValue) finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.first operand) leftValue finalStore
  | second {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {operand : Expr} {leftValue rightValue : Value} :
      EvaluationSize cost1 environment initialStore operand
        (.pair leftValue rightValue) finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.second operand) rightValue finalStore
  | inLeft {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {rightType : Ty} {payload : Expr} {payloadValue : Value} :
      EvaluationSize cost1 environment initialStore payload payloadValue finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.inLeft rightType payload)
        (.inLeft rightType payloadValue) finalStore
  | inRight {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {leftType : Ty} {payload : Expr} {payloadValue : Value} :
      EvaluationSize cost1 environment initialStore payload payloadValue finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.inRight leftType payload)
        (.inRight leftType payloadValue) finalStore
  | caseLeft {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {scrutinee leftBranch rightBranch : Expr}
      {rightType : Ty} {payload result : Value} :
      EvaluationSize cost1 environment initialStore scrutinee
        (.inLeft rightType payload) branchStore →
      EvaluationSize cost2 (payload :: environment) branchStore leftBranch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.caseE scrutinee leftBranch rightBranch) result finalStore
  | caseRight {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {scrutinee leftBranch rightBranch : Expr}
      {leftType : Ty} {payload result : Value} :
      EvaluationSize cost1 environment initialStore scrutinee
        (.inRight leftType payload) branchStore →
      EvaluationSize cost2 (payload :: environment) branchStore rightBranch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.caseE scrutinee leftBranch rightBranch) result finalStore
  | lambda
      {environment : Environment} {store : Store}
      {parameterType resultType : Ty} {body : Expr} :
      EvaluationSize 1 environment store (.lambda parameterType resultType body)
        (.closure parameterType resultType body environment) store
  | apply {cost1 cost2 cost3 : Nat}
      {environment capturedEnvironment : Environment}
      {initialStore argumentStore bodyStore finalStore : Store}
      {function argument body : Expr} {parameterType resultType : Ty}
      {argumentValue result : Value} :
      EvaluationSize cost1 environment initialStore function
        (.closure parameterType resultType body capturedEnvironment)
        argumentStore →
      EvaluationSize cost2 environment argumentStore argument argumentValue bodyStore →
      EvaluationSize cost3 (argumentValue :: capturedEnvironment) bodyStore body result
        finalStore →
      EvaluationSize (cost1 + cost2 + cost3 + 1) environment initialStore (.apply function argument) result finalStore
  | var
      {environment : Environment} {store : Store}
      {index : Nat} {value : Value} :
      environment[index]? = some value →
      EvaluationSize 1 environment store (.var index) value store
  | newCell {cost1 : Nat}
      {environment : Environment} {initialStore initializedStore : Store}
      {elementType : Ty} {initializer : Expr} {initialValue : Value} :
      EvaluationSize cost1 environment initialStore initializer initialValue initializedStore →
      EvaluationSize (cost1 + 1) environment initialStore (.newCell elementType initializer)
        (.cellRef elementType initializedStore.length)
        (initializedStore ++ [initialValue])
  | loadCell {cost1 : Nat}
      {environment : Environment} {initialStore referenceStore : Store}
      {reference : Expr} {elementType : Ty} {location : Location}
      {value : Value} :
      EvaluationSize cost1 environment initialStore reference
        (.cellRef elementType location) referenceStore →
      Store.read? referenceStore location = some value →
      EvaluationSize (cost1 + 1) environment initialStore (.loadCell reference) value referenceStore
  | storeCell {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore referenceStore valueStore finalStore : Store}
      {reference value : Expr} {elementType : Ty} {location : Location}
      {oldValue newValue : Value} :
      EvaluationSize cost1 environment initialStore reference
        (.cellRef elementType location) referenceStore →
      Store.read? referenceStore location = some oldValue →
      EvaluationSize cost2 environment referenceStore value newValue valueStore →
      Store.write? valueStore location newValue = some finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore (.storeCell reference value) .unit finalStore
  | construct {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {constructor : ConstructorId} {payload : Expr} {payloadValue : Value} :
      EvaluationSize cost1 environment initialStore payload payloadValue finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.construct constructor payload)
        (.constructed constructor payloadValue) finalStore
  | matchData {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {dataType : DataTypeId} {resultType : Ty}
      {scrutinee branch : Expr} {branches : List Expr}
      {constructor : ConstructorId} {payload result : Value} :
      EvaluationSize cost1 environment initialStore scrutinee
        (.constructed constructor payload) branchStore →
      constructor.owner = dataType →
      branches[constructor.index]? = some branch →
      EvaluationSize cost2 (payload :: environment) branchStore branch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.matchData dataType resultType scrutinee branches) result finalStore
  | unary {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {op : UnaryOp} {operand : Expr} {operandValue result : Value} :
      EvaluationSize cost1 environment initialStore operand operandValue finalStore →
      op.apply operandValue = some result →
      EvaluationSize (cost1 + 1) environment initialStore (.unary op operand) result finalStore
  | binary {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore rightStore finalStore : Store}
      {op : BinaryOp} {left right : Expr}
      {leftValue rightValue result : Value} :
      EvaluationSize cost1 environment initialStore left leftValue rightStore →
      EvaluationSize cost2 environment rightStore right rightValue finalStore →
      op.apply leftValue rightValue = some result →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore (.binary op left right) result finalStore
  | ternary {cost1 cost2 cost3 : Nat}
      {environment : Environment}
      {initialStore secondStore thirdStore finalStore : Store}
      {op : TernaryOp} {first second third : Expr}
      {firstValue secondValue thirdValue result : Value} :
      EvaluationSize cost1 environment initialStore first firstValue secondStore →
      EvaluationSize cost2 environment secondStore second secondValue thirdStore →
      EvaluationSize cost3 environment thirdStore third thirdValue finalStore →
      op.apply firstValue secondValue thirdValue = some result →
      EvaluationSize (cost1 + cost2 + cost3 + 1) environment initialStore (.ternary op first second third)
        result finalStore
  | letE {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore bodyStore finalStore : Store}
      {value body : Expr} {boundValue result : Value} :
      EvaluationSize cost1 environment initialStore value boundValue bodyStore →
      EvaluationSize cost2 (boundValue :: environment) bodyStore body result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore (.letE value body) result finalStore
  | ifTrue {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {condition thenBranch elseBranch : Expr} {result : Value} :
      EvaluationSize cost1 environment initialStore condition (.bool true) branchStore →
      EvaluationSize cost2 environment branchStore thenBranch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.ifE condition thenBranch elseBranch) result finalStore
  | ifFalse {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {condition thenBranch elseBranch : Expr} {result : Value} :
      EvaluationSize cost1 environment initialStore condition (.bool false) branchStore →
      EvaluationSize cost2 environment branchStore elseBranch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.ifE condition thenBranch elseBranch) result finalStore


theorem EvaluationSize.sound
    {size : Nat} {environment : Environment} {before after : Store} {expression : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before expression value after) :
    Evaluates environment before expression value after := by
  induction evaluation with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | pair _ _ left right => exact .pair left right
  | first _ operand => exact .first operand
  | second _ operand => exact .second operand
  | inLeft _ payload => exact .inLeft payload
  | inRight _ payload => exact .inRight payload
  | caseLeft _ _ scrutinee branch => exact .caseLeft scrutinee branch
  | caseRight _ _ scrutinee branch => exact .caseRight scrutinee branch
  | lambda => exact .lambda
  | apply _ _ _ function argument body => exact .apply function argument body
  | var found => exact .var found
  | newCell _ initializer => exact .newCell initializer
  | loadCell _ found reference => exact .loadCell reference found
  | storeCell _ read _ write reference value => exact .storeCell reference read value write
  | construct _ payload => exact .construct payload
  | matchData _ owned found _ scrutinee branch => exact .matchData scrutinee owned found branch
  | unary _ applied operand => exact .unary operand applied
  | binary _ _ applied left right => exact .binary left right applied
  | ternary _ _ _ applied first second third => exact .ternary first second third applied
  | letE _ _ value body => exact .letE value body
  | ifTrue _ _ condition branch => exact .ifTrue condition branch
  | ifFalse _ _ condition branch => exact .ifFalse condition branch

theorem evaluation_has_size
    {environment : Environment} {before after : Store} {expression : Expr} {value : Value}
    (evaluation : Evaluates environment before expression value after) :
    ∃ size, EvaluationSize size environment before expression value after := by
  induction evaluation with
  | unit => exact ⟨_, .unit⟩
  | bool => exact ⟨_, .bool⟩
  | word => exact ⟨_, .word⟩
  | integer => exact ⟨_, .integer⟩
  | pair _ _ left right =>
    obtain ⟨_, left⟩ := left; obtain ⟨_, right⟩ := right
    exact ⟨_, .pair left right⟩
  | first _ operand => obtain ⟨_, operand⟩ := operand; exact ⟨_, .first operand⟩
  | second _ operand => obtain ⟨_, operand⟩ := operand; exact ⟨_, .second operand⟩
  | inLeft _ payload => obtain ⟨_, payload⟩ := payload; exact ⟨_, .inLeft payload⟩
  | inRight _ payload => obtain ⟨_, payload⟩ := payload; exact ⟨_, .inRight payload⟩
  | caseLeft _ _ scrutinee branch =>
    obtain ⟨_, scrutinee⟩ := scrutinee; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .caseLeft scrutinee branch⟩
  | caseRight _ _ scrutinee branch =>
    obtain ⟨_, scrutinee⟩ := scrutinee; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .caseRight scrutinee branch⟩
  | lambda => exact ⟨_, .lambda⟩
  | apply _ _ _ function argument body =>
    obtain ⟨_, function⟩ := function; obtain ⟨_, argument⟩ := argument; obtain ⟨_, body⟩ := body
    exact ⟨_, .apply function argument body⟩
  | var found => exact ⟨_, .var found⟩
  | newCell _ initializer => obtain ⟨_, initializer⟩ := initializer; exact ⟨_, .newCell initializer⟩
  | loadCell _ found reference => obtain ⟨_, reference⟩ := reference; exact ⟨_, .loadCell reference found⟩
  | storeCell _ read _ write reference value =>
    obtain ⟨_, reference⟩ := reference; obtain ⟨_, value⟩ := value
    exact ⟨_, .storeCell reference read value write⟩
  | construct _ payload => obtain ⟨_, payload⟩ := payload; exact ⟨_, .construct payload⟩
  | matchData _ owned found _ scrutinee branch =>
    obtain ⟨_, scrutinee⟩ := scrutinee; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .matchData scrutinee owned found branch⟩
  | unary _ applied operand => obtain ⟨_, operand⟩ := operand; exact ⟨_, .unary operand applied⟩
  | binary _ _ applied left right =>
    obtain ⟨_, left⟩ := left; obtain ⟨_, right⟩ := right
    exact ⟨_, .binary left right applied⟩
  | ternary _ _ _ applied first second third =>
    obtain ⟨_, first⟩ := first; obtain ⟨_, second⟩ := second; obtain ⟨_, third⟩ := third
    exact ⟨_, .ternary first second third applied⟩
  | letE _ _ value body =>
    obtain ⟨_, value⟩ := value; obtain ⟨_, body⟩ := body
    exact ⟨_, .letE value body⟩
  | ifTrue _ _ condition branch =>
    obtain ⟨_, condition⟩ := condition; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .ifTrue condition branch⟩
  | ifFalse _ _ condition branch =>
    obtain ⟨_, condition⟩ := condition; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .ifFalse condition branch⟩

theorem evaluation_iff_size
    {environment : Environment} {before after : Store} {expression : Expr} {value : Value} :
    Evaluates environment before expression value after ↔ ∃ size, EvaluationSize size environment before expression value after :=
  ⟨evaluation_has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem EvaluationSize.positive
    {size : Nat} {environment : Environment} {before after : Store} {expression : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before expression value after) : 0 < size := by
  cases evaluation <;> omega

end Solcore.SourceSemantics.CoreLowering.CoreProof
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
/-! Invert finite evaluations of actual Core helpers while retaining a strict
bound on the continuation derivation. Known firstEvaluation evaluations are compared
using Core determinism; no source execution is assumed by these lemmas. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CoreProof

open Core

theorem EvaluationSize.case_left
    {size : Nat} {environment : Environment} {before middle after : Store}
    {scrutinee left right : Expr} {rightType : Ty} {payload result : Value}
    (evaluation : EvaluationSize size environment before (.caseE scrutinee left right) result after)
    (firstEvaluation : Evaluates environment before scrutinee (.inLeft rightType payload) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (payload :: environment) middle left result after := by
  cases evaluation with
  | caseLeft other branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    cases same
    exact ⟨_, by omega, branch⟩
  | caseRight other _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic other.sound firstEvaluation
    cases impossible

theorem EvaluationSize.case_right
    {size : Nat} {environment : Environment} {before middle after : Store}
    {scrutinee left right : Expr} {leftType : Ty} {payload result : Value}
    (evaluation : EvaluationSize size environment before (.caseE scrutinee left right) result after)
    (firstEvaluation : Evaluates environment before scrutinee (.inRight leftType payload) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (payload :: environment) middle right result after := by
  cases evaluation with
  | caseRight other branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    cases same
    exact ⟨_, by omega, branch⟩
  | caseLeft other _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic other.sound firstEvaluation
    cases impossible

theorem EvaluationSize.let_body
    {size : Nat} {environment : Environment} {before middle after : Store}
    {initializer body : Expr} {bound result : Value}
    (evaluation : EvaluationSize size environment before (.letE initializer body) result after)
    (firstEvaluation : Evaluates environment before initializer bound middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (bound :: environment) middle body result after := by
  cases evaluation with
  | letE other branch =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    exact ⟨_, by omega, branch⟩

theorem EvaluationSize.if_true
    {size : Nat} {environment : Environment} {before middle after : Store}
    {condition left right : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (.ifE condition left right) result after)
    (firstEvaluation : Evaluates environment before condition (.bool true) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller environment middle left result after := by
  cases evaluation with
  | ifTrue other branch =>
    obtain ⟨_, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    exact ⟨_, by omega, branch⟩
  | ifFalse other _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic other.sound firstEvaluation
    cases impossible

theorem EvaluationSize.if_false
    {size : Nat} {environment : Environment} {before middle after : Store}
    {condition left right : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (.ifE condition left right) result after)
    (firstEvaluation : Evaluates environment before condition (.bool false) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller environment middle right result after := by
  cases evaluation with
  | ifFalse other branch =>
    obtain ⟨_, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    exact ⟨_, by omega, branch⟩
  | ifTrue other _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic other.sound firstEvaluation
    cases impossible

theorem EvaluationSize.apply_body
    {size : Nat} {environment captured : Environment} {before argumentStore bodyStore after : Store}
    {function argument body : Expr} {parameterType resultType : Ty} {input result : Value}
    (evaluation : EvaluationSize size environment before (.apply function argument) result after)
    (callee : Evaluates environment before function (.closure parameterType resultType body captured) argumentStore)
    (argumentEvaluation : Evaluates environment argumentStore argument input bodyStore) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (input :: captured) bodyStore body result after := by
  cases evaluation with
  | apply otherFunction otherArgument bodyEvaluation =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic otherFunction.sound callee
    cases same
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic otherArgument.sound argumentEvaluation
    exact ⟨_, by omega, bodyEvaluation⟩

theorem EvaluationSize.bind_success
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {computation body : Expr} {payload result : Value}
    (evaluation : EvaluationSize size environment before (LanguageResult.bind type computation body) result after)
    (firstEvaluation : Evaluates environment before computation (.inRight .word payload) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (payload :: environment) middle body result after :=
  evaluation.case_right firstEvaluation

theorem EvaluationSize.choose_true
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {condition left right : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalControl.choose type condition left right) result after)
    (firstEvaluation : Evaluates environment before condition (.inRight .word (.bool true)) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (.bool true :: environment) middle (left.weakenAt 0) result after := by
  obtain ⟨next, smaller, continuation⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨last, smallerAgain, branch⟩ := continuation.if_true (.var rfl)
  exact ⟨last, Nat.lt_trans smallerAgain smaller, branch⟩

theorem EvaluationSize.choose_false
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {condition left right : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalControl.choose type condition left right) result after)
    (firstEvaluation : Evaluates environment before condition (.inRight .word (.bool false)) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (.bool false :: environment) middle (right.weakenAt 0) result after := by
  obtain ⟨next, smaller, continuation⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨last, smallerAgain, branch⟩ := continuation.if_false (.var rfl)
  exact ⟨last, Nat.lt_trans smallerAgain smaller, branch⟩

theorem EvaluationSize.sequence_fallthrough
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {computation next : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.sequence type computation next) result after)
    (firstEvaluation : Evaluates environment before computation (LocalLoop.fallthroughValue type) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller
      (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: environment)
      middle (((next.weakenAt 0).weakenAt 0).weakenAt 0) result after := by
  obtain ⟨first, smaller, branch⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨second, smallerAgain, branch⟩ := branch.case_left (.var rfl)
  obtain ⟨third, smallerLast, branch⟩ := branch.case_left (.var rfl)
  exact ⟨third, Nat.lt_trans smallerLast (Nat.lt_trans smallerAgain smaller), branch⟩

theorem EvaluationSize.invoke_body
    {size : Nat} {environment captured : Environment} {before middle after : Store}
    {type : Ty} {reason : Word} {reference body : Expr} {location : Location} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.invoke type reference reason) result after)
    (referenceEvaluation : Evaluates environment before reference
      (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location) middle)
    (installed : middle.read? location = some (.inRight .unit (.closure .unit (LocalLoop.resultType type) body captured))) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (.unit :: captured) middle body result after := by
  obtain ⟨first, smaller, application⟩ := evaluation.bind_success (OptionalCell.read_success reason referenceEvaluation installed)
  obtain ⟨second, smallerAgain, body⟩ := application.apply_body (.var rfl) .unit
  exact ⟨second, Nat.lt_trans smallerAgain smaller, body⟩

/-- The exact installed closure and store are forced by the generated prelude.
Its finite entry-body derivation is strictly smaller than the whole loop. -/
theorem EvaluationSize.iterate_entry
    {size : Nat} {environment : Environment} {before after : Store}
    {type : Ty} {reason : Word} {condition body post : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.iterate type condition body post reason) result after) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller
      (.unit :: .cellRef (OptionalCell.cellType (LocalLoop.functionType type)) before.length :: environment)
      (before ++ [.inRight .unit (LocalLoop.installedClosure type condition body post reason before.length environment)])
      (LocalLoop.loopBody type condition body post reason) result after := by
  obtain ⟨first, smaller, storeSelf⟩ := evaluation.let_body (OptionalCell.allocate_evaluates _ _ _)
  have write : Evaluates
      (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) before.length :: environment)
      (before ++ [.inLeft (LocalLoop.functionType type) .unit])
      (.storeCell (.var 0) (.inRight .unit (.lambda .unit (LocalLoop.resultType type)
        (LocalLoop.loopBody type condition body post reason)))) .unit
      (before ++ [.inRight .unit (LocalLoop.installedClosure type condition body post reason before.length environment)]) := by
    apply Evaluates.storeCell (oldValue := .inLeft (LocalLoop.functionType type) .unit) (.var rfl)
    · simp [Store.read?]
    · exact .inRight .lambda
    · simp [Store.write?, LocalLoop.installedClosure]
  obtain ⟨second, smallerAgain, invoke⟩ := storeSelf.let_body write
  obtain ⟨third, smallerLast, bodyEval⟩ := invoke.invoke_body
    (body := LocalLoop.loopBody type condition body post reason)
    (captured := .cellRef (OptionalCell.cellType (LocalLoop.functionType type)) before.length :: environment)
    (.var rfl) (by simp [Store.read?, LocalLoop.installedClosure])
  exact ⟨third, Nat.lt_trans smallerLast (Nat.lt_trans smallerAgain smaller), bodyEval⟩


/-- Inspect the computation of a bind without assuming either language-result
branch, then use its smaller certificate to reconstruct its source meaning. -/
theorem EvaluationSize.bind_computation
    {size : Nat} {environment : Environment} {before after : Store}
    {type : Ty} {computation body : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LanguageResult.bind type computation body) result after) :
    ∃ smaller middle value, smaller < size ∧ EvaluationSize smaller environment before computation value middle := by
  cases evaluation with
  | caseLeft computation _ => exact ⟨_, _, _, by omega, computation⟩
  | caseRight computation _ => exact ⟨_, _, _, by omega, computation⟩

theorem EvaluationSize.advance_fallthrough
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {computation next : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.advance type computation next) result after)
    (firstEvaluation : Evaluates environment before computation (LocalLoop.fallthroughValue type) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller
      (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: environment)
      middle (((next.weakenAt 0).weakenAt 0).weakenAt 0) result after := by
  obtain ⟨first, smaller, branch⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨second, smallerAgain, branch⟩ := branch.case_left (.var rfl)
  obtain ⟨third, smallerLast, branch⟩ := branch.case_left (.var rfl)
  exact ⟨third, Nat.lt_trans smallerLast (Nat.lt_trans smallerAgain smaller), branch⟩

theorem EvaluationSize.advance_continuing
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {computation next : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.advance type computation next) result after)
    (firstEvaluation : Evaluates environment before computation (LocalLoop.continuingValue type) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller
      (.unit :: .inRight .unit .unit :: .inRight (LocalControl.controlType type) (.inRight .unit .unit) :: environment)
      middle (((next.weakenAt 0).weakenAt 0).weakenAt 0) result after := by
  obtain ⟨first, smaller, branch⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨second, smallerAgain, branch⟩ := branch.case_right (.var rfl)
  obtain ⟨third, smallerLast, branch⟩ := branch.case_right (.var rfl)
  exact ⟨third, Nat.lt_trans smallerLast (Nat.lt_trans smallerAgain smaller), branch⟩

end Solcore.SourceSemantics.CoreLowering.CoreProof
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement
/-! A finite prefix with a known value can be composed around, or removed
from, any finite continuation evaluation. This is an agreement between the
existing mathematical evaluations, with no executable evaluator added. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CoreProof

open Core

structure ContinuationAgreement (environment : Environment) (store : Store) (whole : Expr)
    (nextEnvironment : Environment) (nextStore : Store) (next : Expr) : Prop where
  wrap : ∀ {result finalStore}, Evaluates nextEnvironment nextStore next result finalStore →
    Evaluates environment store whole result finalStore
  unwrap : ∀ {result finalStore}, Evaluates environment store whole result finalStore →
    Evaluates nextEnvironment nextStore next result finalStore

namespace ContinuationAgreement

theorem refl (environment : Environment) (store : Store) (code : Expr) :
    ContinuationAgreement environment store code environment store code := ⟨id, id⟩

theorem trans {environment middleEnvironment nextEnvironment : Environment}
    {store middleStore nextStore : Store} {whole middle next : Expr}
    (first : ContinuationAgreement environment store whole middleEnvironment middleStore middle)
    (second : ContinuationAgreement middleEnvironment middleStore middle nextEnvironment nextStore next) :
    ContinuationAgreement environment store whole nextEnvironment nextStore next :=
  ⟨fun evaluation => first.wrap (second.wrap evaluation), fun evaluation => second.unwrap (first.unwrap evaluation)⟩

theorem letE {environment : Environment} {before middle : Store} {initializer body : Expr} {value : Value}
    (evaluated : Evaluates environment before initializer value middle) :
    ContinuationAgreement environment before (.letE initializer body) (value :: environment) middle body := by
  constructor
  · exact fun body => .letE evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.let_body evaluated
    exact body.sound

theorem bind {environment : Environment} {before middle : Store} {computation body : Expr} {type : Ty} {value : Value}
    (evaluated : Evaluates environment before computation (.inRight .word value) middle) :
    ContinuationAgreement environment before (LanguageResult.bind type computation body) (value :: environment) middle body := by
  constructor
  · exact fun body => LanguageResult.bind_success type evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.bind_success evaluated
    exact body.sound

end ContinuationAgreement

end Solcore.SourceSemantics.CoreLowering.CoreProof
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CoreContinuationSize
/-! A real prefix retains a subderivation of the original native evaluation.
The Boolean distinguishes strict prefixes from an empty prefix. Forgetting
sizes recovers ordinary continuation agreement; the converse is not asserted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CoreProof
open Core

structure ContinuationSize (strict : Bool) (environment : Environment) (store : Store) (whole : Expr)
    (nextEnvironment : Environment) (nextStore : Store) (next : Expr) : Prop where
  wrap : ∀ {result finalStore}, Evaluates nextEnvironment nextStore next result finalStore →
    Evaluates environment store whole result finalStore
  remaining : ∀ {size result finalStore}, EvaluationSize size environment store whole result finalStore →
    ∃ child, (if strict then child < size else child ≤ size) ∧
      EvaluationSize child nextEnvironment nextStore next result finalStore

namespace ContinuationSize
variable {a b : Bool} {environment middleEnvironment nextEnvironment : Environment}
  {store middleStore nextStore : Store} {whole middle next : Expr}

/-- Erasure is the only direction that chooses a size for an unsized input. -/
theorem agreement (receipt : ContinuationSize a environment store whole nextEnvironment nextStore next) :
    ContinuationAgreement environment store whole nextEnvironment nextStore next := by
  refine ⟨receipt.wrap, ?_⟩
  intro result finalStore evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨child, _, completed⟩ := receipt.remaining sized
  exact completed.sound

theorem weak (receipt : ContinuationSize a environment store whole nextEnvironment nextStore next) :
    ContinuationSize false environment store whole nextEnvironment nextStore next := by
  refine ⟨receipt.wrap, ?_⟩
  intro size result finalStore evaluated
  obtain ⟨child, bound, completed⟩ := receipt.remaining evaluated
  exact ⟨child, by cases a <;> simp_all <;> omega, completed⟩

theorem refl (environment : Environment) (store : Store) (code : Expr) :
    ContinuationSize false environment store code environment store code :=
  ⟨id, fun evaluated => ⟨_, Nat.le_refl _, evaluated⟩⟩

theorem trans (first : ContinuationSize a environment store whole middleEnvironment middleStore middle)
    (second : ContinuationSize b middleEnvironment middleStore middle nextEnvironment nextStore next) :
    ContinuationSize (a || b) environment store whole nextEnvironment nextStore next := by
  refine ⟨fun evaluated => first.wrap (second.wrap evaluated), ?_⟩
  intro size result finalStore evaluated
  obtain ⟨middleSize, firstBound, middleEval⟩ := first.remaining evaluated
  obtain ⟨child, lastBound, completed⟩ := second.remaining middleEval
  exact ⟨child, by cases a <;> cases b <;> simp_all <;> omega, completed⟩

theorem letE {environment : Environment} {before middle : Store} {initializer body : Expr} {value : Value}
    (evaluated : Evaluates environment before initializer value middle) :
    ContinuationSize true environment before (.letE initializer body) (value :: environment) middle body := by
  refine ⟨fun body => .letE evaluated body, ?_⟩
  intro size result finalStore original
  exact original.let_body evaluated

theorem bind {environment : Environment} {before middle : Store} {computation body : Expr} {type : Ty} {value : Value}
    (evaluated : Evaluates environment before computation (.inRight .word value) middle) :
    ContinuationSize true environment before (LanguageResult.bind type computation body) (value :: environment) middle body := by
  refine ⟨fun body => LanguageResult.bind_success type evaluated body, ?_⟩
  intro size result finalStore original
  exact original.bind_success evaluated

theorem case_left {environment : Environment} {before middle : Store} {scrutinee left right : Expr}
    {rightType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inLeft rightType value) middle) :
    ContinuationSize true environment before (.caseE scrutinee left right) (value :: environment) middle left := by
  refine ⟨fun body => .caseLeft evaluated body, ?_⟩
  intro size result finalStore original
  exact original.case_left evaluated

theorem case_right {environment : Environment} {before middle : Store} {scrutinee left right : Expr}
    {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationSize true environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  refine ⟨fun body => .caseRight evaluated body, ?_⟩
  intro size result finalStore original
  exact original.case_right evaluated

end ContinuationSize
/-- Ordered lexical slots and canonical values grow by prefixes of equal
length. Their elements are not identified with administrative temporaries. -/
def CanonicalPrefix {α : Type} (scope : List α) (canonical : Environment)
    (nextScope : List α) (nextCanonical : Environment) : Prop :=
  ∃ addedScope addedValues, addedScope.length = addedValues.length ∧
    nextScope = addedScope ++ scope ∧ nextCanonical = addedValues ++ canonical

namespace CanonicalPrefix
theorem refl {α : Type} (scope : List α) (canonical : Environment) :
    CanonicalPrefix scope canonical scope canonical := ⟨[], [], rfl, rfl, rfl⟩

theorem cons {α : Type} (scope : List α) (canonical : Environment) (binding : α) (value : Value) :
    CanonicalPrefix scope canonical (binding :: scope) (value :: canonical) :=
  ⟨[binding], [value], rfl, rfl, rfl⟩

theorem trans {α : Type} {scope middleScope nextScope : List α}
    {canonical middleCanonical nextCanonical : Environment}
    (first : CanonicalPrefix scope canonical middleScope middleCanonical)
    (second : CanonicalPrefix middleScope middleCanonical nextScope nextCanonical) :
    CanonicalPrefix scope canonical nextScope nextCanonical := by
  obtain ⟨firstScope, firstValues, firstLength, rfl, rfl⟩ := first
  obtain ⟨lastScope, lastValues, lastLength, rfl, rfl⟩ := second
  exact ⟨lastScope ++ firstScope, lastValues ++ firstValues,
    by simp [firstLength, lastLength], by simp [List.append_assoc], by simp [List.append_assoc]⟩

theorem fold {α β : Type} (scope : List α) (canonical : Environment) (bindings : List β) (project : β → α)
    {added : Environment} (same : added.length = bindings.length) :
    CanonicalPrefix scope canonical (bindings.foldl (fun current binding => project binding :: current) scope)
      (added ++ canonical) := by
  have ordered : ∀ current, bindings.foldl (fun scope binding => project binding :: scope) current =
      bindings.reverse.map project ++ current := by
    clear same
    induction bindings with
    | nil => intro current; rfl
    | cons head tail ih =>
      intro current
      simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]
  exact ⟨bindings.reverse.map project, added, by simp [same], ordered scope, rfl⟩
end CanonicalPrefix

end Solcore.SourceSemantics.CoreLowering.CoreProof
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NativeExpressionContextSupport
/-! A checked syntactic bound records which free slots the actual code uses.
Typing transport inspects only that prefix. Unused input suffixes may differ;
this transports syntax typing, never runtime closures or their captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NativeExpressionContextSupport
open Core

mutual
  def supported : Expr → Nat → Bool
    | .unit, _ | .bool _, _ | .word _, _ | .integer _, _ => true
    | .var index, bound => decide (index < bound)
    | .pair left right, bound | .apply left right, bound | .storeCell left right, bound
    | .binary _ left right, bound => supported left bound && supported right bound
    | .first value, bound | .second value, bound | .inLeft _ value, bound | .inRight _ value, bound
    | .newCell _ value, bound | .loadCell value, bound | .construct _ value, bound
    | .unary _ value, bound => supported value bound
    | .lambda _ _ body, bound => supported body (bound + 1)
    | .caseE value left right, bound => supported value bound && supported left (bound + 1) && supported right (bound + 1)
    | .letE value body, bound => supported value bound && supported body (bound + 1)
    | .ifE condition yes no, bound | .ternary _ condition yes no, bound =>
        supported condition bound && supported yes bound && supported no bound
    | .matchData _ _ value branches, bound => supported value bound && branchesSupported branches bound
  def branchesSupported : List Expr → Nat → Bool
    | [], _ => true
    | head :: tail, bound => supported head (bound + 1) && branchesSupported tail bound
end

/-- Only lookups used by the certified prefix must be retained. -/
def Agrees (bound : Nat) (source target : Context) : Prop :=
  ∀ index, index < bound → target[index]? = source[index]?

theorem Agrees.lift {bound : Nat} {source target : Context} (same : Agrees bound source target) (head : Ty) :
    Agrees (bound + 1) (head :: source) (head :: target) := by
  intro index smaller
  cases index with
  | zero => rfl
  | succ index => exact same index (by omega)

theorem typing {definitions : DataEnvironment} {source : Context} {code : Expr} {type : Ty}
    (typed : HasType source code type definitions) {bound : Nat} {target : Context}
    (support : supported code bound = true) (same : Agrees bound source target) :
    HasType target code type definitions := by
  induction typed using HasType.rec
      (motive_2 := fun source result payloads branches definitions _ => ∀ {bound target},
        branchesSupported branches bound = true → Agrees bound source target →
        BranchesHaveType target result payloads branches definitions)
      generalizing bound target with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | var found =>
      simp only [supported, decide_eq_true_eq] at support
      exact .var ((same _ support).trans found)
  | pair _ _ left right =>
      simp only [supported, Bool.and_eq_true] at support
      exact .pair (left support.1 same) (right support.2 same)
  | first _ ih => exact .first (ih support same)
  | second _ ih => exact .second (ih support same)
  | lambda parameter result _ ih => exact .lambda parameter result (ih support (same.lift _))
  | apply _ _ f a =>
      simp only [supported, Bool.and_eq_true] at support
      exact .apply (f support.1 same) (a support.2 same)
  | inLeft wellFormed _ ih => exact .inLeft wellFormed (ih support same)
  | inRight wellFormed _ ih => exact .inRight wellFormed (ih support same)
  | caseE _ _ _ value left right =>
      simp only [supported, Bool.and_eq_true] at support
      exact .caseE (value support.1.1 same) (left support.1.2 (same.lift _)) (right support.2 (same.lift _))
  | newCell _ ih => exact .newCell (ih support same)
  | loadCell _ ih => exact .loadCell (ih support same)
  | storeCell _ _ ref value =>
      simp only [supported, Bool.and_eq_true] at support
      exact .storeCell (ref support.1 same) (value support.2 same)
  | construct found _ ih => exact .construct found (ih support same)
  | matchData found wellFormed _ _ value branches =>
      simp only [supported, Bool.and_eq_true] at support
      exact .matchData found wellFormed (value support.1 same) (branches support.2 same)
  | unary _ ih => exact .unary (ih support same)
  | binary _ _ left right =>
      simp only [supported, Bool.and_eq_true] at support
      exact .binary (left support.1 same) (right support.2 same)
  | ternary _ _ _ first second third =>
      simp only [supported, Bool.and_eq_true] at support
      exact .ternary (first support.1.1 same) (second support.1.2 same) (third support.2 same)
  | letE _ _ value body =>
      simp only [supported, Bool.and_eq_true] at support
      exact .letE (value support.1 same) (body support.2 (same.lift _))
  | ifE _ _ _ condition yes no =>
      simp only [supported, Bool.and_eq_true] at support
      exact .ifE (condition support.1.1 same) (yes support.1.2 same) (no support.2 same)
  | nil => exact .nil
  | cons _ _ head tail =>
      rename_i bound target support same
      simp only [branchesSupported, Bool.and_eq_true] at support
      exact .cons (head support.1 (same.lift _)) (tail support.2 same)

/-- A syntax typing derivation bounds every free slot, including inside
lambda, case and data-match binders. -/
theorem of_typing {definitions : DataEnvironment} {context : Context} {code : Expr} {type : Ty}
    (typed : HasType context code type definitions) : supported code context.length = true := by
  induction typed using HasType.rec
      (motive_2 := fun context _ _ branches _ _ => branchesSupported branches context.length = true) with
  | var found => simpa [supported] using (List.getElem?_eq_some_iff.mp found).1
  | unit | bool | word | integer => rfl
  | pair _ _ a b | apply _ _ a b | storeCell _ _ a b | binary _ _ a b => simp [supported, a, b]
  | first _ ih | second _ ih | inLeft _ _ ih | inRight _ _ ih | newCell _ ih | loadCell _ ih
    | construct _ _ ih | unary _ ih => exact ih
  | lambda _ _ _ ih => simpa [supported] using ih
  | caseE _ _ _ a b c => simpa [supported, a, b, c] using And.intro b c
  | ternary _ _ _ a b c | ifE _ _ _ a b c => simp [supported, a, b, c]
  | letE _ _ a b => simpa [supported, a] using b
  | matchData _ _ _ _ a b => simp [supported, a, b]
  | nil => rfl
  | cons _ _ a b => simpa [branchesSupported, b] using a

theorem prefix_typing {definitions : DataEnvironment} {leading sourceSuffix targetSuffix : Context}
    {code : Expr} {type : Ty} (typed : HasType (leading ++ sourceSuffix) code type definitions)
    (support : supported code leading.length = true) :
    HasType (leading ++ targetSuffix) code type definitions := by
  apply typing typed support
  intro index smaller
  simp [List.getElem?_append, smaller]

end Solcore.SourceSemantics.CoreLowering.NativeExpressionContextSupport
end
