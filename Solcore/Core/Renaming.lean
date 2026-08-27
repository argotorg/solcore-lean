import Solcore.Core.RenamingSyntax
import Solcore.Core.Typing

set_option autoImplicit false

namespace Solcore.Core

namespace Context

def insertAt : Context → Nat → Ty → Context
  | context, 0, type => type :: context
  | [], _ + 1, type => [type]
  | head :: tail, cutoff + 1, type => head :: insertAt tail cutoff type

end Context

namespace Renaming

def Respects (mapping : Renaming) (source target : Context) : Prop :=
  ∀ ⦃index type⦄, source[index]? = some type →
    target[mapping index]? = some type

@[simp] theorem respects_id (context : Context) :
    Respects id context context := by
  intro index type found
  exact found

theorem Respects.comp
    {inner outer : Renaming} {first second third : Context}
    (outerRespect : Respects outer second third)
    (innerRespect : Respects inner first second) :
    Respects (comp outer inner) first third := by
  intro index type found
  exact outerRespect (innerRespect found)

theorem Respects.lift
    {mapping : Renaming} {source target : Context}
    (respect : Respects mapping source target)
    (binder : Ty) :
    Respects mapping.lift (binder :: source) (binder :: target) := by
  intro index type found
  cases index with
  | zero => simpa [Renaming.lift] using found
  | succ index =>
      simp [Renaming.lift] at found ⊢
      exact respect found

theorem insertion_respects_insertAt
    (source : Context) (cutoff : Nat) (inserted : Ty) :
    Respects (insertion cutoff) source (source.insertAt cutoff inserted) := by
  induction cutoff generalizing source with
  | zero =>
      intro index type found
      simpa [insertion, Context.insertAt] using found
  | succ cutoff inductionHypothesis =>
      cases source with
      | nil =>
          intro index type found
          simp at found
      | cons head tail =>
          rw [← lift_insertion cutoff]
          exact (inductionHypothesis tail).lift head

end Renaming

theorem HasType.rename
    {context : Context} {expr : Expr} {type : Ty}
    {definitions : DataEnvironment}
    (typing : HasType context expr type definitions)
    {target : Context} {mapping : Renaming}
    (respect : mapping.Respects context target) :
    HasType target (expr.rename mapping) type definitions := by
  induction typing using HasType.rec
      (motive_2 := fun context resultType payloadTypes branches definitions _ =>
        ∀ {target : Context} {mapping : Renaming},
          mapping.Respects context target →
          BranchesHaveType target resultType payloadTypes
            (Expr.renameList branches mapping.lift) definitions)
      generalizing target mapping with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var found => exact .var (respect found)
  | pair _ _ leftIH rightIH => exact .pair (leftIH respect) (rightIH respect)
  | first _ operandIH => exact .first (operandIH respect)
  | second _ operandIH => exact .second (operandIH respect)
  | lambda parameterWellFormed resultWellFormed _ bodyIH =>
      exact .lambda parameterWellFormed resultWellFormed
        (bodyIH (respect.lift _))
  | apply _ _ functionIH argumentIH =>
      exact .apply (functionIH respect) (argumentIH respect)
  | inLeft annotationWellFormed _ payloadIH =>
      exact .inLeft annotationWellFormed (payloadIH respect)
  | inRight annotationWellFormed _ payloadIH =>
      exact .inRight annotationWellFormed (payloadIH respect)
  | caseE _ _ _ scrutineeIH leftIH rightIH =>
      exact .caseE (scrutineeIH respect)
        (leftIH (respect.lift _)) (rightIH (respect.lift _))
  | newCell _ payload initializerIH =>
      exact .newCell (initializerIH respect) payload
  | loadCell _ payload referenceIH =>
      exact .loadCell (referenceIH respect) payload
  | storeCell _ _ payload referenceIH valueIH =>
      exact .storeCell (referenceIH respect) (valueIH respect) payload
  | construct found _ payloadIH =>
      exact .construct found (payloadIH respect)
  | matchData found resultWellFormed _ _ scrutineeIH branchesIH =>
      exact .matchData found resultWellFormed
        (scrutineeIH respect) (branchesIH respect)
  | unary _ operandIH => exact .unary (operandIH respect)
  | binary _ _ leftIH rightIH => exact .binary (leftIH respect) (rightIH respect)
  | ternary _ _ _ firstIH secondIH thirdIH =>
      exact .ternary (firstIH respect) (secondIH respect) (thirdIH respect)
  | letE _ _ valueIH bodyIH =>
      exact .letE (valueIH respect) (bodyIH (respect.lift _))
  | ifE _ _ _ conditionIH thenIH elseIH =>
      exact .ifE (conditionIH respect) (thenIH respect) (elseIH respect)
  | nil => exact BranchesHaveType.nil
  | cons _ _ branchIH branchesIH =>
      apply BranchesHaveType.cons
      · apply branchIH
        exact Renaming.Respects.lift (by assumption) _
      · apply branchesIH
        assumption

theorem BranchesHaveType.rename
    {context : Context} {resultType : Ty} {payloadTypes : List Ty}
    {branches : List Expr} {definitions : DataEnvironment}
    (typing : BranchesHaveType context resultType payloadTypes branches definitions)
    {target : Context} {mapping : Renaming}
    (respect : mapping.Respects context target) :
    BranchesHaveType target resultType payloadTypes
      (Expr.renameList branches mapping.lift) definitions :=
  by
    induction payloadTypes generalizing branches with
    | nil =>
        cases typing
        exact BranchesHaveType.nil
    | cons payloadType payloadTypes inductionHypothesis =>
        cases typing with
        | cons branchTyping branchesTyping =>
            exact BranchesHaveType.cons
              (branchTyping.rename (respect.lift _))
              (inductionHypothesis branchesTyping)


theorem HasType.weakenAt
    {context : Context} {expr : Expr} {type inserted : Ty}
    {definitions : DataEnvironment}
    (typing : HasType context expr type definitions)
    (cutoff : Nat) :
    HasType (context.insertAt cutoff inserted)
      (expr.weakenAt cutoff) type definitions := by
  rw [← Expr.rename_insertion]
  exact typing.rename (Renaming.insertion_respects_insertAt context cutoff inserted)

theorem infer_rename
    {context target : Context} {expr : Expr} {type : Ty}
    {definitions : DataEnvironment} {mapping : Renaming}
    (inferred : infer? context expr definitions = some type)
    (respect : mapping.Respects context target) :
    infer? target (expr.rename mapping) definitions = some type :=
  infer_complete ((infer_sound inferred).rename respect)

end Solcore.Core
