import Solcore.Core.LocalLoop
import Solcore.Core.Renaming

/-! Native typing inversion follows the emitted lexical insertions. Removing
unused administrative binders is a static syntax theorem; no closure or store
weakening is claimed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedLexicalWhile.Native
open Core

def PullsBack (mapping : Renaming) (source target : Core.Context) : Prop :=
  ∀ index type, target[mapping index]? = some type → source[index]? = some type

theorem PullsBack.lift {mapping : Renaming} {source target : Core.Context}
    (back : PullsBack mapping source target) (head : Ty) :
    PullsBack mapping.lift (head :: source) (head :: target) := by
  intro index type found
  cases index with
  | zero => simpa [Renaming.lift] using found
  | succ index => exact back index type found

mutual
  theorem typing {definitions : DataEnvironment} : ∀ (expression : Expr)
      {source target : Core.Context} {mapping : Renaming} {type : Ty},
      PullsBack mapping source target → HasType target (expression.rename mapping) type definitions →
      HasType source expression type definitions
    | .unit, _, _, _, _, _, typed => by cases typed; exact .unit
    | .bool _, _, _, _, _, _, typed => by cases typed; exact .bool
    | .word _, _, _, _, _, _, typed => by cases typed; exact .word
    | .integer _, _, _, _, _, _, typed => by cases typed; exact .integer
    | .var index, _, _, _, _, back, typed => by
      cases typed with | var found => exact .var (back index _ found)
    | .pair left right, _, _, _, _, back, typed => by
      cases typed with | pair l r => exact .pair (typing left back l) (typing right back r)
    | .first value, _, _, _, _, back, typed => by
      cases typed with | first v => exact .first (typing value back v)
    | .second value, _, _, _, _, back, typed => by
      cases typed with | second v => exact .second (typing value back v)
    | .lambda parameter result body, _, _, _, _, back, typed => by
      cases typed with | lambda p r b => exact .lambda p r (typing body (back.lift parameter) b)
    | .apply function argument, _, _, _, _, back, typed => by
      cases typed with | apply f a => exact .apply (typing function back f) (typing argument back a)
    | .inLeft right value, _, _, _, _, back, typed => by
      cases typed with | inLeft r v => exact .inLeft r (typing value back v)
    | .inRight left value, _, _, _, _, back, typed => by
      cases typed with | inRight l v => exact .inRight l (typing value back v)
    | .caseE value left right, _, _, _, _, back, typed => by
      cases typed with | caseE v l r => exact .caseE (typing value back v) (typing left (back.lift _) l) (typing right (back.lift _) r)
    | .newCell payload initializer, _, _, _, _, back, typed => by
      cases typed with | newCell v => exact .newCell (typing initializer back v)
    | .loadCell reference, _, _, _, _, back, typed => by
      cases typed with | loadCell r => exact .loadCell (typing reference back r)
    | .storeCell reference value, _, _, _, _, back, typed => by
      cases typed with | storeCell r v => exact .storeCell (typing reference back r) (typing value back v)
    | .construct constructor payload, _, _, _, _, back, typed => by
      cases typed with | construct found p => exact .construct found (typing payload back p)
    | .matchData dataType result value branches, _, _, _, _, back, typed => by
      cases typed with | matchData found wf v b => exact .matchData found wf (typing value back v) (branchTyping branches back b)
    | .unary operator value, _, _, _, _, back, typed => by
      cases typed with | unary v => exact .unary (typing value back v)
    | .binary operator left right, _, _, _, _, back, typed => by
      cases typed with | binary l r => exact .binary (typing left back l) (typing right back r)
    | .ternary operator first second third, _, _, _, _, back, typed => by
      cases typed with | ternary f s t => exact .ternary (typing first back f) (typing second back s) (typing third back t)
    | .letE value body, _, _, _, _, back, typed => by
      cases typed with | letE v b => exact .letE (typing value back v) (typing body (back.lift _) b)
    | .ifE condition left right, _, _, _, _, back, typed => by
      cases typed with | ifE c l r => exact .ifE (typing condition back c) (typing left back l) (typing right back r)

  theorem branchTyping {definitions : DataEnvironment} : ∀ (expressions : List Expr)
      {source target : Core.Context} {mapping : Renaming} {payloads : List Ty} {type : Ty},
      PullsBack mapping source target →
      BranchesHaveType target type payloads (Expr.renameList expressions mapping.lift) definitions →
      BranchesHaveType source type payloads expressions definitions
    | [], _, _, _, _, _, _, typed => by cases typed; exact .nil
    | expression :: expressions, _, _, _, _, _, back, typed => by
      cases typed with
      | cons h t => exact .cons (typing expression (back.lift _) h) (branchTyping expressions back t)
end

theorem remove_front {definitions : DataEnvironment} {context : Core.Context} {head type : Ty} {expression : Expr}
    (typed : HasType (head :: context) (expression.weakenAt 0) type definitions) :
    HasType context expression type definitions := by
  rw [← Expr.rename_insertion] at typed
  exact typing expression (by intro index type found; simpa [Renaming.insertion] using found) typed

theorem remove_second {definitions : DataEnvironment} {context : Core.Context} {first head type : Ty} {expression : Expr}
    (typed : HasType (first :: head :: context) (expression.weakenAt 1) type definitions) :
    HasType (first :: context) expression type definitions := by
  rw [← Expr.rename_insertion] at typed
  exact typing expression (by intro index type found; cases index <;> simpa [Renaming.insertion] using found) typed

theorem bind_inv {definitions : DataEnvironment} {context : Core.Context} {output : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) (LanguageResult.resultType output) definitions) :
    ∃ payload, HasType context computation (LanguageResult.resultType payload) definitions ∧
      HasType (payload :: context) body (LanguageResult.resultType output) definitions := by
  cases typed with
  | caseE computation failure body =>
    cases failure with
    | inLeft wf value =>
      cases value with
      | var found =>
        simp at found
        cases found
        exact ⟨_, computation, body⟩

theorem discard_inv {definitions : DataEnvironment} {context : Core.Context} {output : Ty} {computation body : Expr}
    (typed : HasType context (LocalSequence.discard output computation body) (LanguageResult.resultType output) definitions) :
    HasType context body (LanguageResult.resultType output) definitions := by
  obtain ⟨_, _, next⟩ := bind_inv typed
  exact remove_front next

theorem conditional_inv {definitions : DataEnvironment} {context : Core.Context} {type : Ty} {condition thenBranch elseBranch : Expr}
    (typed : HasType context (LocalLoop.conditional type condition thenBranch elseBranch) (LocalLoop.resultType type) definitions) :
    HasType context condition (LanguageResult.resultType .bool) definitions ∧
    HasType context thenBranch (LocalLoop.resultType type) definitions ∧
    HasType context elseBranch (LocalLoop.resultType type) definitions := by
  obtain ⟨payload, condition, branch⟩ := bind_inv typed
  cases branch with
  | ifE tested yes no =>
    cases tested with
    | var found =>
      simp at found
      cases found
      exact ⟨condition, remove_front yes, remove_front no⟩

theorem sequence_children {definitions : DataEnvironment} {context : Core.Context} {type result : Ty} {computation body : Expr}
    (typed : HasType context (LocalLoop.sequence type computation body) result definitions) :
    (∃ headType, HasType context computation headType definitions) ∧
    (∃ tailType, HasType context body tailType definitions) := by
  cases typed with
  | caseE computation failure next =>
    cases next with
    | caseE outer inner transfer =>
      cases inner with
      | caseE tested continued returned =>
        exact ⟨⟨_, computation⟩, ⟨_, remove_front (remove_front (remove_front continued))⟩⟩

theorem conditional_children {definitions : DataEnvironment} {context : Core.Context} {type result : Ty} {condition thenBranch elseBranch : Expr}
    (typed : HasType context (LocalLoop.conditional type condition thenBranch elseBranch) result definitions) :
    (∃ thenType, HasType context thenBranch thenType definitions) ∧
    (∃ elseType, HasType context elseBranch elseType definitions) := by
  cases typed with
  | caseE condition failure branch =>
    cases branch with
    | ifE tested yes no => exact ⟨⟨_, remove_front yes⟩, ⟨_, remove_front no⟩⟩

theorem discard_child {definitions : DataEnvironment} {context : Core.Context} {type result : Ty} {computation body : Expr}
    (typed : HasType context (LocalSequence.discard type computation body) result definitions) :
    ∃ tailType, HasType context body tailType definitions := by
  cases typed with | caseE computation failure body => exact ⟨_, remove_front body⟩

theorem advance_child {definitions : DataEnvironment} {context : Core.Context} {type result : Ty} {computation body : Expr}
    (typed : HasType context (LocalLoop.advance type computation body) result definitions) :
    ∃ headType, HasType context computation headType definitions := by
  cases typed with | caseE computation failure body => exact ⟨_, computation⟩

theorem while_body {definitions : DataEnvironment} {context : Core.Context} {type result : Ty} {condition body : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.whileLoop type condition body reason) result definitions) :
    (∃ bodyType, HasType context body bodyType definitions) ∧
    HasType context (LocalLoop.whileLoop type condition body reason) (LocalLoop.resultType type) definitions := by
  cases typed with
  | letE allocation installed =>
    cases allocation with
    | newCell empty =>
      cases installed with
      | letE written invoked =>
        cases written with
        | storeCell reference closure =>
          cases closure with
          | inRight unitWF raw =>
            cases raw with
            | lambda parameterWF resultWF loop =>
              obtain ⟨⟨_, yes⟩, _⟩ := conditional_children loop
              obtain ⟨_, shifted⟩ := advance_child yes
              refine ⟨⟨_, remove_front (remove_front shifted)⟩, ?_⟩
              apply HasType.letE (.newCell empty)
              apply HasType.letE (.storeCell reference (.inRight unitWF (.lambda parameterWF resultWF loop)))
              apply LocalLoop.invoke_hasType reason ?_ (.var rfl)
              cases resultWF with
              | sum _ control =>
                cases control with
                | sum normal transfer =>
                  cases normal with | sum _ returned => exact returned

theorem finished_flow {definitions : DataEnvironment} {context : Core.Context} {type result : Ty}
    {flow fallback : Expr} {escaped : Word}
    (typed : HasType context (LocalControl.finish type (LocalLoop.toControl type flow escaped) fallback) result definitions) :
    ∃ flowType, HasType context flow flowType definitions := by
  cases typed with
  | caseE control failure next =>
    cases control with | caseE flow failure next => exact ⟨_, flow⟩

end Solcore.SourceSemantics.CoreLowering.TypedLexicalWhile.Native
