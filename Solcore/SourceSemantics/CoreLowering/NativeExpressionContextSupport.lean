import Solcore.Core.Renaming

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
