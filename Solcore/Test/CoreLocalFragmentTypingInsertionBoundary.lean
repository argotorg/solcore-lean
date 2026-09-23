import Solcore.Core.LocalFragment
import Solcore.Core.Renaming
import Solcore.Core.Machine

/-! Typing insertion has a real position boundary. Whole structural membership
does not imply typing, even when an unselected ill-typed branch is never run. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentTypingInsertionBoundary

open Solcore.Core

private theorem weakenedBeyond : (Expr.var 0).weakenAt 1 = .var 0 := by simp [Expr.weakenAt]
private def badPrimitive : Expr := .binary .wordAdd (.bool true) (.var 0)
private theorem badFragment : badPrimitive.LocalFragment := .binary .bool .var
private theorem noTypingOfNone {context : Context} {expr : Expr} {definitions : DataEnvironment}
    (rejected : infer? context expr definitions = none) (type : Ty) : ¬HasType context expr type definitions := by
  intro typing
  have inferred := infer_complete typing
  rw [rejected] at inferred
  cases inferred
private theorem inferNoneOfNoTyping {context : Context} {expr : Expr} {definitions : DataEnvironment}
    (rejected : ∀ type, ¬HasType context expr type definitions) : infer? context expr definitions = none := by
  cases inferred : infer? context expr definitions with
  | none => rfl
  | some type => exact False.elim (rejected type (infer_sound inferred))
private theorem missingRejected (definitions : DataEnvironment) : infer? [] (.var 0) definitions = none := by
  apply inferNoneOfNoTyping
  intro type typing
  cases typing with
  | var found => cases found
private theorem badNoTyping {context : Context} {definitions : DataEnvironment} {type : Ty} :
    ¬HasType context badPrimitive type definitions := by
  intro typing
  cases typing with
  | binary left _ => cases left

theorem clamped_out_of_range_insertion_can_enable_an_unshifted_missing_reference
    (definitions : DataEnvironment) :
    Context.insertAt [] 1 .bool = [.bool] ∧ (Expr.var 0).weakenAt 1 = .var 0 ∧
    Expr.LocalFragment (.var 0) ∧
    HasType (Context.insertAt [] 1 .bool) ((Expr.var 0).weakenAt 1) .bool definitions ∧
    ¬HasType [] (.var 0) .bool definitions ∧
    infer? (Context.insertAt [] 1 .bool) ((Expr.var 0).weakenAt 1) definitions = some .bool ∧
    infer? [] (.var 0) definitions = none := by
  have enabled : HasType (Context.insertAt [] 1 .bool) ((Expr.var 0).weakenAt 1) .bool definitions := by
    rw [weakenedBeyond]
    exact .var rfl
  refine ⟨rfl, weakenedBeyond, .var, enabled, ?_, infer_complete enabled, ?_⟩
  · intro typing
    cases typing with
    | var found => cases found
  · exact missingRejected definitions

theorem properly_shifted_missing_references_remain_rejected_without_original_scope
    (inserted resultType : Ty) (definitions : DataEnvironment) :
    Expr.LocalFragment ((Expr.var 0).weakenAt 0) ∧
    ¬HasType [] (.var 0) resultType definitions ∧
    ¬HasType [inserted] ((Expr.var 0).weakenAt 0) resultType definitions ∧
    infer? [] (.var 0) definitions = none ∧
    infer? [inserted] ((Expr.var 0).weakenAt 0) definitions = none := by
  have rejected := missingRejected definitions
  have missing := noTypingOfNone rejected resultType
  refine ⟨Expr.LocalFragment.weakenAt .var 0, missing, ?_, rejected, ?_⟩
  · intro typing
    exact missing (typing.reflect_weakenAt_zero_localFragment .var)
  · exact (Expr.LocalFragment.var.infer_weaken_zero [] inserted definitions).trans rejected

theorem unshifted_lookup_changes_inference_while_correct_insertion_retains_the_old_type
    (old inserted : Ty) (different : inserted ≠ old) (tail : Context) (definitions : DataEnvironment) :
    infer? (old :: tail) (.var 0) definitions = some old ∧
    infer? (inserted :: old :: tail) (.var 0) definitions = some inserted ∧
    infer? (inserted :: old :: tail) ((Expr.var 0).weakenAt 0) definitions = some old ∧
    HasType (inserted :: old :: tail) ((Expr.var 0).weakenAt 0) old definitions ∧
    infer? (old :: tail) (.var 0) definitions ≠
      infer? (inserted :: old :: tail) (.var 0) definitions := by
  have original : HasType (old :: tail) (.var 0) old definitions := .var rfl
  have shifted := original.weakenAt_zero_localFragment .var inserted
  have originalInfer := infer_complete original
  have newInfer : infer? (inserted :: old :: tail) (.var 0) definitions = some inserted :=
    infer_complete (.var rfl)
  refine ⟨originalInfer, newInfer, infer_complete shifted, shifted, ?_⟩
  rw [originalInfer, newInfer]
  intro same
  exact different (Option.some.inj same).symm

theorem wrong_primitive_remains_rejected_at_every_valid_retained_prefix
    (leading suffix : Context) (inserted : Ty) (definitions : DataEnvironment) :
    badPrimitive.LocalFragment ∧
    infer? (leading ++ suffix) badPrimitive definitions = none ∧
    infer? (leading ++ inserted :: suffix) (badPrimitive.weakenAt leading.length) definitions = none ∧
    (∀ type, ¬HasType (leading ++ suffix) badPrimitive type definitions) ∧
    (∀ type, ¬HasType (leading ++ inserted :: suffix)
      (badPrimitive.weakenAt leading.length) type definitions) := by
  have rejected : infer? (leading ++ suffix) badPrimitive definitions = none :=
    inferNoneOfNoTyping (fun _ => badNoTyping)
  refine ⟨badFragment, rejected, (badFragment.infer_insert leading suffix inserted definitions).trans rejected,
    noTypingOfNone rejected, ?_⟩
  intro type typing
  exact noTypingOfNone rejected type ((badFragment.hasType_insert_iff leading suffix inserted).mp typing)

private def skipped (choice : Bool) : Expr :=
  if choice then .ifE (.bool true) .unit badPrimitive else .ifE (.bool false) badPrimitive .unit
private theorem skippedFragment (choice : Bool) : (skipped choice).LocalFragment := by
  cases choice
  · exact .ifE .bool badFragment .unit
  · exact .ifE .bool .unit badFragment

theorem selected_constant_execution_does_not_type_an_unselected_bad_primitive
    (choice : Bool) (context : Context) (inserted : Ty) (definitions : DataEnvironment)
    (environment : Environment) (store : Store) :
    (skipped choice).LocalFragment ∧
    Evaluates environment store (skipped choice) .unit store ∧
    runStateful 4 (State.initial (skipped choice) environment store) = .done .unit store ∧
    infer? context (skipped choice) definitions = none ∧
    infer? (inserted :: context) ((skipped choice).weakenAt 0) definitions = none ∧
    (∀ type, ¬HasType (inserted :: context) ((skipped choice).weakenAt 0) type definitions) := by
  have rejected : infer? context (skipped choice) definitions = none := by
    apply inferNoneOfNoTyping
    intro type typing
    cases choice
    · cases typing with
      | ifE _ branch _ => exact badNoTyping branch
    · cases typing with
      | ifE _ _ branch => exact badNoTyping branch
  have evaluation : Evaluates environment store (skipped choice) .unit store := by
    cases choice
    · exact .ifFalse .bool .unit
    · exact .ifTrue .bool .unit
  have run : runStateful 4 (State.initial (skipped choice) environment store) = .done .unit store := by
    cases choice <;> rfl
  refine ⟨skippedFragment choice, evaluation, run, rejected,
    ((skippedFragment choice).infer_weaken_zero context inserted definitions).trans rejected, ?_⟩
  intro type typing
  exact noTypingOfNone rejected type
    (((skippedFragment choice).hasType_weaken_zero_iff context inserted).mp typing)

theorem selected_branch_does_not_supply_a_type_for_a_missing_unselected_reference
    (inserted : Ty) (definitions : DataEnvironment) (environment : Environment) (store : Store) :
    Expr.LocalFragment (.ifE (.bool true) .unit (.var 0)) ∧
    Evaluates environment store (.ifE (.bool true) .unit (.var 0)) .unit store ∧
    infer? [] (.ifE (.bool true) .unit (.var 0)) definitions = none ∧
    infer? [inserted] ((Expr.ifE (.bool true) .unit (.var 0)).weakenAt 0) definitions = none := by
  have fragment : Expr.LocalFragment (.ifE (.bool true) .unit (.var 0)) := .ifE .bool .unit .var
  have rejected : infer? [] (.ifE (.bool true) .unit (.var 0)) definitions = none := by
    apply inferNoneOfNoTyping
    intro type typing
    cases typing with
    | ifE _ _ branch =>
        cases branch with
        | var found => cases found
  exact ⟨fragment, .ifTrue .bool .unit, rejected, (fragment.infer_weaken_zero [] inserted definitions).trans rejected⟩

end Tests.CoreLocalFragmentTypingInsertionBoundary
