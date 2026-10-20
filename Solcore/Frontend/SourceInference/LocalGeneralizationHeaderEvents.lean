import Solcore.Frontend.SourceInference.LocalGeneralizationProgress

/-! Header events are recovered from the actual returned item sequence,
including the real entry state of each later initializer. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationEvents
open TypeSystem Detail

theorem inferForItemFuel_event {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context item state = .ok result)
    (ready : Ready state) : Item result.1 := by
  cases fuel with
  | zero => simp [inferForItemFuel, throw] at accepted
  | succ fuel =>
    cases form : item.value with
    | letDecl name annotation initializer =>
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_initialized_accepted form accepted
        exact Item.of_header receipt ready
      | none =>
        unfold inferForItemFuel at accepted
        simp only [form, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals simp_all [Item, pure, Pure.pure, Except.pure, throw]
        all_goals subst_vars
        all_goals simp_all [Item]
    | expression expression | assignValue target operator value | assignBitNot target token =>
      unfold inferForItemFuel at accepted
      simp only [form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals simp_all [Item, pure, Pure.pure, Except.pure, throw]
      all_goals subst_vars
      all_goals simp_all [Item]

theorem inferForItemsFuel_events {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context items state = .ok result)
    (ready : Ready state) : Items result.items := by
  induction items generalizing state result with
  | nil =>
    simp only [inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    intro item impossible
    cases impossible
  | cons item items ih =>
    unfold inferForItemsFuel at accepted
    cases first : inferForItemFuel fuel context item state with
    | error error => simp [first, bind, Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨head, next⟩
      cases tail : inferForItemsFuel fuel context items next with
      | error error => simp [first, tail, bind, Except.bind, Functor.map, Except.map] at accepted
      | ok rest =>
        simp only [first, tail, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        intro value member
        rcases List.mem_cons.mp member with same | remaining
        · cases same
          exact inferForItemFuel_event first ready
        · exact ih tail (ready.progress (LocalReadEvents.inferForItemFuel_origins_progress first)) value remaining

end Solcore.Frontend.SourceInference.LocalGeneralizationEvents
