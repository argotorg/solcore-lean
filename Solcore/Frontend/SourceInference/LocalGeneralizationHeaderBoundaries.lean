import Solcore.Frontend.SourceInference.LocalGeneralizationBoundaryReceipts
import Solcore.Frontend.SourceInference.LocalReadScopeInference

/-! Each actual header initializer retains its retired-read boundary through
the remaining header items. Later initializers use their real entry states. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

theorem inferForItemFuel_boundary {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context item state = .ok result)
    (ready : Ready state) (below : state.LocalBindersBelowNextLocal) :
    ItemSince state.nextLocal result.2 result.1 := by
  cases fuel with
  | zero => simp [inferForItemFuel, throw] at accepted
  | succ fuel =>
    cases form : item.value with
    | letDecl name annotation initializer =>
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_initialized_accepted form accepted
        exact ItemSince.of_header receipt ready below
      | none =>
        unfold inferForItemFuel at accepted
        simp only [form, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals simp_all [ItemSince, pure, Pure.pure, Except.pure, throw]
        all_goals subst_vars
        all_goals simp_all [ItemSince]
    | expression expression | assignValue target operator value | assignBitNot target token =>
      unfold inferForItemFuel at accepted
      simp only [form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals simp_all [ItemSince, pure, Pure.pure, Except.pure, throw]
      all_goals subst_vars
      all_goals simp_all [ItemSince]

theorem inferForItemsFuel_boundaries {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context items state = .ok result)
    (ready : Ready state) (below : state.LocalBindersBelowNextLocal) :
    ItemsSince state.nextLocal result.state result.items := by
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
          have following := LocalReadScopeProgress.inferForItemsFuel_scope_progress tail
          exact (inferForItemFuel_boundary first ready below).progress following
        · exact ((ih tail (ready.progress (LocalReadEvents.inferForItemFuel_origins_progress first))
            (inferForItemFuel_preserves_localBindersBelowNextLocal below first)) value remaining).weaken
              (inferForItemFuel_nextLocal_le first)

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
