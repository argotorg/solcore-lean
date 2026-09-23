import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

/-! Actual values, worlds and stores are independent evidence, not inferred
from accepted source syntax. A typed continuation is a separate obligation. -/
set_option autoImplicit false
namespace Tests.FrontendLocalApplicationRuntimeSafety
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RuntimeCall", by decide⟩], by decide⟩⟩, 8⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def aid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 999⟩
private def names : LocalNameTable := [("f", fid), ("x", aid), ("f", aid)]
private def context (a b : Core.Ty) : Resolved.Context := [(aid, a), (fid, .function a b)]
private def span : Syntax.SourceSpan := ⟨⟨.main, "runtime-call.sol"⟩, 31, 4⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def source (s t : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .call (ref s "f") ⟨t, [ref t "x"]⟩⟩
private def core : Core.Expr := .apply (.var 1) (.var 0)
private def environment (f x : Core.Value) : Resolved.Environment := [(aid, x), (fid, f)]
private theorem elaborated (a b : Core.Ty) (s t : Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates names (context a b) (source s t) core b :=
  .call (parameterType := a) (.identifier .head)
    (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head))
    (.identifier (.tail (by change "f" ≠ "x"; decide) .head)) (.var .head) (.var .head)
private theorem callCost (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (x value : Core.Value) (store final : Core.Store) (cost : Nat) (s t : Syntax.SourceSpan)
    (path : Core.Steps cost (.initial body (x :: captured) store) (.final value final)) :
    LocalFunctionApplicationEvaluatesWithCost names (environment (.closure a b body captured) x)
      store (source s t) value final (1 + 1 + cost + 3) :=
  .call (.identifier .head (.tail (by decide) .head))
    (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head) path
private theorem environmentTyped {world : Core.StoreTyping} {a b : Core.Ty} {f x : Core.Value}
    (ft : Core.RuntimeValueHasType world f (.function a b)) (xt : Core.RuntimeValueHasType world x a) :
    Core.RuntimeEnvironmentHasTypes world (environment f x).values (context a b).values :=
  .cons xt (.cons ft .nil)
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private theorem delayTyped (n index : Nat) (a b : Core.Ty) (rest : Core.Context)
    (found : (a :: rest)[index]? = some b) : Core.HasType (a :: rest) (delay n index) b := by
  induction n generalizing index rest with
  | zero => exact .var found
  | succ n ih => exact .letE (.var rfl) (ih (index + 1) (a :: rest) (by simpa using found))
private theorem delayPath (n index : Nat) (x v : Core.Value) (rest : Core.Environment)
    (store : Core.Store) (k : List Core.Frame) (found : (x :: rest)[index]? = some v) :
    Core.Steps (3 * n + 1) ⟨.eval (delay n index) (x :: rest), k, store⟩ ⟨.ret v, k, store⟩ := by
  induction n generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (x :: rest) k (by simpa using found))))
private def delayed (a b : Core.Ty) (n : Nat) (v : Core.Value) : Core.Value := .closure a b (delay n 1) [v]
private theorem delayedTyped {world : Core.StoreTyping} {a b : Core.Ty} {v : Core.Value}
    (typed : Core.RuntimeValueHasType world v b) (n : Nat) :
    Core.RuntimeValueHasType world (delayed a b n v) (.function a b) :=
  .closure (.cons typed .nil) (delayTyped n 1 a b [b] rfl)
private theorem delayedCost (a b : Core.Ty) (n : Nat) (x v : Core.Value) (store : Core.Store)
    (s t : Syntax.SourceSpan) : LocalFunctionApplicationEvaluatesWithCost names
      (environment (delayed a b n v) x) store (source s t) v store (3 * n + 6) := by
  have path := callCost a b (delay n 1) [v] x v store store (3 * n + 1) s t (delayPath n 1 x v [v] store [] rfl)
  have equal : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
  exact equal ▸ path

theorem independent_actual_typed_depth_has_exact_cost {world : Core.StoreTyping} {a b : Core.Ty}
    {x v : Core.Value} (xt : Core.RuntimeValueHasType world x a) (vt : Core.RuntimeValueHasType world v b)
    (n : Nat) (store : Core.Store) (s t : Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates names (context a b) (source s t) core b ∧
    Core.RuntimeEnvironmentHasTypes world (environment (delayed a b n v) x).values (context a b).values ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment (delayed a b n v) x) store (source s t) v store (3 * n + 6) ∧
    ∀ k, Core.Steps (3 * n + 6) ⟨.eval core (environment (delayed a b n v) x).values, k, store⟩ ⟨.ret v, k, store⟩ := by
  refine ⟨elaborated a b s t, environmentTyped (delayedTyped vt n) xt, delayedCost a b n x v store s t, ?_⟩
  intro k
  have path := CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    (delayPath n 1 x v [v] store [] rfl) (function := .var 1) (argument := .var 0)
    (environment := (environment (delayed a b n v) x).values) (parameterType := a) (resultType := b) (continuation := k)
  have equal : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
  exact equal ▸ path

theorem fixed_source_and_types_have_no_uniform_actual_body_cost (bound : Nat) :
    ∃ f cost, Core.RuntimeEnvironmentHasTypes [] (environment f .unit).values (context .unit .unit).values ∧
      LocalFunctionApplicationEvaluatesWithCost names (environment f .unit) [] (source span span) .unit [] cost ∧ bound < cost :=
  ⟨delayed .unit .unit bound .unit, 3 * bound + 6, environmentTyped (delayedTyped .unit bound) .unit,
    delayedCost .unit .unit bound .unit .unit [] span span, by omega⟩

private def reader : Core.Value := .closure .unit .word (.loadCell (.var 1)) [.cellRef .word 0]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private theorem readerTyped : Core.RuntimeValueHasType [.word] reader (.function .unit .word) :=
  .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl) .word)
private theorem wordStore (n : Nat) : Core.StoreHasTypes [.word] [w n] := by
  simpa [w] using Core.StoreHasTypes.nil.allocate .word (Core.ValueHasType.word (value := Core.Word.ofNatModulo n))
private theorem readerCost (n : Nat) : LocalFunctionApplicationEvaluatesWithCost names
    (environment reader .unit) [w n] (source span span) (w n) [w n] 8 :=
  callCost .unit .word (.loadCell (.var 1)) [.cellRef .word 0] .unit (w n) [w n] [w n] 3 span span
    (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
private def checkpoint (store : Core.Store) : Core.State :=
  ⟨.eval (.var 0) (environment reader .unit).values, [.applyClosure .unit .word (.loadCell (.var 1)) [.cellRef .word 0]], store⟩

theorem captured_reference_has_independent_world_store_and_value (n : Nat) :
    Core.RuntimeEnvironmentHasTypes [.word] (environment reader .unit).values (context .unit .word).values ∧
    Core.StoreHasTypes [.word] [w n] ∧ Core.RuntimeValueHasType [.word] (w n) .word ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment reader .unit) [w n] (source span span) (w n) [w n] 8 :=
  ⟨environmentTyped readerTyped .unit, wordStore n, .word, readerCost n⟩

theorem typed_reader_preserves_its_genuine_checkpoint_and_safe_resumption
    (n fuel additional : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.StateHasType (.initial core (environment reader .unit).values [w n]) .word ∧
    Core.runStateful fuel (.initial core (environment reader .unit).values [w n]) ≠ .fault error faultState ∧
    Core.runStateful 3 (.initial core (environment reader .unit).values [w n]) = .outOfFuel (checkpoint [w n]) ∧
    Core.StateHasType (checkpoint [w n]) .word ∧
    Core.runStateful additional (checkpoint [w n]) ≠ .fault error faultState ∧
    Core.runStateful additional (checkpoint [w n]) = Core.runStateful (3 + additional) (.initial core (environment reader .unit).values [w n]) ∧
    Core.Steps 5 (checkpoint [w n]) (.final (w n) [w n]) := by
  have e := elaborated .unit .word span span
  have envt := environmentTyped readerTyped Core.RuntimeValueHasType.unit
  have stopped : Core.runStateful 3 (.initial core (environment reader .unit).values [w n]) = .outOfFuel (checkpoint [w n]) := rfl
  exact ⟨e.runtime_state_hasType envt (wordStore n) .nil,
    e.runtime_run_never_faults envt (wordStore n) .nil fuel error faultState, stopped,
    e.runtime_checkpoint_hasType envt (wordStore n) .nil stopped,
    e.runtime_checkpoint_never_faults envt (wordStore n) .nil stopped additional error faultState,
    Core.runStateful_resume stopped additional, ((readerCost n).toSteps e rfl).residual_of_outOfFuel stopped |>.2⟩

theorem typed_completion_retains_the_independently_fixed_value_and_cost
    {world : Core.StoreTyping} {a b : Core.Ty} {x v : Core.Value}
    (xt : Core.RuntimeValueHasType world x a) (vt : Core.RuntimeValueHasType world v b)
    (n : Nat) {store : Core.Store} (st : Core.StoreHasTypes world store) :
    ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future store ∧
      Core.RuntimeValueHasType future v b ∧ LocalFunctionApplicationEvaluatesWithCost names
        (environment (delayed a b n v) x) store (source span span) v store (3 * n + 6) := by
  obtain ⟨future, final, result, cost, ext, stored, typed, evaluated⟩ :=
    (elaborated a b span span).hasType.runtime_evaluates rfl (environmentTyped (delayedTyped vt n) xt) st
  obtain ⟨rfl, rfl, rfl⟩ := evaluated.deterministic (delayedCost a b n x v store span span)
  exact ⟨future, ext, stored, typed, evaluated⟩

theorem actual_cost_precedes_all_endpoints_and_closed_fuel_thresholds
    {world : Core.StoreTyping} {a b : Core.Ty} {x v : Core.Value}
    (xt : Core.RuntimeValueHasType world x a) (vt : Core.RuntimeValueHasType world v b)
    (n : Nat) {store : Core.Store} (st : Core.StoreHasTypes world store) :
    (∀ k, Core.Steps (3 * n + 6) ⟨.eval core (environment (delayed a b n v) x).values, k, store⟩ ⟨.ret v, k, store⟩) ∧
    ∀ fuel, (Core.runStateful fuel (.initial core (environment (delayed a b n v) x).values store) = .done v store ↔ 3 * n + 6 ≤ fuel) ∧
      ((∃ cp, Core.runStateful fuel (.initial core (environment (delayed a b n v) x).values store) = .outOfFuel cp) ↔ fuel < 3 * n + 6) := by
  obtain ⟨_, final, result, cost, _, _, _, evaluated, paths, thresholds⟩ :=
    (elaborated a b span span).runtime_typed_execution rfl (environmentTyped (delayedTyped vt n) xt) st
  obtain ⟨rfl, rfl, rfl⟩ := evaluated.deterministic (delayedCost a b n x v store span span)
  exact ⟨paths, thresholds⟩

theorem preservation_and_checker_soundness_keep_the_actual_store (n : Nat) :
    (∃ future, Core.WorldExtends [.word] future ∧ Core.StoreHasTypes future [w n] ∧ Core.RuntimeValueHasType future (w n) .word) ∧
    LocalFunctionApplicationEvaluates names (environment reader .unit) [w n] (source span span) (w n) [w n] := by
  have e := elaborated .unit .word span span
  have et := environmentTyped readerTyped Core.RuntimeValueHasType.unit
  have preservation := (readerCost n).erase.preserves_runtime_type e rfl et (wordStore n)
  have completed := ((readerCost n).toSteps e rfl).runStateful_done_iff.mpr (Nat.le_refl 8)
  have sound := elaborateLocalFunctionApplication?_runtime_run_done_sound e.complete rfl et (wordStore n) completed
  exact ⟨preservation, sound.1⟩

private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
theorem allocation_changes_both_the_store_and_its_world {world : Core.StoreTyping} {store : Core.Store}
    (st : Core.StoreHasTypes world store) (n : Nat) :
    Core.RuntimeEnvironmentHasTypes world (environment allocator (w n)).values (context .word (.cell .word)).values ∧
    Core.WorldExtends world (world ++ [.word]) ∧ Core.StoreHasTypes (world ++ [.word]) (store ++ [w n]) ∧
    Core.RuntimeValueHasType (world ++ [.word]) (.cellRef .word store.length) (.cell .word) ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment allocator (w n)) store (source span span)
      (.cellRef .word store.length) (store ++ [w n]) 8 ∧ store ++ [w n] ≠ store := by
  refine ⟨environmentTyped (.closure .nil (.newCell (.var rfl) .word)) .word, ⟨[.word], rfl⟩,
    st.allocate .word .word, .cellRef ?_, ?_, ?_⟩
  · simp [← st.length_eq]
  · exact callCost .word (.cell .word) (.newCell .word (.var 0)) [] (w n) (.cellRef .word store.length)
      store (store ++ [w n]) 3 span span (.cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
  · intro equal
    have lengths := congrArg List.length equal
    simp at lengths

theorem arbitrary_outer_frames_need_their_own_typing (n fuel : Nat) (k : List Core.Frame) (result : Core.Ty)
    (kt : Core.ContinuationHasType [.word] k .word result) (error : Core.MachineFault) (faultState : Core.State) :
    Core.StateHasType ⟨.eval core (environment reader .unit).values, k, [w n]⟩ result ∧
    Core.runStateful fuel ⟨.eval core (environment reader .unit).values, k, [w n]⟩ ≠ .fault error faultState :=
  ⟨(elaborated .unit .word span span).runtime_state_hasType (environmentTyped readerTyped .unit) (wordStore n) kt,
    (elaborated .unit .word span span).runtime_run_never_faults (environmentTyped readerTyped .unit) (wordStore n) kt fuel error faultState⟩

theorem runtime_world_alone_does_not_validate_an_empty_store :
    Core.RuntimeEnvironmentHasTypes [.word] (environment reader .unit).values (context .unit .word).values ∧
    ¬ Core.StoreHasTypes [.word] [] ∧
    Core.runStateful 7 (.initial core (environment reader .unit).values []) =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ := by
  refine ⟨environmentTyped readerTyped .unit, ?_, rfl⟩
  intro stored
  have lengths := stored.length_eq
  cases lengths

theorem equal_lengths_do_not_make_wrong_payloads_runtime_safe :
    ([Core.Ty.word] : Core.StoreTyping).length = ([Core.Value.bool true] : Core.Store).length ∧
    ¬ Core.StoreHasTypes [.word] [.bool true] ∧
    Core.runStateful 8 (.initial core (environment reader .unit).values [.bool true]) = .done (.bool true) [.bool true] ∧
    ¬ Core.RuntimeValueHasType [.word] (.bool true) .word := by
  refine ⟨rfl, ?_, rfl, by intro typed; cases typed⟩
  intro stored
  obtain ⟨v, found, _, typed⟩ := stored.lookup (location := 0) rfl
  have same : v = .bool true := Option.some.inj found.symm
  subst v
  cases typed

theorem structural_reference_typing_does_not_supply_a_runtime_world :
    Core.ValueHasType (.cellRef .word 700) (.cell .word) ∧
    ¬ Core.RuntimeValueHasType [] (.cellRef .word 700) (.cell .word) := by
  refine ⟨.cellRef, ?_⟩
  intro typed
  cases typed with
  | cellRef found => cases found

private def nominal : Core.Ty := .namedData ⟨0⟩
private def nominalIdentity : Core.Value := .closure nominal nominal (.var 0) []
private theorem noNominal (dataType : Core.DataTypeId) {v : Core.Value}
    (typed : Core.RuntimeValueHasType [] v (.namedData dataType)) : False := by
  cases typed with
  | constructed lookup _ => cases lookup
theorem higher_order_nominal_functions_are_values_without_nominal_inhabitants :
    (¬ ∃ v, Core.RuntimeValueHasType [] v nominal) ∧
    Core.RuntimeValueHasType [] nominalIdentity (.function nominal nominal) ∧
    Core.RuntimeEnvironmentHasTypes []
      (environment (delayed (.function nominal nominal) (.function nominal nominal) 0 nominalIdentity) nominalIdentity).values
      (context (.function nominal nominal) (.function nominal nominal)).values ∧
    LocalFunctionApplicationEvaluatesWithCost names
      (environment (delayed (.function nominal nominal) (.function nominal nominal) 0 nominalIdentity) nominalIdentity)
      [] (source span span) nominalIdentity [] 6 := by
  have typed : Core.RuntimeValueHasType [] nominalIdentity (.function nominal nominal) := .closure .nil (.var rfl)
  refine ⟨?_, typed, environmentTyped (delayedTyped typed 0) typed,
    delayedCost _ _ 0 nominalIdentity nominalIdentity [] span span⟩
  rintro ⟨v, vt⟩
  exact noNominal ⟨0⟩ vt

theorem a_typed_call_endpoint_does_not_type_an_arbitrary_pending_frame :
    Core.RuntimeEnvironmentHasTypes [] (environment (delayed .unit .unit 0 .unit) .unit).values (context .unit .unit).values ∧
    (¬ ∃ result, Core.ContinuationHasType [] [.unaryApply .wordNot] .unit result) ∧
    Core.Steps 6 ⟨.eval core (environment (delayed .unit .unit 0 .unit) .unit).values, [.unaryApply .wordNot], []⟩
      ⟨.ret .unit, [.unaryApply .wordNot], []⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], []⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], []⟩ := by
  refine ⟨environmentTyped (delayedTyped .unit 0) .unit, ?_,
    (independent_actual_typed_depth_has_exact_cost (world := []) .unit .unit 0 [] span span).2.2.2 _, rfl⟩
  rintro ⟨_, kt⟩
  cases kt with
  | cons frame _ => cases frame

end Tests.FrontendLocalApplicationRuntimeSafety
