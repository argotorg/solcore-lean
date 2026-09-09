import Solcore.Frontend.ComputationReturnTreeRuntimeSafetyProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.FuelResumptionProperties

/-! A fixed original mixed body has independent source and literal Core paths.
Actual closure bodies/captures choose its value, store and cost. Runtime-world
safety identifies these existing witnesses; it does not manufacture them. -/
set_option autoImplicit false
namespace Tests.FrontendComputationRuntimeSafety
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RuntimeBody",by decide⟩],by decide⟩⟩,73⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"runtime-body.sol"⟩,0,41⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def call : Syntax.Expr := ⟨span,.call (ref "f") ⟨span,[ref "x"]⟩⟩
private def source : Syntax.Block := ⟨span,[⟨span,.letDecl ⟨span,"r"⟩ none (some call)⟩,
  ⟨span,.expression (ref "r") true⟩,⟨span,.returnStmt (some (ref "r"))⟩]⟩
private def inputs (a b : Core.Ty) : LocalTypeInputs :=
  (LocalTypeInputs.empty.bindFresh owner "f" (.function a b)).bindFresh owner "x" a
private def environment (f x : Core.Value) : Resolved.Environment := [(⟨owner,1⟩,x),(⟨owner,0⟩,f)]
private def invocation : Core.Expr := .apply (.var 1) (.var 0)
private def tailCore : Core.Expr := .letE (.var 0) (.var 1)
private def core : Core.Expr := .letE invocation tailCore
private theorem child (a b : Core.Ty) :
    RecursiveLocalComputationElaborates (inputs a b).names (inputs a b).context call invocation b :=
  .application (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head))
    (.var (.tail (by change (⟨owner,1⟩ : Resolved.LocalId) ≠ ⟨owner,0⟩; decide) .head))
    (.var (.tail (by change (⟨owner,1⟩ : Resolved.LocalId) ≠ ⟨owner,0⟩; decide) .head)))
    (.pure (.identifier .head) (.var .head) (.var .head))
private theorem elaborated (a b : Core.Ty) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs a b) source core b := by
  have shift : (Core.Expr.var 0).weakenAt 0 = .var 1 := by simp [Core.Expr.weakenAt]
  simp only [source,core,tailCore,←shift]
  exact .inferred (by change "r" ∉ ["x","f"]; decide) (child a b)
    (.discard (.pure (.identifier .head) (.var .head) (.var .head))
      (.expression (.pure (.identifier .head) (.var .head) (.var .head))))
private theorem counted (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (x value : Core.Value) (store final : Core.Store) (cost : Nat)
    (path : Core.Steps cost (.initial body (x::captured) store) (.final value final)) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a b).names
      (environment (.closure a b body captured) x) store source value final (cost+11) := by
  have callCount : RecursiveLocalComputationEvaluatesWithCost (inputs a b).names
      (environment (.closure a b body captured) x) store call value final (1+1+cost+3) :=
    .application (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head)
      (.tail (by change (⟨owner,1⟩ : Resolved.LocalId) ≠ ⟨owner,0⟩; decide) .head)))
      (.pure (.identifier .head .head)) path
  have result : RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a b).names
      (environment (.closure a b body captured) x) store source value final (1+1+cost+3+4+2) :=
    ComputationReturnTreeEvaluatesWithCost.inferred (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      (initializerCost := 1+1+cost+3) (tailCost := 4) callCount
      (ComputationReturnTreeEvaluatesWithCost.discard (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        (.pure (.identifier .head .head)) (.expression (.pure (.identifier .head .head))))
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
private theorem callPath (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (x value : Core.Value) (store final : Core.Store) (cost : Nat) (k : List Core.Frame)
    (path : Core.Steps cost ⟨.eval body (x::captured),k,store⟩ ⟨.ret value,k,final⟩) :
    Core.Steps (cost+5) ⟨.eval invocation (environment (.closure a b body captured) x).values,k,store⟩
      ⟨.ret value,k,final⟩ := by
  simpa [invocation,Nat.add_assoc] using Core.Steps.cons .enterApply
    (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure path))))
private theorem manual (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (x value : Core.Value) (store final : Core.Store) (cost : Nat)
    (path : ∀ k, Core.Steps cost ⟨.eval body (x::captured),k,store⟩ ⟨.ret value,k,final⟩)
    (k : List Core.Frame) : Core.Steps (cost+11)
      ⟨.eval core (environment (.closure a b body captured) x).values,k,store⟩ ⟨.ret value,k,final⟩ := by
  simpa only [core,Nat.add_assoc] using CostStepComposition.letE
    (callPath a b body captured x value store final cost _ (path _))
    (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))) :
      Core.Steps 4 ⟨.eval tailCore (value::(environment (.closure a b body captured) x).values),k,final⟩
        ⟨.ret value,k,final⟩)
private theorem environmentTyped {world : Core.StoreTyping} {a b : Core.Ty} {f x : Core.Value}
    (ft : Core.RuntimeValueHasType world f (.function a b)) (xt : Core.RuntimeValueHasType world x a) :
    Core.RuntimeEnvironmentHasTypes world (environment f x).values (inputs a b).context.values :=
  .cons xt (.cons ft .nil)

theorem original_body_has_independent_cost_and_all_paths (a b : Core.Ty) (body : Core.Expr)
    (captured : Core.Environment) (x value : Core.Value) (store final : Core.Store) (cost : Nat)
    (path : ∀ k, Core.Steps cost ⟨.eval body (x::captured),k,store⟩ ⟨.ret value,k,final⟩) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs a b) source core b ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a b).names
      (environment (.closure a b body captured) x) store source value final (cost+11) ∧
    ∀ k, Core.Steps (cost+11) ⟨.eval core (environment (.closure a b body captured) x).values,k,store⟩
      ⟨.ret value,k,final⟩ :=
  ⟨elaborated a b,counted a b body captured x value store final cost (path []),
    manual a b body captured x value store final cost path⟩

theorem same_world_safety_identifies_the_independent_actual_path
    {world : Core.StoreTyping} {a b : Core.Ty} {body : Core.Expr} {captured : Core.Environment}
    {x value : Core.Value} {store final : Core.Store} {cost : Nat}
    (ft : Core.RuntimeValueHasType world (.closure a b body captured) (.function a b))
    (xt : Core.RuntimeValueHasType world x a) (st : Core.StoreHasTypes world store)
    (path : ∀ k, Core.Steps cost ⟨.eval body (x::captured),k,store⟩ ⟨.ret value,k,final⟩) :
    ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future final ∧
      Core.RuntimeValueHasType future value b ∧
      RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a b).names
        (environment (.closure a b body captured) x) store source value final (cost+11) ∧
      (∀ k, Core.Steps (cost+11) ⟨.eval core (environment (.closure a b body captured) x).values,k,store⟩
        ⟨.ret value,k,final⟩) ∧
      ∀ fuel, (Core.runStateful fuel (.initial core (environment (.closure a b body captured) x).values store)=
        .done value final ↔ cost+11≤fuel) ∧
        ((∃ cp, Core.runStateful fuel (.initial core (environment (.closure a b body captured) x).values store)=
          .outOfFuel cp) ↔ fuel<cost+11) := by
  obtain ⟨future,resultStore,result,n,ext,stored,typed,raw,paths,thresholds⟩ :=
    ComputationReturnTreeElaborates.runtime_typed_execution
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates)
      (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost
      RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
      (elaborated a b) rfl (environmentTyped ft xt) st
  obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique (manual a b body captured x value store final cost path [])
  exact ⟨future,ext,stored,typed,raw,paths,thresholds⟩

private def delay : Nat → Nat → Core.Expr
  | 0,index => .var index | n+1,index => .letE (.var 0) (delay n (index+1))
private theorem delayTyped (n index : Nat) (a b : Core.Ty) (rest : Core.Context)
    (found : (a::rest)[index]?=some b) : Core.HasType (a::rest) (delay n index) b := by
  induction n generalizing index rest with
  | zero => exact .var found
  | succ n ih => exact .letE (.var rfl) (ih (index+1) (a::rest) (by simpa using found))
private theorem delayPath (n index : Nat) (x value : Core.Value) (rest : Core.Environment)
    (store : Core.Store) (k : List Core.Frame) (found : (x::rest)[index]?=some value) :
    Core.Steps (3*n+1) ⟨.eval (delay n index) (x::rest),k,store⟩ ⟨.ret value,k,store⟩ := by
  induction n generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      simpa [delay,Nat.mul_add,Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index+1) (x::rest) k (by simpa using found))))
private def closure (a b : Core.Ty) (n : Nat) (value : Core.Value) (captured : Core.Environment) :=
  Core.Value.closure a b (delay n 1) (value::captured)
private theorem closureTyped {world : Core.StoreTyping} {a b : Core.Ty} {value : Core.Value}
    {captured : Core.Environment} {context : Core.Context}
    (vt : Core.RuntimeValueHasType world value b) (ct : Core.RuntimeEnvironmentHasTypes world captured context)
    (n : Nat) : Core.RuntimeValueHasType world (closure a b n value captured) (.function a b) :=
  .closure (.cons vt ct) (delayTyped n 1 a b (b::context) rfl)

theorem arbitrary_well_typed_delays_keep_literal_captures_and_source_cost
    {world : Core.StoreTyping} {a b : Core.Ty} {x value : Core.Value}
    {captured : Core.Environment} {context : Core.Context} {store : Core.Store}
    (xt : Core.RuntimeValueHasType world x a) (vt : Core.RuntimeValueHasType world value b)
    (ct : Core.RuntimeEnvironmentHasTypes world captured context) (st : Core.StoreHasTypes world store) (n : Nat) :
    Core.RuntimeEnvironmentHasTypes world (environment (closure a b n value captured) x).values (inputs a b).context.values ∧
    ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future store ∧
      Core.RuntimeValueHasType future value b ∧
      RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a b).names
        (environment (closure a b n value captured) x) store source value store (3*n+12) := by
  have ft := closureTyped (a := a) vt ct n
  obtain ⟨future,ext,stored,typed,raw,_⟩ := same_world_safety_identifies_the_independent_actual_path
    ft xt st (fun k => delayPath n 1 x value (value::captured) store k rfl)
  exact ⟨environmentTyped ft xt,future,ext,stored,typed,by simpa [closure,Nat.add_assoc] using raw⟩

theorem fixed_original_source_has_no_uniform_actual_cost (bound : Nat) :
    ∃ f cost, Core.RuntimeEnvironmentHasTypes [] (environment f .unit).values (inputs .unit .unit).context.values ∧
      RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit .unit).names
        (environment f .unit) [] source .unit [] cost ∧ bound<cost := by
  obtain ⟨envt,_,_,_,_,raw⟩ := arbitrary_well_typed_delays_keep_literal_captures_and_source_cost
    Core.RuntimeValueHasType.unit Core.RuntimeValueHasType.unit Core.RuntimeEnvironmentHasTypes.nil Core.StoreHasTypes.nil bound
  exact ⟨closure .unit .unit bound .unit [],3*bound+12,envt,raw,by omega⟩

theorem same_typed_capture_swaps_change_the_actual_result (n : Nat) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit .bool).names
      (environment (closure .unit .bool n (.bool false) []) .unit) [] source (.bool false) [] (3*n+12) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit .bool).names
      (environment (closure .unit .bool n (.bool true) []) .unit) [] source (.bool true) [] (3*n+12) := by
  constructor
  all_goals
    obtain ⟨_,_,_,_,_,raw⟩ := arbitrary_well_typed_delays_keep_literal_captures_and_source_cost
      Core.RuntimeValueHasType.unit Core.RuntimeValueHasType.bool Core.RuntimeEnvironmentHasTypes.nil Core.StoreHasTypes.nil n
    exact raw

private def hidden (f x value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.eval tailCore (value::(environment f x).values),[],store⟩
theorem actual_bound_slot_and_every_resumed_fuel (a b : Core.Ty) (n : Nat)
    (x value : Core.Value) (captured : Core.Environment) (store : Core.Store) (additional : Nat) :
    Core.runStateful (3*n+8) (.initial core (environment (closure a b n value captured) x).values store)=
      .outOfFuel (hidden (closure a b n value captured) x value store) ∧
    Core.Steps 4 (hidden (closure a b n value captured) x value store) (.final value store) ∧
    Core.runStateful additional (hidden (closure a b n value captured) x value store)=
      Core.runStateful (3*n+8+additional) (.initial core (environment (closure a b n value captured) x).values store) := by
  have prefixPath : Core.Steps (3*n+8) (.initial core (environment (closure a b n value captured) x).values store)
      (hidden (closure a b n value captured) x value store) := by
    simpa [core,hidden,closure,Core.State.initial,Nat.add_assoc] using Core.Steps.cons .enterLet
      ((callPath a b (delay n 1) (value::captured) x value store store (3*n+1) _
        (delayPath n 1 x value (value::captured) store _ rfl)).trans (.cons .bindLet .refl))
  have exhausted := Core.runStateful_outOfFuel_complete prefixPath (Core.advance_next_iff.mpr .enterLet)
  exact ⟨exhausted,.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))),
    Core.runStateful_resume exhausted additional⟩

private def discarded (f x value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 1) (value::value::(environment f x).values),[],store⟩
theorem discard_adds_the_actual_hidden_slot (a b : Core.Ty) (n : Nat)
    (x value : Core.Value) (captured : Core.Environment) (store : Core.Store) (additional : Nat) :
    Core.runStateful (3*n+11) (.initial core (environment (closure a b n value captured) x).values store)=
      .outOfFuel (discarded (closure a b n value captured) x value store) ∧
    Core.runStateful 1 (discarded (closure a b n value captured) x value store)=.done value store ∧
    Core.runStateful additional (discarded (closure a b n value captured) x value store)=
      Core.runStateful (3*n+11+additional) (.initial core (environment (closure a b n value captured) x).values store) := by
  have before := (actual_bound_slot_and_every_resumed_fuel a b n x value captured store 0).1
  have suffix : Core.Steps 3 (hidden (closure a b n value captured) x value store)
      (discarded (closure a b n value captured) x value store) :=
    .cons .enterLet (.cons (.var rfl) (.cons .bindLet .refl))
  have path : Core.Steps (3*n+11) (.initial core (environment (closure a b n value captured) x).values store)
      (discarded (closure a b n value captured) x value store) := by
    simpa [Nat.add_assoc] using (Core.runStateful_outOfFuel_sound before).1.trans suffix
  have exhausted := Core.runStateful_outOfFuel_complete path (Core.advance_next_iff.mpr (.var rfl))
  exact ⟨exhausted,rfl,Core.runStateful_resume exhausted additional⟩

theorem all_actual_checkpoints_keep_the_exact_remaining_cost (a b : Core.Ty) (n : Nat)
    (x value : Core.Value) (captured : Core.Environment) (store : Core.Store) {spent : Nat} {cp : Core.State}
    (exhausted : Core.runStateful spent (.initial core (environment (closure a b n value captured) x).values store)=.outOfFuel cp) :
    spent<3*n+12 ∧ Core.Steps (3*n+12-spent) cp (.final value store) ∧
      ∀ additional, (Core.runStateful additional cp=.done value store ↔ 3*n+12-spent≤additional) ∧
        Core.runStateful additional cp=Core.runStateful (spent+additional)
          (.initial core (environment (closure a b n value captured) x).values store) := by
  have path : Core.Steps (3*n+12) (.initial core (environment (closure a b n value captured) x).values store) (.final value store) := by
    simpa [closure,Core.State.initial,Core.State.final,Nat.add_assoc] using manual a b (delay n 1) (value::captured) x value store store (3*n+1)
      (fun k => delayPath n 1 x value (value::captured) store k rfl) []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨residual.1,residual.2,fun _ => ⟨path.resumed_done_iff exhausted,Core.runStateful_resume exhausted _⟩⟩

theorem allocation_extends_the_world_of_the_original_body {world : Core.StoreTyping} {store : Core.Store}
    (st : Core.StoreHasTypes world store) (word : Core.Word) :
    Core.WorldExtends world (world++[.word]) ∧ Core.StoreHasTypes (world++[.word]) (store++[.word word]) ∧
    Core.RuntimeValueHasType (world++[.word]) (.cellRef .word store.length) (.cell .word) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .word (.cell .word)).names
      (environment (.closure .word (.cell .word) (.newCell .word (.var 0)) []) (.word word))
        store source (.cellRef .word store.length) (store++[.word word]) 14 ∧
    ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future (store++[.word word]) ∧
      Core.RuntimeValueHasType future (.cellRef .word store.length) (.cell .word) := by
  have path (k) : Core.Steps 3 ⟨.eval (.newCell .word (.var 0)) [.word word],k,store⟩
      ⟨.ret (.cellRef .word store.length),k,store++[.word word]⟩ :=
    .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  obtain ⟨future,ext,stored,typed,raw,_⟩ := same_world_safety_identifies_the_independent_actual_path
    (Core.RuntimeValueHasType.closure .nil (.newCell (.var rfl) .word)) Core.RuntimeValueHasType.word st path
  refine ⟨⟨[.word],rfl⟩,st.allocate .word .word,.cellRef ?_,raw,future,ext,stored,typed⟩
  simp [←st.length_eq]

end Tests.FrontendComputationRuntimeSafety
