import Solcore.Frontend.Fragments.Internal.Computation
import Solcore.Frontend.Fragments.Internal.RecursiveComputation
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Core.Fuel
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.RuntimeParameters
import Solcore.Frontend.Fragments.Internal.SourceValues
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Syntax.Parser.Internal.TypeBasics
import Solcore.Frontend.Fragments.Internal.Foundations

/-!
# Runtime value tests

Runtime values and their owners, closures, type extension, type tables and checkpoint worlds.
-/

section
-- leanmerge: from Solcore.Test.FrontendCheckpointWorldBoundaryProperties
/-! A genuine checkpoint is essential, and independently typed endpoint stores
do not compensate for an untyped pending write. No source-ID law is needed. -/
set_option autoImplicit false
namespace Tests.FrontendCheckpointWorldBoundary
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"WorldBoundary",by decide⟩],by decide⟩⟩,93⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-world-boundary.sol"⟩,0,7⟩
private def body : Syntax.Block := ⟨span,[⟨span,.returnStmt none⟩]⟩
private def child (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) (_ : Core.Expr) (_ : Core.Ty) : Prop := False
private theorem childType {names context source core type} (h : child names context source core type) :
    Core.HasType context.values core type := False.elim h
private theorem elaboration :
    ComputationReturnTreeElaborates child [] owner .empty body .unit .unit := .bare
private def pending : List Core.Frame := [.newCellApply .unit,.loadCellApply]
private def started (store : Core.Store) : Core.State := ⟨.eval .unit [],pending,store⟩
private def saved (store : Core.Store) : Core.State := ⟨.ret .unit,pending,store⟩
private def allocated (store : Core.Store) : Core.State :=
  ⟨.ret (.cellRef .unit store.length),[.loadCellApply],store++[.unit]⟩
private theorem pendingTyped (world : Core.StoreTyping) : Core.ContinuationHasType world pending .unit .unit :=
  .cons .newCellApply (.cons .loadCellApply .nil)
private theorem stopped (store : Core.Store) : Core.runStateful 1 (started store) = .outOfFuel (saved store) := rfl
private theorem allocatedPath (store : Core.Store) : Core.Steps 1 (saved store) (allocated store) :=
  .cons .applyNewCell .refl

theorem original_bare_body_has_an_actual_pending_allocation_checkpoint (store : Core.Store) :
    ComputationReturnTreeElaborates child [] owner .empty body .unit .unit ∧
    Core.Steps 1 (started store) (saved store) ∧
    Core.runStateful 1 (started store) = .outOfFuel (saved store) ∧
    Core.runStateful 1 (saved store) = .outOfFuel (allocated store) := by
  refine ⟨elaboration,.cons .unit .refl,stopped store,?_⟩
  exact Core.runStateful_outOfFuel_complete (allocatedPath store)
    (Core.advance_next_iff.mpr (.applyLoadCell (Core.Store.allocate_fresh_lookup store .unit)))

theorem extending_worlds_retain_every_old_reference_across_actual_resume_paths
    (world : Core.StoreTyping) (store : Core.Store) (typed : Core.StoreHasTypes world store) :
    ∃ checkpointWorld, Core.WorldExtends world checkpointWorld ∧
      Core.RuntimeStoreHasTypes checkpointWorld (saved store).store ∧
      ∀ {steps next}, Core.Steps steps (saved store) next →
        ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future next.store ∧
          ∀ {location : Nat} {type : Core.Ty}, world[location]? = some type → future[location]? = some type := by
  obtain ⟨checkpointWorld,extension,stored,further⟩ :=
    elaboration.runtime_checkpoint_world_extension childType
      (world := world) (environment := []) (store := store)
      Core.RuntimeEnvironmentHasTypes.nil typed (pendingTyped world) (stopped store)
  refine ⟨checkpointWorld,extension,stored,?_⟩
  intro steps next path
  obtain ⟨future,more,stored⟩ := further path
  exact ⟨future,extension.trans more,stored,fun found => (extension.trans more).lookup found⟩

theorem allocation_grows_the_world_without_changing_old_cell_types
    (world : Core.StoreTyping) (store : Core.Store) (typed : Core.StoreHasTypes world store) :
    ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future (store++[.unit]) ∧
      world.length < future.length ∧
      ∀ {location : Nat} {type : Core.Ty}, world[location]? = some type → future[location]? = some type := by
  obtain ⟨_,_,_,further⟩ := extending_worlds_retain_every_old_reference_across_actual_resume_paths world store typed
  obtain ⟨future,extension,stored,retained⟩ := further (allocatedPath store)
  refine ⟨future,extension,stored,?_,retained⟩
  have lengths := stored.length_eq
  have original := typed.length_eq
  change future.length = (store++[Core.Value.unit]).length at lengths
  simp only [List.length_append,List.length_singleton] at lengths
  omega

theorem old_checkpoint_safety_and_new_world_extension_apply_to_the_same_saved_state
    (world : Core.StoreTyping) (store : Core.Store) (typed : Core.StoreHasTypes world store) :
    Core.StateHasType (saved store) .unit ∧
      (∀ fuel error faultState, Core.runStateful fuel (saved store) ≠ .fault error faultState) ∧
      ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future (saved store).store := by
  have old := elaboration.runtime_checkpoint_safety childType
    (world := world) (environment := []) (store := store)
    Core.RuntimeEnvironmentHasTypes.nil typed (pendingTyped world)
  obtain ⟨future,extension,stored,_⟩ :=
    elaboration.runtime_checkpoint_world_extension childType
      (world := world) (environment := []) (store := store)
      Core.RuntimeEnvironmentHasTypes.nil typed (pendingTyped world) (stopped store)
  exact ⟨(old.2.2 (stopped store)).1,(old.2.2 (stopped store)).2,future,extension,stored⟩

private def badStart (word : Core.Word) : Core.State :=
  ⟨.eval .unit [],[.storeCellApply .word 0],[.word word]⟩
private def badSaved (word : Core.Word) : Core.State :=
  ⟨.ret .unit,[.storeCellApply .word 0],[.word word]⟩
private def badFinal : Core.State := ⟨.ret .unit,[],[.unit]⟩
private def foreignSaved : Core.State := ⟨.ret .unit,[.newCellApply .unit],[.unit]⟩
private theorem noExtension : ¬ Core.WorldExtends [.word] [.unit] := by
  intro extension
  have found := extension.lookup (location := 0) (type := .word) rfl
  cases found

theorem separately_typed_equal_length_stores_do_not_supply_a_world_extension
    (word : Core.Word) :
    ComputationReturnTreeElaborates child [] owner .empty body .unit .unit ∧
    Core.StoreHasTypes [.word] [.word word] ∧ Core.StoreHasTypes [.unit] [.unit] ∧
    Core.Steps 2 (badStart word) badFinal ∧
    Core.runStateful 1 (badStart word) = .outOfFuel (badSaved word) ∧
    Core.runStateful 1 (badSaved word) = .done .unit [.unit] ∧
    ([.word] : Core.StoreTyping).length = ([.unit] : Core.StoreTyping).length ∧
    ¬ Core.WorldExtends [.word] [.unit] :=
  ⟨elaboration,Core.StoreHasTypes.nil.allocate .word .word,
    Core.StoreHasTypes.nil.allocate .unit .unit,
    .cons .unit (.cons (.applyStoreCell rfl) .refl),rfl,rfl,rfl,noExtension⟩

theorem a_typed_source_and_store_cannot_replace_the_pending_frame_premise
    (word : Core.Word) :
    Core.HasType [] .unit .unit ∧ Core.RuntimeEnvironmentHasTypes [.word] [] [] ∧
    Core.StoreHasTypes [.word] (badStart word).store ∧
    (¬ ∃ result, Core.ContinuationHasType [.word] [.storeCellApply .word 0] .unit result) ∧
    (¬ ∃ result, Core.StateHasType (badStart word) result) := by
  refine ⟨.unit,.nil,Core.StoreHasTypes.nil.allocate .word .word,?_,?_⟩
  · rintro ⟨result,typed⟩
    cases typed with | cons frame _ => cases frame
  · rintro ⟨result,typed⟩
    cases typed with | eval _ _ unitTyped continuation =>
      cases unitTyped
      cases continuation with | cons frame _ => cases frame

theorem no_alternative_world_can_hide_the_changed_type_of_the_original_cell :
    ∀ world, Core.RuntimeStoreHasTypes world [.unit] → ¬ Core.WorldExtends [.word] world := by
  intro world typed extension
  obtain ⟨value,found,valueTyped⟩ := typed.lookup (extension.lookup (location := 0) (type := .word) rfl)
  change some Core.Value.unit = some value at found
  cases found
  cases valueTyped

theorem an_unrelated_typed_state_is_not_a_genuine_checkpoint (word : Core.Word) :
    Core.StateHasType foreignSaved (.cell .unit) ∧
    Core.runStateful 0 foreignSaved = .outOfFuel foreignSaved ∧
    (∀ fuel, Core.runStateful fuel (started [.word word]) ≠ .outOfFuel foreignSaved) := by
  refine ⟨.ret ((Core.StoreHasTypes.nil.allocate .unit .unit).toRuntime) .unit (.cons .newCellApply .nil),rfl,?_⟩
  intro fuel exhausted
  obtain ⟨future,extension,typed,_⟩ :=
    elaboration.runtime_checkpoint_world_extension childType
      (world := [.word]) (environment := []) (store := [.word word])
      Core.RuntimeEnvironmentHasTypes.nil (Core.StoreHasTypes.nil.allocate .word .word)
      (pendingTyped [.word]) exhausted
  exact no_alternative_world_can_hide_the_changed_type_of_the_original_cell future typed extension

end Tests.FrontendCheckpointWorldBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendCheckpointWorldExtensionProperties
/-! One original body is fixed while actual typed closure bodies allocate or
write. Literal paths retain every actual capture and pending continuation. -/
set_option autoImplicit false
namespace Tests.FrontendCheckpointWorldExtension
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"CheckpointWorld",by decide⟩],by decide⟩⟩,82⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"checkpoint-world.sol"⟩,0,25⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def call : Syntax.Expr := ⟨span,.call (ref "f") ⟨span,[ref "x"]⟩⟩
private def source : Syntax.Block := ⟨span,[⟨span,.letDecl ⟨span,"r"⟩ none (some call)⟩,
  ⟨span,.returnStmt (some (ref "r"))⟩]⟩
private def inputs (b : Core.Ty) : LocalTypeInputs :=
  (LocalTypeInputs.empty.bindFresh owner "f" (.function .word b)).bindFresh owner "x" .word
private def environment (f x : Core.Value) : Resolved.Environment := [(⟨owner,1⟩,x),(⟨owner,0⟩,f)]
private def invocation : Core.Expr := .apply (.var 1) (.var 0)
private def core : Core.Expr := .letE invocation (.var 0)
private theorem elaborated (b : Core.Ty) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs b) source core b :=
  .inferred
    (.application (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head))
      (.var (.tail (by change (⟨owner,1⟩ : Resolved.LocalId) ≠ ⟨owner,0⟩; decide) .head))
      (.var (.tail (by change (⟨owner,1⟩ : Resolved.LocalId) ≠ ⟨owner,0⟩; decide) .head)))
      (.pure (.identifier .head) (.var .head) (.var .head)))
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem counted (b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (x value : Core.Value) (s final : Core.Store) (cost : Nat)
    (path : Core.Steps cost (.initial body (x::captured) s) (.final value final)) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs b).names
      (environment (.closure .word b body captured) x) s source value final (cost+8) := by
  have p : RecursiveLocalComputationEvaluatesWithCost (inputs b).names
      (environment (.closure .word b body captured) x) s call value final (1+1+cost+3) :=
    .application (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head)
      (.tail (by change (⟨owner,1⟩ : Resolved.LocalId) ≠ ⟨owner,0⟩; decide) .head)))
      (.pure (.identifier .head .head)) path
  simpa [source,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    (ComputationReturnTreeEvaluatesWithCost.inferred (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      (initializerCost := 1+1+cost+3) (tailCost := 1)
      p (.expression (.pure (.identifier .head .head))) :
      RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs b).names
        (environment (.closure .word b body captured) x) s source value final ((1+1+cost+3)+1+2))
private theorem callPath (b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (x value : Core.Value) (s final : Core.Store) (cost : Nat) (k : List Core.Frame)
    (path : Core.Steps cost ⟨.eval body (x::captured),k,s⟩ ⟨.ret value,k,final⟩) :
    Core.Steps (cost+5) ⟨.eval invocation (environment (.closure .word b body captured) x).values,k,s⟩
      ⟨.ret value,k,final⟩ := by
  simpa [invocation,Nat.add_assoc] using Core.Steps.cons .enterApply
    (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure path))))
private def held (f x value : Core.Value) (s : Core.Store) (k : List Core.Frame) : Core.State :=
  ⟨.ret value,.letBody (.var 0) (environment f x).values::k,s⟩
private theorem heldPath (b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (x value : Core.Value) (s final : Core.Store) (cost : Nat)
    (path : ∀ k, Core.Steps cost ⟨.eval body (x::captured),k,s⟩ ⟨.ret value,k,final⟩)
    (k : List Core.Frame) : Core.Steps (cost+6)
      ⟨.eval core (environment (.closure .word b body captured) x).values,k,s⟩
      (held (.closure .word b body captured) x value final k) := by
  simpa [core,held,Nat.add_assoc] using Core.Steps.cons .enterLet
    (callPath b body captured x value s final cost _ (path _))
private def allocations : Nat → Nat → Core.Expr
  | 0,index => .newCell .word (.var index)
  | n+1,index => .letE (.newCell .word (.var index)) (allocations n (index+1))
private theorem allocationsTyped (n index : Nat) (context : Core.Context)
    (found : context[index]?=some .word) : Core.HasType context (allocations n index) (.cell .word) := by
  induction n generalizing index context with
  | zero => exact .newCell (.var found)
  | succ n ih => exact .letE (.newCell (.var found)) (ih (index+1) (.cell .word::context) (by simpa using found))
private theorem allocationsPath (n index : Nat) (env : Core.Environment) (s : Core.Store)
    (word : Core.Word) (k : List Core.Frame) (found : env[index]?=some (.word word)) :
    Core.Steps (5*n+3) ⟨.eval (allocations n index) env,k,s⟩
      ⟨.ret (.cellRef .word (s.length+n)),k,s++List.replicate (n+1) (.word word)⟩ := by
  induction n generalizing index env s k with
  | zero =>
      simpa [allocations] using Core.Steps.cons .enterNewCell
        (.cons (.var found) (.cons Core.Transition.applyNewCell .refl))
  | succ n ih =>
      have first (k) : Core.Steps 3 ⟨.eval (.newCell .word (.var index)) env,k,s⟩
          ⟨.ret (.cellRef .word s.length),k,s++[.word word]⟩ :=
        .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))
      have combined := CostStepComposition.letE (first _) (ih (index+1) (.cellRef .word s.length::env)
        (s++[.word word]) k (by simpa using found))
      have costEq : 3+(5*n+3)+2=5*(n+1)+3 := by omega
      have refEq : (s++[Core.Value.word word]).length+n=s.length+(n+1) := by simp; omega
      have storesEq : (s++[Core.Value.word word])++List.replicate (n+1) (.word word)=
          s++List.replicate (n+1+1) (.word word) := by simp [List.append_assoc,List.replicate_succ]
      rw [costEq,refEq,storesEq] at combined
      exact combined
private def allocator (n : Nat) (captured : Core.Environment) : Core.Value :=
  .closure .word (.cell .word) (allocations n 0) captured

private abbrev worldChain (world : Core.StoreTyping) (cp : Core.State) : Prop :=
  ∃ saved, Core.WorldExtends world saved ∧ Core.RuntimeStoreHasTypes saved cp.store ∧
    ∀ {steps next}, Core.Steps steps cp next →
      ∃ later, Core.WorldExtends saved later ∧ Core.RuntimeStoreHasTypes later next.store
private theorem checkpoint {world : Core.StoreTyping} {f : Core.Value} {b result : Core.Ty}
    {word : Core.Word} {s : Core.Store} {k : List Core.Frame} {spent : Nat} {cp : Core.State}
    (ft : Core.RuntimeValueHasType world f (.function .word b)) (st : Core.StoreHasTypes world s)
    (kt : Core.ContinuationHasType world k b result)
    (exhausted : Core.runStateful spent ⟨.eval core (environment f (.word word)).values,k,s⟩=.outOfFuel cp) :
    worldChain world cp ∧ Core.StateHasType cp result ∧
      ∀ additional error fault, Core.runStateful additional cp ≠ .fault error fault := by
  have envt : Core.RuntimeEnvironmentHasTypes world (environment f (.word word)).values (inputs b).context.values :=
    .cons .word (.cons ft .nil)
  have previous := ComputationReturnTreeElaborates.runtime_checkpoint_safety
    RecursiveLocalComputationElaborates.core_hasType (elaborated b) envt st kt
  exact ⟨ComputationReturnTreeElaborates.runtime_checkpoint_world_extension
    RecursiveLocalComputationElaborates.core_hasType (elaborated b) envt st kt exhausted,previous.2.2 exhausted⟩

theorem fixed_source_has_independent_unbounded_allocation_cost
    (n : Nat) (captured : Core.Environment) (word : Core.Word) (s : Core.Store) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs (.cell .word)) source core (.cell .word) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs (.cell .word)).names
      (environment (allocator n captured) (.word word)) s source (.cellRef .word (s.length+n))
        (s++List.replicate (n+1) (.word word)) (5*n+11) ∧
    ∀ k, Core.Steps (5*n+11) ⟨.eval core (environment (allocator n captured) (.word word)).values,k,s⟩
      ⟨.ret (.cellRef .word (s.length+n)),k,s++List.replicate (n+1) (.word word)⟩ := by
  have p := fun k => allocationsPath n 0 (.word word::captured) s word k rfl
  refine ⟨elaborated _,?_,?_⟩
  · simpa only [allocator,Nat.add_assoc] using counted (.cell .word) (allocations n 0) captured _ _ _ _ _ (p [])
  · intro k
    have held := heldPath (.cell .word) (allocations n 0) captured _ _ _ _ _ p k
    simpa only [allocator,Nat.add_assoc] using held.trans (.cons .bindLet (.cons (.var rfl) .refl))

private def bound (f x value : Core.Value) (s : Core.Store) (k : List Core.Frame) : Core.State :=
  ⟨.eval (.var 0) (value::(environment f x).values),k,s⟩
theorem arbitrary_allocations_retain_original_captures_and_typed_pending_frames
    {world : Core.StoreTyping} {s : Core.Store} {captured : Core.Environment} {context : Core.Context}
    {k : List Core.Frame} {result : Core.Ty} (n : Nat) (word : Core.Word)
    (ct : Core.RuntimeEnvironmentHasTypes world captured context) (st : Core.StoreHasTypes world s)
    (kt : Core.ContinuationHasType world k (.cell .word) result) :
    let f := allocator n captured
    let value := Core.Value.cellRef .word (s.length+n)
    let final := s++List.replicate (n+1) (.word word)
    let cp := bound f (.word word) value final k
    Core.runStateful (5*n+9) ⟨.eval core (environment f (.word word)).values,k,s⟩=.outOfFuel (held f (.word word) value final k) ∧
    Core.runStateful (5*n+10) ⟨.eval core (environment f (.word word)).values,k,s⟩=.outOfFuel cp ∧
    worldChain world cp ∧ Core.StateHasType cp result ∧
    (∀ additional error fault, Core.runStateful additional cp ≠ .fault error fault) ∧
    ∀ additional, Core.runStateful additional cp=
      Core.runStateful (5*n+10+additional) ⟨.eval core (environment f (.word word)).values,k,s⟩ := by
  dsimp only
  have p := fun k => allocationsPath n 0 (.word word::captured) s word k rfl
  have first : Core.Steps (5*n+9) ⟨.eval core (environment (allocator n captured) (.word word)).values,k,s⟩
      (held (allocator n captured) (.word word) (.cellRef .word (s.length+n)) (s++List.replicate (n+1) (.word word)) k) := by
    simpa only [allocator,Nat.add_assoc] using heldPath (.cell .word) (allocations n 0) captured _ _ _ _ _ p k
  have before := Core.runStateful_outOfFuel_complete first (Core.advance_next_iff.mpr .bindLet)
  have second := first.trans (Core.Steps.cons Core.Transition.bindLet Core.Steps.refl)
  have exhausted : Core.runStateful (5*n+10) ⟨.eval core (environment (allocator n captured) (.word word)).values,k,s⟩=
      .outOfFuel (bound (allocator n captured) (.word word) (.cellRef .word (s.length+n)) (s++List.replicate (n+1) (.word word)) k) := by
    simpa [bound,Nat.add_assoc] using Core.runStateful_outOfFuel_complete second (Core.advance_next_iff.mpr (.var rfl))
  have ft : Core.RuntimeValueHasType world (allocator n captured) (.function .word (.cell .word)) :=
    .closure ct (allocationsTyped n 0 (.word::context) rfl)
  obtain ⟨extension,typed,nofault⟩ := checkpoint ft st kt exhausted
  exact ⟨before,exhausted,extension,typed,nofault,Core.runStateful_resume exhausted⟩

theorem every_resumed_exhaustion_extends_the_same_saved_world
    {world : Core.StoreTyping} {cp : Core.State} (chain : worldChain world cp) :
    ∃ saved, Core.WorldExtends world saved ∧ Core.RuntimeStoreHasTypes saved cp.store ∧
      ∀ {additional next}, Core.runStateful additional cp=.outOfFuel next →
        ∃ later, Core.WorldExtends saved later ∧ Core.RuntimeStoreHasTypes later next.store := by
  obtain ⟨saved,ext,typed,further⟩ := chain
  exact ⟨saved,ext,typed,fun exhausted => further (Core.runStateful_outOfFuel_sound exhausted).1⟩

theorem no_source_only_bound_controls_actual_cost_or_allocated_cells (limit : Nat) :
    ∃ f value final cost,
      Core.RuntimeEnvironmentHasTypes [] (environment f (.word Core.Word.zero)).values (inputs (.cell .word)).context.values ∧
      RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs (.cell .word)).names
        (environment f (.word Core.Word.zero)) [] source value final cost ∧ limit<cost ∧ limit<final.length := by
  refine ⟨allocator limit [],_,_,5*limit+11,.cons .word (.cons (.closure .nil (allocationsTyped limit 0 [.word] rfl)) .nil),
    (fixed_source_has_independent_unbounded_allocation_cost limit [] Core.Word.zero []).2.1,by omega,?_⟩
  simp

theorem all_allocation_checkpoints_keep_exact_residual_cost_and_both_world_extensions
    {world : Core.StoreTyping} {s : Core.Store} {captured : Core.Environment} {context : Core.Context}
    (n : Nat) (word : Core.Word) (ct : Core.RuntimeEnvironmentHasTypes world captured context)
    (st : Core.StoreHasTypes world s) {spent : Nat} {cp : Core.State}
    (exhausted : Core.runStateful spent (.initial core (environment (allocator n captured) (.word word)).values s)=.outOfFuel cp) :
    spent<5*n+11 ∧
    Core.Steps (5*n+11-spent) cp (.final (.cellRef .word (s.length+n)) (s++List.replicate (n+1) (.word word))) ∧
    worldChain world cp ∧
    ∀ additional, (Core.runStateful additional cp=.done (.cellRef .word (s.length+n)) (s++List.replicate (n+1) (.word word)) ↔
      5*n+11-spent≤additional) ∧ Core.runStateful additional cp=
        Core.runStateful (spent+additional) (.initial core (environment (allocator n captured) (.word word)).values s) := by
  have path := (fixed_source_has_independent_unbounded_allocation_cost n captured word s).2.2 []
  have residual := path.residual_of_outOfFuel exhausted
  have ft : Core.RuntimeValueHasType world (allocator n captured) (.function .word (.cell .word)) :=
    .closure ct (allocationsTyped n 0 (.word::context) rfl)
  exact ⟨residual.1,residual.2,(checkpoint ft st .nil exhausted).1,
    fun _ => ⟨path.resumed_done_iff exhausted,Core.runStateful_resume exhausted _⟩⟩

private def writeBody : Core.Expr := .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))
theorem typed_writes_change_actual_values_without_changing_any_world_type
    {world : Core.StoreTyping} {s updated : Core.Store} {captured : Core.Environment} {context : Core.Context}
    {k : List Core.Frame} {result : Core.Ty} {location : Nat} (old word : Core.Word)
    (different : old ≠ word) (st : Core.StoreHasTypes world s) (found : world[location]?=some .word)
    (read : s.read? location=some (.word old)) (written : s.write? location (.word word)=some updated)
    (ct : Core.RuntimeEnvironmentHasTypes world captured context) (kt : Core.ContinuationHasType world k .word result) :
    let f := Core.Value.closure .word .word writeBody (.cellRef .word location::captured)
    let cp := bound f (.word word) (.word word) updated k
    Core.StoreHasTypes world updated ∧ updated ≠ s ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .word).names
      (environment f (.word word)) s source (.word word) updated 18 ∧
    Core.runStateful 17 ⟨.eval core (environment f (.word word)).values,k,s⟩=.outOfFuel cp ∧
    worldChain world cp ∧ Core.StateHasType cp result ∧
      ∀ additional error fault, Core.runStateful additional cp ≠ .fault error fault := by
  dsimp only
  have after := Core.Store.write?_reads_written written
  have changed : updated ≠ s := by
    intro same
    rw [same,read] at after
    exact different (Core.Value.word.inj (Option.some.inj after))
  have p (k) : Core.Steps 10
      ⟨.eval writeBody (.word word::.cellRef .word location::captured),k,s⟩ ⟨.ret (.word word),k,updated⟩ :=
    CostStepComposition.letE
      (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue read)
        (.cons (.var rfl) (.cons (.applyStoreCell written) .refl)))))
      (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell after) .refl)))
  have prefixPath := (heldPath .word writeBody (.cellRef .word location::captured) _ _ _ _ 10 p k).trans
    (Core.Steps.cons Core.Transition.bindLet Core.Steps.refl)
  have exhausted : Core.runStateful 17
      ⟨.eval core (environment (.closure .word .word writeBody (.cellRef .word location::captured)) (.word word)).values,k,s⟩=
      .outOfFuel (bound (.closure .word .word writeBody (.cellRef .word location::captured)) (.word word) (.word word) updated k) :=
    Core.runStateful_outOfFuel_complete prefixPath (Core.advance_next_iff.mpr (.var rfl))
  have ft : Core.RuntimeValueHasType world (.closure .word .word writeBody (.cellRef .word location::captured)) (.function .word .word) :=
    .closure (.cons (.cellRef found) ct) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))
  exact ⟨st.write found .word written,changed,counted .word writeBody _ _ _ _ _ 10 (p []),exhausted,
    checkpoint ft st kt exhausted⟩

private def nestedReference (element : Core.Ty) (location : Nat) : Core.Value :=
  .closure .unit .unit (.var 0) [.closure .unit .unit (.var 0) [.cellRef element location]]
theorem literal_nested_captures_and_pending_references_survive_every_later_world
    {world : Core.StoreTyping} {s : Core.Store} {element result : Core.Ty} {location : Nat}
    {pending : List Core.Frame} (n : Nat) (word : Core.Word) (found : world[location]?=some element)
    (st : Core.StoreHasTypes world s)
    (kt : Core.ContinuationHasType world pending (.product (.function .unit .unit) (.cell .word)) result) :
    let nested := nestedReference element location
    let k := Core.Frame.pairApply nested::pending
    let cp := bound (allocator n [nested]) (.word word) (.cellRef .word (s.length+n)) (s++List.replicate (n+1) (.word word)) k
    Core.runStateful (5*n+10) ⟨.eval core (environment (allocator n [nested]) (.word word)).values,k,s⟩=.outOfFuel cp ∧
    ∃ saved, Core.WorldExtends world saved ∧ Core.RuntimeStoreHasTypes saved cp.store ∧
      Core.RuntimeValueHasType saved nested (.function .unit .unit) ∧
      Core.RuntimeValueHasType saved (.cellRef element location) (.cell element) ∧
      ∀ {steps next}, Core.Steps steps cp next → ∃ later,
        Core.WorldExtends saved later ∧ Core.RuntimeStoreHasTypes later next.store ∧
          Core.RuntimeValueHasType later nested (.function .unit .unit) := by
  dsimp only
  have nt : Core.RuntimeValueHasType world (nestedReference element location) (.function .unit .unit) :=
    .closure (.cons (.closure (.cons (.cellRef found) .nil) (.var rfl)) .nil) (.var rfl)
  have facts := arbitrary_allocations_retain_original_captures_and_typed_pending_frames n word
    (.cons nt .nil) st (.cons (.pairApply nt) kt)
  obtain ⟨saved,ext,stored,further⟩ := facts.2.2.1
  refine ⟨facts.2.1,saved,ext,stored,nt.weaken ext,(Core.RuntimeValueHasType.cellRef found).weaken ext,?_⟩
  intro steps next path
  obtain ⟨later,extension,typed⟩ := further path
  exact ⟨later,extension,typed,nt.weaken (ext.trans extension)⟩

end Tests.FrontendCheckpointWorldExtension
end

section
-- leanmerge: from Solcore.Test.FrontendParsedCheckpointWorldExtensions
/-! Original allocation/write order and literal saved states precede the world
extension kernel. Raw construction and validation never guard the old entry. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedCheckpointWorldExtensions
private def check (b : Bool) (label : String) : IO Unit := do unless b do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"CheckpointWorlds",by decide⟩],by decide⟩⟩,89⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def reader : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word 0]
private def nested : Core.Value := .closure .word .word (.apply (.var 1) (.var 0)) [reader]
private def writer : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
private def rawArgs : List Core.Value := [allocator,writer,nested,w 14]
private def env : Core.Environment := [w 14,nested,writer,allocator]
private def types : TypeNameTable :=
  [(["A"],allocator.type),(["W"],writer.type),(["R"],nested.type),(["X"],.word),(["P"],.cell .word)]
private def finalCall : Core.Expr := .apply (.var 4) (.var 3)
private def secondLet : Core.Expr := .letE (.apply (.var 5) (.apply (.var 3) (.var 2))) finalCall
private def tailCore : Core.Expr := .letE (.apply (.var 3) (.var 1)) secondLet
private def core : Core.Expr := .letE (.apply (.var 3) (.apply (.var 1) (.var 0))) tailCore
private def pending : List Core.Frame := [.pairApply (.bool true)]
private def finalStore : Core.Store := [w 14,w 23,w 14]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function checkpoints(a:A,w:W,r:R,x:X) returns(X){let p:P=a(r(x));w(x);let q:P=a(r(x));return r(x);}"
  let file : Syntax.SourceFile := ⟨⟨.main,"checkpoint-world-extensions.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original declaration")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span &&
    source.span.contains source.value.body.span) "complete original header/body spans"
  return source
private def arguments : (raw : List Core.Value) → IO (Σ args : List TypedRuntimeArgument, PLift (args.map (·.value)=raw))
  | [] => return ⟨[],⟨rfl⟩⟩
  | value::rest => do
      match built : buildRuntimeArgument? value with
      | none => throw (IO.userError "raw structural construction")
      | some argument =>
          let tail ← arguments rest
          return ⟨argument::tail.1,⟨by simp only [List.map_cons,buildRuntimeArgument?_iff.mp built,tail.2.down]⟩⟩
private def meaning (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes table source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : table.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "source annotation")
  | _ => throw (IO.userError "annotation shape")
private def parameters (table : TypeNameTable) (initial : LocalInputs) (ps : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Σ final, PLift (RuntimeParametersBindFrom table owner initial ps args final)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨initial,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter ranges"
      let m ← meaning table annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let next ← parameters table (initial.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused next.2.down⟩⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter shape/arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates inputs.names inputs.context source)) := do
  match shape : source with
  | ⟨_,.identifier name⟩ => match named : inputs.names.lookup? name.value with
    | some id => match typed : inputs.context.lookup? id, indexed : Resolved.LocalScope.index? inputs.context.ids id with
      | some t,some i => return ⟨.var i,t,by
          rw [shape]
          exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
            (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "source name")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← child inputs fn; let a ← child inputs arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "call argument")
      | _ => throw (IO.userError "callee")
  | _ => throw (IO.userError "child shape")
termination_by sizeOf source
private def body (table : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates table owner inputs source)) := do
  check (source.value.all fun s => source.span.contains s.span) "original statement spans"
  match shape : source with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let a ← child inputs e; return ⟨a.core,a.type,by rw [shape]; exact .expression a.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      if unused : name.value ∉ inputs.names.map Prod.fst then
        let a ← child inputs e; let b ← body table (inputs.bindFresh owner name.value a.type) ⟨span,rest⟩
        match annotationAt : annotation with
        | none => return ⟨.letE a.core b.core,b.type,by rw [shape,annotationAt]; exact .inferred a.evidence b.evidence⟩
        | some t =>
            let m ← meaning table t
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,by rw [shape,annotationAt]; exact .binding (same ▸ m.2.down) a.evidence b.evidence⟩
            else throw (IO.userError "binding annotation")
      else throw (IO.userError "fresh binding")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ =>
      let a ← child inputs e; let b ← body table inputs ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,by rw [shape]; exact .discard a.evidence b.evidence⟩
  | _ => throw (IO.userError "body shape")
termination_by sizeOf source
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) :
    IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧
      p.core=core ∧ p.returnType=.word ∧ p.inputs.environment.values=env)) := do
  let ps ← parameters types .empty source.value.signature.parameters.elements args
  let b ← body types ps.1.toTypeInputs source.value.body
  if fixed : b.core=core ∧ b.type=.word ∧ ps.1.environment.values=env then
    check (decide (ps.1.names=[("x",⟨owner,3⟩),("r",⟨owner,2⟩),("w",⟨owner,1⟩),("a",⟨owner,0⟩)])) "actual reverse-once rows"
    match clause : source.value.signature.returnsClause with
    | some ⟨_,⟨_,[annotation]⟩⟩ =>
        let m ← meaning types annotation
        if same : m.1=.word then
          if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
            let p : PreparedRuntimeFunction := ⟨ps.1,core,.word⟩
            have annotationMeaning : StructuralTypeDenotes types annotation .word := by simpa only [same] using m.2.down
            have h : RuntimeFunctionHeader types source.value.signature .word :=
              ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single annotationMeaning⟩
            return ⟨p,⟨⟨⟨h,ps.2.down,by simpa only [fixed.1,fixed.2.1] using b.evidence⟩,rfl,rfl,fixed.2.2⟩⟩⟩
          else throw (IO.userError "header policy")
        else throw (IO.userError "declared return type")
    | _ => throw (IO.userError "single return type")
  else throw (IO.userError "independent literal Core/type/environment")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured =>
            let r ← path n b (arg.value::captured) arg.final
            return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match found : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual operands")
    | _ => throw (IO.userError "manual grammar")
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private theorem storeWorld {world : Core.StoreTyping} {store : Core.Store}
    (typed : Core.RuntimeStoreHasTypes world store) : world=store.map Core.Value.type :=
  typed.world_eq
private def verify (source : Syntax.FunctionDecl) : IO Unit := do
  let manual ← path 80 core env [w 23]
  check (decide (manual.cost=74 ∧ manual.value=w 14 ∧ manual.final=finalStore)) "independent literal raw path and effects"
  let args ← arguments rawArgs
  check (decide (args.1.map (·.value)=rawArgs)) "literal original raw values"
  let p ← prepare source args.1
  have original : RecursiveComputationReturnTreeElaborates types owner p.1.inputs.toTypeInputs source.value.body core .word := by
    simpa only [p.2.down.2.1,p.2.down.2.2.1] using p.2.down.1.body
  if validated : validateRuntimeInputs [.word] args.1 [w 23]=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have reversed := runtimeArguments args.1.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
    have actual : Core.RuntimeEnvironmentHasTypes [.word] env p.1.inputs.toTypeInputs.context.values := by
      have bound : Core.RuntimeEnvironmentHasTypes [.word] p.1.inputs.environment.values p.1.inputs.context.values := by
        simpa only [LocalInputs.environment,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,
          p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      simpa only [p.2.down.2.2.2,LocalInputs.toTypeInputs_context] using bound
    have typedK : Core.ContinuationHasType [.word] pending .word (.product .bool .word) := .cons (.pairApply .bool) .nil
    have safe := original.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK
    have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    have _ := accepted
    let start : Core.State := ⟨.eval core env,pending,[w 23]⟩
    let result := Core.Value.pair (.bool true) (w 14)
    have wholePath : Core.Steps (manual.cost+1) start ⟨.ret (.pair (.bool true) manual.value),[],manual.final⟩ :=
      (manual.evidence pending).trans (.cons .applyPair .refl)
    for fuel in List.range 77 do
      check (decide (runRecursiveComputationFunction? types owner source args.1 fuel [w 23]=
        some (.word,Core.runStateful fuel (.initial core env [w 23])))) "unchanged full compiled entry result"
      match exhausted : Core.runStateful fuel start with
      | .done value store => check (decide (75≤fuel ∧ value=result ∧ store=finalStore)) "typed pending frame completes after original body"
      | .fault _ _ => throw (IO.userError "typed original pending frame fault")
      | .outOfFuel cp =>
          have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK exhausted
          have _ := safe.2.2 exhausted
          have _ := wholePath.residual_of_outOfFuel exhausted
          have oldReference : ∃ savedWorld, Core.WorldExtends [.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ savedWorld[0]?=some .word := by
            obtain ⟨savedWorld,extension,stored,_⟩ := saved
            exact ⟨savedWorld,extension,stored,extension.lookup rfl⟩
          have _ := oldReference
          have terminal : ∃ savedWorld future, Core.WorldExtends [.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧
              Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future manual.final := by
            obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
            obtain ⟨future,growth,finalTyped⟩ := resumed (wholePath.residual_of_outOfFuel exhausted).2
            exact ⟨savedWorld,future,extension,stored,growth,finalTyped⟩
          have _ := terminal
          check (decide (fuel<75 ∧ Core.runStateful (75-fuel) cp=.done result finalStore)) "all genuine saved states retain exact remaining execution"
          for extra in [0,1,7,75] do
            check (decide (Core.runStateful extra cp=Core.runStateful (fuel+extra) start)) "full original/resumed state equality"
            match again : Core.runStateful extra cp with
            | .outOfFuel next =>
                have chain : ∃ saved future, Core.WorldExtends [.word] saved ∧ Core.RuntimeStoreHasTypes saved cp.store ∧
                    Core.WorldExtends saved future ∧ Core.RuntimeStoreHasTypes future next.store ∧ future[0]?=some .word := by
                  obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
                  obtain ⟨future,growth,nextTyped⟩ := resumed (Core.runStateful_outOfFuel_sound again).1
                  exact ⟨savedWorld,future,extension,stored,growth,nextTyped,(extension.trans growth).lookup rfl⟩
                have _ := chain
            | .done _ _ => pure ()
            | .fault _ _ => throw (IO.userError "resumed typed checkpoint fault")
    let first : Core.State := ⟨.ret (.cellRef .word 1),.letBody tailCore env::pending,[w 23,w 23]⟩
    let written : Core.State := ⟨.ret (w 14),.letBody secondLet (.cellRef .word 1::env)::pending,[w 14,w 23]⟩
    let second : Core.State := ⟨.ret (.cellRef .word 2),.letBody finalCall (w 14::.cellRef .word 1::env)::pending,finalStore⟩
    for (spent,cp) in [(21,first),(38,written),(60,second)] do
      if genuine : Core.runStateful spent start=.outOfFuel cp then
        have identified : Core.WorldExtends [.word] (cp.store.map Core.Value.type) ∧ Core.RuntimeStoreHasTypes (cp.store.map Core.Value.type) cp.store := by
          obtain ⟨world,ext,stored,_⟩ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK genuine
          simpa only [storeWorld stored] using And.intro ext stored
        have _ := identified
        check (decide (Core.runStateful (75-spent) cp=.done result finalStore)) "allocation/write/allocation preserve actual saved binders/captures"
      else throw (IO.userError "literal checkpoint mismatch")
    if chain : Core.runStateful 21 start=.outOfFuel first ∧ Core.runStateful 17 first=.outOfFuel written ∧ Core.runStateful 22 written=.outOfFuel second then
      have exactWorlds : Core.WorldExtends [.word] [.word,.word] ∧ Core.RuntimeStoreHasTypes [.word,.word] first.store ∧
          Core.RuntimeStoreHasTypes [.word,.word] written.store ∧ Core.WorldExtends [.word,.word] [.word,.word,.word] ∧
          Core.RuntimeStoreHasTypes [.word,.word,.word] second.store := by
        obtain ⟨saved,ext,stored,further⟩ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK chain.1
        have writePath := (Core.runStateful_outOfFuel_sound chain.2.1).1
        obtain ⟨afterWrite,_,writeTyped⟩ := further writePath
        obtain ⟨afterAllocate,extended,allocationTyped⟩ := further (writePath.trans (Core.runStateful_outOfFuel_sound chain.2.2).1)
        have firstTypes : saved=[.word,.word] := storeWorld stored
        have writtenTypes : afterWrite=[.word,.word] := storeWorld writeTyped
        have secondTypes : afterAllocate=[.word,.word,.word] := storeWorld allocationTyped
        subst saved; subst afterWrite; subst afterAllocate
        exact ⟨ext,stored,writeTyped,extended,allocationTyped⟩
      have _ := exactWorlds
    else throw (IO.userError "independent 17/22-transition saved-state chain")
    check (decide (first.store.length=written.store.length ∧ first.store≠written.store ∧
      first.store.map Core.Value.type=written.store.map Core.Value.type ∧ second.store.length=written.store.length+1)) "typed write changes payload, second allocation extends locations"
  else throw (IO.userError "constructed input validation")
end ParsedCheckpointWorldExtensions
open ParsedCheckpointWorldExtensions
def frontendParsedCheckpointWorldExtensionTests : IO Unit := do verify (← parsed)
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeClosureValues
set_option autoImplicit false
namespace Tests
namespace ParsedRuntimeClosureValues
open Solcore Solcore.Frontend

/- Only inert representation data is constructed here: no source evaluation, typing or admission. -/
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def verify {α : Type} [DecidableEq α] (actual expected : α)
    (_exact : actual = expected) (label : String) : IO Unit := check (decide (actual = expected)) label
private def fileId : Syntax.SourceId := ⟨.main,"runtime-closure-values.sol"⟩
private def span (first last : Nat) : Syntax.SourceSpan := ⟨fileId,first,last⟩
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"RuntimeClosureValues",by decide⟩],by decide⟩⟩,152⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner,index⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def word (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def names : List (String × Resolved.LocalId) :=
  [("x",id 7),("x",id 31),("foreign",foreign),("orphan",id 99)]
private def captures : List (Resolved.LocalId × RuntimeValue) :=
  [(id 31,.word (word 41)),(id 7,.bool true),
    (id 31,.coreClosure .word .unit (.var 99) [.cellRef .word 700,.bool false]),
    (foreign,.pair (.word (word 17)) .unit),(id 777,.cellRef .word 1)]
private def packed (source : Syntax.Expr) : RuntimeValue := .sourceClosure source owner names captures
private theorem original_data (source : Syntax.Expr) :
    match packed source with
    | .sourceClosure actual actualOwner actualNames actualCaptures =>
        actual = source ∧ actualOwner = owner ∧ actualNames = names ∧ actualCaptures = captures
    | _ => False := ⟨rfl,rfl,rfl,rfl⟩
private theorem literal_rows : names.map Prod.snd = [id 7,id 31,foreign,id 99] ∧
    captures.map Prod.fst = [id 31,id 7,id 31,foreign,id 777] ∧
    names.length ≠ captures.length := by decide
private theorem captured_payloads : captures.map (fun row => row.2.toCore?) =
    [some (.word (word 41)),some (.bool true),
      some (.closure .word .unit (.var 99) [.cellRef .word 700,.bool false]),
      some (.pair (.word (word 17)) .unit),some (.cellRef .word 1)] := by
  simp [captures,RuntimeValue.toCore?]
private def blocked (source : Syntax.Expr) : List RuntimeValue :=
  let value := packed source
  [value,.pair value .unit,.pair (.bool false) value,
    .inLeft (.namedData ⟨777⟩) value,.inRight (.cell (.function .word .word)) value,
    .constructed ⟨⟨777⟩,888⟩ value,
    .coreClosure .word .word (.word Core.Word.zero) [.unit,value,.bool true],
    .coreClosure .unit .unit (.var 99) [.pair .unit (.coreClosure .unit .unit .unit [value])],
    .sourceClosure source {owner with declarationIndex:=901} [] [(foreign,value)]]
private theorem blocked_exact (source : Syntax.Expr) :
    (blocked source).map RuntimeValue.toCore? = List.replicate 9 none := by
  simp [blocked,packed,RuntimeValue.toCore?]
private def mixedStore (source : Syntax.Expr) : List RuntimeValue :=
  [.word (word 17),packed source,.cellRef .word 1]
private theorem stored_exact (source : Syntax.Expr) :
    (mixedStore source).mapM RuntimeValue.toCore? = none ∧
    ((mixedStore source)[1]?).map RuntimeValue.toCore? = some none ∧
    (RuntimeValue.cellRef .word 1).toCore? = some (.cellRef .word 1) := by
  simp [mixedStore,packed,RuntimeValue.toCore?]
private theorem not_old_image (source : Syntax.Expr) (core : Core.Value) : packed source ≠ .ofCore core := by
  intro equality
  have projected := RuntimeValue.toCore?_eq_some_iff.mpr equality
  simp [packed,RuntimeValue.toCore?] at projected
private def oldValues : List Core.Value :=
  [.unit,.bool false,.word (word 41),.hostFunction .callContractWordWithValue,
    .pair (.word (word 17)) (.bool true),
    .closure (.cell (.function .word .word)) (.namedData ⟨777⟩) (.var 99)
      [.bool true,.closure .bool .unit (.var 400) [.cellRef .word 700],.word (word 41)],
    .inLeft (.namedData ⟨777⟩) (.bool true),.inRight (.cell .word) (.word (word 17)),
    .cellRef (.function .word .word) 900,.constructed ⟨⟨777⟩,888⟩ (.pair .unit (.bool false))]

private def typeName (name : String) (first last : Nat) : Syntax.TypeExpr :=
  ⟨span first last,.named ⟨span first last,⟨⟨⟨span first last,name⟩,[]⟩⟩⟩ none⟩
private def identifier (name : String) (first last : Nat) : Syntax.Expr :=
  ⟨span first last,.identifier ⟨span first last,name⟩⟩
private def richText := "lam(x:A)->B{let x:A=x;return saved;}"
/- An independent complete syntax literal, including the original shadowing initializer and tail. -/
private def richOriginal : Syntax.Expr :=
  ⟨span 0 36,.lambda (span 0 3)
    ⟨span 3 8,[⟨span 4 7,.typed none ⟨span 4 5,"x"⟩ (typeName "A" 6 7)⟩]⟩
    (some (typeName "B" 10 11))
    ⟨span 11 36,[⟨span 12 22,.letDecl ⟨span 16 17,"x"⟩
      (some (typeName "A" 18 19)) (some (identifier "x" 20 21))⟩,
      ⟨span 22 35,.returnStmt (some (identifier "saved" 29 34))⟩]⟩⟩
private def parameterTag (parameter : Syntax.LambdaParameter) : String :=
  match parameter.value with
  | .inferred name => "inferred:" ++ name.value
  | .typed marker name _ => (if marker.isSome then "marked:" else "typed:") ++ name.value
  | .error => "error"
private def shape (source : Syntax.Expr) : String :=
  match source.value with
  | .lambda _ parameters returns _ =>
      "lambda " ++ reprStr (parameters.elements.map parameterTag) ++
        (if returns.isSome then " annotated" else " omitted")
  | .identifier name => "identifier:" ++ name.value
  | .call _ _ => "call"
  | .group _ => "group"
  | .error => "error"
  | _ => "other"
private def parsed (text : String) (expected : String) (diagnostics : Nat) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨fileId,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd &&
        decide (source.span = Syntax.SourceSpan.fullFile file)) "complete original expression span"
      check (decide (shape source = expected ∧ next.diagnostics.length = diagnostics)) "actual AST and diagnostics"
      if let .lambda keyword parameters returns body := source.value then
        check (source.span.contains keyword && source.span.contains parameters.span &&
          source.span.contains body.span && parameters.elements.all (fun p => parameters.span.contains p.span) &&
          returns.toList.all (fun annotation => source.span.contains annotation.span) &&
          body.value.all (fun statement => body.span.contains statement.span)) "unchanged nested source spans"
      return source
  | .reject _ _ => throw (IO.userError "parser rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
private def inspect (text : String) (expected : String) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text expected diagnostics
  if text = richText then check (source == richOriginal) "independent full original syntax literal"
  match valueEq : packed source with
  | .sourceClosure actual actualOwner actualNames actualCaptures =>
      have saved : actual = source ∧ actualOwner = owner ∧ actualNames = names ∧ actualCaptures = captures := by
        simpa only [valueEq] using original_data source
      check (actual == source) "the complete original Expr is retained, including error and nonlambda data"
      verify actual.span source.span (congrArg Syntax.Located.span saved.1) "literal source span"
      verify actualOwner owner saved.2.1 "owner is not recomputed from the source or capture IDs"
      verify actualNames names saved.2.2.1 "ordered duplicate names are not normalized"
      check (decide (actualNames.length ≠ actualCaptures.length)) "no name/capture alignment premise"
      verify (actualCaptures.map Prod.fst) [id 31,id 7,id 31,foreign,id 777]
        (by simpa only [saved.2.2.2] using literal_rows.2.1) "ordered duplicate, foreign and environment-only capture IDs"
      verify (actualCaptures.map (fun row => row.2.toCore?))
        [some (.word (word 41)),some (.bool true),
          some (.closure .word .unit (.var 99) [.cellRef .word 700,.bool false]),
          some (.pair (.word (word 17)) .unit),some (.cellRef .word 1)]
        (by simpa only [saved.2.2.2] using captured_payloads) "all actual capture payloads, tags and Core code"
  | _ => throw (IO.userError "original source data constructor changed")
  verify ((blocked source).map RuntimeValue.toCore?) (List.replicate 9 none)
    (blocked_exact source) "source data nested in pairs, sums, data, unused Core captures and source captures"
  verify ((mixedStore source).mapM RuntimeValue.toCore?) none (stored_exact source).1 "raw mixed-store projection"
  verify (((mixedStore source)[1]?).map RuntimeValue.toCore?) (some none)
    (stored_exact source).2.1 "actual referenced slot is nonprojectable"
  verify (RuntimeValue.cellRef .word 1).toCore? (some (.cellRef .word 1))
    (stored_exact source).2.2 "cell reference projection does not follow that raw store"
  have noReplacement : ∀ core, packed source ≠ RuntimeValue.ofCore core := not_old_image source
  have noCore : ¬ ∃ core, (packed source).toCore? = some core := by
    rintro ⟨core,projected⟩
    exact noReplacement core (RuntimeValue.toCore?_eq_some_iff.mp projected)
  check (decide ((packed source).toCore? = none)) "inert source cannot be replaced with an invented Core closure"
  have _ : ¬ ∃ core, (packed source).toCore? = some core := noCore
end ParsedRuntimeClosureValues

open ParsedRuntimeClosureValues in
/-- Parsed code and lexical metadata are inert data; this test claims no source execution or typing. -/
def frontendParsedRuntimeClosureValueTests : IO Unit := do
  for core in oldValues do
    verify (Solcore.Frontend.RuntimeValue.ofCore core).toCore? (some core)
      (Solcore.Frontend.RuntimeValue.toCore?_ofCore core)
      "every old constructor is in the exact embedding image, regardless of runtime validity"
    match projected : (Solcore.Frontend.RuntimeValue.ofCore core).toCore? with
    | some actual =>
        have image := Solcore.Frontend.RuntimeValue.toCore?_eq_some_iff.mp projected
        verify actual core (Solcore.Frontend.RuntimeValue.ofCore_injective image.symm)
          "successful projection reflects the exact image and injectivity recovers the original value"
    | none => throw (IO.userError "embedded Core data lost its projection")
  do
    inspect "lam(x){return x;}" "lambda [\"inferred:x\"] omitted"
    inspect richText "lambda [\"typed:x\"] annotated"
    inspect "lam(x,)->A{return saved;}" "lambda [\"inferred:x\"] annotated"
    inspect "lam(){return saved;}" "lambda [] omitted"
    inspect "lam(x,y){return x;}" "lambda [\"inferred:x\", \"inferred:y\"] omitted"
    inspect "lam(comptime x:A){return x;}" "lambda [\"marked:x\"] omitted"
    inspect "lam(comptime){return comptime;}" "lambda [\"inferred:comptime\"] omitted" 1
    inspect "lam(comptime:A){return comptime;}" "lambda [\"typed:comptime\"] omitted" 1
    inspect "lam(comptime x){return x;}" "lambda [\"error\"] omitted" 1
    inspect "lam(x){let ;}" "lambda [\"inferred:x\"] omitted" 1
    inspect "lam(x:Missing)->Missing{return absent;}" "lambda [\"typed:x\"] annotated"
    inspect "lam(x){return lam(y){return x;};}" "lambda [\"inferred:x\"] omitted"
    inspect "saved" "identifier:saved"
    inspect "saved(x)" "call"
    inspect "(lam(x){return x;})" "group"
    inspect "let" "error" 2

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeTypeExtensionEntries
/-! The original complete declaration and actual arguments remain fixed while only
first-match type meanings change. Exact records, paths and saved states are retained. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RuntimeTypeExtensionEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RuntimeTypeExtensionEntry", by decide⟩], by decide⟩⟩, 17⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table (type : Core.Ty) : TypeNameTable := [(["T"], type), (["Bool"], .bool)]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "runtime-type-extension-entry.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩) && source.span.contains source.value.body.span) s!"original complete ranges changed: {content}"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent type leaf missing")
  | ⟨_, .tuple [left, right]⟩ =>
      let a ← meaning types left; let b ← meaning types right
      return ⟨.product a.type b.type, by rw [atSource]; exact .pair a.evidence b.evidence⟩
  | _ => throw (IO.userError "outside independent annotation grammar")
termination_by sizeOf source
private structure Parameters (types : TypeNameTable) (initial : LocalInputs)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial params args inputs
private def parameters (types : TypeNameTable) (initial : LocalInputs)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types initial params args) := do
  match atParams : params, atArgs : args with
  | [], [] => return ⟨initial, by rw [atParams, atArgs]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest, argument :: tailArgs =>
      check (span.contains name.span && span.contains annotation.span) "original parameter range changed"
      let m ← meaning types annotation
      if same : m.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← parameters types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest tailArgs
          return ⟨tail.inputs, by rw [atParams, atArgs]; exact .cons (same ▸ m.evidence) unused tail.evidence⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "original actual type mismatch")
  | _, _ => throw (IO.userError "unsupported parameter or argument count")
private structure Expression (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def expression (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Expression s source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "independent context row missing")
      | none => throw (IO.userError "independent name missing")
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s left; let b ← expression s right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing⟩
  | _ => throw (IO.userError "outside independent expression grammar")
termination_by sizeOf source
private structure Body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : TypedLetReturnTreeElaborates types owner s source core type
private def body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) : IO (Body types s source) := do
  match atSource : source with
  | ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ =>
      let a ← expression s returned
      return ⟨a.core, a.type, by rw [atSource]; exact .single (.expression a.resolution
        (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing)⟩
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      let child ← body types s ⟨innerSpan, statements⟩
      return ⟨child.core, child.type, by rw [atSource]; exact .block child.evidence⟩
  | ⟨span, ⟨ls, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span) "original initializer spans changed"
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s initializer
        let b ← body types (s.bindFresh owner name.value a.type) ⟨span, rest⟩
        match atAnnotation : annotation with
        | none => return ⟨.letE a.core b.core, b.type, by rw [atSource, atAnnotation]; exact .inferred unused a.resolution a.lowered a.typing b.evidence⟩
        | some written =>
            let m ← meaning types written
            if same : m.type = a.type then
              return ⟨.letE a.core b.core, b.type, by rw [atSource, atAnnotation]; exact .binding (same ▸ m.evidence) unused a.resolution a.lowered a.typing b.evidence⟩
            else throw (IO.userError "written annotation disagreed")
      else throw (IO.userError "ancestor name reused")
  | ⟨span, ⟨_, .expression source true⟩ :: rest⟩ =>
      let a ← expression s source; let b ← body types s ⟨span, rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0), b.type,
        by rw [atSource]; exact .discard a.resolution a.lowered a.typing b.evidence⟩
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s guard; let a ← body types s yes; let b ← body types s no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
          return ⟨.ifE c.core a.core b.core, a.type, by rw [atSource]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.evidence (bt ▸ b.evidence)⟩
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard is not Bool")
  | _ => throw (IO.userError "outside independent body grammar")
termination_by sizeOf source
private structure Preparation (types : TypeNameTable) (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) where
  prepared : PreparedRuntimeFunction
  evidence : RuntimeFunctionPrepares types owner source args prepared
private def prepare (types : TypeNameTable) (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) :
    IO (Preparation types source args) := do
  let ps ← parameters types .empty source.value.signature.parameters.elements args
  let b ← body types ps.inputs.toTypeInputs source.value.body
  match atClause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [returned]⟩⟩ =>
      let m ← meaning types returned
      if same : m.type = b.type then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          return ⟨⟨ps.inputs, b.core, b.type⟩, ⟨⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [atClause]; exact .single (same ▸ m.evidence)⟩, ps.evidence, b.evidence⟩⟩
        else throw (IO.userError "header policy rejected")
      else throw (IO.userError "return contract differs")
  | _ => throw (IO.userError "return clause is not singleton")

private def mixed : Core.Expr := .letE (.var 2) (.letE (.var 3) (.ifE (.var 2)
  (.letE (.pair (.var 0) (.var 3)) (.var 1)) (.letE (.var 3) (.var 1))))
private theorem mixedPaths (x y : Core.Value) (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (if c then 17 else 13) ⟨.eval mixed [.bool c, y, x], k, store⟩ ⟨.ret x, k, store⟩ := by
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
      (.cons .bindLet (.cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))))))))
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
      (.cons .bindLet (.cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterLet
        (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl)
          (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl))))))))))))))))

private def alternate (type : Core.Ty) : TypeNameTable := ((["T"], type) :: table type) ++ [(["T"], .unit)]
private def enlarged (type : Core.Ty) : TypeNameTable := table type ++ [(["Alias"], type)]
private theorem sameLookup (type : Core.Ty) (key : List String) : (table type).lookup? key = (alternate type).lookup? key := by
  by_cases t : ["T"] = key
  · subst key; rfl
  by_cases b : ["Bool"] = key
  · subst key; rfl
  simp [table, alternate, TypeNameTable.lookup?, t, b]
private theorem fromLookup {old next : TypeNameTable}
    (same : ∀ key, old.lookup? key = next.lookup? key) : TypeNameTable.Extends old next := by
  intro key type found
  exact TypeNameTable.lookup?_iff.mp ((same key).symm.trans (TypeNameTable.lookup?_iff.mpr found))
private theorem forward (type : Core.Ty) : TypeNameTable.Extends (table type) (alternate type) := fromLookup (sameLookup type)
private theorem backward (type : Core.Ty) : TypeNameTable.Extends (alternate type) (table type) := fromLookup (fun key => (sameLookup type key).symm)
private def rows (inputs : LocalInputs) := inputs.bindings.map fun b => (b.name, b.id, b.type, b.value)
private def payload (p : PreparedRuntimeFunction) := (rows p.inputs, p.core, p.returnType)
private def text (body : String) := "function f(x:T,y:T,c:Bool) returns(T){" ++ body ++ "}"
private def mixedText (annotated : Bool) : String :=
  "{x;{let z" ++ (if annotated then ":T" else "") ++ "=x;{if(c){{(z,y);{return z;}}}else{{y;{return z;}}}}}}"
private def verify (old next : TypeNameTable) (extension : TypeNameTable.Extends old next)
    (content : String) (x y : TypedRuntimeArgument) (c : Bool) (expectedCore : Core.Expr) (cost : Nat)
    (paths : ∀ store k, Core.Steps cost ⟨.eval expectedCore [.bool c, y.value, x.value], k, store⟩ ⟨.ret x.value, k, store⟩) : IO Unit := do
  let source ← parsed content
  let args := [x, y, (⟨.bool, .bool c, .bool⟩ : TypedRuntimeArgument)]
  let original ← prepare old source args
  let prepared := original.prepared
  check (decide (prepared.core = expectedCore ∧ prepared.returnType = x.type ∧ rows prepared.inputs =
    [("c", ⟨owner, 2⟩, .bool, .bool c), ("y", ⟨owner, 1⟩, y.type, y.value), ("x", ⟨owner, 0⟩, x.type, x.value)]))
    "independent complete record or one reversal changed"
  have _ := RuntimeParametersBindFrom.extend_types original.evidence.parameters extension
  have _ := RuntimeParametersBind.extend_types original.evidence.parameters extension
  have _ := bindRuntimeParameters?_some_of_extends extension original.evidence.parameters.complete
  have _ := original.evidence.extend_types extension
  have _ := original.evidence.hasType.extend_types extension
  have preserved := prepareRuntimeFunction?_some_of_extends extension original.evidence.complete
  match atNext : prepareRuntimeFunction? next owner source args with
  | none => throw (IO.userError "successful full preparation lost")
  | some result =>
      have _ : result = prepared := Option.some.inj (atNext.symm.trans preserved)
      check (decide (payload result = payload prepared)) "actual prepared record was replaced by a static projection"
  check (decide ((prepareRuntimeFunction? old owner source args).map payload = some (payload prepared)))
    "independent original preparation disagreed with executable preparation"
  for store in [[], [w 91, .cellRef .word 999]] do
    have _ := paths store [.unaryApply .wordNot]
    let start := Core.State.initial expectedCore [.bool c, y.value, x.value] store
    check (decide (evaluateTypedLetReturnTreeWithCost? owner prepared.inputs.names prepared.inputs.environment source.value.body =
      some (x.value, cost))) "original selected raw value or independent cost changed"
    for fuel in List.range 21 do
      match atRun : runRuntimeFunction? old owner source args fuel store with
      | none => throw (IO.userError "successful preparation did not run")
      | some outcome =>
          have _ := runRuntimeFunction?_some_of_extends extension atRun
          check (decide (outcome = (x.type, Core.runStateful fuel start) ∧
            runRuntimeFunction? next owner source args fuel store = some outcome)) "full outcome or saved state changed"
          check (match outcome.2 with
            | .done value final => decide (cost ≤ fuel ∧ value = x.value ∧ final = store)
            | .outOfFuel _ => decide (fuel < cost)
            | _ => false) "independent exact cost threshold changed"
    for spent in List.range cost do
      match exhausted : runRuntimeFunction? old owner source args spent store with
      | some (_, .outOfFuel cp) =>
          have _ := runRuntimeFunction?_resume exhausted (cost - spent)
          check (decide (Core.runStateful (cost - spent) cp = .done x.value store)) "actual residual changed"
          if cost - spent > 1 then
            let .outOfFuel second := Core.runStateful 1 cp | throw (IO.userError "second chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) second = .done x.value store)) "three chunks lost captured data"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done x.value store) "restart substituted for resumption"
      | _ => throw (IO.userError "genuine checkpoint missing")
private def checkMutual (type : Core.Ty) (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO Unit := do
  have _ := bindRuntimeParameters?_eq_of_mutual_extends (forward type) (backward type) owner source.value.signature.parameters.elements args
  have _ := prepareRuntimeFunction?_eq_of_mutual_extends (forward type) (backward type) owner source args
  check (decide ((prepareRuntimeFunction? (table type) owner source args).map payload =
    (prepareRuntimeFunction? (alternate type) owner source args).map payload)) "mutual full preparation disagreed"
  for store in [[], [w 91]] do
    for fuel in List.range 21 do
      have _ := runRuntimeFunction?_eq_of_mutual_extends (forward type) (backward type) owner source args fuel store
      check (decide (runRuntimeFunction? (table type) owner source args fuel store =
        runRuntimeFunction? (alternate type) owner source args fuel store)) "mutual None or full run result changed"
private def checked (type : Core.Ty) (x y : Core.Value) (xt : Core.ValueHasType x type) (yt : Core.ValueHasType y type) : IO Unit := do
  for annotated in [false, true] do
    for c in [false, true] do
      let content := text (mixedText annotated)
      verify (table type) (alternate type) (forward type) content ⟨type,x,xt⟩ ⟨type,y,yt⟩ c mixed (if c then 17 else 13) (mixedPaths x y c)
      verify (table type) (enlarged type) (TypeNameTable.Extends.append_right _ _) content ⟨type,x,xt⟩ ⟨type,y,yt⟩ c mixed (if c then 17 else 13) (mixedPaths x y c)
      checkMutual type (← parsed content) [⟨type,x,xt⟩, ⟨type,y,yt⟩, ⟨.bool,.bool c,.bool⟩]
end RuntimeTypeExtensionEntries
open RuntimeTypeExtensionEntries

def frontendParsedRuntimeTypeExtensionEntryTests : IO Unit := do
  checked .word (w 9) (w 2) .word .word
  checked .unit .unit .unit .unit .unit
  checked (.product .word .bool) (.pair (w 9) (.bool true)) (.pair (w 2) (.bool false)) (.pair .word .bool) (.pair .word .bool)
  checked (.cell .word) (.cellRef .word 700) (.cellRef .word 701) .cellRef .cellRef
  checked (.function .word .word) (.closure .word .word (.var 0) []) (.closure .word .word (.var 1) [w 7])
    (.closure .nil (.var rfl)) (.closure (.cons .word .nil) (.var rfl))
  let args : List TypedRuntimeArgument := [⟨.word,w 9,.word⟩, ⟨.word,w 2,.word⟩, ⟨.bool,.bool true,.bool⟩]
  for content in ["function f(x:Alias,y:T,c:Bool) returns(T){{return x;}}",
      "function f(x:T,y:T,c:Bool) returns(Alias){{return x;}}"] do
    let source ← parsed content
    check ((prepareRuntimeFunction? (table .word) owner source args).isNone) "unknown whole annotation unexpectedly accepted"
    checkMutual .word source args
    verify (enlarged .word) (enlarged .word) (TypeNameTable.Extends.refl _) content ⟨.word,w 9,.word⟩ ⟨.word,w 2,.word⟩ true (.var 2) 1
      (fun _ _ => .cons (.var rfl) .refl)
  let repairedText := text "{if(c){return x;}else{let z:Alias=y;return z;}}"
  let repaired ← parsed repairedText
  let original ← parameters (table .word) .empty repaired.value.signature.parameters.elements args
  check ((prepareRuntimeFunction? (table .word) owner repaired args).isNone &&
    decide (evaluateTypedLetReturnTreeWithCost? owner original.inputs.names original.inputs.environment repaired.value.body = some (w 9, 4)))
    "unselected unknown annotation confused raw execution with whole acceptance"
  verify (enlarged .word) (enlarged .word) (TypeNameTable.Extends.refl _) repairedText ⟨.word,w 9,.word⟩ ⟨.word,w 2,.word⟩ true
    (.ifE (.var 0) (.var 2) (.letE (.var 1) (.var 0))) 4
    (fun _ _ => .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl))))
  for content in [text "{if(c){return x;}else{missing;return y;}}",
      "function f<G>(x:T,y:T,c:Bool) returns(T){{return x;}}",
      "function f(x:T,x:T,c:Bool) returns(T){{return x;}}", "function f(x:T,y:T,c:Bool) returns(Bool){{return x;}}"] do
    let source ← parsed content
    check ((prepareRuntimeFunction? (table .word) owner source args).isNone) "whole gate relaxed"
    checkMutual .word source args
  let source ← parsed (text "{{return x;}}")
  for badArgs in [[], args.drop 1, args.reverse, args ++ [⟨.unit,.unit,.unit⟩]] do
    check ((prepareRuntimeFunction? (table .word) owner source badArgs).isNone) "argument gate relaxed"
    checkMutual .word source badArgs
  let changed : List TypedRuntimeArgument := [⟨.word,w 14,.word⟩, ⟨.word,w 2,.word⟩, ⟨.bool,.bool true,.bool⟩]
  let first ← prepare (table .word) source args; let second ← prepare (table .word) source changed
  have _ := prepareRuntimeFunction?_static_projection_eq (types := table .word) (owner := owner) (declaration := source)
    (leftArguments := args) (rightArguments := changed) (by rfl)
  check (decide (first.prepared.core = second.prepared.core ∧ first.prepared.returnType = second.prepared.returnType ∧
      first.prepared.inputs.context = second.prepared.inputs.context ∧ first.prepared.inputs.names = second.prepared.inputs.names) &&
    decide (rows first.prepared.inputs ≠ rows second.prepared.inputs) &&
    decide (runRuntimeFunction? (table .word) owner source args 1 [] = some (.word,.done (w 9) []) ∧
      runRuntimeFunction? (table .word) owner source changed 1 [] = some (.word,.done (w 14) [])))
    "equal argument types erased different actual values"
  for type in [Core.Ty.namedData ⟨90⟩, .product (.namedData ⟨90⟩) (.cell (.namedData ⟨13⟩))] do
    let source ← parsed (text (mixedText true))
    let some inputs := declareRuntimeParameters? (table type) owner source.value.signature.parameters.elements
      | throw (IO.userError "nominal static parameters demanded runtime values")
    let certified ← body (table type) inputs source.value.body
    have _ := certified.evidence.complete
    check (decide (certified.core = mixed ∧ certified.type = type ∧ inputs.context.values = [.bool,type,type]))
      "nominal independent static meaning changed"
  have _ : ¬ TypeNameTable.Extends (table .word) ((["T"], .bool) :: table .word) := by
    intro extension
    have wrong : Core.Ty.word = .bool := (extension (.head : TypeNameTable.Lookup (table .word) ["T"] .word)).type_unique .head
    cases wrong
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRuntimeOwners
/-! Caller-owned declaration identities change input IDs, not the prepared
Core or runtime values. Compare complete parsed entries at identical fuel. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-owner.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  assertTrue lexed.diagnostics.isEmpty s!"{content}: lexer diagnostics"
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      assertTrue (next.atEnd && next.diagnostics.isEmpty) s!"{content}: incomplete or diagnosed declaration"
      return source
  | .reject _ _ => throw (IO.userError s!"{content}: expected a complete declaration")
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def firstOwner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"First", by decide⟩], by decide⟩⟩, 3⟩
private def secondOwner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Second", by decide⟩], by decide⟩⟩, 9⟩
private def types : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], .word), (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def store : Core.Store := [.word nine, .bool false]
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def wordArg (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩
private def closure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩

private def checkAccepted (content : String) (arguments : List TypedRuntimeArgument)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (initialStore : Core.Store := store) : IO Unit := do
  let source ← parsed content
  let some original := prepareRuntimeFunction? types firstOwner source arguments
    | throw (IO.userError s!"{content}: original entry rejected")
  assertTrue (decide (original.core = core ∧ original.returnType = type))
    s!"{content}: wrong original Core/type"
  for owner in [firstOwner, secondOwner] do
    let some prepared := prepareRuntimeFunction? types owner source arguments
      | throw (IO.userError s!"{content}: changing the owner rejected a valid entry")
    assertTrue (decide (prepared.core = original.core ∧ prepared.returnType = original.returnType))
      s!"{content}: owner changed exact Core/type"
    assertTrue (decide (prepared.inputs.environment.values = arguments.reverse.map (·.value)))
      s!"{content}: owner changed actual runtime values or row order"
    assertTrue (decide (prepared.inputs.context.values = arguments.reverse.map (·.type)))
      s!"{content}: owner changed context types or row order"
    let expectedIds := (List.range arguments.length).reverse.map fun index => (⟨owner, index⟩ : Resolved.LocalId)
    assertTrue (decide (prepared.inputs.ids = expectedIds)) s!"{content}: incorrect owner-relative identities"
    -- This concrete table contains only firstOwner IDs; this is not a global ID map law.
    assertTrue (decide (prepared.inputs.names = LocalNameTable.mapIds
      (fun id => ⟨owner, id.binderIndex⟩) original.inputs.names)) s!"{content}: wrong name-table relabeling"
    if owner == secondOwner && !arguments.isEmpty then
      assertTrue (decide (prepared.inputs.ids ≠ original.inputs.ids))
        s!"{content}: distinct owners should change nonempty identity tables"
    for fuel in [0, 1, 2, 3, 4, 5, 6, 8, cost - 1, cost, cost + 5] do
      assertTrue (decide (runRuntimeFunction? types owner source arguments fuel initialStore =
        runRuntimeFunction? types firstOwner source arguments fuel initialStore))
        s!"{content}: owner changed a full same-fuel result or suspended state"
    assertTrue (decide (runRuntimeFunction? types owner source arguments 0 initialStore =
      some (type, .outOfFuel (Core.State.initial core original.inputs.environment.values initialStore))))
      s!"{content}: wrong exact zero-fuel state"
    for fuel in [0, cost - 1] do
      match runRuntimeFunction? types owner source arguments fuel initialStore with
      | some (actualType, .outOfFuel _) =>
          assertTrue (decide (actualType = type)) s!"{content}: exhaustion changed type"
      | _ => throw (IO.userError s!"{content}: expected exhaustion below cost")
    for fuel in [cost, cost + 5] do
      assertTrue (decide (runRuntimeFunction? types owner source arguments fuel initialStore =
        some (type, .done value initialStore))) s!"{content}: wrong value, cost, or preserved store"

def frontendParsedRuntimeOwnerTests : IO Unit := do
  checkAccepted "function unit() { return; }" [] .unit .unit .unit 1
  checkAccepted "function literal() returns (Word) { return 7; }" [] (.word seven) .word (.word seven) 1
  for left in [false, true] do
    for right in [false, true] do
      checkAccepted "function first(x: Bool, y: Bool) returns (Bool) { return x; }"
        [boolArg left, boolArg right] (.var 1) .bool (.bool left) 1
      checkAccepted "function last(x: Bool, y: Bool) returns (Bool) { return y; }"
        [boolArg left, boolArg right] (.var 0) .bool (.bool right) 1
  for choice in [false, true] do
    let arguments := [boolArg choice, wordArg seven, wordArg nine]
    checkAccepted "function choose(c: Bool, t: Word, f: Word) returns (Word) { return c ? ~t : f; }"
      arguments (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
      (.word (if choice then seven.bitNot else nine)) (if choice then 6 else 4)
    checkAccepted "function bits(c: Bool, t: Word, f: Word) returns (Word) { return t ^ f; }"
      arguments (.binary .wordXor (.var 1) (.var 0)) .word (.word (seven.bitXor nine)) 5
  checkAccepted "function cell(x: Cell) returns (Cell) { return x; }"
    [⟨.cell .word, .cellRef .word 40, .cellRef⟩] (.var 0) (.cell .word) (.cellRef .word 40) 1 []
  checkAccepted "function closure(x: Fn) returns (Fn) { return x; }"
    [closure] (.var 0) closure.type closure.value 1
  for choice in [false, true] do
    let arguments := [boolArg choice, wordArg seven, wordArg nine]
    for content in [
        "function missing(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : missing; }",
        "function branches(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : c; }",
        "function mismatch(c: Bool, t: Word, f: Word) returns (Bool) { return t; }",
        "function duplicate(c: Bool, t: Word, c: Word) returns (Word) { return t; }",
        "function generic<T>(c: Bool, t: Word, f: Word) returns (Word) { return t; }",
        "function empty(c: Bool, t: Word, f: Word) returns () { return; }"] do
      let source ← parsed content
      for owner in [firstOwner, secondOwner] do
        assertTrue (prepareRuntimeFunction? types owner source arguments).isNone
          s!"{content}: owner bypassed whole preparation"
        for fuel in [0, 1, 4, 6, 20] do
          assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone
            s!"{content}: invalid whole declaration ran after owner change"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypeNames
/-! Actual, completely consumed canonical type text feeds the explicit type
table. Parser acceptance is distinct from this monomorphic adapter's scope. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsedType? (content : String) : IO (Option Syntax.TypeExpr) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-type-name.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.typeExpr (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def table : TypeNameTable :=
  [(["Word"], .word), (["Word"], .bool), (["Bool"], .bool),
    (["Pkg", "Flag"], .bool), (["Pkg", "Cell"], .cell .word),
    (["Pkg", "Fn"], .function .word .bool), (["Pkg", "Pair"], .product .word .bool),
    (["W"], .word)]

private def checkNamed (content : String) (components : List String) (expected : Core.Ty) : IO Unit := do
  let some source ← parsedType? content
    | throw (IO.userError s!"{content}: expected one complete type")
  let .named name none := source.value
    | throw (IO.userError s!"{content}: expected an unapplied named type")
  assertTrue (decide (qualifiedTypeNameKey name = components))
    s!"{content}: changed qualified spelling components or their order"
  assertTrue (decide (interpretTypeName? table source = some expected))
    s!"{content}: wrong explicit type meaning or duplicate priority"
  assertTrue (interpretTypeName? [] source).isNone
    s!"{content}: acquired a meaning without a caller table"
  let invalidSpan : Syntax.SourceSpan := ⟨⟨.main, "unrelated.sol"⟩, 900, 2⟩
  let movedName : Syntax.QualifiedName := {
    span := invalidSpan
    value := { components := name.value.components.map fun component =>
      { component with span := invalidSpan } }
  }
  let moved : Syntax.TypeExpr := ⟨invalidSpan, .named movedName none⟩
  assertTrue (decide (interpretTypeName? table moved = some expected))
    s!"{content}: meaning depended on an outer, path, or component range"

def frontendParsedTypeNameTests : IO Unit := do
  checkNamed "Word" ["Word"] .word
  checkNamed "Bool" ["Bool"] .bool
  checkNamed "W" ["W"] .word
  checkNamed "Pkg.Flag" ["Pkg", "Flag"] .bool
  checkNamed " /* lead */ Pkg /* gap */ . Flag /* end */ " ["Pkg", "Flag"] .bool
  checkNamed "Pkg.Cell" ["Pkg", "Cell"] (.cell .word)
  checkNamed "Pkg.Fn" ["Pkg", "Fn"] (.function .word .bool)
  checkNamed "Pkg.Pair" ["Pkg", "Pair"] (.product .word .bool)
  let some wordSource ← parsedType? "Word"
    | throw (IO.userError "Word: complete parsing failed")
  assertTrue (decide (interpretTypeName? [(["Word"], .bool)] wordSource = some .bool))
    "Word spelling must not override the caller's explicitly supplied meaning"
  for content in ["Unknown", "word", "Flag", "Flag.Pkg", "Pkg.Other"] do
    let some source ← parsedType? content
      | throw (IO.userError s!"{content}: unknown names must still parse")
    assertTrue (interpretTypeName? table source).isNone
      s!"{content}: unknown or differently qualified name used a fallback meaning"
  for content in ["Word<Bool>", "Pkg.Flag<Word>", "mapping(Word => Bool)",
      "@Word", "function(Word) returns (Bool)", "comptime<Word>", "()", "(Word, Bool)"] do
    let some source ← parsedType? content
      | throw (IO.userError s!"{content}: unsupported adapter form should still parse")
    assertTrue (interpretTypeName? table source).isNone
      s!"{content}: unsupported type form received a monomorphic name meaning"
  for content in ["", "Word Bool", "Pkg.", ".Flag", "Word<", "Word<>",
      "Word;", "Word trailing", "\"Word\""] do
    assertTrue (← parsedType? content).isNone
      s!"{content}: accepted invalid or only partially consumed type text"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypeTableExtensions
/-! Caller dictionaries preserve exact parsed compilation only when their
first-match meanings persist. Mutual preservation includes rejection; adding
an unknown nominal meaning can instead enable compilation without any value. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def base : TypeNameTable := [(["Opaque"], .namedData ⟨91⟩), (["Bool"], .bool),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Pkg.Token"], .word), (["Word"], .word), (["Opaque"], .bool)]
private def clean : TypeNameTable := [(["Word"], .word), (["Pkg.Token"], .word),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Bool"], .bool), (["Opaque"], .namedData ⟨91⟩)]
private def extras : TypeNameTable :=
  [(["Opaque"], .bool), (["Unknown"], .namedData ⟨93⟩), (["Pkg", "Extra"], .unit)]
private def owners : List Resolved.DeclarationId :=
  [⟨⟨.main, ⟨[⟨"TypeExtensions", by decide⟩], by decide⟩⟩, 7⟩,
    ⟨⟨.main, ⟨[⟨"OtherTypes", by decide⟩], by decide⟩⟩, 41⟩]
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)
private def projection (compiled : CompiledRuntimeFunction) :
    Core.Expr × Core.Ty × List (String × Resolved.LocalId × Core.Ty) :=
  (compiled.core, compiled.returnType, rows compiled.inputs)

private theorem cleanedLookup (key : List String) :
    TypeNameTable.lookup? base key = TypeNameTable.lookup? clean key := by
  by_cases nominalKey : ["Opaque"] = key
  · subst key; rfl
  by_cases flag : ["Bool"] = key
  · subst key; rfl
  by_cases qualified : ["Pkg", "Token"] = key
  · subst key; rfl
  by_cases flattened : ["Pkg.Token"] = key
  · subst key; rfl
  by_cases word : ["Word"] = key
  · subst key; rfl
  simp [base, clean, TypeNameTable.lookup?, nominalKey, flag, qualified, flattened, word]

private theorem extendsOfLookupEquality {old next : TypeNameTable}
    (same : ∀ key, TypeNameTable.lookup? old key = TypeNameTable.lookup? next key) :
    TypeNameTable.Extends old next := by
  intro key type found
  exact TypeNameTable.lookup?_iff.mp ((same key).symm.trans (TypeNameTable.lookup?_iff.mpr found))

private theorem samePrepend {table : TypeNameTable} {key : List String} {type : Core.Ty}
    (present : TypeNameTable.Lookup table key type) :
    TypeNameTable.Extends table ((key, type) :: table) ∧
      TypeNameTable.Extends ((key, type) :: table) table := by
  constructor
  · intro selected actual found
    by_cases same : key = selected
    · subst selected
      cases found.type_unique present
      exact .head
    · exact .tail same found
  · intro selected actual found
    cases found with
    | head => exact present
    | tail _ original => exact original

private theorem changedMeaning {old next : TypeNameTable} {key : List String}
    {before after : Core.Ty} (original : TypeNameTable.Lookup old key before)
    (changed : TypeNameTable.Lookup next key after) (different : before ≠ after) :
    ¬ TypeNameTable.Extends old next := fun extension => different ((extension original).type_unique changed)

private theorem preserveTail {old next : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom old owner initial parameters final)
    (extension : TypeNameTable.Extends old next) (parameter : Syntax.FunctionParameter)
    (rest : List Syntax.FunctionParameter) (atHead : parameters = parameter :: rest) :
    ∃ extendedInitial, extendedInitial.bindings ≠ [] ∧
      RuntimeParametersDeclareFrom old owner extendedInitial rest final ∧
      RuntimeParametersDeclareFrom next owner extendedInitial rest final := by
  subst parameters
  cases declared with
  | cons meaning unused tail =>
      exact ⟨_, by simp [LocalTypeInputs.bindFresh], tail, tail.extend_types extension⟩

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-type-extensions.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"lexer invariant: {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")

private def annotations (source : Syntax.FunctionDecl) : List Syntax.TypeExpr :=
  source.value.signature.parameters.elements.filterMap (fun parameter => match parameter.value with
    | .typed _ _ annotation => some annotation
    | _ => none) ++ (source.value.signature.returnsClause.map (·.types.elements)).getD []

private def preserveMeaning {old next : TypeNameTable} (extension : TypeNameTable.Extends old next)
    (annotation : Syntax.TypeExpr) : IO Unit := do
  match accepted : interpretTypeName? old annotation with
  | none => pure ()
  | some type =>
      have _ := (interpretTypeName?_sound accepted).extend_types extension
      have _ := interpretTypeName?_some_of_extends extension accepted
      assertTrue (decide (interpretTypeName? next annotation = some type)) "a successful annotation meaning changed"

private def preserve {old next : TypeNameTable} (extension : TypeNameTable.Extends old next)
    (source : Syntax.FunctionDecl) (core : Core.Expr) (type : Core.Ty) (parameterTypes : List Core.Ty) : IO Unit := do
  for annotation in annotations source do preserveMeaning extension annotation
  for owner in owners do
    match accepted : compileRuntimeFunction? old owner source with
    | none => throw (IO.userError "positive source did not compile under its original dictionary")
    | some compiled =>
        let provenance := compileRuntimeFunction?_sound accepted
        have _ := provenance.header.returnsMeaning.extend_types extension
        have _ := provenance.header.extend_types extension
        have _ := RuntimeParametersDeclareFrom.extend_types provenance.parameters extension
        have _ := RuntimeParametersDeclare.extend_types provenance.parameters extension
        have _ := declareRuntimeParameters?_some_of_extends extension provenance.parameters.complete
        match atHead : source.value.signature.parameters.elements with
        | [] => pure ()
        | parameter :: rest =>
            have _ := preserveTail provenance.parameters extension parameter rest atHead
            pure ()
        let transported := provenance.extend_types extension
        have exact := compileRuntimeFunction?_some_of_extends extension accepted
        have _ := transported.complete
        match nextAt : compileRuntimeFunction? next owner source with
        | none => throw (IO.userError "meaning extension lost a successful whole entry")
        | some changed =>
            have _ : changed = compiled := Option.some.inj (nextAt.symm.trans exact)
            assertTrue (decide (projection changed = projection compiled ∧ changed.inputs.ids = compiled.inputs.ids ∧
              changed.core = core ∧ changed.returnType = type ∧
              changed.inputs.context.values = parameterTypes.reverse)) "extension did not retain the complete compiled record"

private def checkMutual {old next : TypeNameTable} (forward : TypeNameTable.Extends old next)
    (backward : TypeNameTable.Extends next old) (source : Syntax.FunctionDecl) : IO Unit := do
  for key in [["Opaque"], ["Bool"], ["Word"], ["Pkg", "Token"], ["Pkg.Token"], ["Token", "Pkg"], ["Unknown"], []] do
    have _ := TypeNameTable.lookup?_eq_of_mutual_extends forward backward key
    assertTrue (decide (TypeNameTable.lookup? old key = TypeNameTable.lookup? next key)) "mutual first-match lookup or absence changed"
  for annotation in annotations source do
    have _ := interpretTypeName?_eq_of_mutual_extends forward backward annotation
    assertTrue (decide (interpretTypeName? old annotation = interpretTypeName? next annotation)) "mutual annotation result changed"
  for owner in owners do
    let parameters := source.value.signature.parameters.elements
    have _ := declareRuntimeParameters?_eq_of_mutual_extends forward backward owner parameters
    have _ := compileRuntimeFunction?_eq_of_mutual_extends forward backward owner source
    assertTrue (decide ((declareRuntimeParameters? old owner parameters).map rows =
      (declareRuntimeParameters? next owner parameters).map rows ∧
      (compileRuntimeFunction? old owner source).map projection = (compileRuntimeFunction? next owner source).map projection))
      "mutual extension failed to preserve a complete optional result"

def frontendParsedTypeTableExtensionTests : IO Unit := do
  let cleaned : TypeNameTable.Extends base clean := extendsOfLookupEquality cleanedLookup
  let restored : TypeNameTable.Extends clean base := extendsOfLookupEquality (fun key => (cleanedLookup key).symm)
  let same := samePrepend (show TypeNameTable.Lookup base ["Opaque"] (.namedData ⟨91⟩) from .head)
  let appended : TypeNameTable.Extends base (base ++ extras) := TypeNameTable.Extends.append_right base extras
  let fresh : TypeNameTable.Extends (base ++ extras) ((["Fresh"], .unit) :: (base ++ extras)) :=
    TypeNameTable.Extends.cons_fresh (base ++ extras) ["Fresh"] Core.Ty.unit (by decide)
  let extensions : List { next : TypeNameTable // TypeNameTable.Extends base next } :=
    [⟨base, TypeNameTable.Extends.refl base⟩, ⟨base ++ extras, appended⟩,
      ⟨(["Fresh"], .unit) :: (base ++ extras), TypeNameTable.Extends.trans appended fresh⟩,
      ⟨(["Opaque"], .namedData ⟨91⟩) :: base, same.1⟩, ⟨clean, cleaned⟩]
  assertTrue (decide (base ≠ clean ∧ base.length = clean.length + 1 ∧ ["Opaque"] ∈ base.map Prod.fst))
    "pruning/reordering or same-key prepend fixture became trivial"
  let fixtures : List (String × Core.Expr × Core.Ty × List Core.Ty) := [
    ("function nominal(x: Opaque,y: Word) returns (Opaque){return x;}", .var 1, .namedData ⟨91⟩, [.namedData ⟨91⟩, .word]),
    ("function qualified(x: Pkg /* exact components */ . Token) returns (Pkg.Token){return x;}", .var 0, .namedData ⟨92⟩, [.namedData ⟨92⟩]),
    ("function nominal(c: Bool,x: Opaque,y: Opaque) returns (Opaque){if(c){return x;}else{return y;}}",
      .ifE (.var 2) (.var 1) (.var 0), .namedData ⟨91⟩, [.bool, .namedData ⟨91⟩, .namedData ⟨91⟩]),
    ("function unused(x: Opaque){return;}", .unit, .unit, [.namedData ⟨91⟩]),
    ("function bare(c: Bool,x: Opaque){if(c){return;}else{return;}}", .ifE (.var 1) .unit .unit, .unit, [.bool, .namedData ⟨91⟩])]
  for (content, core, type, parameterTypes) in fixtures do
    let some source ← parsed? (Syntax.Parser.functionDecl .module) content
      | throw (IO.userError "positive function did not completely parse")
    for extension in extensions do preserve extension.property source core type parameterTypes
    checkMutual cleaned restored source
    checkMutual same.1 same.2 source
  for content in ["function unknown(x: Unknown) returns (Unknown){return x;}",
      "function duplicate(x: Opaque,x: Word) returns (Opaque){return x;}",
      "function unsupported(x: Opaque<Word>) returns (Opaque){return x;}",
      "function generic<T>(x: Opaque) returns (Opaque){return x;}",
      "function many(x: Opaque) returns (Opaque,Opaque){return x;}",
      "function wrong(x: Opaque) returns (Word){return x;}",
      "function invalid(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return missing;}}",
      "function extra(x: Opaque) returns (Opaque){return x;return x;}",
      "function missing(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}}"] do
    let some source ← parsed? (Syntax.Parser.functionDecl .module) content
      | throw (IO.userError "semantic failure did not completely parse")
    for owner in owners do assertTrue (compileRuntimeFunction? base owner source).isNone "expected original rejection changed"
    checkMutual cleaned restored source
    checkMutual same.1 same.2 source
  for content in ["Opaque", "Pkg /* components */ . Token", "Unknown", "Opaque<Bool>", "mapping(Word => Bool)"] do
    let some annotation ← parsed? Syntax.Parser.typeExpr content | throw (IO.userError "complete type did not parse")
    for extension in extensions do preserveMeaning extension.property annotation
    have _ := interpretTypeName?_eq_of_mutual_extends cleaned restored annotation
    assertTrue (decide (interpretTypeName? base annotation = interpretTypeName? clean annotation)) "full type Option result changed"
  let some qualified ← parsed? Syntax.Parser.typeExpr "Pkg /* distinguish dotted key */ . Token"
    | throw (IO.userError "qualified type failed to parse")
  let .named name none := qualified.value | throw (IO.userError "qualified named shape changed")
  assertTrue (decide (qualifiedTypeNameKey name = ["Pkg", "Token"] ∧
    interpretTypeName? base qualified = some (.namedData ⟨92⟩) ∧ TypeNameTable.lookup? base ["Pkg.Token"] = some .word))
    "qualified component lists were flattened or reordered"
  let some unknown ← parsed? (Syntax.Parser.functionDecl .module)
      "function enabled(x: Unknown) returns (Unknown){return x;}" | throw (IO.userError "unknown-type entry did not parse")
  for annotation in annotations unknown do
    assertTrue (decide (interpretTypeName? base annotation = none ∧
      interpretTypeName? (base ++ extras) annotation = some (.namedData ⟨93⟩))) "new nominal meaning did not enable unknown annotation"
  for owner in owners do
    assertTrue ((declareRuntimeParameters? base owner unknown.value.signature.parameters.elements).isNone &&
      (compileRuntimeFunction? base owner unknown).isNone) "unknown-name rejection was lost in original table"
    let some compiled := compileRuntimeFunction? (base ++ extras) owner unknown
      | throw (IO.userError "one-way extension failed to enable unknown nominal compilation")
    assertTrue (decide (compiled.core = .var 0 ∧ compiled.returnType = .namedData ⟨93⟩ ∧
      rows compiled.inputs = [("x", ⟨owner, 0⟩, .namedData ⟨93⟩)])) "new nominal compilation fabricated or changed static data"
  let shadow : TypeNameTable := (["Opaque"], .bool) :: base
  have _ : ¬ TypeNameTable.Extends base shadow := changedMeaning (.head) (.head) (by decide)
  let some self ← parsed? (Syntax.Parser.functionDecl .module)
      "function self(x: Opaque) returns (Opaque){return x;}" | throw (IO.userError "shadow contrast did not parse")
  for owner in owners do
    assertTrue (decide ((compileRuntimeFunction? base owner self).map (·.returnType) = some (.namedData ⟨91⟩) ∧
      (compileRuntimeFunction? shadow owner self).map (·.returnType) = some .bool)) "meaning-changing shadow became exact-record preservation"
  let wrongGuard : TypeNameTable := (["Bool"], .word) :: base
  have _ : ¬ TypeNameTable.Extends base wrongGuard :=
    changedMeaning (.tail (by decide) .head) .head (by decide)
  let some guarded ← parsed? (Syntax.Parser.functionDecl .module)
      "function guard(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}}"
    | throw (IO.userError "guard-shadow contrast did not parse")
  for owner in owners do
    assertTrue ((compileRuntimeFunction? base owner guarded).isSome &&
      (declareRuntimeParameters? wrongGuard owner guarded.value.signature.parameters.elements).isSome &&
      (compileRuntimeFunction? wrongGuard owner guarded).isNone) "changed guard meaning bypassed whole-body typing"
  let dropped : TypeNameTable := [(["Opaque"], .namedData ⟨91⟩)]
  have _ : ¬ TypeNameTable.Extends base dropped := by
    intro extension
    have found : TypeNameTable.Lookup base ["Bool"] .bool := .tail (by decide) .head
    have impossible := TypeNameTable.lookup?_iff.mpr (extension found)
    change none = some Core.Ty.bool at impossible
    cases impossible
  for owner in owners do
    assertTrue (decide ((compileRuntimeFunction? base owner self).map projection =
      (compileRuntimeFunction? dropped owner self).map projection)) "unused live-key deletion changed unrelated source"
  for content in ["function missing(x){return x;}", "function f(x: Opaque){return x;} trailing"] do
    assertTrue (← parsed? (Syntax.Parser.functionDecl .module) content).isNone "dictionary extension affected parser completeness"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendPreparedCheckpointBoundaryProperties
/-! Original identity functions expose the distinct actual-argument, store,
pending-frame and genuine-checkpoint premises. Structural preparation is not a
runtime-world check, and independent preparation does not validate a checker. -/
set_option autoImplicit false
namespace Tests.FrontendPreparedCheckpointBoundaries
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"PreparedCheckpoint",by decide⟩],by decide⟩⟩,141⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"prepared-checkpoint-boundary.sol"⟩,0,57⟩
private def named : Syntax.TypeExpr := ⟨span,.named ⟨span,⟨⟨⟨span,"A"⟩,[]⟩⟩⟩ none⟩
private def ref : Syntax.Expr := ⟨span,.identifier ⟨span,"x"⟩⟩
private def entry : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span,⟨span,"identity"⟩,none,⟨span,[⟨span,.typed none ⟨span,"x"⟩ named⟩]⟩,
    ⟨none,none⟩,some ⟨span,⟨span,[named]⟩⟩,none⟩,⟨span,[⟨span,.returnStmt (some ref)⟩]⟩⟩⟩
private def types (a : Core.Ty) : TypeNameTable := [(["A"],a),(["A"],.bool)]
private def prepared (arg : TypedRuntimeArgument) : PreparedRuntimeFunction :=
  ⟨LocalInputs.empty.bindFresh owner "x" arg.type arg.value arg.valueTyped,.var 0,arg.type⟩
private theorem preparation (arg : TypedRuntimeArgument) :
    RecursiveComputationFunctionPrepares (types arg.type) owner entry [arg] (prepared arg) :=
  ⟨⟨rfl,rfl,rfl,rfl,.single (.named .head)⟩,.cons (.named .head) (by simp) .nil,
    .expression (.pure (.identifier .head) (.var .head) (.var .head))⟩
private theorem argumentsTyped {world : Core.StoreTyping} {arg : TypedRuntimeArgument}
    (typed : Core.RuntimeValueHasType world arg.value arg.type) :
    ∀ actual ∈ [arg], Core.RuntimeValueHasType world actual.value actual.type := by
  intro actual member; simpa only [List.mem_singleton.mp member] using typed
private def start (arg : TypedRuntimeArgument) (k : List Core.Frame) (store : Core.Store) : Core.State :=
  ⟨.eval (prepared arg).core (prepared arg).inputs.environment.values,k,store⟩
private def saved (arg : TypedRuntimeArgument) (k : List Core.Frame) (store : Core.Store) : Core.State :=
  ⟨.ret arg.value,k,store⟩
private def cellArg (location : Nat) : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word location,.cellRef⟩
private def unitArg : TypedRuntimeArgument := ⟨.unit,.unit,.unit⟩
private def wordArg (word : Core.Word) : TypedRuntimeArgument := ⟨.word,.word word,.word⟩
private def pending (arg : TypedRuntimeArgument) : List Core.Frame := [.newCellApply arg.type,.pairApply (.bool false)]
private theorem pendingTyped {world : Core.StoreTyping} {arg : TypedRuntimeArgument}
    (_payload : Core.CellPayload arg.type) :
    Core.ContinuationHasType world (pending arg) arg.type (.product .bool (.cell arg.type)) :=
  .cons (.newCellApply) (.cons (.pairApply .bool) .nil)
private theorem stopped (arg : TypedRuntimeArgument) (store : Core.Store) :
    Core.runStateful 1 (start arg (pending arg) store) = .outOfFuel (saved arg (pending arg) store) := rfl

theorem literal_arguments_and_a_different_caller_result_type_remain_safe
    (arg : TypedRuntimeArgument) (_payload : Core.CellPayload arg.type)
    {world : Core.StoreTyping} {store : Core.Store}
    (typed : Core.RuntimeValueHasType world arg.value arg.type) (stored : Core.StoreHasTypes world store) :
    RecursiveComputationFunctionPrepares (types arg.type) owner entry [arg] (prepared arg) ∧
    Core.StateHasType (start arg (pending arg) store) (.product .bool (.cell arg.type)) ∧
    (∀ fuel error state, Core.runStateful fuel (start arg (pending arg) store) ≠ .fault error state) ∧
    Core.StateHasType (saved arg (pending arg) store) (.product .bool (.cell arg.type)) ∧
    (∀ fuel error state, Core.runStateful fuel (saved arg (pending arg) store) ≠ .fault error state) ∧
    (∀ more, Core.runStateful more (saved arg (pending arg) store) = Core.runStateful (1+more) (start arg (pending arg) store)) ∧
    Core.runStateful 2 (saved arg (pending arg) store) =
      .done (.pair (.bool false) (.cellRef arg.type store.length)) (store++[arg.value]) := by
  have safety := (preparation arg).runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType
    (argumentsTyped typed) stored (pendingTyped _payload)
  exact ⟨preparation arg,safety.1,safety.2.1,(safety.2.2 (stopped arg store)).1,
    (safety.2.2 (stopped arg store)).2,Core.runStateful_resume (stopped arg store),rfl⟩

theorem actual_caller_allocation_extends_the_original_world_and_keeps_old_references
    (arg : TypedRuntimeArgument) (_payload : Core.CellPayload arg.type)
    {world : Core.StoreTyping} {store : Core.Store}
    (typed : Core.RuntimeValueHasType world arg.value arg.type) (stored : Core.StoreHasTypes world store) :
    ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future (store++[arg.value]) ∧
      world.length < future.length ∧
      ∀ {location : Nat} {type : Core.Ty}, world[location]?=some type → future[location]?=some type := by
  obtain ⟨_,extension,_,further⟩ := (preparation arg).runtime_checkpoint_world_extension
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped typed) stored (pendingTyped _payload) (stopped arg store)
  have path : Core.Steps 1 (saved arg (pending arg) store)
      ⟨.ret (.cellRef arg.type store.length),[.pairApply (.bool false)],store++[arg.value]⟩ := .cons .applyNewCell .refl
  obtain ⟨future,more,finalTyped⟩ := further path
  refine ⟨future,extension.trans more,finalTyped,?_,fun found => (extension.trans more).lookup found⟩
  have initialLength := stored.length_eq
  have finalLength := finalTyped.length_eq
  change future.length = (store++[arg.value]).length at finalLength
  simp only [List.length_append,List.length_singleton] at finalLength
  omega

theorem structurally_prepared_references_need_not_be_allocated (location : Nat) :
    RecursiveComputationFunctionPrepares (types (.cell .word)) owner entry [cellArg location] (prepared (cellArg location)) ∧
    Core.ContinuationHasType [] [.loadCellApply] (.cell .word) .word ∧
    Core.StoreHasTypes [] [] ∧
    (¬ Core.RuntimeValueHasType [] (cellArg location).value (cellArg location).type) ∧
    Core.runStateful 1 (start (cellArg location) [.loadCellApply] []) =
      .fault (.invalidCellLocation location) (saved (cellArg location) [.loadCellApply] []) := by
  refine ⟨preparation (cellArg location),.cons .loadCellApply .nil,.nil,?_,?_⟩
  · intro typed; cases typed with | cellRef found => simp at found
  · simp [start,saved,prepared,cellArg,LocalInputs.environment,LocalInputs.bindFresh,LocalInputs.empty,
      Resolved.LocalScope.values,Core.runStateful,Core.advance,Core.Store.read?]

theorem a_terminating_run_need_not_have_runtime_typed_arguments :
    RecursiveComputationFunctionPrepares (types (.cell .word)) owner entry [cellArg 700] (prepared (cellArg 700)) ∧
    Core.runStateful 1 (start (cellArg 700) [] []) = .done (.cellRef .word 700) [] ∧
    ¬ Core.RuntimeValueHasType [] (.cellRef .word 700) (.cell .word) := by
  refine ⟨preparation (cellArg 700),rfl,?_⟩
  intro typed; cases typed with | cellRef found => cases found

theorem arguments_and_store_must_use_the_same_world (bit : Bool) :
    RecursiveComputationFunctionPrepares (types (.cell .word)) owner entry [cellArg 0] (prepared (cellArg 0)) ∧
    Core.RuntimeValueHasType [.word] (cellArg 0).value (cellArg 0).type ∧
    Core.StoreHasTypes [.bool] [.bool bit] ∧
    Core.ContinuationHasType [.word] [.loadCellApply,.unaryApply .wordNot] (.cell .word) .word ∧
    (¬ Core.StoreHasTypes [.word] [.bool bit]) ∧
    Core.runStateful 2 (start (cellArg 0) [.loadCellApply,.unaryApply .wordNot] [.bool bit]) =
      .fault (.invalidUnaryOperand .wordNot (.bool bit)) ⟨.ret (.bool bit),[.unaryApply .wordNot],[.bool bit]⟩ := by
  refine ⟨preparation (cellArg 0),.cellRef rfl,Core.StoreHasTypes.nil.allocate .bool .bool,
    .cons .loadCellApply (.cons .unaryApply .nil),?_,rfl⟩
  intro typed
  obtain ⟨value,found,_,valueTyped⟩ := typed.lookup (location := 0) rfl
  have same : value=.bool bit := (Option.some.inj found).symm
  subst value; cases valueTyped

theorem structural_preparation_and_a_typed_store_do_not_validate_pending_work :
    RecursiveComputationFunctionPrepares (types .unit) owner entry [unitArg] (prepared unitArg) ∧
    Core.RuntimeValueHasType [] unitArg.value unitArg.type ∧ Core.StoreHasTypes [] [] ∧
    (¬ ∃ result, Core.ContinuationHasType [] [.unaryApply .wordNot] .unit result) ∧
    Core.runStateful 1 (start unitArg [.unaryApply .wordNot] []) =
      .fault (.invalidUnaryOperand .wordNot .unit) (saved unitArg [.unaryApply .wordNot] []) ∧
    Core.runStateful 0 (saved unitArg [.unaryApply .wordNot] []) =
      .fault (.invalidUnaryOperand .wordNot .unit) (saved unitArg [.unaryApply .wordNot] []) := by
  refine ⟨preparation unitArg,.unit,.nil,?_,rfl,rfl⟩
  rintro ⟨_,typed⟩; cases typed with | cons frame _ => cases frame

private def foreign : Core.State := ⟨.ret (.word (Core.Word.ofNatModulo 0)),[.newCellApply .word],[.unit]⟩
theorem an_independently_typed_state_is_not_a_genuine_prepared_checkpoint (word : Core.Word) :
    Core.StateHasType foreign (.cell .word) ∧
    ∀ fuel, Core.runStateful fuel (start (wordArg word) (pending (wordArg word)) [.word word]) ≠ .outOfFuel foreign := by
  refine ⟨.ret ((Core.StoreHasTypes.nil.allocate .unit .unit).toRuntime) .word (.cons .newCellApply .nil),?_⟩
  intro fuel exhausted
  obtain ⟨future,extension,stored,_⟩ := (preparation (wordArg word)).runtime_checkpoint_world_extension
    RecursiveLocalComputationElaborates.core_hasType (world := [.word]) (argumentsTyped .word)
    (Core.StoreHasTypes.nil.allocate .word .word) (pendingTyped .word) exhausted
  obtain ⟨value,found,typed⟩ := stored.lookup (extension.lookup (location := 0) (type := .word) rfl)
  change some Core.Value.unit=some value at found
  cases found; cases typed

private def reject (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) := none
theorem independent_checkpoint_safety_does_not_prove_an_arbitrary_checker_accepts :
    RecursiveComputationFunctionPrepares (types .unit) owner entry [unitArg] (prepared unitArg) ∧
    (∀ fuel error state, Core.runStateful fuel (start unitArg [] []) ≠ .fault error state) ∧
    prepareComputationFunction? reject (types .unit) owner entry [unitArg] = none ∧
    ∀ fuel store, runComputationFunction? reject (types .unit) owner entry [unitArg] fuel store = none := by
  have safety := (preparation unitArg).runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType
    (world := []) (argumentsTyped .unit) Core.StoreHasTypes.nil Core.ContinuationHasType.nil
  have absent : prepareComputationFunction? reject (types .unit) owner entry [unitArg] = none := by
    simp [prepareComputationFunction?,elaborateComputationReturnTree?,entry,reject]
  exact ⟨preparation unitArg,safety.2.1,absent,fun _ _ => by simp [runComputationFunction?,absent]⟩

end Tests.FrontendPreparedCheckpointBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeCapturedOwnerBoundaryProperties
/- Independent collision calculations precede the covariance APIs. Duplicate rows
remain ordered, and opaque closure syntax, cells and full payloads are literal.
Word selection needs no owner injectivity and does not inspect skipped suffixes. -/
set_option autoImplicit false
namespace Tests.RuntimeCapturedOwnerBoundaries
open Solcore Solcore.Frontend
private abbrev L := Resolved.LocalScope.Lookup (α := RuntimeValue)
private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"OwnerBoundary",by decide⟩],by decide⟩⟩,n⟩
private def id (o n : Nat) : Resolved.LocalId := ⟨owner o,n⟩
private def collapse (_ : Resolved.DeclarationId) := owner 0
private def collisionRows : Resolved.LocalScope RuntimeValue :=
  [(id 2 7,.bool false),(id 9 7,.bool true),(id 9 7,.unit)]
private def foreignNames : LocalNameTable := [("dup",id 9 7),("dup",id 9 7)]

/-- Collapsing distinct owners changes the first payload and the allocated index. -/
theorem noninjective_owner_collision_breaks_lookup_and_fresh :
    ¬ Function.Injective collapse ∧
    L collisionRows (id 9 7) (.bool true) ∧
    Resolved.LocalScope.lookup? collisionRows (id 9 7) = some (.bool true) ∧
    Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners collapse collisionRows)
      (ownerLocalIdMap collapse (id 9 7)) = some (.bool false) ∧
    Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners collapse collisionRows)
      (ownerLocalIdMap collapse (id 9 7)) ≠
        (Resolved.LocalScope.lookup? collisionRows (id 9 7)).map (RuntimeValue.mapOwners collapse) ∧
    Resolved.freshLocalId (owner 2) (foreignNames.map Prod.snd) = id 2 0 ∧
    Resolved.freshLocalId (collapse (owner 2))
      ((LocalNameTable.mapIds (ownerLocalIdMap collapse) foreignNames).map Prod.snd) = id 0 8 ∧
    Resolved.freshLocalId (collapse (owner 2))
      ((LocalNameTable.mapIds (ownerLocalIdMap collapse) foreignNames).map Prod.snd) ≠
        ownerLocalIdMap collapse (Resolved.freshLocalId (owner 2) (foreignNames.map Prod.snd)) := by
  have found : L collisionRows (id 9 7) (.bool true) := .tail (by decide) .head
  have original : Resolved.LocalScope.lookup? collisionRows (id 9 7) = some (.bool true) := rfl
  have mapped : Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners collapse collisionRows)
      (ownerLocalIdMap collapse (id 9 7)) = some (.bool false) := by
    simp [collisionRows,mapRuntimeCapturedOwners,RuntimeValue.mapOwners,ownerLocalIdMap,collapse,id,
      Resolved.LocalScope.lookup?]
  have oldFresh : Resolved.freshLocalId (owner 2) (foreignNames.map Prod.snd) = id 2 0 := rfl
  have newFresh : Resolved.freshLocalId (collapse (owner 2))
      ((LocalNameTable.mapIds (ownerLocalIdMap collapse) foreignNames).map Prod.snd) = id 0 8 := rfl
  have notInjective : ¬ Function.Injective collapse := by
    intro injective
    have same := injective (show collapse (owner 2) = collapse (owner 9) from rfl)
    have impossible := congrArg Resolved.DeclarationId.declarationIndex same
    contradiction
  refine ⟨notInjective,found,original,mapped,?_,oldFresh,newFresh,?_⟩
  · rw [mapped,original]
    simp [RuntimeValue.mapOwners]
  · rw [newFresh,oldFresh]
    decide

private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId :=
  ⟨o.moduleId,o.declarationIndex+1⟩
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  cases left; cases right
  simp only [shift] at modules indices
  cases modules
  have equal := Nat.add_right_cancel indices
  cases equal
  rfl
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨before,equal⟩ := onto (owner 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex equal
  change before.declarationIndex+1=0 at impossible
  omega
private def span (n : Nat) : Syntax.SourceSpan := ⟨⟨.main,"owner-boundary.sol"⟩,n,n+1⟩
private def source : Syntax.Expr := ⟨span 10,.identifier ⟨span 11,"opaque"⟩⟩
private def core : RuntimeValue :=
  .coreClosure .unit .word (.var 99) [.cellRef .word 700,.hostFunction .storageWrite]
private def payload : RuntimeValue := .sourceClosure source (owner 2)
  [("q",id 2 7),("q",id 9 7)] [(id 2 7,core),(id 2 7,.unit)]
private def shiftedPayload : RuntimeValue := .sourceClosure source (owner 3)
  [("q",id 3 7),("q",id 10 7)] [(id 3 7,core),(id 3 7,.unit)]
private def rows : Resolved.LocalScope RuntimeValue :=
  [(id 9 7,.unit),(id 2 7,payload),(id 2 7,.bool false),(id 2 8,.cellRef .word 900)]
private def names : LocalNameTable :=
  [("x",id 2 7),("x",id 9 7),("y",id 2 8),("y",id 2 8),("z",id 9 90)]
private theorem payload_calculation : payload.mapOwners shift = shiftedPayload := by
  simp [payload,shiftedPayload,core,RuntimeValue.mapOwners,LocalNameTable.mapIds,ownerLocalIdMap,shift,id,owner]

/-- Surjectivity and unique rows are unnecessary: first matches and fresh index stay exact. -/
theorem injective_nonsurjective_transport_keeps_duplicate_first_match :
    Function.Injective shift ∧ ¬ Function.Surjective shift ∧
    LocalNameTable.Lookup names "x" (id 2 7) ∧
    LocalNameTable.Lookup (LocalNameTable.mapIds (ownerLocalIdMap shift) names) "x" (id 3 7) ∧
    LocalNameTable.lookup? names "missing" = none ∧
    LocalNameTable.lookup? (LocalNameTable.mapIds (ownerLocalIdMap shift) names) "missing" = none ∧
    L rows (id 2 7) payload ∧
    Resolved.LocalScope.lookup? rows (id 2 7) = some payload ∧
    Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners shift rows) (id 3 7) = some shiftedPayload ∧
    L (mapRuntimeCapturedOwners shift rows) (id 3 7) shiftedPayload ∧
    Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners shift rows) (id 3 99) = none ∧
    Resolved.freshLocalId (owner 2) (names.map Prod.snd) = id 2 9 ∧
    Resolved.freshLocalId (owner 3)
      ((LocalNameTable.mapIds (ownerLocalIdMap shift) names).map Prod.snd) = id 3 9 ∧
    Resolved.freshLocalId (owner 3)
      ((LocalNameTable.mapIds (ownerLocalIdMap shift) names).map Prod.snd) =
        ownerLocalIdMap shift (Resolved.freshLocalId (owner 2) (names.map Prod.snd)) := by
  have named : LocalNameTable.Lookup names "x" (id 2 7) := .head
  have mappedNamed : LocalNameTable.Lookup (LocalNameTable.mapIds (ownerLocalIdMap shift) names) "x" (id 3 7) := .head
  have missingName : LocalNameTable.lookup? names "missing" = none := rfl
  have mappedMissingName : LocalNameTable.lookup? (LocalNameTable.mapIds (ownerLocalIdMap shift) names) "missing" = none := rfl
  have found : L rows (id 2 7) payload := .tail (by decide) .head
  have original : Resolved.LocalScope.lookup? rows (id 2 7) = some payload := rfl
  have absent : Resolved.LocalScope.lookup? rows (id 2 99) = none := rfl
  have mapped : Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners shift rows) (id 3 7) = some shiftedPayload := by
    simp [rows,mapRuntimeCapturedOwners,Resolved.LocalScope.lookup?,ownerLocalIdMap,shift,id,owner,
      payload_calculation,RuntimeValue.mapOwners]
  have fresh : Resolved.freshLocalId (owner 2) (names.map Prod.snd) = id 2 9 := rfl
  have mappedFresh : Resolved.freshLocalId (owner 3)
      ((LocalNameTable.mapIds (ownerLocalIdMap shift) names).map Prod.snd) = id 3 9 := rfl
  have transported := mapRuntimeCapturedOwners_lookup shift shift_injective found
  have absentTransport := lookup?_mapRuntimeCapturedOwners shift shift_injective rows (id 2 99)
  have freshTransport := freshLocalId_mapRuntimeNamesOwners shift shift_injective (owner 2) names
  have mappedFound : L (mapRuntimeCapturedOwners shift rows) (id 3 7) shiftedPayload := by
    simpa only [payload_calculation,ownerLocalIdMap,shift,id,owner,L] using transported
  have mappedAbsent : Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners shift rows) (id 3 99) = none := by
    rw [absent] at absentTransport
    simpa only [Option.map_none,ownerLocalIdMap,shift,id,owner] using absentTransport
  exact ⟨shift_injective,shift_not_surjective,named,mappedNamed,missingName,mappedMissingName,
    found,original,mapped,mappedFound,mappedAbsent,fresh,
    mappedFresh,freshTransport⟩

private def body (n : Nat) : Syntax.Block := ⟨span n,[]⟩
private def literalCase (text : String) (n : Nat) : Syntax.MatchCase :=
  ⟨span (n+1),⟨⟨span (n+2),.literal ⟨span (n+3),.decimal text⟩⟩,body n⟩⟩
private def wildcardCase : Syntax.MatchCase := ⟨span 31,⟨⟨span 32,.wildcard (span 33)⟩,body 30⟩⟩
private def badCase : Syntax.MatchCase :=
  ⟨span 51,⟨⟨span 52,.literal ⟨span 53,.string "unvisited"⟩⟩,body 50⟩⟩
private def literalCases := [literalCase "0" 10,literalCase "1" 20,literalCase "1" 21,badCase]
private def one : Core.Word := ⟨1,by decide⟩
private theorem zeroMeaning : WordMatchPatternClassifies (literalCase "0" 10).value.pattern (some Core.Word.zero) := by
  refine .literal ⟨_,rfl,?_⟩
  exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) (by decide)) .nil)
private theorem oneMeaning : WordMatchPatternClassifies (literalCase "1" 20).value.pattern (some one) := by
  refine .literal ⟨_,rfl,?_⟩
  exact .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) (by decide)) .nil)

/-- Literal position/count, mixed wildcard/default, and first non-Word rejection survive any map. -/
theorem owner_changes_preserve_ordered_word_selection
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) :
    literalCases[1]? = some (literalCase "1" 20) ∧
    RuntimeWordMatchChooses ((RuntimeValue.word one).mapOwners mapping) literalCases (some (body 40)) (body 20) 2 ∧
    chooseRuntimeWordMatch? ((RuntimeValue.word one).mapOwners mapping) literalCases (some (body 40)) = some (body 20,2) ∧
    RuntimeWordMatchChooses (payload.mapOwners mapping) [wildcardCase,badCase] (some (body 40)) (body 30) 0 ∧
    chooseRuntimeWordMatch? (payload.mapOwners mapping) [wildcardCase,badCase] (some (body 40)) = some (body 30,0) ∧
    RuntimeWordMatchChooses (payload.mapOwners mapping) [] (some (body 40)) (body 40) 0 ∧
    chooseRuntimeWordMatch? (payload.mapOwners mapping) [] (some (body 40)) = some (body 40,0) ∧
    chooseRuntimeWordMatch? (payload.mapOwners mapping) literalCases (some (body 40)) = none := by
  have literalOriginal : RuntimeWordMatchChooses (.word one) literalCases (some (body 40)) (body 20) 2 :=
    .miss zeroMeaning (by decide) (.hit oneMeaning)
  have wildcardOriginal : RuntimeWordMatchChooses payload [wildcardCase,badCase] (some (body 40)) (body 30) 0 :=
    .wildcard (.wildcard rfl)
  have defaultOriginal : RuntimeWordMatchChooses payload [] (some (body 40)) (body 40) 0 := .fallback
  have literalRun : chooseRuntimeWordMatch? (.word one) literalCases (some (body 40)) = some (body 20,2) :=
    chooseRuntimeWordMatch?_iff.mpr literalOriginal
  have wildcardRun : chooseRuntimeWordMatch? payload [wildcardCase,badCase] (some (body 40)) = some (body 30,0) :=
    chooseRuntimeWordMatch?_iff.mpr wildcardOriginal
  have defaultRun : chooseRuntimeWordMatch? payload [] (some (body 40)) = some (body 40,0) :=
    chooseRuntimeWordMatch?_iff.mpr defaultOriginal
  have rejected : chooseRuntimeWordMatch? payload literalCases (some (body 40)) = none := by
    simp only [literalCases,chooseRuntimeWordMatch?,interpretWordMatchPattern?_iff.mpr zeroMeaning,payload]
  exact ⟨rfl,(runtimeWordMatchChooses_mapOwners_iff mapping).mpr literalOriginal,
    (chooseRuntimeWordMatch?_mapOwners mapping _ _ _).trans literalRun,
    (runtimeWordMatchChooses_mapOwners_iff mapping).mpr wildcardOriginal,
    (chooseRuntimeWordMatch?_mapOwners mapping _ _ _).trans wildcardRun,
    (runtimeWordMatchChooses_mapOwners_iff mapping).mpr defaultOriginal,
    (chooseRuntimeWordMatch?_mapOwners mapping _ _ _).trans defaultRun,
    (chooseRuntimeWordMatch?_mapOwners mapping _ _ _).trans rejected⟩

end Tests.RuntimeCapturedOwnerBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeOwnerProperties
/-! Owner changes relabel identities, not positional Core or runtime values.
Independent entry witnesses retain every header and parameter restriction. -/

set_option autoImplicit false

namespace Tests.FrontendRuntimeOwner

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "runtime-owner.sol"⟩, 9, 1⟩
private def firstOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"RuntimeOwner", by decide⟩], by decide⟩⟩, 0⟩
private def secondOwner : Resolved.DeclarationId := { firstOwner with declarationIndex := 1 }
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Bool"], .bool), (["Value"], type)]
private def params := [parameter "c" "Bool", parameter "x" "Value"]
private def args (argument : TypedRuntimeArgument) := [⟨.bool, .bool true, .bool⟩, argument]
private def inputs (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "c" .bool (.bool true) .bool).bindFresh
    owner "x" argument.type argument.value argument.valueTyped
private def source : Syntax.Expr := ⟨span, .conditional (ref "c") span (ref "x") span (ref "x")⟩
private def core : Core.Expr := .ifE (.var 1) (.var 0) (.var 0)
private def declaration (body : Syntax.Expr := source) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "selected"⟩, none, ⟨span, params⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Value"]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some body)⟩]⟩⟩⟩
private def prepared (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) : PreparedRuntimeFunction :=
  ⟨inputs owner argument, core, argument.type⟩
private theorem namesDifferent : "x" ≠ "c" := by decide
private theorem idsDifferent (owner : Resolved.DeclarationId) :
    Resolved.freshLocalId owner [Resolved.freshLocalId owner []] ≠ Resolved.freshLocalId owner [] :=
  Resolved.freshLocalId_cons_fresh_ne owner []
private theorem bound (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) :
    RuntimeParametersBind (types argument.type) owner params (args argument) (inputs owner argument) :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "x" ∉ ["c"]; simp) .nil)
private theorem preparation (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) :
    RuntimeFunctionPrepares (types argument.type) owner declaration (args argument) (prepared owner argument) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩, bound owner argument,
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.conditional (.identifier (.tail namesDifferent .head)) (.identifier .head) (.identifier .head))
      (.ifE (.var (.tail (idsDifferent owner) .head)) (.var .head) (.var .head))
      (.ifE (.var (.tail (idsDifferent owner) .head)) (.var .head) (.var .head))⟩
private theorem cost (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types argument.type) owner declaration (args argument)
      store argument.type argument.value store 4 := by
  have condition : LocalExpressionEvaluatesWithCost (inputs owner argument).names
      (inputs owner argument).environment store (ref "c") (.bool true) store 1 :=
    .identifier (.tail namesDifferent .head) (.tail (idsDifferent owner) .head)
  have selected : LocalExpressionEvaluatesWithCost (inputs owner argument).names
      (inputs owner argument).environment store (ref "x") argument.value store 1 :=
    .identifier .head .head
  exact .intro (preparation owner argument) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.ifTrue condition selected))

theorem injective_owner_transport_keeps_independent_parameters_and_exact_preparation
    (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    let mapped := (inputs owner argument).mapIds (ownerLocalIdMap mapping)
      (ownerLocalIdMap_injective mapping injective)
    RuntimeParametersBind (types argument.type) (mapping owner) params (args argument) mapped ∧
    RuntimeFunctionPrepares (types argument.type) (mapping owner) declaration (args argument)
      ⟨mapped, core, argument.type⟩ := by
  intro mapped
  exact ⟨(bound owner argument).map_owner mapping injective,
    (preparation owner argument).mapOwner mapping injective⟩

theorem distinct_owners_change_real_ids_but_preserve_checked_core_and_runtime_values
    (argument : TypedRuntimeArgument) :
    firstOwner ≠ secondOwner ∧
    prepareRuntimeFunction? (types argument.type) firstOwner declaration (args argument) =
      some (prepared firstOwner argument) ∧
    prepareRuntimeFunction? (types argument.type) secondOwner declaration (args argument) =
      some (prepared secondOwner argument) ∧
    (inputs firstOwner argument).ids = [⟨firstOwner, 1⟩, ⟨firstOwner, 0⟩] ∧
    (inputs secondOwner argument).ids = [⟨secondOwner, 1⟩, ⟨secondOwner, 0⟩] ∧
    (inputs firstOwner argument).ids ≠ (inputs secondOwner argument).ids ∧
    (inputs firstOwner argument).environment.values = [argument.value, .bool true] ∧
    (inputs secondOwner argument).environment.values = [argument.value, .bool true] := by
  refine ⟨by decide, (preparation firstOwner argument).complete,
    (preparation secondOwner argument).complete, rfl, rfl, ?_, rfl, rfl⟩
  intro same
  change [(⟨firstOwner, 1⟩ : Resolved.LocalId), ⟨firstOwner, 0⟩] = [⟨secondOwner, 1⟩, ⟨secondOwner, 0⟩] at same
  exact (by decide : firstOwner ≠ secondOwner) (congrArg Resolved.LocalId.owner (List.cons.inj same).1)

theorem every_fuel_preserves_full_results_including_the_same_intermediate_state
    (leftOwner rightOwner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) (store : Core.Store) :
    (∀ fuel, runRuntimeFunction? (types argument.type) leftOwner declaration (args argument) fuel store =
      runRuntimeFunction? (types argument.type) rightOwner declaration (args argument) fuel store) ∧
    runRuntimeFunction? (types argument.type) leftOwner declaration (args argument) 0 store =
      some (argument.type, .outOfFuel (Core.State.initial core [argument.value, .bool true] store)) ∧
    runRuntimeFunction? (types argument.type) rightOwner declaration (args argument) 0 store =
      some (argument.type, .outOfFuel (Core.State.initial core [argument.value, .bool true] store)) ∧
    (∃ suspended,
      runRuntimeFunction? (types argument.type) leftOwner declaration (args argument) 2 store =
        some (argument.type, .outOfFuel suspended) ∧
      runRuntimeFunction? (types argument.type) rightOwner declaration (args argument) 2 store =
        some (argument.type, .outOfFuel suspended)) ∧
    runRuntimeFunction? (types argument.type) rightOwner declaration (args argument) 4 store =
      some (argument.type, .done argument.value store) := by
  have same (fuel : Nat) := runRuntimeFunction?_owner_eq
    (types argument.type) leftOwner rightOwner declaration (args argument) fuel store
  have zero : runRuntimeFunction? (types argument.type) leftOwner declaration (args argument) 0 store =
      some (argument.type, .outOfFuel (Core.State.initial core [argument.value, .bool true] store)) := by
    rw [runRuntimeFunction?, (preparation leftOwner argument).complete]
    rfl
  obtain ⟨suspended, exhausted⟩ := ((cost leftOwner argument store).run_outOfFuel_iff (fuel := 2)).mpr (by decide)
  exact ⟨same, zero, (same 0).symm.trans zero,
    ⟨suspended, exhausted, (same 2).symm.trans exhausted⟩,
    (same 4).symm.trans ((cost leftOwner argument store).run_done_iff.mpr (by decide))⟩

private def missing : Syntax.Expr :=
  ⟨span, .conditional (ref "c") span (ref "x") span (ref "missing")⟩
private theorem missingRejected (owner : Resolved.DeclarationId) (argument : TypedRuntimeArgument) :
    prepareRuntimeFunction? (types argument.type) owner (declaration missing) (args argument) = none := by
  apply prepareRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨target, accepted⟩
  have sameInputs := accepted.parameters.result_unique (bound owner argument)
  have body := accepted.body
  rw [sameInputs] at body
  cases body with
  | single body =>
      cases body with
      | expression resolution _ _ =>
          cases resolution with
          | conditional _ _ right =>
              cases right with
              | identifier found =>
                  have impossible := LocalNameTable.lookup?_iff.mpr found
                  change none = some _ at impossible
                  cases impossible

theorem skipped_missing_reference_remains_a_whole_entry_failure_after_owner_change
    (leftOwner rightOwner : Resolved.DeclarationId) (argument : TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) :
    ReturnBodyEvaluatesWithCost (inputs leftOwner argument).names (inputs leftOwner argument).environment
      store (declaration missing).value.body argument.value store 4 ∧
    prepareRuntimeFunction? (types argument.type) leftOwner (declaration missing) (args argument) = none ∧
    prepareRuntimeFunction? (types argument.type) rightOwner (declaration missing) (args argument) = none ∧
    runRuntimeFunction? (types argument.type) leftOwner (declaration missing) (args argument) fuel store = none ∧
    runRuntimeFunction? (types argument.type) rightOwner (declaration missing) (args argument) fuel store = none := by
  have rejected := missingRejected leftOwner argument
  have rightRejected : prepareRuntimeFunction? (types argument.type) rightOwner (declaration missing)
      (args argument) = none := by
    have same := prepareRuntimeFunction?_owner_projection_eq
      (types argument.type) leftOwner rightOwner (declaration missing) (args argument)
    rw [rejected] at same
    cases result : prepareRuntimeFunction? (types argument.type) rightOwner (declaration missing) (args argument) with
    | none => rfl
    | some target => simp only [result, Option.map_none, Option.map_some, reduceCtorEq] at same
  have condition : LocalExpressionEvaluatesWithCost (inputs leftOwner argument).names
      (inputs leftOwner argument).environment store (ref "c") (.bool true) store 1 :=
    .identifier (.tail namesDifferent .head) (.tail (idsDifferent leftOwner) .head)
  have selected : LocalExpressionEvaluatesWithCost (inputs leftOwner argument).names
      (inputs leftOwner argument).environment store (ref "x") argument.value store 1 := .identifier .head .head
  exact ⟨.expression (.ifTrue condition selected), rejected, rightRejected,
    by simp only [runRuntimeFunction?, rejected, bind, Option.bind_none],
    by simp only [runRuntimeFunction?, rightRejected, bind, Option.bind_none]⟩

theorem opaque_closures_and_unallocated_cells_are_returned_without_interpretation
    (owner : Resolved.DeclarationId) (location : Core.Location) (store : Core.Store)
    (closure : Core.Value) (closureTyped : Core.ValueHasType closure (.function .bool .bool)) :
    runRuntimeFunction? (types (.function .bool .bool)) owner declaration
      (args ⟨.function .bool .bool, closure, closureTyped⟩) 4 store =
        some (.function .bool .bool, .done closure store) ∧
    runRuntimeFunction? (types (.cell .word)) owner declaration
      (args ⟨.cell .word, .cellRef .word location, .cellRef⟩) 4 store =
        some (.cell .word, .done (.cellRef .word location) store) ∧
    ([] : Core.Store)[location]? = none :=
  ⟨(cost owner ⟨.function .bool .bool, closure, closureTyped⟩ store).run_done_iff.mpr (by decide),
    (cost owner ⟨.cell .word, .cellRef .word location, .cellRef⟩ store).run_done_iff.mpr (by decide), by simp⟩

private def shift (id : Resolved.LocalId) : Resolved.LocalId :=
  { id with binderIndex := id.binderIndex + 10 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  cases left
  cases right
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases owners
  cases indices
  rfl

theorem arbitrary_injective_index_shifts_do_not_commute_with_empty_allocation
    (owner : Resolved.DeclarationId) :
    Function.Injective shift ∧
    shift (Resolved.freshLocalId owner []) = ⟨owner, 10⟩ ∧
    Resolved.freshLocalId owner ([].map shift) = ⟨owner, 0⟩ ∧
    shift (Resolved.freshLocalId owner []) ≠ Resolved.freshLocalId owner ([].map shift) := by
  refine ⟨shiftInjective, rfl, rfl, ?_⟩
  intro same
  have indices := congrArg Resolved.LocalId.binderIndex same
  change 10 = 0 at indices
  cases indices

end Tests.FrontendRuntimeOwner
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeTypeExtensionProperties
/-! Preserve actual input bundles, not merely their static projections.
Original annotations, independent provenance and manual paths fix expectations. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeTypeExtension
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RuntimeExtension", by decide⟩], by decide⟩⟩, 0⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "runtime-extension.sol"⟩, 17, 4⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) (annotation : Syntax.TypeExpr) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ annotation⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Cond"], .bool)]
private def parameters := [parameter "p" (named "Payload"), parameter "c" (named "Cond")]
private def pair : Syntax.Expr := ⟨span, .tuple ⟨span, [ref "saved", ref "c"]⟩⟩
private def body : Syntax.Block := ⟨span, [⟨span, .block [
  ⟨span, .letDecl ⟨span, "saved"⟩ (some (named "Payload")) (some (ref "p"))⟩,
  ⟨span, .expression pair true⟩, ⟨span, .returnStmt (some (ref "saved"))⟩]⟩]⟩
private def core : Core.Expr := .letE (.var 1) (.letE (.pair (.var 0) (.var 1)) (.var 1))
private def entry (result : String := "Payload") : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "same"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [named result]⟩⟩, none⟩, body⟩⟩
private def static (type : Core.Ty) := (LocalTypeInputs.empty.bindFresh owner "p" type).bindFresh owner "c" .bool
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def arguments {type : Core.Ty} (value : Actual type) (choice : Bool) : List TypedRuntimeArgument :=
  [⟨type, value.val, value.property⟩, ⟨.bool, .bool choice, .bool⟩]
private def inputs {type : Core.Ty} (value : Actual type) (choice : Bool) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "p" type value.val value.property).bindFresh owner "c" .bool (.bool choice) .bool
private def prepared {type : Core.Ty} (value : Actual type) (choice : Bool) : PreparedRuntimeFunction :=
  ⟨inputs value choice, core, type⟩
private theorem bound {type : Core.Ty} (value : Actual type) (choice : Bool) :
    RuntimeParametersBind (types type) owner parameters (arguments value choice) (inputs value choice) :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "c" ∉ ["p"]; decide) .nil)
private theorem header (type : Core.Ty) : RuntimeFunctionHeader (types type) entry.value.signature type :=
  ⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩
private theorem elaborated (type : Core.Ty) :
    TypedLetReturnTreeElaborates (types type) owner (static type) body core type := by
  have tail : TypedLetReturnTreeElaborates (types type) owner ((static type).bindFresh owner "saved" type)
      ⟨span, [⟨span, .expression pair true⟩, ⟨span, .returnStmt (some (ref "saved"))⟩]⟩
      (.letE (.pair (.var 0) (.var 1)) ((Core.Expr.var 0).weakenAt 0)) type :=
    .discard (.pair (.identifier .head) (.identifier (.tail (by change "saved" ≠ "c"; decide) .head)))
      (.pair (.var .head) (.var (.tail (by change id 2 ≠ id 1; decide) .head)))
      (.pair (.var .head) (.var (.tail (by change id 2 ≠ id 1; decide) .head)))
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
  simp only [Core.Expr.weakenAt] at tail
  exact .block (.binding (.named .head) (by change "saved" ∉ ["c", "p"]; decide)
    (.identifier (.tail (by change "c" ≠ "p"; decide) .head))
    (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var (.tail (by change id 1 ≠ id 0; decide) .head)) tail)
private theorem preparation {type : Core.Ty} (value : Actual type) (choice : Bool) :
    RuntimeFunctionPrepares (types type) owner entry (arguments value choice) (prepared value choice) :=
  ⟨header type, bound value choice, elaborated type⟩
private theorem counted {type : Core.Ty} (value : Actual type) (choice : Bool) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (inputs value choice).names (inputs value choice).environment
      store body value.val store 11 :=
  .block (.binding (name := ⟨span, "saved"⟩) (initializer := ref "p") (initializerCost := 1) (tailCost := 8)
    (.identifier (.tail (by change "c" ≠ "p"; decide) .head) (.tail (by change id 1 ≠ id 0; decide) .head))
    (.discard (expression := pair) (expressionCost := 5) (tailCost := 1)
      (.pair (left := ref "saved") (right := ref "c") (.identifier .head .head) (.identifier (.tail (by change "saved" ≠ "c"; decide) .head)
        (.tail (by change id 2 ≠ id 1; decide) .head))) (.single (.expression (.identifier .head .head)))))
private theorem path (value : Core.Value) (choice : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 11 ⟨.eval core [.bool choice, value], k, store⟩ ⟨.ret value, k, store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl)
    (CostStepComposition.letE (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
      (.cons (.var rfl) (.cons .applyPair .refl))))) (.cons (.var rfl) .refl))
private theorem runExact {type : Core.Ty} (value : Actual type) (choice : Bool) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? (types type) owner entry (arguments value choice) fuel store =
      some (type, Core.runStateful fuel (Core.State.initial core [.bool choice, value.val] store)) :=
  runRuntimeFunction?_eq_some_iff.mpr ⟨prepared value choice, preparation value choice, rfl, rfl⟩

theorem arbitrary_initial_actual_rows_and_values_are_not_erased
    (initial : LocalInputs) (argument : TypedRuntimeArgument) (own : Resolved.DeclarationId)
    (unused : "next" ∉ initial.names.map Prod.fst) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types argument.type) next) :
    RuntimeParametersBindFrom (types argument.type) own initial [parameter "next" (named "Payload")] [argument]
      (initial.bindFresh own "next" argument.type argument.value argument.valueTyped) ∧
    RuntimeParametersBindFrom next own initial [parameter "next" (named "Payload")] [argument]
      (initial.bindFresh own "next" argument.type argument.value argument.valueTyped) := by
  have original : RuntimeParametersBindFrom (types argument.type) own initial [parameter "next" (named "Payload")] [argument]
      (initial.bindFresh own "next" argument.type argument.value argument.valueTyped) := .cons (.named .head) unused .nil
  exact ⟨original, original.extend_types extension⟩

private def sparse : LocalInputs := ⟨[⟨"old", id 7, .unit, .unit, .unit⟩,
  ⟨"old", ⟨other, 99⟩, .bool, .bool true, .bool⟩, ⟨"old", id 2, .unit, .unit, .unit⟩], by decide⟩
theorem sparse_mixed_owners_and_duplicate_old_spellings_keep_max_plus_one (extras : TypeNameTable) :
    ¬ (sparse.names.map Prod.fst).Nodup ∧ Resolved.freshLocalId owner sparse.ids = id 8 ∧
    RuntimeParametersBindFrom (types .bool ++ extras) owner sparse [parameter "next" (named "Payload")]
      [⟨.bool, .bool false, .bool⟩] (sparse.bindFresh owner "next" .bool (.bool false) .bool) ∧
    (sparse.bindFresh owner "next" .bool (.bool false) .bool).environment.values = [.bool false, .unit, .bool true, .unit] :=
  ⟨by decide, rfl, (arbitrary_initial_actual_rows_and_values_are_not_erased sparse ⟨.bool, .bool false, .bool⟩ owner
    (by decide) _ (TypeNameTable.Extends.append_right _ extras)).2, rfl⟩

theorem independent_whole_preparation_preserves_the_full_actual_bundle
    {type : Core.Ty} (value : Actual type) (choice : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types type) next) :
    RuntimeParametersBind next owner parameters (arguments value choice) (inputs value choice) ∧
    bindRuntimeParameters? next owner parameters (arguments value choice) = some (inputs value choice) ∧
    RuntimeFunctionPrepares next owner entry (arguments value choice) (prepared value choice) ∧
    RuntimeFunctionHasType next owner entry (arguments value choice) type ∧
    prepareRuntimeFunction? next owner entry (arguments value choice) = some (prepared value choice) ∧
    (prepared value choice).inputs.environment.values = [.bool choice, value.val] :=
  ⟨RuntimeParametersBind.extend_types (bound value choice) extension,
    bindRuntimeParameters?_some_of_extends extension (bound value choice).complete,
    (preparation value choice).extend_types extension, (preparation value choice).hasType.extend_types extension,
    prepareRuntimeFunction?_some_of_extends extension (preparation value choice).complete, rfl⟩

theorem one_way_extension_preserves_every_present_fuel_result
    {type : Core.Ty} (value : Actual type) (choice : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types type) next) (store : Core.Store) (fuel : Nat) (k : List Core.Frame) :
    runRuntimeFunction? next owner entry (arguments value choice) fuel store =
      some (type, Core.runStateful fuel (Core.State.initial core [.bool choice, value.val] store)) ∧
    Core.Steps 11 ⟨.eval core [.bool choice, value.val], k, store⟩ ⟨.ret value.val, k, store⟩ ∧
    (runRuntimeFunction? (types type) owner entry (arguments value choice) fuel store = some (type, .done value.val store) ↔ 11 ≤ fuel) :=
  ⟨runRuntimeFunction?_some_of_extends extension (runExact value choice fuel store), path _ choice store k,
    (RuntimeFunctionEvaluatesWithCost.intro (preparation value choice) (counted value choice store)).run_done_iff⟩

private def duplicate (type : Core.Ty) := (["Payload"], type) :: types type
private theorem mutualExtension (type : Core.Ty) : TypeNameTable.Extends (types type) (duplicate type) ∧ TypeNameTable.Extends (duplicate type) (types type) := by
  constructor
  · intro key result found
    cases found with
    | head => exact .head
    | tail different found => exact .tail different (.tail different found)
  · intro key result found
    cases found with
    | head => exact .head
    | tail _ found => exact found
theorem unequal_mutual_tables_preserve_whole_options_not_just_success
    (type : Core.Ty) (own : Resolved.DeclarationId) (params : List Syntax.FunctionParameter)
    (declaration : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    types type ≠ duplicate type ∧
    bindRuntimeParameters? (types type) own params args = bindRuntimeParameters? (duplicate type) own params args ∧
    prepareRuntimeFunction? (types type) own declaration args = prepareRuntimeFunction? (duplicate type) own declaration args ∧
    runRuntimeFunction? (types type) own declaration args fuel store = runRuntimeFunction? (duplicate type) own declaration args fuel store := by
  refine ⟨?_, bindRuntimeParameters?_eq_of_mutual_extends (mutualExtension type).1 (mutualExtension type).2 own params args,
    prepareRuntimeFunction?_eq_of_mutual_extends (mutualExtension type).1 (mutualExtension type).2 own declaration args,
    runRuntimeFunction?_eq_of_mutual_extends (mutualExtension type).1 (mutualExtension type).2 own declaration args fuel store⟩
  intro same
  have lengths := congrArg List.length same
  change 2 = 3 at lengths
  cases lengths

private def checkpoint (value : Core.Value) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.pair value (.bool choice)), [.letBody (.var 1) [value, .bool choice, value]], store⟩
theorem genuine_saved_pair_states_and_remaining_two_steps_are_identical
    {type : Core.Ty} (value : Actual type) (choice : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types type) next) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (types type) owner entry (arguments value choice) 9 store = some (type, .outOfFuel (checkpoint value.val choice store)) ∧
    runRuntimeFunction? next owner entry (arguments value choice) 9 store = some (type, .outOfFuel (checkpoint value.val choice store)) ∧
    Core.Steps 2 (checkpoint value.val choice store) (Core.State.final value.val store) ∧
    runRuntimeFunction? next owner entry (arguments value choice) (9 + additional) store =
      some (type, Core.runStateful additional (checkpoint value.val choice store)) := by
  have stopped : runRuntimeFunction? (types type) owner entry (arguments value choice) 9 store =
      some (type, .outOfFuel (checkpoint value.val choice store)) := runExact value choice 9 store
  have transported := runRuntimeFunction?_some_of_extends extension stopped
  exact ⟨stopped, transported, .cons .bindLet (.cons (.var rfl) .refl), runRuntimeFunction?_resume transported additional⟩

theorem empty_and_single_tuple_parameters_are_not_component_argument_lists
    {type : Core.Ty} (value : Actual type) (choice : Bool) (extras : TypeNameTable) :
    bindRuntimeParameters? (types type ++ extras) owner [] [] = some .empty ∧
    RuntimeParametersBind (types type ++ extras) owner
      [parameter "one" ⟨span, .tuple [named "Payload", named "Cond"]⟩]
      [⟨.product type .bool, .pair value.val (.bool choice), .pair value.property .bool⟩]
      (LocalInputs.empty.bindFresh owner "one" (.product type .bool) (.pair value.val (.bool choice)) (.pair value.property .bool)) ∧
    bindRuntimeParameters? (types type) owner parameters [] = none := by
  have original : RuntimeParametersBind (types type) owner [parameter "one" ⟨span, .tuple [named "Payload", named "Cond"]⟩]
      [⟨.product type .bool, .pair value.val (.bool choice), .pair value.property .bool⟩]
      (LocalInputs.empty.bindFresh owner "one" (.product type .bool) (.pair value.val (.bool choice)) (.pair value.property .bool)) :=
    .cons (.pair (.named .head) (.named (.tail (by decide) .head))) (by simp [LocalInputs.empty, LocalInputs.names]) .nil
  exact ⟨rfl, RuntimeParametersBind.extend_types original (TypeNameTable.Extends.append_right _ extras), rfl⟩

theorem unknown_meaning_can_enable_the_same_actual_arguments
    {type : Core.Ty} (value : Actual type) (choice : Bool) :
    TypeNameTable.Extends [(["Cond"], .bool)] (types type) ∧
    bindRuntimeParameters? [(["Cond"], .bool)] owner parameters (arguments value choice) = none ∧
    bindRuntimeParameters? (types type) owner parameters (arguments value choice) = some (inputs value choice) ∧
    prepareRuntimeFunction? [(["Cond"], .bool)] owner entry (arguments value choice) = none ∧
    prepareRuntimeFunction? (types type) owner entry (arguments value choice) = some (prepared value choice) := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Payload"] type (by decide), ?_, (bound value choice).complete,
    ?_, (preparation value choice).complete⟩
  · apply bindRuntimeParameters?_eq_none_iff.mpr
    rintro ⟨output, evidence⟩
    cases evidence with
    | cons meaning _ _ =>
        have accepted := meaning.complete
        simp only [named, interpretStructuralType?_named_eq_typeName] at accepted
        change none = some type at accepted
        cases accepted
  · simp only [prepareRuntimeFunction?, entry, interpretRuntimeFunctionHeader?, interpretRuntimeReturnType?, named,
      interpretStructuralType?_named_eq_typeName]
    rfl

theorem mutually_extending_tables_keep_unknown_header_rejection
    {type : Core.Ty} (value : Actual type) (choice : Bool) (fuel : Nat) (store : Core.Store) :
    prepareRuntimeFunction? (types type) owner (entry "Unknown") (arguments value choice) = none ∧
    prepareRuntimeFunction? (duplicate type) owner (entry "Unknown") (arguments value choice) = none ∧
    runRuntimeFunction? (duplicate type) owner (entry "Unknown") (arguments value choice) fuel store = none := by
  have absent : prepareRuntimeFunction? (types type) owner (entry "Unknown") (arguments value choice) = none := by
    simp only [prepareRuntimeFunction?, entry, interpretRuntimeFunctionHeader?, interpretRuntimeReturnType?, named,
      interpretStructuralType?_named_eq_typeName]
    rfl
  have same := prepareRuntimeFunction?_eq_of_mutual_extends (mutualExtension type).1 (mutualExtension type).2 owner (entry "Unknown") (arguments value choice)
  exact ⟨absent, same.symm.trans absent, by simp [runRuntimeFunction?, same.symm.trans absent]⟩

theorem retained_rows_do_not_license_changed_first_meanings (value : Actual .word) :
    TypeNameTable.lookup? ((["Payload"], .bool) :: types .word) ["Payload"] = some .bool ∧
    ¬ TypeNameTable.Extends (types .word) ((["Payload"], .bool) :: types .word) ∧
    bindRuntimeParameters? ((["Payload"], .bool) :: types .word) owner parameters (arguments value true) = none := by
  refine ⟨rfl, ?_, ?_⟩
  · intro extension
    cases (extension (.head : TypeNameTable.Lookup (types .word) ["Payload"] .word)).type_unique
      (.head : TypeNameTable.Lookup ((["Payload"], .bool) :: types .word) ["Payload"] .bool)
  · apply bindRuntimeParameters?_eq_none_iff.mpr
    rintro ⟨output, evidence⟩
    cases evidence with
    | cons meaning _ _ => cases meaning.type_unique (.named (.head : TypeNameTable.Lookup
        ((["Payload"], .bool) :: types .word) ["Payload"] .bool))

theorem nominal_static_compilation_cannot_invent_actual_arguments (nominal : Core.DataTypeId) (extras : TypeNameTable) :
    compileRuntimeFunction? (types (.namedData nominal) ++ extras) owner entry = some ⟨static (.namedData nominal), core, .namedData nominal⟩ ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  have original : RuntimeFunctionCompiles (types (.namedData nominal)) owner entry ⟨static (.namedData nominal), core, .namedData nominal⟩ :=
    ⟨header _, .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named (.tail (by decide) .head)) (by change "c" ∉ ["p"]; decide) .nil), elaborated _⟩
  refine ⟨compileRuntimeFunction?_some_of_extends (TypeNameTable.Extends.append_right _ extras) original.complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩; cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_actual_cells_and_closures_survive_extension (location : Core.Location) (word : Core.Word)
    (extras : TypeNameTable) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? (types (.cell .word) ++ extras) owner entry (arguments ⟨.cellRef .word location, .cellRef⟩ true) fuel store =
      some (.cell .word, Core.runStateful fuel (Core.State.initial core [.bool true, .cellRef .word location] store)) ∧
    runRuntimeFunction? (types (.function .bool .word) ++ extras) owner entry
      (arguments ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ false) fuel store =
      some (.function .bool .word, Core.runStateful fuel (Core.State.initial core [.bool false, .closure .bool .word (.var 1) [.word word]] store)) :=
  ⟨runRuntimeFunction?_some_of_extends (TypeNameTable.Extends.append_right _ extras) (runExact _ true fuel store),
    runRuntimeFunction?_some_of_extends (TypeNameTable.Extends.append_right _ extras) (runExact _ false fuel store)⟩

private def number (n : Nat) : Actual .word := ⟨.word (Core.Word.ofNatModulo n), .word⟩
theorem the_same_compiled_projection_does_not_identify_different_actual_preparations :
    (prepared (number 3) true).toCompiled = (prepared (number 7) true).toCompiled ∧
    prepared (number 3) true ≠ prepared (number 7) true ∧
    runRuntimeFunction? (types .word) owner entry (arguments (number 3) true) 11 [] = some (.word, .done (number 3).val []) ∧
    runRuntimeFunction? (types .word) owner entry (arguments (number 7) true) 11 [] = some (.word, .done (number 7).val []) ∧
    (number 3).val ≠ (number 7).val := by
  have different : (number 3).val ≠ (number 7).val := by
    intro same
    have words := Core.Value.word.inj same
    have numbers := congrArg Fin.val words
    change 3 = 7 at numbers
    cases numbers
  refine ⟨rfl, ?_, runExact (number 3) true 11 [], runExact (number 7) true 11 [], different⟩
  intro same
  have rows := congrArg (fun prepared : PreparedRuntimeFunction => prepared.inputs.environment.values) same
  exact different (List.cons.inj (List.cons.inj rows).2).1

end Tests.FrontendRuntimeTypeExtension
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeValueBoundaryProperties
/-! Structural nonprojectability tests. These witnesses describe finite value
subterms, never reachable heap contents, source admission or execution. -/
set_option autoImplicit false
namespace Tests.RuntimeValueBoundaries
open Solcore Solcore.Frontend

private inductive ContainsSource : RuntimeValue → Prop where
  | source (source : Syntax.Expr) (owner : Resolved.DeclarationId)
      (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue)) :
      ContainsSource (.sourceClosure source owner names captured)
  | pairLeft {left right : RuntimeValue} : ContainsSource left → ContainsSource (.pair left right)
  | pairRight {left right : RuntimeValue} : ContainsSource right → ContainsSource (.pair left right)
  | inLeft {type : Core.Ty} {payload : RuntimeValue} :
      ContainsSource payload → ContainsSource (.inLeft type payload)
  | inRight {type : Core.Ty} {payload : RuntimeValue} :
      ContainsSource payload → ContainsSource (.inRight type payload)
  | constructed {constructor : Core.ConstructorId} {payload : RuntimeValue} :
      ContainsSource payload → ContainsSource (.constructed constructor payload)
  | coreCapture {a b : Core.Ty} {body : Core.Expr} {captured : List RuntimeValue} {value : RuntimeValue} :
      value ∈ captured → ContainsSource value → ContainsSource (.coreClosure a b body captured)

private theorem project_attached (values : List RuntimeValue) :
    values.attach.mapM (fun value => RuntimeValue.toCore? value.val) = values.mapM RuntimeValue.toCore? := by
  change values.attach.mapM (RuntimeValue.toCore? ∘ Subtype.val) = _
  rw [← List.mapM_map, List.attach_map_subtype_val]

private theorem list_fails_at_member {value : RuntimeValue} (values : List RuntimeValue)
    (member : value ∈ values) (absent : value.toCore? = none) :
    values.mapM RuntimeValue.toCore? = none := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      simp only [List.mapM_cons, bind]
      rcases member with same | member
      · subst head
        simp only [absent, Option.bind_none]
      · rw [ih member]
        cases head.toCore? <;> rfl

theorem every_finite_source_occurrence_blocks_projection {value : RuntimeValue}
    (contains : ContainsSource value) : value.toCore? = none := by
  induction contains with
  | source => simp only [RuntimeValue.toCore?]
  | pairLeft _ ih => simp only [RuntimeValue.toCore?, ih, bind, Option.bind_none]
  | @pairRight left _ _ ih =>
      simp only [RuntimeValue.toCore?, ih, bind]
      cases left.toCore? <;> rfl
  | inLeft _ ih | inRight _ ih | constructed _ ih =>
      simp only [RuntimeValue.toCore?, ih, Option.map_none]
  | coreCapture member _ ih =>
      simp only [RuntimeValue.toCore?, project_attached, list_fails_at_member _ member ih,
        Option.map_none]

theorem source_closures_are_outside_the_entire_core_image
    (source : Syntax.Expr) (owner : Resolved.DeclarationId)
    (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue))
    (core : Core.Value) : RuntimeValue.sourceClosure source owner names captured ≠ RuntimeValue.ofCore core := by
  intro same
  have projected := congrArg RuntimeValue.toCore? same
  rw [RuntimeValue.toCore?_ofCore] at projected
  simp only [RuntimeValue.toCore?, reduceCtorEq] at projected

theorem projection_failure_exactly_excludes_an_old_value (value : RuntimeValue) :
    value.toCore? = none ↔ ¬ ∃ core, value = RuntimeValue.ofCore core := by
  constructor
  · intro absent ⟨core, same⟩
    have projected := RuntimeValue.toCore?_eq_some_iff.mpr same
    rw [absent] at projected
    cases projected
  · intro noImage
    cases projected : value.toCore? with
    | none => rfl
    | some core => exact False.elim (noImage ⟨core, RuntimeValue.toCore?_eq_some_iff.mp projected⟩)

theorem raw_store_failure_does_not_drop_unobserved_slots
    (leading trailing : List RuntimeValue) {value : RuntimeValue} (contains : ContainsSource value) :
    (leading ++ value :: trailing).mapM RuntimeValue.toCore? = none :=
  list_fails_at_member _ (by simp) (every_finite_source_occurrence_blocks_projection contains)

theorem even_an_unused_core_capture_prevents_projection
    (source : Syntax.Expr) (owner : Resolved.DeclarationId)
    (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue))
    (leading trailing : List RuntimeValue) (a b : Core.Ty) :
    (RuntimeValue.coreClosure a b .unit
      (leading ++ .sourceClosure source owner names captured :: trailing)).toCore? = none :=
  every_finite_source_occurrence_blocks_projection
    (.coreCapture (value := .sourceClosure source owner names captured) (by simp) (.source _ _ _ _))

theorem projection_does_not_dereference_the_ambient_store
    (source : Syntax.Expr) (owner : Resolved.DeclarationId)
    (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue))
    (type : Core.Ty) :
    (RuntimeValue.cellRef type 0).toCore? = some (.cellRef type 0) ∧
    ([RuntimeValue.sourceClosure source owner names captured] : List RuntimeValue).mapM
      RuntimeValue.toCore? = none :=
  ⟨by simp only [RuntimeValue.toCore?], raw_store_failure_does_not_drop_unobserved_slots [] [] (.source _ _ _ _)⟩

theorem projection_preserves_even_unbound_core_code_and_arbitrary_captures
    (a b : Core.Ty) (captured : List Core.Value) :
    (RuntimeValue.coreClosure a b (.var (captured.length + 99)) (captured.map RuntimeValue.ofCore)).toCore? =
      some (.closure a b (.var (captured.length + 99)) captured) := by
  have roundtrip := RuntimeValue.toCore?_ofCore (.closure a b (.var (captured.length + 99)) captured)
  simpa only [RuntimeValue.ofCore, List.attach_map_val] using roundtrip

end Tests.RuntimeValueBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeValueOwnerProperties
/- Handwritten nested values exercise literal Core code, tags, locations and
duplicate rows. Direct structural calculations precede the representation laws. -/
set_option autoImplicit false
namespace Tests.RuntimeValueOwnerMixed
open Solcore Solcore.Frontend

private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId := ⟨owner,index⟩
private def plainCore (tag : Core.ConstructorId) (word : Core.Word) : Core.Value :=
  .closure .unit .word (.var 99)
    [.constructed tag (.inLeft .word (.pair (.word word) (.cellRef .word 701))),.hostFunction .storageWrite]
private def deep (source : Syntax.Expr) (caller foreign : Resolved.DeclarationId) : RuntimeValue :=
  .sourceClosure source foreign [("deep",localId caller 9),("deep",localId foreign 2)]
    [(localId foreign 2,.unit),(localId foreign 2,.cellRef .word 702)]
private def mixed (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId)
    (tag : Core.ConstructorId) (word : Core.Word) : RuntimeValue :=
  .pair
    (.sourceClosure source saved [("p",localId saved 7),("p",localId saved 1),("x",localId foreign 8)]
      [(localId saved 7,.coreClosure .unit .word (.var 17)
        [deep source caller foreign,.ofCore (plainCore tag word)]),
       (localId saved 7,.bool false),(localId saved 9,.hostFunction .storageRead)])
    (.coreClosure .bool .unit (.var 3)
      [.constructed tag (.inRight .word
        (.sourceClosure source caller [("p",localId saved 9)]
          [(localId caller 0,.pair (.cellRef .word 703) (.word word))]))])

private theorem direct_mapping (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId)
    (tag : Core.ConstructorId) (word : Core.Word) :
    (mixed source caller saved foreign tag word).mapOwners mapping =
      mixed source (mapping caller) (mapping saved) (mapping foreign) tag word := by
  simp only [mixed,deep,plainCore,RuntimeValue.ofCore,List.attach_map_val,
    RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners_sourceClosure,RuntimeValue.mapOwners,
    mapRuntimeCapturedOwners,LocalNameTable.mapIds,ownerLocalIdMap,localId,List.map_cons,List.map_nil]

private theorem direct_projection (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId)
    (tag : Core.ConstructorId) (word : Core.Word) :
    (mixed source caller saved foreign tag word).toCore? = none := by
  simp only [mixed,RuntimeValue.toCore?,bind,Option.bind_none]

private theorem direct_core_projection (tag : Core.ConstructorId) (word : Core.Word) :
    (RuntimeValue.ofCore (plainCore tag word)).toCore? = some (plainCore tag word) := by
  simp [plainCore,RuntimeValue.ofCore,RuntimeValue.toCore?]

/-- Deep closures and duplicate captures retain every field through all seven representation laws. -/
theorem complete_mixed_representation
    (mapping second : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (source : Syntax.Expr)
    (caller saved foreign : Resolved.DeclarationId) (tag : Core.ConstructorId) (word : Core.Word) :
    let value := mixed source caller saved foreign tag word
    let captures := [(localId saved 7,value),(localId saved 7,RuntimeValue.unit)]
    let store := [RuntimeValue.cellRef .word 704,value,RuntimeValue.ofCore (plainCore tag word)]
    value.mapOwners mapping = mixed source (mapping caller) (mapping saved) (mapping foreign) tag word ∧
    store.map (RuntimeValue.mapOwners mapping) = [.cellRef .word 704,
      mixed source (mapping caller) (mapping saved) (mapping foreign) tag word,RuntimeValue.ofCore (plainCore tag word)] ∧
    value.mapOwners id = value ∧
    (value.mapOwners mapping).mapOwners second = value.mapOwners (second ∘ mapping) ∧
    (RuntimeValue.ofCore (plainCore tag word)).mapOwners mapping = RuntimeValue.ofCore (plainCore tag word) ∧
    ((RuntimeValue.ofCore (plainCore tag word)).mapOwners mapping).toCore? = some (plainCore tag word) ∧
    (value.mapOwners mapping).toCore? = none ∧
    (∀ left right : RuntimeValue, left.mapOwners mapping = right.mapOwners mapping ↔ left = right) ∧
    mapRuntimeCapturedOwners id captures = captures ∧
    mapRuntimeCapturedOwners second (mapRuntimeCapturedOwners mapping captures) =
      mapRuntimeCapturedOwners (second ∘ mapping) captures := by
  have exactFields := direct_mapping mapping source caller saved foreign tag word
  have projection := direct_projection source caller saved foreign tag word
  have coreProjection := direct_core_projection tag word
  have exactStore : [RuntimeValue.cellRef .word 704,mixed source caller saved foreign tag word,
      RuntimeValue.ofCore (plainCore tag word)].map (RuntimeValue.mapOwners mapping) =
      [.cellRef .word 704,mixed source (mapping caller) (mapping saved) (mapping foreign) tag word,
        RuntimeValue.ofCore (plainCore tag word)] := by
    simp only [List.map_cons,List.map_nil,exactFields]
    simp only [plainCore,RuntimeValue.ofCore,List.attach_map_val,RuntimeValue.mapOwners_coreClosure,
      RuntimeValue.mapOwners,List.map_cons,List.map_nil]
  refine ⟨exactFields,exactStore,RuntimeValue.mapOwners_id _,RuntimeValue.mapOwners_comp _ mapping second,
    RuntimeValue.mapOwners_ofCore mapping _,?_,?_,?_,mapRuntimeCapturedOwners_id _,mapRuntimeCapturedOwners_comp _ mapping second⟩
  · exact (RuntimeValue.toCore?_mapOwners mapping _).trans coreProjection
  · exact (RuntimeValue.toCore?_mapOwners mapping _).trans projection
  · intro left right
    exact ⟨fun same => RuntimeValue.mapOwners_injective mapping injective same,
      congrArg (RuntimeValue.mapOwners mapping)⟩

/-- Noninjective relabeling can collapse distinct saved owners even though projection stays absent. -/
theorem constant_mapping_loses_owner (source : Syntax.Expr)
    (left right replacement : Resolved.DeclarationId) (distinct : left ≠ right) :
    let a := RuntimeValue.sourceClosure source left [] []
    let b := RuntimeValue.sourceClosure source right [] []
    a ≠ b ∧ a.mapOwners (fun _ => replacement) = b.mapOwners (fun _ => replacement) ∧
    a.toCore? = none ∧ b.toCore? = none := by
  refine ⟨?_,?_,?_,?_⟩
  · intro same
    exact distinct (RuntimeValue.sourceClosure.inj same).2.1
  · simp only [RuntimeValue.mapOwners_sourceClosure,LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_nil]
  · simp only [RuntimeValue.toCore?]
  · simp only [RuntimeValue.toCore?]

private def span : Syntax.SourceSpan := ⟨⟨.main,"owner-representation.sol"⟩,0,1⟩
private def source : Syntax.Expr := ⟨span,.tuple ⟨span,[]⟩⟩
private def caller : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Caller",by decide⟩],by decide⟩⟩,1⟩
private def saved : Resolved.DeclarationId := {caller with declarationIndex:=2}
private def foreign : Resolved.DeclarationId := {caller with declarationIndex:=3}
private def shift (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {owner with declarationIndex:=owner.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  cases left with
  | mk lm li =>
    cases right with
    | mk rm ri =>
      change lm = rm at modules
      change li+5 = ri+5 at indices
      have equal : li = ri := by omega
      cases modules
      cases equal
      rfl

/-- A concrete non-surjective injection preserves this nested, owner-separated fixture. -/
theorem shifted_fixture (tag : Core.ConstructorId) (word : Core.Word) :
    caller ≠ saved ∧ saved ≠ foreign ∧ ¬ Function.Surjective shift ∧
    (mixed source caller saved foreign tag word).mapOwners shift =
      mixed source (shift caller) (shift saved) (shift foreign) tag word ∧
    (mixed source caller saved foreign tag word).mapOwners (fun _ => caller) =
      mixed source caller caller caller tag word := by
  have collision := direct_mapping (fun _ => caller) source caller saved foreign tag word
  have consumed := complete_mixed_representation shift shift shift_injective source caller saved foreign tag word
  refine ⟨by decide,by decide,?_,consumed.1,collision⟩
  intro onto
  obtain ⟨preimage,same⟩ := onto {caller with declarationIndex:=0}
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change preimage.declarationIndex+5 = 0 at impossible
  omega

end Tests.RuntimeValueOwnerMixed
end

section
-- leanmerge: from Solcore.Test.FrontendRuntimeValueProperties
/-! These are representation tests, not value typing or operational semantics.
Every old payload, code body, tag, capture and raw store slot is retained literally;
no runtime inhabitance, validity, world, allocation or host-support premise is used. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeValue
open Solcore Solcore.Frontend

theorem all_atomic_core_constructors_preserve_arbitrary_original_payloads
    (boolean : Bool) (word : Core.Word) (host : Core.HostFunction)
    (elementType : Core.Ty) (location : Core.Location) :
    RuntimeValue.ofCore .unit=.unit ∧
    RuntimeValue.ofCore (.bool boolean)=.bool boolean ∧
    RuntimeValue.ofCore (.word word)=.word word ∧
    RuntimeValue.ofCore (.hostFunction host)=.hostFunction host ∧
    RuntimeValue.ofCore (.cellRef elementType location)=.cellRef elementType location := by
  simp [RuntimeValue.ofCore]

theorem all_composite_core_constructors_preserve_sides_tags_and_payloads
    (left right payload : Core.Value) (otherSide : Core.Ty) (constructor : Core.ConstructorId) :
    RuntimeValue.ofCore (.pair left right)=.pair (RuntimeValue.ofCore left) (RuntimeValue.ofCore right) ∧
    RuntimeValue.ofCore (.inLeft otherSide payload)=.inLeft otherSide (RuntimeValue.ofCore payload) ∧
    RuntimeValue.ofCore (.inRight otherSide payload)=.inRight otherSide (RuntimeValue.ofCore payload) ∧
    RuntimeValue.ofCore (.constructed constructor payload)=.constructed constructor (RuntimeValue.ofCore payload) := by
  simp [RuntimeValue.ofCore]

theorem core_closure_code_types_and_every_ordered_capture_remain_literal
    (parameterType resultType : Core.Ty) (body : Core.Expr) (captured : Core.Environment) :
    RuntimeValue.ofCore (.closure parameterType resultType body captured)=
      .coreClosure parameterType resultType body (captured.map RuntimeValue.ofCore) ∧
    RuntimeValue.toCore? (.coreClosure parameterType resultType body (captured.map RuntimeValue.ofCore))=
      some (.closure parameterType resultType body captured) := by
  have literal : RuntimeValue.ofCore (.closure parameterType resultType body captured)=
      .coreClosure parameterType resultType body (captured.map RuntimeValue.ofCore) := by
    simp only [RuntimeValue.ofCore,List.attach_map_val]
  exact ⟨literal,literal ▸ RuntimeValue.toCore?_ofCore _⟩

theorem roundtrip_and_exact_image_need_no_semantic_premises (old : Core.Value) (value : RuntimeValue) :
    RuntimeValue.toCore? (RuntimeValue.ofCore old)=some old ∧
    (RuntimeValue.toCore? value=some old ↔ value=RuntimeValue.ofCore old) :=
  ⟨RuntimeValue.toCore?_ofCore old,RuntimeValue.toCore?_eq_some_iff⟩

private theorem listRoundtrip (values : List Core.Value) :
    (values.map RuntimeValue.ofCore).mapM RuntimeValue.toCore?=some values := by
  induction values with
  | nil => rfl
  | cons value tail ih =>
      simp only [List.map_cons,List.mapM_cons,RuntimeValue.toCore?_ofCore,ih,bind,Option.bind_some,pure]
private theorem listReflect (values : List RuntimeValue) (cores : List Core.Value)
    (projected : values.mapM RuntimeValue.toCore?=some cores) : values=cores.map RuntimeValue.ofCore := by
  induction values generalizing cores with
  | nil =>
      have same : []=cores := Option.some.inj projected
      subst cores; rfl
  | cons value tail ih =>
      simp only [List.mapM_cons,bind,Option.bind_eq_some_iff] at projected
      obtain ⟨core,valueProjected,rest,tailProjected,same⟩ := projected
      cases Option.some.inj same
      change value::tail=RuntimeValue.ofCore core::rest.map RuntimeValue.ofCore
      rw [RuntimeValue.toCore?_eq_some_iff.mp valueProjected,ih rest tailProjected]

theorem every_original_raw_store_roundtrips_with_order_and_length
    (store : Core.Store) :
    (store.map RuntimeValue.ofCore).mapM RuntimeValue.toCore?=some store ∧
    (store.map RuntimeValue.ofCore).length=store.length :=
  ⟨listRoundtrip store,List.length_map _⟩

theorem whole_ordered_list_projection_has_exactly_the_original_list_image
    (values : List RuntimeValue) (cores : List Core.Value) :
    values.mapM RuntimeValue.toCore?=some cores ↔ values=cores.map RuntimeValue.ofCore := by
  constructor
  · exact listReflect values cores
  · intro same; rw [same]; exact listRoundtrip cores

theorem successful_projection_cannot_drop_reorder_or_replace_actual_slots
    (values : List RuntimeValue) (cores : List Core.Value)
    (projected : values.mapM RuntimeValue.toCore?=some cores) :
    values.length=cores.length ∧ ∀ index : Nat,values[index]?=(cores[index]?).map RuntimeValue.ofCore := by
  rw [listReflect values cores projected]
  exact ⟨List.length_map _,fun index => List.getElem?_map⟩

theorem embedding_distinguishes_original_values_and_ordered_raw_stores
    (left right : Core.Value) (leftStore rightStore : Core.Store) :
    (RuntimeValue.ofCore left=RuntimeValue.ofCore right ↔ left=right) ∧
    (leftStore.map RuntimeValue.ofCore=rightStore.map RuntimeValue.ofCore ↔ leftStore=rightStore) := by
  constructor
  · exact ⟨fun equal => RuntimeValue.ofCore_injective equal,congrArg RuntimeValue.ofCore⟩
  · constructor
    · intro equal
      have projected := congrArg (List.mapM RuntimeValue.toCore?) equal
      simpa only [listRoundtrip,Option.some.injEq] using projected
    · intro equal; rw [equal]

theorem arbitrary_capture_prefix_and_suffix_preserve_the_selected_middle_value
    (a b : Core.Ty) (body : Core.Expr) (leading suffix : Core.Environment) (middle : Core.Value) :
    RuntimeValue.ofCore (.closure a b body (leading++middle::suffix))=
      .coreClosure a b body (leading.map RuntimeValue.ofCore++RuntimeValue.ofCore middle::suffix.map RuntimeValue.ofCore) ∧
    RuntimeValue.toCore? (.coreClosure a b body
      (leading.map RuntimeValue.ofCore++RuntimeValue.ofCore middle::suffix.map RuntimeValue.ofCore))=
      some (.closure a b body (leading++middle::suffix)) := by
  simpa only [List.map_append,List.map_cons] using
    core_closure_code_types_and_every_ordered_capture_remain_literal a b body (leading++middle::suffix)

private def coreTree (a b otherSide : Core.Ty) (body : Core.Expr) (constructor : Core.ConstructorId)
    (value : Core.Value) : Nat → Core.Value
  | 0 => value
  | n+1 => .pair (.closure a b body [coreTree a b otherSide body constructor value n,value])
      (.constructed constructor (.inLeft otherSide (coreTree a b otherSide body constructor value n)))
private def mixedTree (a b otherSide : Core.Ty) (body : Core.Expr) (constructor : Core.ConstructorId)
    (value : Core.Value) : Nat → RuntimeValue
  | 0 => RuntimeValue.ofCore value
  | n+1 => .pair (.coreClosure a b body [mixedTree a b otherSide body constructor value n,RuntimeValue.ofCore value])
      (.constructed constructor (.inLeft otherSide (mixedTree a b otherSide body constructor value n)))
private theorem treeLiteral (a b otherSide : Core.Ty) (body : Core.Expr) (constructor : Core.ConstructorId)
    (value : Core.Value) (n : Nat) :
    RuntimeValue.ofCore (coreTree a b otherSide body constructor value n)=mixedTree a b otherSide body constructor value n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coreTree,mixedTree,RuntimeValue.ofCore,List.attach_map_val,List.map_cons,List.map_nil,ih]

theorem arbitrary_depth_literal_capture_trees_preserve_old_code_and_data
    (a b otherSide : Core.Ty) (body : Core.Expr) (constructor : Core.ConstructorId)
    (value : Core.Value) (depth : Nat) :
    RuntimeValue.ofCore (coreTree a b otherSide body constructor value depth)=mixedTree a b otherSide body constructor value depth ∧
    RuntimeValue.toCore? (mixedTree a b otherSide body constructor value depth)=
      some (coreTree a b otherSide body constructor value depth) :=
  ⟨treeLiteral a b otherSide body constructor value depth,
    (treeLiteral a b otherSide body constructor value depth) ▸ RuntimeValue.toCore?_ofCore _⟩

end Tests.FrontendRuntimeValue
end

section
-- leanmerge: from Solcore.Test.FrontendTypeNameProperties
/-! ADR-0167 consumers: an explicit ordered table interprets exact components.
No spelling or source-range validity is required, and unsupported shapes remain
outside this adapter even when their child types have supplied meanings. -/

set_option autoImplicit false

namespace Tests.FrontendTypeName

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "type-name.sol"⟩, 0, 4⟩
private def qualified (nameSpan componentSpan : Syntax.SourceSpan)
    (head : String) (tail : List String) : Syntax.QualifiedName :=
  ⟨nameSpan, ⟨⟨⟨componentSpan, head⟩, tail.map (fun text => ⟨componentSpan, text⟩)⟩⟩⟩
private def named (head : String) (tail : List String := []) : Syntax.TypeExpr :=
  ⟨span, .named (qualified span span head tail) none⟩

private theorem qualified_key (nameSpan componentSpan : Syntax.SourceSpan)
    (head : String) (tail : List String) :
    qualifiedTypeNameKey (qualified nameSpan componentSpan head tail) = head :: tail := by
  simp [qualifiedTypeNameKey, qualified, Syntax.NonemptyList.toList, List.map_map, Function.comp_def]

theorem any_core_type_can_be_assigned_to_any_nonempty_component_sequence
    (head : String) (tail : List String) (type : Core.Ty) (rest : TypeNameTable)
    (outer nameSpan componentSpan : Syntax.SourceSpan) :
    qualifiedTypeNameKey (qualified nameSpan componentSpan head tail) = head :: tail ∧
    TypeNameDenotes (((head :: tail), type) :: rest)
      ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ type ∧
    interpretTypeName? (((head :: tail), type) :: rest)
      ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ = some type := by
  have meaning : TypeNameDenotes (((head :: tail), type) :: rest)
      ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ type := by
    apply TypeNameDenotes.named
    rw [qualified_key]
    exact .head
  exact ⟨qualified_key nameSpan componentSpan head tail, meaning,
    meaning.complete⟩

private def aliases : TypeNameTable := [(["Word"], .bool), (["Alias"], .bool), (["Word"], .word)]
private theorem wordMeaning : TypeNameDenotes aliases (named "Word") .bool := .named .head
private theorem aliasMeaning : TypeNameDenotes aliases (named "Alias") .bool :=
  .named (.tail (by decide) .head)

theorem caller_assignments_allow_aliases_and_first_duplicate_wins :
    TypeNameDenotes aliases (named "Word") .bool ∧
    TypeNameDenotes aliases (named "Alias") .bool ∧
    interpretTypeName? aliases (named "Word") = some .bool ∧
    interpretTypeName? aliases (named "Alias") = some .bool ∧
    (["Word"], Core.Ty.word) ∈ aliases ∧
    ¬ TypeNameDenotes aliases (named "Word") .word := by
  refine ⟨wordMeaning, aliasMeaning, wordMeaning.complete,
    aliasMeaning.complete, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
  intro wrong
  have accepted := wrong.complete
  have first := wordMeaning.complete
  rw [first] at accepted
  cases accepted

theorem unknown_names_have_no_reserved_fallback (name : Syntax.QualifiedName)
    (outer : Syntax.SourceSpan) :
    interpretTypeName? [] ⟨outer, .named name none⟩ = none ∧
    (¬ ∃ type, TypeNameDenotes [] ⟨outer, .named name none⟩ type) ∧
    interpretTypeName? [(["Bool"], .word)] (named "Word") = none ∧
    TypeNameDenotes [(["Bool"], .word)] (named "Bool") .word := by
  refine ⟨rfl, ?_, by decide, .named .head⟩
  rintro ⟨type, meaning⟩
  cases meaning with | named found => cases found

private def unsupported (child : Syntax.TypeExpr) : List Syntax.TypeExprValue :=
  [.named (qualified span span "Word" []) (some ⟨span, ⟨child, []⟩⟩),
   .mapping span span child child, .proxy span child,
   .function span ⟨span, [child]⟩ (some ⟨span, [child]⟩),
   .comptime span span child, .tuple [child], .error]

theorem every_other_shape_is_outside_the_adapter_even_with_a_meaningful_child
    (table : TypeNameTable) (child : Syntax.TypeExpr) (childType : Core.Ty)
    (childMeaning : TypeNameDenotes table child childType)
    (payload : Syntax.TypeExprValue) (present : payload ∈ unsupported child)
    (outer : Syntax.SourceSpan) :
    interpretTypeName? table child = some childType ∧
    interpretTypeName? table ⟨outer, payload⟩ = none ∧
    ¬ ∃ type, TypeNameDenotes table ⟨outer, payload⟩ type := by
  refine ⟨childMeaning.complete, ?_⟩
  simp only [unsupported, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, by rintro ⟨type, meaning⟩; cases meaning⟩

theorem raw_dots_and_empty_components_are_not_normalized :
    qualifiedTypeNameKey (qualified span span "A.B" []) = ["A.B"] ∧
    qualifiedTypeNameKey (qualified span span "A" ["B"]) = ["A", "B"] ∧
    interpretTypeName? [(["A", "B"], .word)] (named "A.B") = none ∧
    interpretTypeName? [(["A.B"], .bool)] (named "A" ["B"]) = none ∧
    interpretTypeName? [(["A", "", "B"], .unit)] (named "A" ["", "B"]) = some .unit ∧
    interpretTypeName? [(["A", "B"], .word)] (named "A" ["", "B"]) = none ∧
    interpretTypeName? [([], .word)] (named "") = none ∧
    TypeNameDenotes [([""], .bool)] (named "") .bool := by
  exact ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, .named .head⟩

private def nonMatchingSpellings : List String :=
  ["word", "WORD", " Word", "Word ", "Ｗord", "Wоrd", "é"]

theorem case_space_and_unicode_payloads_are_matched_exactly
    (spelling : String) (present : spelling ∈ nonMatchingSpellings) :
    interpretTypeName? [(["Word"], .word), (["é"], .bool)] (named spelling) = none ∧
    ¬ ∃ type, TypeNameDenotes [(["Word"], .word), (["é"], .bool)] (named spelling) type := by
  have allRejected : ∀ candidate ∈ nonMatchingSpellings,
      interpretTypeName? [(["Word"], .word), (["é"], .bool)] (named candidate) = none := by decide
  have rejected := allRejected spelling present
  refine ⟨rejected, ?_⟩
  rintro ⟨type, meaning⟩
  have accepted := meaning.complete
  rw [rejected] at accepted
  cases accepted

theorem arbitrary_range_changes_preserve_success_failure_and_independent_meaning
    (table : TypeNameTable) (head : String) (tail : List String) (type : Core.Ty)
    (outer otherOuter nameSpan otherNameSpan componentSpan otherComponentSpan : Syntax.SourceSpan) :
    interpretTypeName? table ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ =
      interpretTypeName? table ⟨otherOuter, .named (qualified otherNameSpan otherComponentSpan head tail) none⟩ ∧
    (TypeNameDenotes table ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ type ↔
      TypeNameDenotes table ⟨otherOuter, .named (qualified otherNameSpan otherComponentSpan head tail) none⟩ type) := by
  have same : interpretTypeName? table ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ =
      interpretTypeName? table ⟨otherOuter, .named (qualified otherNameSpan otherComponentSpan head tail) none⟩ := by
    exact interpretTypeName?_key_eq table (by rw [qualified_key, qualified_key]) outer otherOuter
  exact ⟨same, by rw [← interpretTypeName?_iff, ← interpretTypeName?_iff, same]⟩

private def reversed : Syntax.SourceSpan := ⟨⟨.external "raw", "not-a-validated-path"⟩, 99, 2⟩
theorem invalid_ranges_do_not_prevent_explicit_interpretation (file : Syntax.SourceFile) :
    (¬ reversed.ValidFor file) ∧
    TypeNameDenotes [(["Word"], .bool)]
      ⟨reversed, .named (qualified reversed reversed "Word" []) none⟩ .bool ∧
    interpretTypeName? [(["Word"], .bool)]
      ⟨reversed, .named (qualified reversed reversed "Word" []) none⟩ = some .bool := by
  have meaning : TypeNameDenotes [(["Word"], .bool)]
      ⟨reversed, .named (qualified reversed reversed "Word" []) none⟩ .bool := .named .head
  exact ⟨by simp [Syntax.SourceSpan.ValidFor, reversed], meaning, meaning.complete⟩

theorem successful_results_recover_unique_independent_meaning_and_table_provenance
    (table : TypeNameTable) (source : Syntax.TypeExpr) (type : Core.Ty)
    (accepted : interpretTypeName? table source = some type) :
    TypeNameDenotes table source type ∧
    (∃ key, (key, type) ∈ table) ∧
    (∀ other, TypeNameDenotes table source other → other = type) ∧
    ¬ interpretTypeName? table source = none := by
  have meaning := interpretTypeName?_iff.mp accepted
  refine ⟨meaning, meaning.mem, ?_, ?_⟩
  · intro other otherMeaning
    exact otherMeaning.type_unique meaning
  · intro rejected
    exact (interpretTypeName?_eq_none_iff.mp rejected) ⟨type, meaning⟩

end Tests.FrontendTypeName
end

section
-- leanmerge: from Solcore.Test.FrontendTypeTableExtensionProperties
/-! Existing meanings retain exact static compilation. One-way extension may
enable unknown annotations; duplicate membership does not license shadowing. -/

set_option autoImplicit false

namespace Tests.FrontendTypeTableExtension

open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TableExtension", by decide⟩], by decide⟩⟩, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "table-extension.sol"⟩, 29, 11⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def body (conditional : Bool) : Syntax.Block :=
  if conditional then ⟨span, [⟨span, .ifThen (ref "c") (returned "x") (some (returned "y"))⟩]⟩ else returned "x"
private def parameters := [parameter "c" "Cond", parameter "x" "Payload", parameter "y" "Payload"]
private def types (payload : Core.Ty) : TypeNameTable := [(["Payload"], payload), (["Cond"], .bool)]
private def entry (result : String) (conditional : Bool) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "choose"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation result]⟩⟩, none⟩, body conditional⟩⟩
private def inputs (id : Resolved.DeclarationId) (payload : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh id "c" .bool).bindFresh id "x" payload).bindFresh id "y" payload
private def core (conditional : Bool) : Core.Expr := if conditional then .ifE (.var 2) (.var 1) (.var 0) else .var 1
private def compiled (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) : CompiledRuntimeFunction :=
  ⟨inputs id payload, core conditional, payload⟩
private theorem payloadMeaning (payload : Core.Ty) :
    TypeNameDenotes (types payload) (annotation "Payload") payload := .named .head
private theorem conditionMeaning (payload : Core.Ty) :
    TypeNameDenotes (types payload) (annotation "Cond") .bool := .named (.tail (by decide) .head)
private theorem declared (id : Resolved.DeclarationId) (payload : Core.Ty) :
    RuntimeParametersDeclare (types payload) id parameters (inputs id payload) :=
  .cons (conditionMeaning payload).structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (payloadMeaning payload).structural (by change "x" ∉ ["c"]; decide)
      (.cons (payloadMeaning payload).structural (by change "y" ∉ ["x", "c"]; decide) .nil))
private theorem header (payload : Core.Ty) (conditional : Bool) :
    RuntimeFunctionHeader (types payload) (entry "Payload" conditional).value.signature payload :=
  ⟨rfl, rfl, rfl, rfl, .single (payloadMeaning payload).structural⟩
private theorem compilation (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) :
    RuntimeFunctionCompiles (types payload) id (entry "Payload" conditional) (compiled id payload conditional) := by
  cases conditional
  · exact runtimeFunction_parameter_compiles (index := 1) (declared id payload)
      rfl (payloadMeaning payload) (header payload false) rfl
  · exact runtimeFunction_conditional_parameters_compiles (conditionIndex := 0) (thenIndex := 1) (elseIndex := 2)
      (declared id payload) rfl rfl rfl (conditionMeaning payload) (payloadMeaning payload) (payloadMeaning payload)
      (header payload true) rfl

theorem annotations_headers_rows_and_both_whole_compilations_retain_the_exact_original_data
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types payload) next) :
    TypeNameDenotes next (annotation "Payload") payload ∧
    RuntimeReturnTypeDenotes next (entry "Payload" conditional).value.signature.returnsClause payload ∧
    RuntimeFunctionHeader next (entry "Payload" conditional).value.signature payload ∧
    RuntimeParametersDeclare next id parameters (inputs id payload) ∧
    RuntimeFunctionCompiles next id (entry "Payload" conditional) (compiled id payload conditional) ∧
    interpretTypeName? next (annotation "Payload") = some payload ∧
    declareRuntimeParameters? next id parameters = some (inputs id payload) ∧
    compileRuntimeFunction? next id (entry "Payload" conditional) = some (compiled id payload conditional) :=
  ⟨(payloadMeaning payload).extend_types extension, (header payload conditional).returnsMeaning.extend_types extension,
    (header payload conditional).extend_types extension, (declared id payload).extend_types extension,
    (compilation id payload conditional).extend_types extension,
    interpretTypeName?_some_of_extends extension (payloadMeaning payload).complete,
    declareRuntimeParameters?_some_of_extends extension (declared id payload).complete,
    compileRuntimeFunction?_some_of_extends extension (compilation id payload conditional).complete⟩

theorem arbitrary_initial_rows_and_the_same_fresh_identity_are_retained
    (id : Resolved.DeclarationId) (payload : Core.Ty) (initial : LocalTypeInputs)
    (unused : "next" ∉ initial.names.map Prod.fst) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types payload) next) :
    RuntimeParametersDeclareFrom (types payload) id initial [parameter "next" "Payload"]
      (initial.bindFresh id "next" payload) ∧
    RuntimeParametersDeclareFrom next id initial [parameter "next" "Payload"]
      (initial.bindFresh id "next" payload) ∧
    (initial.bindFresh id "next" payload).bindings =
      ⟨"next", Resolved.freshLocalId id initial.ids, payload⟩ :: initial.bindings := by
  have original : RuntimeParametersDeclareFrom (types payload) id initial [parameter "next" "Payload"]
      (initial.bindFresh id "next" payload) := .cons (payloadMeaning payload).structural unused .nil
  exact ⟨original, original.extend_types extension, rfl⟩

theorem a_nonempty_nominal_initial_row_needs_no_old_annotation_meaning_or_value
    (payload : Core.Ty) (dataType : Core.DataTypeId) (extras : TypeNameTable) :
    let initial := LocalTypeInputs.empty.bindFresh (owner 1) "retained" (.namedData dataType)
    RuntimeParametersDeclareFrom (types payload ++ extras) (owner 0) initial [parameter "next" "Payload"]
      (initial.bindFresh (owner 0) "next" payload) ∧
    (initial.bindFresh (owner 0) "next" payload).context =
      [(⟨owner 0, 0⟩, payload), (⟨owner 1, 0⟩, .namedData dataType)] := by
  intro initial
  exact ⟨(arbitrary_initial_rows_and_the_same_fresh_identity_are_retained (owner 0) payload initial
    (by change "next" ∉ ["retained"]; decide) _ (TypeNameTable.Extends.append_right _ extras)).2.1, rfl⟩

theorem fresh_prepend_and_arbitrary_right_duplicates_compose_without_overriding_meanings
    (id : Resolved.DeclarationId) (payload : Core.Ty) (dataType : Core.DataTypeId)
    (extras : TypeNameTable) (conditional : Bool) :
    TypeNameTable.Extends (types payload) (types payload) ∧
    TypeNameTable.Extends (types payload) (types payload ++ extras) ∧
    compileRuntimeFunction?
      (((["Fresh"], .namedData dataType) :: types payload) ++
        ((["Payload"], .word) :: (["Cond"], .unit) :: extras)) id (entry "Payload" conditional) =
      some (compiled id payload conditional) := by
  have prepend : TypeNameTable.Extends (types payload) ((["Fresh"], .namedData dataType) :: types payload) :=
    TypeNameTable.Extends.cons_fresh (types payload) ["Fresh"] (.namedData dataType)
    (by change ["Fresh"] ∉ [["Payload"], ["Cond"]]; decide)
  have extension : TypeNameTable.Extends (types payload)
      (((["Fresh"], .namedData dataType) :: types payload) ++ ((["Payload"], .word) :: (["Cond"], .unit) :: extras)) :=
    prepend.trans (TypeNameTable.Extends.append_right _ ((["Payload"], .word) :: (["Cond"], .unit) :: extras))
  exact ⟨TypeNameTable.Extends.refl _, TypeNameTable.Extends.append_right _ _,
    compileRuntimeFunction?_some_of_extends extension (compilation id payload conditional).complete⟩

private def duplicate (payload : Core.Ty) : TypeNameTable := (["Payload"], payload) :: types payload
private theorem duplicates_extend (payload : Core.Ty) :
    TypeNameTable.Extends (types payload) (duplicate payload) ∧ TypeNameTable.Extends (duplicate payload) (types payload) := by
  constructor
  · intro key type found
    cases found with
    | head => exact .head
    | tail different found => exact .tail different (.tail different found)
  · intro key type found
    cases found with
    | head => exact .head
    | tail _ found => exact found

theorem a_nonfresh_same_meaning_prefix_preserves_every_optional_result
    (payload : Core.Ty) (key : List String) (source : Syntax.TypeExpr) (id : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) (declaration : Syntax.FunctionDecl) :
    ["Payload"] ∈ (types payload).map Prod.fst ∧ types payload ≠ duplicate payload ∧
    TypeNameTable.lookup? (types payload) key = TypeNameTable.lookup? (duplicate payload) key ∧
    interpretTypeName? (types payload) source = interpretTypeName? (duplicate payload) source ∧
    declareRuntimeParameters? (types payload) id params = declareRuntimeParameters? (duplicate payload) id params ∧
    compileRuntimeFunction? (types payload) id declaration = compileRuntimeFunction? (duplicate payload) id declaration := by
  obtain ⟨forward, backward⟩ := duplicates_extend payload
  refine ⟨by simp [types], ?_, TypeNameTable.lookup?_eq_of_mutual_extends forward backward key,
    interpretTypeName?_eq_of_mutual_extends forward backward source,
    declareRuntimeParameters?_eq_of_mutual_extends forward backward id params,
    compileRuntimeFunction?_eq_of_mutual_extends forward backward id declaration⟩
  intro same
  have lengths := congrArg List.length same
  change 2 = 3 at lengths
  cases lengths

theorem mutually_extending_nonidentical_tables_retain_unknown_header_rejection
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) :
    compileRuntimeFunction? (types payload) id (entry "Unknown" conditional) = none ∧
    compileRuntimeFunction? (duplicate payload) id (entry "Unknown" conditional) = none := by
  have rejected : compileRuntimeFunction? (types payload) id (entry "Unknown" conditional) = none := by
    simp only [compileRuntimeFunction?, entry, interpretRuntimeFunctionHeader?,
      interpretRuntimeReturnType?, annotation, interpretStructuralType?_named_eq_typeName]
    rfl
  have same := compileRuntimeFunction?_eq_of_mutual_extends
    (duplicates_extend payload).1 (duplicates_extend payload).2 id (entry "Unknown" conditional)
  exact ⟨rejected, same.symm.trans rejected⟩

theorem adding_an_unknown_nominal_meaning_can_turn_rejection_into_exact_compilation
    (id : Resolved.DeclarationId) (dataType : Core.DataTypeId) (conditional : Bool) :
    TypeNameTable.Extends [(["Cond"], .bool)] (types (.namedData dataType)) ∧
    compileRuntimeFunction? [(["Cond"], .bool)] id (entry "Payload" conditional) = none ∧
    compileRuntimeFunction? (types (.namedData dataType)) id (entry "Payload" conditional) =
      some (compiled id (.namedData dataType) conditional) ∧
    ¬ TypeNameTable.Extends (types (.namedData dataType)) [(["Cond"], .bool)] ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData dataType := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Payload"] (.namedData dataType) (by decide),
    ?_, (compilation id (.namedData dataType) conditional).complete, ?_, ?_⟩
  · simp only [compileRuntimeFunction?, entry, interpretRuntimeFunctionHeader?,
      interpretRuntimeReturnType?, annotation, interpretStructuralType?_named_eq_typeName]
    rfl
  · intro backward
    have found := TypeNameTable.lookup?_iff.mpr (backward (.head : TypeNameTable.Lookup (types (.namedData dataType)) ["Payload"] _))
    change (none : Option Core.Ty) = some (.namedData dataType) at found
    cases found
  · rintro ⟨⟨type, value, typed⟩, same⟩
    cases same
    cases typed with
    | constructed found _ =>
        simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem retaining_old_rows_is_not_enough_when_a_prefix_changes_the_first_meaning :
    TypeNameTable.lookup? (types .bool) ["Cond"] = some .bool ∧
    TypeNameTable.lookup? ((["Cond"], .word) :: types .bool) ["Cond"] = some .word ∧
    ¬ TypeNameTable.Extends (types .bool) ((["Cond"], .word) :: types .bool) := by
  refine ⟨rfl, rfl, ?_⟩
  intro extension
  have changed := (extension (.tail (by decide) (.head : TypeNameTable.Lookup [(["Cond"], .bool)] ["Cond"] .bool))).type_unique
    (.head : TypeNameTable.Lookup ((["Cond"], .word) :: types .bool) ["Cond"] .word)
  cases changed

private def qualified : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, "Pkg"⟩, [⟨span, "Thing"⟩]⟩⟩⟩ none⟩
theorem exact_component_keys_do_not_flatten_into_a_single_dotted_spelling
    (payload : Core.Ty) (dataType : Core.DataTypeId) :
    let old : TypeNameTable := [(["Pkg", "Thing"], payload)]
    let next := (["Pkg.Thing"], .namedData dataType) :: old
    TypeNameTable.Extends old next ∧ interpretTypeName? next qualified = some payload ∧
    interpretTypeName? old (annotation "Pkg.Thing") = none ∧
    interpretTypeName? next (annotation "Pkg.Thing") = some (.namedData dataType) := by
  intro old next
  have extension : TypeNameTable.Extends old next :=
    TypeNameTable.Extends.cons_fresh old ["Pkg.Thing"] (.namedData dataType)
      (by change ["Pkg.Thing"] ∉ [["Pkg", "Thing"]]; decide)
  exact ⟨extension, interpretTypeName?_some_of_extends extension rfl, rfl, rfl⟩

theorem common_actual_arguments_preserve_every_run_exact_checkpoint_and_cost
    (id : Resolved.DeclarationId) (payload : Core.Ty) (conditional : Bool) (next : TypeNameTable)
    (extension : TypeNameTable.Extends (types payload) next) (arguments : List TypedRuntimeArgument)
    (fuel cost : Nat) (initialStore finalStore : Core.Store) (type : Core.Ty) (value : Core.Value) (checkpoint : Core.State) :
    runRuntimeFunction? (types payload) id (entry "Payload" conditional) arguments fuel initialStore =
      runRuntimeFunction? next id (entry "Payload" conditional) arguments fuel initialStore ∧
    (RuntimeFunctionEvaluatesWithCost (types payload) id (entry "Payload" conditional) arguments initialStore type value finalStore cost ↔
      RuntimeFunctionEvaluatesWithCost next id (entry "Payload" conditional) arguments initialStore type value finalStore cost) ∧
    (runRuntimeFunction? (types payload) id (entry "Payload" conditional) arguments fuel initialStore = some (type, .outOfFuel checkpoint) ↔
      runRuntimeFunction? next id (entry "Payload" conditional) arguments fuel initialStore = some (type, .outOfFuel checkpoint)) := by
  have first := compilation id payload conditional
  have second := first.extend_types extension
  have same := first.run_eq_of_same_core second rfl rfl arguments fuel initialStore
  exact ⟨same, first.cost_iff_of_same_core second rfl rfl, by rw [same]⟩

end Tests.FrontendTypeTableExtension
end
