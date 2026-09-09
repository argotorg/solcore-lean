import Solcore.Frontend.ComputationReturnTreeRuntimeCheckpointProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeWorldProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.WordLessCostStepComposition
import Solcore.Core.FuelResumptionProperties

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
  .inferred (by change "r" ∉ ["x","f"]; decide)
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
  | zero => exact .newCell (.var found) .word
  | succ n ih => exact .letE (.newCell (.var found) .word) (ih (index+1) (.cell .word::context) (by simpa using found))
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
  ∃ saved, Core.WorldExtends world saved ∧ Core.StoreHasTypes saved cp.store ∧
    ∀ {steps next}, Core.Steps steps cp next →
      ∃ later, Core.WorldExtends saved later ∧ Core.StoreHasTypes later next.store
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
    ∃ saved, Core.WorldExtends world saved ∧ Core.StoreHasTypes saved cp.store ∧
      ∀ {additional next}, Core.runStateful additional cp=.outOfFuel next →
        ∃ later, Core.WorldExtends saved later ∧ Core.StoreHasTypes later next.store := by
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
    .closure (.cons (.cellRef found) ct) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))
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
    ∃ saved, Core.WorldExtends world saved ∧ Core.StoreHasTypes saved cp.store ∧
      Core.RuntimeValueHasType saved nested (.function .unit .unit) ∧
      Core.RuntimeValueHasType saved (.cellRef element location) (.cell element) ∧
      ∀ {steps next}, Core.Steps steps cp next → ∃ later,
        Core.WorldExtends saved later ∧ Core.StoreHasTypes later next.store ∧
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
