import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

/-! Independent original preparation with arbitrarily many typed/inferred shadows.
The actual closure, captures, store and caller frames share one runtime world.
Safety needs no callee termination or source-cost premise. Literal allocation
paths below are additional fixture evidence, not consequences of that safety. -/
set_option autoImplicit false
namespace Tests.FrontendComputationFunctionCheckpoint
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private def fnType (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.function s ⟨s,[named s "A"]⟩ (some ⟨s,[named s "B"]⟩)⟩
private def types (a b : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],b),(["A"],.bool)]
private def parameters (s : Syntax.SourceSpan) : List Syntax.FunctionParameter :=
  [⟨s,.typed none ⟨s,"f"⟩ (fnType s)⟩,⟨s,.typed none ⟨s,"x"⟩ (named s "A")⟩]
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def call (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.call (ref s "f") ⟨s,[ref s "x"]⟩⟩
private def statements (s : Syntax.SourceSpan) : Nat → List Syntax.Statement
  | 0 => [⟨s,.returnStmt (some (call s))⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some (named s "A")) (some (ref s "x"))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s "x"))⟩::statements s n
private def entry (s : Syntax.SourceSpan) (n : Nat) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"checkpointShadows"⟩,none,⟨s,parameters s⟩,⟨none,none⟩,
    some ⟨s,⟨s,[named s "B"]⟩⟩,none⟩,⟨s,statements s n⟩⟩⟩
private def scope (o : Resolved.DeclarationId) (a b : Core.Ty) : Nat → LocalTypeInputs
  | 0 => (LocalTypeInputs.empty.bindFresh o "f" (.function a b)).bindFresh o "x" a
  | m+1 => (scope o a b m).bindFresh o "x" a
private def code : Nat → Nat → Core.Expr
  | 0,m => .apply (.var (m+1)) (.var 0)
  | n+1,m => .letE (.var 0) (.letE (.var 0) (code n (m+2)))
private theorem functionMeaning (s : Syntax.SourceSpan) (a b : Core.Ty) : StructuralTypeDenotes (types a b) (fnType s) (.function a b) :=
  .functionReturns (.named .head) (.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head)))
private theorem header (s : Syntax.SourceSpan) (a b : Core.Ty) (n : Nat) : RuntimeFunctionHeader (types a b) (entry s n).value.signature b :=
  ⟨rfl,rfl,rfl,rfl,.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head))⟩
private theorem functionFacts (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    LocalNameTable.Lookup (scope o a b m).names "f" ⟨o,0⟩ ∧
    Resolved.LocalScope.IndexOf (scope o a b m).context.ids ⟨o,0⟩ (m+1) ∧
    Resolved.LocalScope.Lookup (scope o a b m).context ⟨o,0⟩ (.function a b) := by
  induction m with
  | zero =>
      have different := Resolved.freshLocalId_cons_fresh_ne o []
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) .head,.tail different .head,.tail different .head⟩
  | succ m ih =>
      have different : Resolved.freshLocalId o (scope o a b m).ids ≠ ⟨o,0⟩ := by
        intro same
        have member : (⟨o,0⟩ : Resolved.LocalId) ∈ (scope o a b m).names.map Prod.snd := List.mem_map.mpr ⟨("f",⟨o,0⟩),ih.1.mem,rfl⟩
        rw [LocalTypeInputs.names_ids] at member
        exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) ih.1,.tail different ih.2.1,.tail different ih.2.2⟩
private theorem argumentElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    RecursiveLocalComputationElaborates (scope o a b m).names (scope o a b m).context (ref s "x") (.var 0) a := by
  cases m <;> exact .pure (.identifier .head) (.var .head) (.var .head)
private theorem bodyElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n m : Nat) :
    RecursiveComputationReturnTreeElaborates (types a b) o (scope o a b m) ⟨s,statements s n⟩ (code n m) b := by
  induction n generalizing m with
  | zero => exact .expression (.application
      (.pure (.identifier (functionFacts o a b m).1) (.var (functionFacts o a b m).2.1) (.var (functionFacts o a b m).2.2))
      (argumentElab s o a b m))
  | succ n ih =>
      exact .binding (.named .head) (argumentElab s o a b m)
        (.inferred (argumentElab s o a b (m+1)) (ih (m+2)))
private structure Actual where
  argument : TypedRuntimeArgument
  resultType : Core.Ty
  body : Core.Expr
  captured : Core.Environment
  typed : Core.ValueHasType (.closure argument.type resultType body captured) (.function argument.type resultType)
private def Actual.fn (r : Actual) : TypedRuntimeArgument := ⟨.function r.argument.type r.resultType,.closure r.argument.type r.resultType r.body r.captured,r.typed⟩
private def Actual.inputs (r : Actual) (o : Resolved.DeclarationId) :=
  (LocalInputs.empty.bindFresh o "f" r.fn.type r.fn.value r.fn.valueTyped).bindFresh o "x" r.argument.type r.argument.value r.argument.valueTyped
private def prepared (o : Resolved.DeclarationId) (r : Actual) (n : Nat) : PreparedRuntimeFunction := ⟨r.inputs o,code n 0,r.resultType⟩
private theorem binding (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) :
    RuntimeParametersBind (types r.argument.type r.resultType) o (parameters s) [r.fn,r.argument] (r.inputs o) :=
  .cons (functionMeaning s _ _) (by simp) (.cons (.named .head) (by simp [LocalInputs.names,LocalInputs.bindFresh,LocalInputs.empty]) .nil)
private theorem preparation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) :=
  ⟨header s _ _ n,binding s o r,bodyElab s o _ _ n 0⟩

private def start (o : Resolved.DeclarationId) (r : Actual) (n : Nat) (store : Core.Store) (k : List Core.Frame) : Core.State :=
  ⟨.eval (prepared o r n).core (prepared o r n).inputs.environment.values,k,store⟩
private theorem argumentsTyped {world : Core.StoreTyping} (r : Actual)
    (functionTyped : Core.RuntimeValueHasType world r.fn.value r.fn.type)
    (argumentTyped : Core.RuntimeValueHasType world r.argument.value r.argument.type) :
    ∀ arg ∈ [r.fn,r.argument], Core.RuntimeValueHasType world arg.value arg.type := by
  intro arg member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> assumption

theorem original_preparation_retains_both_actual_arguments_and_all_captures
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) ∧
      (prepared o r n).inputs.environment.values=[r.argument.value,.closure r.argument.type r.resultType r.body r.captured] :=
  ⟨preparation s o r n,rfl⟩
theorem arbitrary_shadow_depth_and_typed_callers_never_fault
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (world : Core.StoreTyping) (store : Core.Store) (k : List Core.Frame) (result : Core.Ty)
    (ft : Core.RuntimeValueHasType world r.fn.value r.fn.type)
    (xt : Core.RuntimeValueHasType world r.argument.value r.argument.type)
    (st : Core.StoreHasTypes world store) (kt : Core.ContinuationHasType world k r.resultType result) :
    Core.StateHasType (start o r n store k) result ∧
      ∀ fuel error faultState, Core.runStateful fuel (start o r n store k) ≠ .fault error faultState := by
  have safety := (preparation s o r n).runtime_checkpoint_safety
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st kt
  exact ⟨safety.1,safety.2.1⟩
theorem every_genuine_checkpoint_is_typed_safe_and_exactly_resumable
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (world : Core.StoreTyping) (store : Core.Store) (k : List Core.Frame) (result : Core.Ty)
    (ft : Core.RuntimeValueHasType world r.fn.value r.fn.type)
    (xt : Core.RuntimeValueHasType world r.argument.value r.argument.type)
    (st : Core.StoreHasTypes world store) (kt : Core.ContinuationHasType world k r.resultType result)
    (spent : Nat) (cp : Core.State) (stopped : Core.runStateful spent (start o r n store k)=.outOfFuel cp) :
    Core.StateHasType cp result ∧
      (∀ additional error faultState, Core.runStateful additional cp ≠ .fault error faultState) ∧
      ∀ additional, Core.runStateful additional cp=Core.runStateful (spent+additional) (start o r n store k) := by
  have safety := (preparation s o r n).runtime_checkpoint_safety
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st kt
  exact ⟨(safety.2.2 stopped).1,(safety.2.2 stopped).2,Core.runStateful_resume stopped⟩
theorem one_saved_world_extends_to_every_further_actual_path
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (world : Core.StoreTyping) (store : Core.Store) (k : List Core.Frame) (result : Core.Ty)
    (ft : Core.RuntimeValueHasType world r.fn.value r.fn.type)
    (xt : Core.RuntimeValueHasType world r.argument.value r.argument.type)
    (st : Core.StoreHasTypes world store) (kt : Core.ContinuationHasType world k r.resultType result)
    (spent : Nat) (cp : Core.State) (stopped : Core.runStateful spent (start o r n store k)=.outOfFuel cp) :
    ∃ saved, Core.WorldExtends world saved ∧ Core.RuntimeStoreHasTypes saved cp.store ∧
      ∀ {steps next}, Core.Steps steps cp next →
        ∃ future, Core.WorldExtends saved future ∧ Core.RuntimeStoreHasTypes future next.store ∧
          ∀ {location : Nat} {type : Core.Ty}, world[location]?=some type → future[location]?=some type := by
  obtain ⟨saved,extension,stored,later⟩ := (preparation s o r n).runtime_checkpoint_world_extension
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st kt stopped
  refine ⟨saved,extension,stored,?_⟩
  intro steps next path
  obtain ⟨future,more,typed⟩ := later path
  exact ⟨future,more,typed,fun found => (extension.trans more).lookup found⟩
theorem the_first_initializer_finishes_before_any_actual_callee_effect
    (o : Resolved.DeclarationId) (r : Actual) (n : Nat) (store : Core.Store) (k : List Core.Frame) :
    Core.runStateful 2 (start o r (n+1) store k)=
      .outOfFuel ⟨.ret r.argument.value,.letBody (.letE (.var 0) (code n 2)) [r.argument.value,r.fn.value]::k,store⟩ := rfl

private theorem manual (r : Actual) (n m : Nat) (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) (k : List Core.Frame) :
    Core.Steps (6*n+cost+5) ⟨.eval (code n m) (List.replicate (m+1) r.argument.value++[r.fn.value]),k,initial⟩ ⟨.ret v,k,final⟩ := by
  induction n generalizing m k with
  | zero =>
      have count : 6*0+cost+5=1+1+cost+3 := by omega
      rw [count]
      exact CostStepComposition.apply (parameterType := r.argument.type) (resultType := r.resultType)
        (.cons (.var (by simp [Actual.fn])) .refl) (.cons (.var (by simp)) .refl) actual
  | succ n ih =>
      have count : 6*(n+1)+cost+5=1+(1+(6*n+cost+5)+2)+2 := by omega
      rw [count]
      simpa [code,List.replicate_succ] using CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.letE (.cons (.var rfl) .refl) (ih (m+2) k))

private def delayed (a : Core.Ty) : Nat → Core.Expr
  | 0 => .newCell a (.var 0)
  | m+1 => .letE (.var 0) (delayed a m)
private theorem delayedTyped (a : Core.Ty) (_payload : Core.CellPayload a) (m : Nat) (context : Core.Context) :
    Core.HasType (a::context) (delayed a m) (.cell a) := by
  induction m generalizing context with
  | zero => exact .newCell (.var rfl)
  | succ m ih => exact .letE (.var rfl) (ih (a::context))
private theorem delayedPath (a : Core.Ty) (m : Nat) (v : Core.Value) (captured : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*m+3) ⟨.eval (delayed a m) (v::captured),k,store⟩ ⟨.ret (.cellRef a store.length),k,store++[v]⟩ := by
  induction m generalizing captured k with
  | zero => exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  | succ m ih =>
      have count : 3*(m+1)+3=1+(3*m+3)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (v::captured) k)
private def allocator (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (m : Nat) : Actual :=
  ⟨arg,.cell arg.type,delayed arg.type m,captured,.closure typed (delayedTyped arg.type payload m context)⟩


private def pending (a : Core.Ty) (retained : Core.Value) : List Core.Frame :=
  [.loadCellApply,.newCellApply a,.pairApply retained]
private def saved (a : Core.Ty) (v retained : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret (.cellRef a store.length),pending a retained,store++[v]⟩
private def allocatedAgain (a : Core.Ty) (v retained : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret (.cellRef a (store.length+1)),[.pairApply retained],store++[v,v]⟩
private theorem pendingTyped {world : Core.StoreTyping} {retained : Core.Value} {a b : Core.Ty}
    (_payload : Core.CellPayload a) (typed : Core.RuntimeValueHasType world retained b) :
    Core.ContinuationHasType world (pending a retained) (.cell a) (.product b (.cell a)) :=
  .cons (.loadCellApply) (.cons (.newCellApply) (.cons (.pairApply typed) .nil))
private theorem savedPath (a : Core.Ty) (v retained : Core.Value) (store : Core.Store) :
    Core.Steps 2 (saved a v retained store) (allocatedAgain a v retained store) := by
  have path := Core.Steps.cons (.applyLoadCell (elementType := a) (Core.Store.allocate_fresh_lookup store v))
    (.cons (.applyNewCell (elementType := a) (continuation := [.pairApply retained])) .refl)
  simpa [saved,allocatedAgain,pending,Core.Store.allocate,List.append_assoc] using path
private theorem allocationPath (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context)
    (n m : Nat) (store : Core.Store) (retained : Core.Value) :
    Core.Steps (6*n+3*m+8) (start o (allocator arg payload captured context typed m) n store (pending arg.type retained))
      (saved arg.type arg.value retained store) := by
  simpa [start,prepared,Actual.inputs,LocalInputs.environment,LocalInputs.bindFresh,LocalInputs.empty,
    Resolved.LocalScope.values,saved,allocator,Nat.add_assoc] using manual (allocator arg payload captured context typed m) n 0 store (store++[arg.value])
    (.cellRef arg.type store.length) (3*m+3) (delayedPath arg.type m arg.value captured store []) (pending arg.type retained)

theorem independent_allocation_checkpoint_preserves_the_pending_caller_and_complete_resume
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context)
    (n m : Nat) (store : Core.Store) (retained : Core.Value) :
    let r := allocator arg payload captured context typed m
    RecursiveComputationFunctionPrepares (types arg.type (.cell arg.type)) o (entry s n) [r.fn,arg] (prepared o r n) ∧
      Core.runStateful (6*n+3*m+8) (start o r n store (pending arg.type retained))=.outOfFuel (saved arg.type arg.value retained store) ∧
      Core.runStateful 2 (saved arg.type arg.value retained store)=.outOfFuel (allocatedAgain arg.type arg.value retained store) ∧
      Core.runStateful 3 (saved arg.type arg.value retained store)=
        .done (.pair retained (.cellRef arg.type (store.length+1))) (store++[arg.value,arg.value]) := by
  refine ⟨preparation s o (allocator arg payload captured context typed m) n,?_,?_,?_⟩
  · exact Core.runStateful_outOfFuel_complete (allocationPath o arg payload captured context typed n m store retained)
      (Core.advance_next_iff.mpr (.applyLoadCell (Core.Store.allocate_fresh_lookup store arg.value)))
  · exact Core.runStateful_outOfFuel_complete (savedPath arg.type arg.value retained store)
      (Core.advance_next_iff.mpr .applyPair)
  · exact ((savedPath arg.type arg.value retained store).trans (.cons .applyPair .refl)).runStateful_done_iff.mpr (by decide)

theorem callee_and_caller_allocations_strictly_extend_the_same_saved_world
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (n m : Nat)
    (world : Core.StoreTyping) (store : Core.Store) (retained : Core.Value) (retainedType : Core.Ty)
    (xt : Core.RuntimeValueHasType world arg.value arg.type) (ct : Core.RuntimeEnvironmentHasTypes world captured context)
    (st : Core.StoreHasTypes world store) (rt : Core.RuntimeValueHasType world retained retainedType) :
    Core.StateHasType (saved arg.type arg.value retained store) (.product retainedType (.cell arg.type)) ∧
      (∀ fuel error faultState, Core.runStateful fuel (saved arg.type arg.value retained store) ≠ .fault error faultState) ∧
      ∃ savedWorld future, Core.WorldExtends world savedWorld ∧ Core.WorldExtends savedWorld future ∧
        Core.RuntimeStoreHasTypes savedWorld (store++[arg.value]) ∧ Core.RuntimeStoreHasTypes future (store++[arg.value,arg.value]) ∧
        world.length<savedWorld.length ∧ savedWorld.length<future.length ∧
        ∀ {location : Nat} {type : Core.Ty}, world[location]?=some type → future[location]?=some type := by
  let r := allocator arg payload captured context ct.erase m
  have ft : Core.RuntimeValueHasType world r.fn.value r.fn.type :=
    .closure ct (delayedTyped arg.type payload m context)
  have stopped := (independent_allocation_checkpoint_preserves_the_pending_caller_and_complete_resume
    s o arg payload captured context ct.erase n m store retained).2.1
  have safety := (preparation s o r n).runtime_checkpoint_safety
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st (pendingTyped payload rt)
  obtain ⟨savedWorld,extension,stored,further⟩ := (preparation s o r n).runtime_checkpoint_world_extension
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st (pendingTyped payload rt) stopped
  obtain ⟨future,more,storedAgain⟩ := further (savedPath arg.type arg.value retained store)
  refine ⟨(safety.2.2 stopped).1,(safety.2.2 stopped).2,savedWorld,future,extension,more,stored,storedAgain,?_,?_,
    fun found => (extension.trans more).lookup found⟩
  all_goals
    have firstLength := stored.length_eq
    have secondLength := storedAgain.length_eq
    have initialLength := st.length_eq
    change savedWorld.length=(store++[arg.value]).length at firstLength
    change future.length=(store++[arg.value,arg.value]).length at secondLength
    simp only [List.length_append,List.length_cons,List.length_nil] at firstLength secondLength
    omega

end Tests.FrontendComputationFunctionCheckpoint
