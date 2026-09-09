import Solcore.Frontend.ComputationFunctionRuntimeCheckpointProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveLocalComputationTypingProperties
import Solcore.Core.FuelResumptionProperties

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
    (payload : Core.CellPayload arg.type) :
    Core.ContinuationHasType world (pending arg) arg.type (.product .bool (.cell arg.type)) :=
  .cons (.newCellApply payload) (.cons (.pairApply .bool) .nil)
private theorem stopped (arg : TypedRuntimeArgument) (store : Core.Store) :
    Core.runStateful 1 (start arg (pending arg) store) = .outOfFuel (saved arg (pending arg) store) := rfl

theorem literal_arguments_and_a_different_caller_result_type_remain_safe
    (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
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
    (argumentsTyped typed) stored (pendingTyped payload)
  exact ⟨preparation arg,safety.1,safety.2.1,(safety.2.2 (stopped arg store)).1,
    (safety.2.2 (stopped arg store)).2,Core.runStateful_resume (stopped arg store),rfl⟩

theorem actual_caller_allocation_extends_the_original_world_and_keeps_old_references
    (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    {world : Core.StoreTyping} {store : Core.Store}
    (typed : Core.RuntimeValueHasType world arg.value arg.type) (stored : Core.StoreHasTypes world store) :
    ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future (store++[arg.value]) ∧
      world.length < future.length ∧
      ∀ {location : Nat} {type : Core.Ty}, world[location]?=some type → future[location]?=some type := by
  obtain ⟨_,extension,_,further⟩ := (preparation arg).runtime_checkpoint_world_extension
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped typed) stored (pendingTyped payload) (stopped arg store)
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
  refine ⟨preparation (cellArg location),.cons (.loadCellApply .word) .nil,.nil,?_,?_⟩
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
    .cons (.loadCellApply .word) (.cons .unaryApply .nil),?_,rfl⟩
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
  refine ⟨.ret (Core.StoreHasTypes.nil.allocate .unit .unit) .word (.cons (.newCellApply .word) .nil),?_⟩
  intro fuel exhausted
  obtain ⟨future,extension,stored,_⟩ := (preparation (wordArg word)).runtime_checkpoint_world_extension
    RecursiveLocalComputationElaborates.core_hasType (world := [.word]) (argumentsTyped .word)
    (Core.StoreHasTypes.nil.allocate .word .word) (pendingTyped .word) exhausted
  obtain ⟨value,found,_,typed⟩ := stored.lookup (extension.lookup (location := 0) (type := .word) rfl)
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
