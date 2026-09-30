import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties

/-! Independent original bodies separate positional checkpoint safety from
source lookup, actual allocation, payload typing and pending-frame typing. -/
set_option autoImplicit false
namespace Tests.FrontendComputationRuntimeBoundary
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RuntimeBoundary",by decide⟩],by decide⟩⟩,68⟩
private def xid : Resolved.LocalId := ⟨owner,17⟩
private def fid : Resolved.LocalId := ⟨{owner with declarationIndex := 92},700⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"runtime-boundary.sol"⟩,0,26⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def callSource : Syntax.Expr := ⟨span,.call (ref "f") ⟨span,[ref "x"]⟩⟩
private def pairSource : Syntax.Expr := ⟨span,.tuple ⟨span,[callSource,callSource]⟩⟩
private def body : Syntax.Block := ⟨span,[⟨span,.returnStmt (some pairSource)⟩]⟩
private def bare : Syntax.Block := ⟨span,[⟨span,.returnStmt none⟩]⟩
private def inputs : LocalTypeInputs :=
  ⟨[⟨"x",xid,.unit⟩,⟨"f",fid,.function .unit .word⟩],by decide⟩
private def call : Core.Expr := .apply (.var 1) (.var 0)
private def pairCore : Core.Expr := .pair call call
private def reader (location : Nat) : Core.Value :=
  .closure .unit .word (.loadCell (.var 1)) [.cellRef .word location]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def actual : Core.Environment := [.unit,reader 0]
private theorem elaborated : RecursiveComputationReturnTreeElaborates [] owner inputs body pairCore (.product .word .word) := by
  have x : RecursiveLocalComputationElaborates inputs.names inputs.context (ref "x") (.var 0) .unit :=
    .pure (.identifier .head) (.var .head) (.var .head)
  have f : RecursiveLocalComputationElaborates inputs.names inputs.context (ref "f") (.var 1) (.function .unit .word) :=
    .pure (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head))
  exact .expression (.pair (.application f x) (.application f x))
private theorem bareElaborated : RecursiveComputationReturnTreeElaborates [] owner .empty bare .unit .unit := .bare
private theorem readerTyped {world : Core.StoreTyping} {location : Nat}
    (allocated : world[location]?=some .word) : Core.RuntimeValueHasType world (reader location) (.function .unit .word) :=
  .closure (.cons (.cellRef allocated) .nil) (.loadCell (.var rfl))
private theorem actualTyped : Core.RuntimeEnvironmentHasTypes [.word] actual inputs.context.values :=
  .cons .unit (.cons (readerTyped rfl) .nil)
private theorem wordStore (n : Nat) : Core.StoreHasTypes [.word] [w n] :=
  Core.StoreHasTypes.nil.allocate .word .word
private theorem callPath (n : Nat) (k : List Core.Frame) :
    Core.Steps 8 ⟨.eval call actual,k,[w n]⟩ ⟨.ret (w n),k,[w n]⟩ :=
  .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure
    (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))))))
private theorem pairPath (n : Nat) (k : List Core.Frame) :
    Core.Steps 19 ⟨.eval pairCore actual,k,[w n]⟩ ⟨.ret (.pair (w n) (w n)),k,[w n]⟩ :=
  .cons .enterPair ((callPath n _).trans (.cons .enterPairRight ((callPath n _).trans (.cons .applyPair .refl))))

theorem original_bare_body_keeps_a_typed_actual_pending_value
    {world : Core.StoreTyping} {store : Core.Store} {saved : Core.Value} {a : Core.Ty}
    (stored : Core.StoreHasTypes world store) (typed : Core.RuntimeValueHasType world saved a) :
    RecursiveComputationReturnTreeElaborates [] owner .empty bare .unit .unit ∧
    Core.StateHasType ⟨.eval .unit [],[.pairApply saved],store⟩ (.product a .unit) ∧
    (∀ fuel error state, Core.runStateful fuel ⟨.eval .unit [],[.pairApply saved],store⟩ ≠ .fault error state) ∧
    Core.runStateful 1 ⟨.eval .unit [],[.pairApply saved],store⟩ = .outOfFuel ⟨.ret .unit,[.pairApply saved],store⟩ ∧
    Core.StateHasType ⟨.ret .unit,[.pairApply saved],store⟩ (.product a .unit) ∧
    (∀ additional error state, Core.runStateful additional ⟨.ret .unit,[.pairApply saved],store⟩ ≠ .fault error state) ∧
    (∀ additional, Core.runStateful additional ⟨.ret .unit,[.pairApply saved],store⟩ =
      Core.runStateful (1+additional) ⟨.eval .unit [],[.pairApply saved],store⟩) ∧
    Core.runStateful 1 ⟨.ret .unit,[.pairApply saved],store⟩ = .done (.pair saved .unit) store := by
  have safety := bareElaborated.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType
    (.nil : Core.RuntimeEnvironmentHasTypes world [] []) stored (.cons (.pairApply typed) .nil)
  have stopped : Core.runStateful 1 ⟨.eval .unit [],[.pairApply saved],store⟩ = .outOfFuel ⟨.ret .unit,[.pairApply saved],store⟩ := rfl
  exact ⟨bareElaborated,safety.1,safety.2.1,stopped,(safety.2.2 stopped).1,(safety.2.2 stopped).2,
    fun additional => Core.runStateful_resume stopped additional,rfl⟩

private def pending : List Core.Frame := [.pairApply (.bool false)]
private def checkpoint (n : Nat) : Core.State :=
  ⟨.ret (w n),[.pairRight call actual,.pairApply (.bool false)],[w n]⟩
private def relabelled : Resolved.Environment := [(fid,.unit),(xid,reader 0)]
theorem original_recursive_body_checkpoint_needs_no_source_ID_alignment (n : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner inputs body pairCore (.product .word .word) ∧
    relabelled.ids ≠ inputs.context.ids ∧ relabelled.values=actual ∧
    relabelled.lookup? fid=some .unit ∧ actual[1]?=some (reader 0) ∧
    Core.StateHasType ⟨.eval pairCore relabelled.values,pending,[w n]⟩ (.product .bool (.product .word .word)) ∧
    (∀ fuel error state, Core.runStateful fuel ⟨.eval pairCore actual,pending,[w n]⟩ ≠ .fault error state) ∧
    Core.runStateful 9 ⟨.eval pairCore actual,pending,[w n]⟩ = .outOfFuel (checkpoint n) ∧
    Core.StateHasType (checkpoint n) (.product .bool (.product .word .word)) ∧
    (∀ additional error state, Core.runStateful additional (checkpoint n) ≠ .fault error state) ∧
    (∀ additional, Core.runStateful additional (checkpoint n) = Core.runStateful (9+additional) ⟨.eval pairCore actual,pending,[w n]⟩) ∧
    Core.runStateful 11 (checkpoint n) = .done (.pair (.bool false) (.pair (w n) (w n))) [w n] ∧
    (∀ k, Core.Steps 19 ⟨.eval pairCore actual,k,[w n]⟩ ⟨.ret (.pair (w n) (w n)),k,[w n]⟩) := by
  have safety := elaborated.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType
    actualTyped (wordStore n) (.cons (.pairApply Core.RuntimeValueHasType.bool) .nil : Core.ContinuationHasType [.word] pending (.product .word .word) (.product .bool (.product .word .word)))
  have stopped : Core.runStateful 9 ⟨.eval pairCore actual,pending,[w n]⟩ = .outOfFuel (checkpoint n) := rfl
  exact ⟨elaborated,by decide,rfl,rfl,rfl,safety.1,safety.2.1,stopped,(safety.2.2 stopped).1,(safety.2.2 stopped).2,
    fun additional => Core.runStateful_resume stopped additional,rfl,pairPath n⟩

theorem all_genuine_recursive_checkpoints_retain_full_safe_resumption
    (n spent : Nat) {cp : Core.State}
    (stopped : Core.runStateful spent ⟨.eval pairCore actual,pending,[w n]⟩ = .outOfFuel cp) :
    Core.StateHasType cp (.product .bool (.product .word .word)) ∧
    (∀ additional error state, Core.runStateful additional cp ≠ .fault error state) ∧
    ∀ additional, Core.runStateful additional cp = Core.runStateful (spent+additional) ⟨.eval pairCore actual,pending,[w n]⟩ := by
  have safety := elaborated.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType
    actualTyped (wordStore n) (.cons (.pairApply Core.RuntimeValueHasType.bool) .nil : Core.ContinuationHasType [.word] pending (.product .word .word) (.product .bool (.product .word .word)))
  exact ⟨(safety.2.2 stopped).1,(safety.2.2 stopped).2,Core.runStateful_resume stopped⟩

theorem original_bare_endpoint_does_not_validate_untyped_pending_work :
    RecursiveComputationReturnTreeElaborates [] owner .empty bare .unit .unit ∧
    (∀ k, Core.Steps 1 ⟨.eval .unit [],k,[]⟩ ⟨.ret .unit,k,[]⟩) ∧
    (¬ ∃ result, Core.ContinuationHasType [] [.unaryApply .wordNot] .unit result) ∧
    Core.runStateful 1 ⟨.eval .unit [],[.unaryApply .wordNot],[]⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit,[.unaryApply .wordNot],[]⟩ ∧
    Core.runStateful 0 ⟨.ret .unit,[.unaryApply .wordNot],[]⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit,[.unaryApply .wordNot],[]⟩ := by
  refine ⟨bareElaborated,fun _ => .cons .unit .refl,?_,rfl,rfl⟩
  rintro ⟨_,typing⟩; cases typing with | cons frame _ => cases frame

theorem allocated_capture_does_not_type_missing_or_equal_length_corrupt_stores (b : Bool) :
    RecursiveComputationReturnTreeElaborates [] owner inputs body pairCore (.product .word .word) ∧
    Core.RuntimeEnvironmentHasTypes [.word] actual inputs.context.values ∧
    (¬ Core.StoreHasTypes [.word] []) ∧
    Core.runStateful 8 (.initial pairCore actual []) =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply,.pairRight call actual],[]⟩ ∧
    ([Core.Ty.word] : Core.StoreTyping).length = ([Core.Value.bool b] : Core.Store).length ∧
    (¬ Core.StoreHasTypes [.word] [.bool b]) ∧
    Core.runStateful 19 (.initial pairCore actual [.bool b]) = .done (.pair (.bool b) (.bool b)) [.bool b] ∧
    ¬ Core.RuntimeValueHasType [.word] (.pair (.bool b) (.bool b)) (.product .word .word) := by
  refine ⟨elaborated,actualTyped,?_,rfl,rfl,?_,rfl,?_⟩
  · intro typed; have lengths := typed.length_eq; cases lengths
  · intro typed; obtain ⟨v,found,_,vt⟩ := typed.lookup (location := 0) rfl
    have same : v=.bool b := (Option.some.inj found).symm
    subst v; cases vt
  · intro typed; cases typed with | pair left _ => cases left

theorem structural_capture_700_cannot_discharge_any_short_runtime_world :
    Core.ValueHasType (.cellRef .word 700) (.cell .word) ∧
    Core.ValueHasType (reader 700) (.function .unit .word) ∧
    (∀ world : Core.StoreTyping, world.length≤700 →
      ¬ Core.RuntimeValueHasType world (.cellRef .word 700) (.cell .word)) ∧
    Core.runStateful 8 (.initial pairCore [.unit,reader 700] []) =
      .fault (.invalidCellLocation 700) ⟨.ret (.cellRef .word 700),[.loadCellApply,.pairRight call [.unit,reader 700]],[]⟩ := by
  refine ⟨.cellRef,.closure (.cons .cellRef .nil) (.loadCell (.var rfl)),?_,rfl⟩
  intro world short typed
  cases typed with
  | cellRef found => have bound := (List.getElem?_eq_some_iff.mp found).1; omega

theorem separately_typed_same_location_arguments_have_no_common_runtime_world :
    Core.RuntimeValueHasType [.word] (.cellRef .word 0) (.cell .word) ∧
    Core.RuntimeValueHasType [.bool] (.cellRef .bool 0) (.cell .bool) ∧
    (¬ ∃ world, Core.RuntimeEnvironmentHasTypes world [.cellRef .word 0,.cellRef .bool 0] [.cell .word,.cell .bool]) ∧
    ¬ ∃ world, Core.WorldExtends [.word] world ∧ Core.WorldExtends [.bool] world := by
  refine ⟨.cellRef rfl,.cellRef rfl,?_,?_⟩
  · rintro ⟨world,typed⟩
    cases typed with
    | cons wordRef rest => cases rest with
      | cons boolRef _ => cases wordRef with
        | cellRef wordLookup => cases boolRef with
          | cellRef boolLookup => rw [wordLookup] at boolLookup; cases boolLookup
  · rintro ⟨world,wordExt,boolExt⟩
    have wordLookup := wordExt.lookup (location := 0) rfl
    have boolLookup := boolExt.lookup (location := 0) rfl
    rw [wordLookup] at boolLookup; cases boolLookup

end Tests.FrontendComputationRuntimeBoundary
