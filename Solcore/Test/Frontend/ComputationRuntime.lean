import Solcore.Frontend.Fragments.Internal.Computation
import Solcore.Core.Fuel
import Solcore.Frontend.Fragments.Internal.RecursiveComputation
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.RuntimeParameters
import Solcore.Frontend.Fragments.Internal.Foundations
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Frontend.Fragments.Internal.SourceValues
import Solcore.Resolved.LocalScope

/-!
# Computation runtime tests

Runtime safety of computations: arguments, scopes, type tables, and source lambdas.
-/

section
-- leanmerge: from Solcore.Test.FrontendComputationArgumentBoundaryProperties
/-! An explicitly artificial nondeterministic child tests generic proof premises.
It is not source-language elaboration, a checker graph or a runtime safety claim. -/
set_option autoImplicit false
namespace Tests.FrontendComputationArgumentBoundaries
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr :=
  ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private def types (a : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],.bool)]
private def parameters (s : Syntax.SourceSpan) : List Syntax.FunctionParameter :=
  [⟨s,.typed none ⟨s,"x"⟩ (named s "A")⟩,⟨s,.typed none ⟨s,"y"⟩ (named s "B")⟩]
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"y"⟩⟩
private def entry (s : Syntax.SourceSpan) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"artificialChoices"⟩,none,⟨s,parameters s⟩,⟨none,none⟩,
    some ⟨s,⟨s,[named s "B"]⟩⟩,none⟩,⟨s,[⟨s,.returnStmt (some (ref s))⟩]⟩⟩⟩
private def Choice (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr)
    (core : Core.Expr) (type : Core.Ty) : Prop := (∃ b,core=.bool b) ∧ type=.bool
private def staticInputs (o : Resolved.DeclarationId) (a : Core.Ty) :=
  (LocalTypeInputs.empty.bindFresh o "x" a).bindFresh o "y" .bool
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool,.bool b,.bool⟩
private def actualInputs (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y : Bool) :=
  (LocalInputs.empty.bindFresh o "x" arg.type arg.value arg.valueTyped).bindFresh o "y" .bool (.bool y) .bool
private def compiled (o : Resolved.DeclarationId) (a : Core.Ty) (selected : Bool) : CompiledRuntimeFunction :=
  ⟨staticInputs o a,.bool selected,.bool⟩
private def prepared (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y selected : Bool) : PreparedRuntimeFunction :=
  ⟨actualInputs o arg y,.bool selected,.bool⟩
private theorem header (s : Syntax.SourceSpan) (a : Core.Ty) :
    RuntimeFunctionHeader (types a) (entry s).value.signature .bool :=
  ⟨rfl,rfl,rfl,rfl,.single (.named (.tail (by change (["A"] : List String)≠["B"]; decide) .head))⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RuntimeParametersDeclare (types a) o (parameters s) (staticInputs o a) :=
  .cons (.named .head) (by simp)
    (.cons (.named (.tail (by change (["A"] : List String)≠["B"]; decide) .head))
      (by simp [LocalTypeInputs.names,LocalTypeInputs.bindFresh,LocalTypeInputs.empty]) .nil)
private theorem bound (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y : Bool) :
    RuntimeParametersBind (types arg.type) o (parameters s) [arg,boolArg y] (actualInputs o arg y) :=
  .cons (.named .head) (by simp)
    (.cons (.named (.tail (by change (["A"] : List String)≠["B"]; decide) .head))
      (by simp [LocalInputs.names,LocalInputs.bindFresh,LocalInputs.empty]) .nil)
private theorem compilation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) (selected : Bool) :
    ComputationFunctionCompiles Choice (types a) o (entry s) (compiled o a selected) :=
  ⟨header s a,declared s o a,.expression ⟨⟨selected,rfl⟩,rfl⟩⟩
private theorem preparation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId)
    (arg : TypedRuntimeArgument) (y selected : Bool) :
    ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] (prepared o arg y selected) :=
  ⟨header s arg.type,bound s o arg y,.expression ⟨⟨selected,rfl⟩,rfl⟩⟩

theorem static_compilation_in_this_artificial_model_requires_no_argument_inhabitant
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) (selected : Bool) :
    ComputationFunctionCompiles Choice (types a) o (entry s) (compiled o a selected) :=
  compilation s o a selected
theorem supplied_values_reconstruct_the_exact_independently_bound_record
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y selected : Bool) :
    ∃ p, ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] p ∧
      p=prepared o arg y selected ∧ p.toCompiled=compiled o arg.type selected ∧
      p.inputs.environment.values=[.bool y,arg.value] := by
  obtain ⟨p,evidence,erased⟩ := (compilation s o arg.type selected).prepare_arguments [arg,boolArg y] rfl
  have same : p=prepared o arg y selected :=
    evidence.unique_of_toCompiled_eq (preparation s o arg y selected) erased
  exact ⟨p,evidence,same,erased,evidence.argument_values⟩
theorem erasure_and_reconstruction_keep_the_same_fixed_compiled_projection
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty)
    (args : List TypedRuntimeArgument) (selected : Bool) :
    (∃ p, ComputationFunctionPrepares Choice (types a) o (entry s) args p ∧
      p.toCompiled=compiled o a selected) ↔ args.map (·.type)=[a,.bool] := by
  constructor
  · intro evidence
    exact (computationFunctionPrepares_toCompiled_iff.mp evidence).2
  · intro matching
    exact computationFunctionPrepares_toCompiled_iff.mpr ⟨compilation s o a selected,matching⟩
theorem same_typed_value_permutation_changes_the_prepared_record_not_its_projection
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (selected : Bool) :
    let left := prepared o (boolArg true) false selected
    let right := prepared o (boolArg false) true selected
    ComputationFunctionPrepares Choice (types .bool) o (entry s) [boolArg true,boolArg false] left ∧
    ComputationFunctionPrepares Choice (types .bool) o (entry s) [boolArg false,boolArg true] right ∧
    left.toCompiled=right.toCompiled ∧ left≠right := by
  refine ⟨preparation s o (boolArg true) false selected,preparation s o (boolArg false) true selected,rfl,?_⟩
  intro same
  have values := congrArg (fun p : PreparedRuntimeFunction => p.inputs.environment.values) same
  change [Core.Value.bool false,.bool true]=[.bool true,.bool false] at values
  cases values
theorem arbitrary_child_elaboration_does_not_make_compilation_or_preparation_unique
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y : Bool) :
    let left := prepared o arg y false
    let right := prepared o arg y true
    ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] left ∧
    ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] right ∧
    ComputationFunctionCompiles Choice (types arg.type) o (entry s) left.toCompiled ∧
    ComputationFunctionCompiles Choice (types arg.type) o (entry s) right.toCompiled ∧
    left.inputs=right.inputs ∧ left.toCompiled≠right.toCompiled ∧
    ∀ store k, Core.Steps 1 ⟨.eval left.core left.inputs.environment.values,k,store⟩ ⟨.ret (.bool false),k,store⟩ ∧
      Core.Steps 1 ⟨.eval right.core right.inputs.environment.values,k,store⟩ ⟨.ret (.bool true),k,store⟩ := by
  have left := preparation s o arg y false
  have right := preparation s o arg y true
  refine ⟨left,right,left.compiles,right.compiles,rfl,?_,?_⟩
  · intro same
    have cores := congrArg CompiledRuntimeFunction.core same
    change Core.Expr.bool false=.bool true at cores
    cases cores
  · intro store k; exact ⟨.cons .bool .refl,.cons .bool .refl⟩
theorem this_nondeterministic_interface_cannot_be_an_exact_optional_checker_graph :
    ¬ ∃ checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty),
      ∀ table context source core type, checkChild table context source=some (core,type) ↔ Choice table context source core type := by
  rintro ⟨checkChild,correct⟩
  let source := ref ⟨⟨.main,"artificial-choice.sol"⟩,0,0⟩
  have left := (correct [] [] source (.bool false) .bool).mpr ⟨⟨false,rfl⟩,rfl⟩
  have right := (correct [] [] source (.bool true) .bool).mpr ⟨⟨true,rfl⟩,rfl⟩
  have impossible := Option.some.inj (left.symm.trans right)
  cases impossible
private def wordArg : TypedRuntimeArgument := ⟨.word,.word (Core.Word.ofNatModulo 14),.word⟩
theorem wrong_arity_and_reversed_distinct_types_have_no_fixed_prepared_projection
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (selected : Bool) :
    (¬ ∃ p, ComputationFunctionPrepares Choice (types .word) o (entry s) [] p ∧
      p.toCompiled=compiled o .word selected) ∧
    (¬ ∃ p, ComputationFunctionPrepares Choice (types .word) o (entry s) [boolArg true,wordArg] p ∧
      p.toCompiled=compiled o .word selected) := by
  constructor
  · intro evidence
    have impossible := (erasure_and_reconstruction_keep_the_same_fixed_compiled_projection s o .word [] selected).mp evidence
    cases impossible
  · intro evidence
    have impossible := (erasure_and_reconstruction_keep_the_same_fixed_compiled_projection s o .word [boolArg true,wordArg] selected).mp evidence
    cases impossible
theorem a_matching_type_list_does_not_validate_a_hand_built_compiled_record
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (y : Bool) :
    let fake : CompiledRuntimeFunction := {(compiled o arg.type false) with returnType := .unit}
    [arg,boolArg y].map (·.type)=fake.inputs.context.values.reverse ∧
    ¬ ∃ p, ComputationFunctionPrepares Choice (types arg.type) o (entry s) [arg,boolArg y] p ∧ p.toCompiled=fake := by
  refine ⟨rfl,?_⟩
  intro evidence
  have bad := (computationFunctionPrepares_toCompiled_iff.mp evidence).1
  have impossible := bad.header.type_unique (header s arg.type)
  change Core.Ty.unit=.bool at impossible
  cases impossible
end Tests.FrontendComputationArgumentBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendComputationRuntimeBoundaryProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendComputationRuntimeSafetyProperties
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
  exact .inferred (child a b)
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
    ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future final ∧
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
      ⟨value, final, Core.steps_from_initial_sound (manual a b body captured x value store final cost path [])⟩
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
    ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future store ∧
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
    ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future (store++[.word word]) ∧
      Core.RuntimeValueHasType future (.cellRef .word store.length) (.cell .word) := by
  have path (k) : Core.Steps 3 ⟨.eval (.newCell .word (.var 0)) [.word word],k,store⟩
      ⟨.ret (.cellRef .word store.length),k,store++[.word word]⟩ :=
    .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  obtain ⟨future,ext,stored,typed,raw,_⟩ := same_world_safety_identifies_the_independent_actual_path
    (Core.RuntimeValueHasType.closure .nil (.newCell (.var rfl))) Core.RuntimeValueHasType.word st path
  refine ⟨⟨[.word],rfl⟩,st.allocate .word .word,.cellRef ?_,raw,future,ext,stored,typed⟩
  simp [←st.length_eq]

end Tests.FrontendComputationRuntimeSafety
end

section
-- leanmerge: from Solcore.Test.FrontendComputationScopeBoundaryProperties
/-! Source-only protection is independent of branch execution or child checking.
Bare if scopes differ from explicit blocks and match arms in the pinned resolver. -/

set_option autoImplicit false
namespace Tests.FrontendComputationScopeBoundary
open Solcore Solcore.Frontend

theorem explicit_blocks_protect_every_outer_name
    (names : List String) (outerSpan innerSpan : Syntax.SourceSpan) (statements : List Syntax.Statement) :
    ComputationNamesProtected names ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ ∧
    computationBlockPreservesNames names ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ = true := by
  have protection : ComputationNamesProtected names ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ := by
    intro name exposed
    cases exposed with | tail impossible => cases impossible
  exact ⟨protection, computationBlockPreservesNames_iff.mpr protection⟩

theorem match_arms_protect_every_outer_name
    (names : List String) (outerSpan matchSpan : Syntax.SourceSpan)
    (scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr) (arms : Syntax.MatchArms) :
    ComputationNamesProtected names ⟨outerSpan, [⟨matchSpan, .matchWith scrutinees arms⟩]⟩ ∧
    computationBlockPreservesNames names ⟨outerSpan, [⟨matchSpan, .matchWith scrutinees arms⟩]⟩ = true := by
  have protection : ComputationNamesProtected names ⟨outerSpan, [⟨matchSpan, .matchWith scrutinees arms⟩]⟩ := by
    intro name exposed
    cases exposed with | tail impossible => cases impossible
  exact ⟨protection, computationBlockPreservesNames_iff.mpr protection⟩

theorem exposed_then_shadow_rejects_independently_of_child_checking
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (blockSpan ifSpan : Syntax.SourceSpan) (condition : Syntax.Expr) (yes no : Syntax.Block)
    (name : String) (present : name ∈ inputs.names.map Prod.fst)
    (exposed : ExposesComputationLetName name yes) :
    elaborateComputationReturnTree? checkChild types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition yes (some no)⟩]⟩ = none ∧
    ¬ ∃ core type, ComputationReturnTreeElaborates ChildElab types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition yes (some no)⟩]⟩ core type := by
  have rejected := computationBlockPreservesNames_eq_false_iff.mpr ⟨name, present, exposed⟩
  constructor
  · rw [elaborateComputationReturnTree?]
    cases checkChild inputs.names inputs.context condition with
    | none => rfl
    | some pair => simp only [bind, Option.bind_some, rejected, Bool.false_eq_true, and_false, ↓reduceIte]
  · rintro ⟨core, type, elaboration⟩
    cases elaboration with
    | conditional child protection thenElab elseElab => exact protection name exposed present

theorem a_nested_unscoped_else_shadow_remains_exposed
    (names : List String) (name : Syntax.Identifier) (present : name.value ∈ names)
    (outerSpan ifSpan letSpan bodySpan : Syntax.SourceSpan) (condition : Syntax.Expr)
    (yes : Syntax.Block) (annotation : Option Syntax.TypeExpr) (initializer : Option Syntax.Expr)
    (rest : List Syntax.Statement) :
    ExposesComputationLetName name.value
      ⟨outerSpan, [⟨ifSpan, .ifThen condition yes
        (some ⟨bodySpan, ⟨letSpan, .letDecl name annotation initializer⟩ :: rest⟩)⟩]⟩ ∧
    computationBlockPreservesNames names
      ⟨outerSpan, [⟨ifSpan, .ifThen condition yes
        (some ⟨bodySpan, ⟨letSpan, .letDecl name annotation initializer⟩ :: rest⟩)⟩]⟩ = false := by
  have exposed : ExposesComputationLetName name.value
      ⟨outerSpan, [⟨ifSpan, .ifThen condition yes
        (some ⟨bodySpan, ⟨letSpan, .letDecl name annotation initializer⟩ :: rest⟩)⟩]⟩ :=
    .elseBranch (.binding rfl)
  exact ⟨exposed, computationBlockPreservesNames_eq_false_iff.mpr ⟨name.value, present, exposed⟩⟩

theorem statement_tails_do_not_hide_exposed_shadow
    (names : List String) (name : String) (present : name ∈ names)
    (span : Syntax.SourceSpan) (statement : Syntax.Statement) (rest : List Syntax.Statement)
    (exposed : ExposesComputationLetName name ⟨span, rest⟩) :
    computationBlockPreservesNames names ⟨span, statement :: rest⟩ = false :=
  computationBlockPreservesNames_eq_false_iff.mpr ⟨name, present, .tail exposed⟩

end Tests.FrontendComputationScopeBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendComputationTypeTableProperties
/-! Original symbolic annotations, shadowed names, conditional arms and match
rows are constructed independently of checking. These spans are arbitrary fields,
not a parser claim. The explicit variable/literal fixture alone preserves stores. -/
set_option autoImplicit false
namespace Tests.FrontendComputationTypeTable
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s,.named ⟨s,⟨⟨⟨s,"Payload"⟩,[]⟩⟩⟩ none⟩
private def types (a : Core.Ty) : TypeNameTable := [(["Payload"],a),(["Payload"],.bool)]
private def annotation (s : Syntax.SourceSpan) : Nat → Syntax.TypeExpr
  | 0 => ⟨s,.tuple [named s,⟨s,.tuple []⟩,named s]⟩
  | d+1 => ⟨s,.function s ⟨s,[named s]⟩ (some ⟨s,[annotation s d]⟩)⟩
private def annotatedType (a : Core.Ty) : Nat → Core.Ty
  | 0 => .product a (.product .unit a)
  | d+1 => .function a (annotatedType a d)
private theorem meaning (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) :
    StructuralTypeDenotes (types a) (annotation s d) (annotatedType a d) := by
  induction d with
  | zero => exact .many (.named .head) (.pair .unit (.named .head))
  | succ d ih => exact .functionReturns (.named .head) (.single ih)
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def zero := Core.Word.ofNatModulo 0
private def literal (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.literal ⟨s,.decimal "0"⟩⟩
private theorem denotes (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "0"⟩ zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)
private def condition (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.binary (literal s) ⟨s,.equal⟩ (literal s)⟩
private def guardCore : Core.Expr := .binary .wordEq (.word zero) (.word zero)
private theorem guardElab (s : Syntax.SourceSpan) (i : LocalTypeInputs) :
    RecursiveLocalComputationElaborates i.names i.context (condition s) guardCore .bool :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))) (.binary .word .word) (.binary .word .word)
private def returned (s : Syntax.SourceSpan) (name : String) : Syntax.Block := ⟨s,[⟨s,.returnStmt (some (ref s name))⟩]⟩
private def arm (s : Syntax.SourceSpan) (name : String) : Syntax.MatchCase :=
  ⟨s,⟨⟨s,.group ⟨s,.wildcard s⟩⟩,returned s name⟩⟩
private def matched (s : Syntax.SourceSpan) (name : String) : Syntax.Block :=
  ⟨s,[⟨s,.matchWith ⟨s,⟨literal s,[]⟩⟩ ⟨s,⟨[arm s name],some (returned s name)⟩⟩⟩]⟩
private def statements (s : Syntax.SourceSpan) (d : Nat) : List String → String → List Syntax.Statement
  | [],previous => [⟨s,.ifThen (condition s) (matched s previous) (some (returned s previous))⟩]
  | name::rest,previous => ⟨s,.letDecl ⟨s,name⟩ (some (annotation s d)) (some (ref s previous))⟩ :: statements s d rest name
private def core : Nat → Core.Expr
  | 0 => .ifE guardCore (.letE (.word zero) (.var 1)) (.var 0)
  | n+1 => .letE (.var 0) (core n)
private theorem matchElab (s : Syntax.SourceSpan) (table : TypeNameTable) (o : Resolved.DeclarationId)
    (i : LocalTypeInputs) (name : String) (t : Core.Ty)
    (leaf : RecursiveLocalComputationElaborates i.names i.context (ref s name) (.var 0) t) :
    RecursiveComputationReturnTreeElaborates table o i (matched s name) (.letE (.word zero) (.var 1)) t := by
  refine .wordMatch (entries := [(arm s name,none,.var 0)]) (defaultEntry := some (returned s name,.var 0))
    (.pure (.wordLiteral (denotes s)) .word .word) rfl ?_ (.inl rfl) ?_ rfl ?_ ?_
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .group (.wildcard rfl)
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .expression leaf
  · intro entry member; simp only [Option.toList_some,List.mem_singleton] at member; subst entry; exact .expression leaf
  · simp [Core.Expr.weakenAt]
private theorem elaborated (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId)
    (names : List String) (previous : String) (i : LocalTypeInputs)
    (leaf : RecursiveLocalComputationElaborates i.names i.context (ref s previous) (.var 0) (annotatedType a d)) :
    RecursiveComputationReturnTreeElaborates (types a) o i
      ⟨s,statements s d names previous⟩ (core names.length) (annotatedType a d) := by
  induction names generalizing previous i with
  | nil =>
      exact .conditional (guardElab s i)
        (computationBlockPreservesNames_iff.mp (by simp only [matched,computationBlockPreservesNames]))
        (matchElab s (types a) o i previous _ leaf) (.expression leaf)
  | cons name rest ih =>
      exact .binding (meaning s a d) leaf
        (ih name (i.bindFresh o name (annotatedType a d)) (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem guardCost (s : Syntax.SourceSpan) (table : LocalNameTable) (e : Resolved.Environment) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost table e store (condition s) (.bool true) store 5 :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s)))
private theorem raw (s : Syntax.SourceSpan) (d : Nat) (o : Resolved.DeclarationId)
    (names : List String) (previous : String) (table : LocalNameTable) (e : Resolved.Environment)
    (value : Core.Value) (store : Core.Store)
    (leaf : RecursiveLocalComputationEvaluatesWithCost table e store (ref s previous) value store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost o table e store ⟨s,statements s d names previous⟩ value store (3*names.length+11) := by
  induction names generalizing previous table e with
  | nil =>
      exact .ifTrue (conditionCost := 5) (branchCost := 4) (guardCost s table e store)
        (ComputationReturnTreeEvaluatesWithCost.wordMatch (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
          (scrutineeCost := 1) (branchCost := 1) (tests := 0)
          (.pure (.wordLiteral (denotes s))) (.wildcard (.group (.wildcard rfl))) (.expression leaf))
  | cons name rest ih =>
      have count : 3*(name::rest).length+11=1+(3*rest.length+11)+2 := by simp only [List.length_cons]; omega
      rw [count]
      exact .binding leaf (ih name ((name,Resolved.freshLocalId o (table.map Prod.snd))::table)
        ((Resolved.freshLocalId o (table.map Prod.snd),value)::e) (.pure (.identifier .head .head)))
private theorem manual (n : Nat) (value : Core.Value) (retained : Core.Environment)
    (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+11) ⟨.eval (core n) (value::retained),k,store⟩ ⟨.ret value,k,store⟩ := by
  induction n generalizing retained k with
  | zero =>
      exact CostStepComposition.ifTrue
        (CostStepComposition.binary (.cons .word .refl) (.cons .word .refl) rfl)
        (CostStepComposition.letE (.cons .word .refl) (.cons (.var rfl) .refl))
  | succ n ih =>
      have count : 3*(n+1)+11=1+(3*n+11)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (value::retained) k)
private def starting (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a : Core.Ty) (d : Nat) :=
  i.bindFresh o "x" (annotatedType a d)
private theorem original (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId)
    (i : LocalTypeInputs) (names : List String) :
    RecursiveComputationReturnTreeElaborates (types a) o (starting o i a d)
      ⟨s,statements s d names "x"⟩ (core names.length) (annotatedType a d) :=
  elaborated s a d o names "x" (starting o i a d) (.pure (.identifier .head) (.var .head) (.var .head))

theorem nested_original_annotations_and_all_branches_are_independent
    (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (names : List String) :
    StructuralTypeDenotes (types a) (annotation s d) (annotatedType a d) ∧
    RecursiveComputationReturnTreeElaborates (types a) o (starting o i a d)
      ⟨s,statements s d names "x"⟩ (core names.length) (annotatedType a d) :=
  ⟨meaning s a d,original s a d o i names⟩
theorem independent_typing_and_exact_core_survive_extension
    (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (names : List String)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types a) next) :
    RecursiveComputationReturnTreeHasType next o (starting o i a d) ⟨s,statements s d names "x"⟩ (annotatedType a d) ∧
    RecursiveComputationReturnTreeElaborates next o (starting o i a d)
      ⟨s,statements s d names "x"⟩ (core names.length) (annotatedType a d) := by
  have el := original s a d o i names
  have ht := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,el⟩
  exact ⟨ht.extend_types extension,el.extend_types extension⟩
theorem successful_append_keeps_the_whole_original_body
    (s : Syntax.SourceSpan) (a : Core.Ty) (d : Nat) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (names : List String) (extras : TypeNameTable) :
    elaborateRecursiveComputationReturnTree? (types a++extras) o (starting o i a d)
      ⟨s,statements s d names "x"⟩=some (core names.length,annotatedType a d) :=
  elaborateComputationReturnTree?_some_of_extends (TypeNameTable.Extends.append_right _ _)
    ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (original s a d o i names))
theorem fresh_prepend_keeps_the_whole_original_body
    (s : Syntax.SourceSpan) (a extra : Core.Ty) (d : Nat) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (names : List String) (key : List String) (fresh : key≠["Payload"]) :
    elaborateRecursiveComputationReturnTree? ((key,extra)::types a) o (starting o i a d)
      ⟨s,statements s d names "x"⟩=some (core names.length,annotatedType a d) :=
  elaborateComputationReturnTree?_some_of_extends
    (TypeNameTable.Extends.cons_fresh _ _ _ (by simpa [types] using fresh))
    ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (original s a d o i names))
private theorem hiddenMutual (a hidden : Core.Ty) :
    TypeNameTable.Extends (types a) [(["Payload"],a),(["Payload"],hidden)] ∧
    TypeNameTable.Extends [(["Payload"],a),(["Payload"],hidden)] (types a) := by
  constructor <;> intro key type found <;> cases found with
  | head => exact .head
  | tail different found => cases found with
    | head => exact False.elim (different rfl)
    | tail _ found => cases found
theorem hidden_conflicting_rows_preserve_every_optional_body_result
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (a hidden : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (source : Syntax.Block) :
    elaborateComputationReturnTree? checkChild (types a) o i source=
      elaborateComputationReturnTree? checkChild [(["Payload"],a),(["Payload"],hidden)] o i source :=
  elaborateComputationReturnTree?_eq_of_mutual_extends (hiddenMutual a hidden).1 (hiddenMutual a hidden).2 o i source
theorem actual_raw_cost_and_manual_path_need_no_type_table
    (s : Syntax.SourceSpan) (d : Nat) (o : Resolved.DeclarationId) (names : List String)
    (previous : String) (table : LocalNameTable) (e : Resolved.Environment) (value : Core.Value) (retained : Core.Environment)
    (store : Core.Store) (k : List Core.Frame)
    (leaf : RecursiveLocalComputationEvaluatesWithCost table e store (ref s previous) value store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost o table e store ⟨s,statements s d names previous⟩ value store (3*names.length+11) ∧
    Core.Steps (3*names.length+11) ⟨.eval (core names.length) (value::retained),k,store⟩ ⟨.ret value,k,store⟩ :=
  ⟨raw s d o names previous table e value store leaf,manual names.length value retained store k⟩
theorem exact_fuel_and_all_genuine_resumptions_keep_literal_values
    (n fuel extra : Nat) (value : Core.Value) (retained : Core.Environment) (store : Core.Store) :
    (Core.runStateful fuel (.initial (core n) (value::retained) store)=.done value store ↔ 3*n+11≤fuel) ∧
    ∀ cp, Core.runStateful fuel (.initial (core n) (value::retained) store)=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core n) (value::retained) store) :=
  ⟨(manual n value retained store []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
end Tests.FrontendComputationTypeTable
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationArgumentEffects
/-! Original value-free compilation is built before actual arguments. Independent
literal bindings identify the reconstructed proof witness without extracting Prop
data into IO. Same-typed closure permutations retain types, not values or effects. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationArgumentEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationArgumentEffects",by decide⟩],by decide⟩⟩,140⟩
private def types : TypeNameTable := [(["Word"],.word),(["Word"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word
  (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1)))) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def checkedReader (l : Nat) : Core.Value := .closure .word .word (.binary .wordAdd (.loadCell (.var 1)) (.var 0)) [.cellRef .word l]
private def second : Core.Expr := .letE (.apply (.var 3) (.var 0)) (.var 0)
private def first : Core.Expr := .letE (.apply (.var 2) (.var 1)) second
private def core : Core.Expr := .letE (.apply (.var 2) (.var 0)) first
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:function(Word) returns(Word),g:function(Word) returns(Word),x:Word) returns(Word){f(x);let x:Word=g(x);let x=g(x);return x;}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-argument-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple [a]⟩ => let x ← meaning a; return ⟨x.1,⟨by rw [shape]; exact .single x.2.down⟩⟩
  | ⟨_,.function _ ⟨_,[a]⟩ (some ⟨span,results⟩)⟩ => let x ← meaning a; let y ← meaning ⟨span,.tuple results⟩; return ⟨.function x.1 y.1,⟨by rw [shape]; exact .functionReturns x.2.down y.2.down⟩⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf e
private def declare (i : LocalTypeInputs) (ps : List Syntax.FunctionParameter) : IO (Σ o, PLift (RuntimeParametersDeclareFrom types owner i ps o)) := do
  match shape : ps with
  | [] => return ⟨i,⟨by rw [shape]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if unused : name.value ∉ i.names.map Prod.fst then
        let r ← declare (i.bindFresh owner name.value m.1) rest
        return ⟨r.1,⟨by rw [shape]; exact .cons m.2.down unused r.2.down⟩⟩
      else throw (IO.userError "duplicate parameter")
  | _ => throw (IO.userError "source parameter")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.core (r.core.weakenAt 0),r.type,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.head?=some ⟨owner,i.bindings.length⟩ ∧ i.names.lookup? "x"=some ⟨owner,if i.bindings.length=3 then 2 else 3⟩)) "fresh3/4 retains original x2/3; discard creates no source ID"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private structure Compilation (source : Syntax.FunctionDecl) where
  inputs : LocalTypeInputs
  evidence : RecursiveComputationFunctionCompiles types owner source ⟨inputs,core,.word⟩
private def compile (source : Syntax.FunctionDecl) : IO (Compilation source) := do
  let ps ← declare .empty source.value.signature.parameters.elements; let b ← body ps.1 source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core ∧ b.type=.word then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          return ⟨ps.1,⟨h,ps.2.down,by simpa only [same.2.1,same.2.2] using b.evidence⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core and original return annotation")
  | _ => throw (IO.userError "outer return")
private def bind (i : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Σ o, PLift (RuntimeParametersBindFrom types owner i ps args o)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨i,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨_,.typed none name annotation⟩::rest,arg::tail =>
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ i.names.map Prod.fst then
          let r ← bind (i.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨r.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused r.2.down⟩⟩
        else throw (IO.userError "duplicate actual binding")
      else throw (IO.userError "ordered actual type")
  | _,_ => throw (IO.userError "actual arity")
private structure Preparation (source : Syntax.FunctionDecl) (c : Compilation source) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RecursiveComputationFunctionPrepares types owner source args ⟨inputs,core,.word⟩
  projection : (PreparedRuntimeFunction.mk inputs core .word).toCompiled=⟨c.inputs,core,.word⟩
private def prepare (source : Syntax.FunctionDecl) (c : Compilation source) (args : List TypedRuntimeArgument) : IO (Preparation source c args) := do
  let rows ← bind .empty source.value.signature.parameters.elements args
  if matching : args.map (·.type)=c.inputs.context.values.reverse then
    have realized : ∃ candidate, RecursiveComputationFunctionPrepares types owner source args candidate ∧
        candidate.toCompiled=⟨c.inputs,core,.word⟩ ∧ candidate=⟨rows.1,core,.word⟩ := by
      obtain ⟨candidate,h,erased⟩ := c.evidence.prepare_arguments args matching
      have sameInputs := RuntimeParametersBindFrom.result_unique h.parameters rows.2.down
      have sameCore := congrArg CompiledRuntimeFunction.core erased
      have sameType := congrArg CompiledRuntimeFunction.returnType erased
      refine ⟨candidate,h,erased,?_⟩
      cases candidate; cases sameInputs; cases sameCore; cases sameType; rfl
    have proof : RecursiveComputationFunctionPrepares types owner source args ⟨rows.1,core,.word⟩ ∧
        (PreparedRuntimeFunction.mk rows.1 core .word).toCompiled=⟨c.inputs,core,.word⟩ := by
      obtain ⟨candidate,h,e,same⟩ := realized; simpa only [same] using And.intro h e
    have _ := proof.1.compiles
    have _ := (computationFunctionPrepares_toCompiled_iff.mpr ⟨c.evidence,matching⟩)
    have _ := computationFunctionPrepares_toCompiled_iff.mp ⟨_,proof.1,proof.2⟩
    have _ := proof.1.argument_values
    have unique : ∀ candidate, RecursiveComputationFunctionPrepares types owner source args candidate →
        candidate.toCompiled=⟨c.inputs,core,.word⟩ → candidate=⟨rows.1,core,.word⟩ := by
      intro candidate h erased; exact h.unique_of_toCompiled_eq proof.1 (erased.trans proof.2.symm)
    check (decide (rows.1.environment.values=args.reverse.map (·.value) ∧ rows.1.names=[("x",⟨owner,2⟩),("g",⟨owner,1⟩),("f",⟨owner,0⟩)])) "literal original actual rows, values and captures reversed once"
    return ⟨rows.1,proof.1,proof.2⟩
  else throw (IO.userError "independent compiled ordered type guard")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word w => return ⟨.word w,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual missing write")
      | _,_ => throw (IO.userError "manual write reference")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩ | none => throw (IO.userError "manual binary payload")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private def arguments (f g : Core.Value) : IO (List TypedRuntimeArgument) :=
  [f,g,w 14].mapM fun v => do
    match built : buildRuntimeArgument? v with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=v ∧ a.type=v.type)) "literal supplied values and captures"; return a
    | none => throw (IO.userError "structural actual argument")
private def view (p : PreparedRuntimeFunction) := (p.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),p.core,p.returnType)
private def verify (source : Syntax.FunctionDecl) (c : Compilation source) (f g : Core.Value)
    (s middle next final : Core.Store) (discarded firstValue value : Core.Value) (gCost : Nat) : IO (Σ p : PreparedRuntimeFunction, PLift (p.toCompiled=⟨c.inputs,core,.word⟩)) := do
  let args ← arguments f g; let manual ← path 80 core [w 14,g,f] s; let p ← prepare source c args
  let i := p.inputs; let env := i.environment.values; let cost := 22+2*gCost; let raw ← rawBody i.names i.environment s source.value.body
  if fixed : env=[w 14,g,f] ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost ∧ raw.value=value ∧ raw.final=final ∧ raw.cost=cost then
    have ⟨ev,mv,ms,mc,rv,rs,rc⟩ := fixed
    have literal (k) : Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩ := by rw [ev]; simpa only [mv,ms,mc] using manual.evidence k
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body value final cost := by simpa only [rv,rs,rc] using raw.evidence
    have sourcePath (k) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using counted) p.evidence.body (by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds) k
    have _ := (sourcePath []).final_unique (literal [])
    check (decide ((prepareRecursiveComputationFunction? types owner source args).map view=some (view ⟨i,core,.word⟩))) "complete literal prepared record identified by independent reconstruction"
    for fuel in List.range (cost+2) do
      have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "complete prepared runner and declared tag"
      match genuine : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact cost and actual effects"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel genuine
          for more in [0,1,cost-fuel,cost+2] do
            have _ := Core.runStateful_resume genuine more
            check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core env s))) "all genuine full resumptions"
      | .fault _ _ => throw (IO.userError "successful example faulted")
    let hidden := discarded::env; let bound := firstValue::hidden
    let .closure _ _ gBody captured := g | throw (IO.userError "actual closure")
    let cps : List (Nat × Core.State) := [(17,⟨.eval first hidden,[],middle⟩),(23,⟨.eval gBody (w 14::captured),[.letBody second hidden],middle⟩),
      (18+gCost,⟨.ret firstValue,[.letBody second hidden],next⟩),(19+gCost,⟨.eval second bound,[],next⟩),(cost-2,⟨.ret value,[.letBody (.var 0) bound],final⟩)]++
      (if f=allocator then [(10,⟨.ret (.cellRef .word 2),[.letBody (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))) [w 14,.bool false],.letBody first env],s++[w 14]⟩)] else [])
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env s)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        check (decide (runRecursiveComputationFunction? types owner source args spent s=some (.word,.outOfFuel cp) ∧ Core.runStateful (cost-spent) cp=.done value final)) "genuine hidden discard slot, saved actual capture and latest store"
      else throw (IO.userError "literal checkpoint")
    have _ := literal [.pairApply (.cellRef .word 700)]; have _ := sourcePath [.pairApply (.cellRef .word 700)]
    check (decide (Core.runStateful (cost+1) ⟨.eval core env,[.pairApply (.cellRef .word 700)],s⟩=.done (.pair (.cellRef .word 700) value) final)) "pending caller outside source cost"
    return ⟨⟨i,core,.word⟩,⟨p.projection⟩⟩
  else throw (IO.userError "independent original raw/manual expectations")
private def fault (source : Syntax.FunctionDecl) (c : Compilation source) (mode : Nat) : IO Unit := do
  let f := if mode=0 then reader 700 else allocator
  let g := if mode=0 then writer 0 else if mode=1 then reader 700 else if mode=2 then writer 700 else checkedReader 0
  let s := if mode=3 then [Core.Value.bool false,w 99] else [w 41,w 99]
  let args ← arguments f g; let p ← prepare source c args; let env := p.inputs.environment.values
  let captured := [w 14,Core.Value.cellRef .word (if mode=3 then 0 else 700)]
  let outer := if mode=0 then Core.Frame.letBody first env else .letBody second (w 15::env)
  let frames := (if mode≤1 then [.loadCellApply] else if mode=2 then [.storeCellValue (.var 0) captured,.letBody (.loadCell (.var 2)) captured] else [.binaryApply .wordAdd (.bool false)])++[outer]
  let spent := if mode=0 then 8 else if mode=1 then 25 else if mode=2 then 26 else 29
  let final := if mode=0 then s else s++[w 14]; let v := if mode=3 then w 14 else Core.Value.cellRef .word 700
  let error := if mode=3 then Core.MachineFault.invalidBinaryOperands .wordAdd (.bool false) (w 14) else .invalidCellLocation 700
  let before : Core.State := ⟨.eval (.var (if mode=3 then 0 else 1)) captured,frames,final⟩
  let failed : Core.StatefulRunResult := .fault error ⟨.ret v,frames,final⟩
  check (decide (Core.runStateful (spent-1) (.initial core env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "discard fault skips later calls; later faults preserve earlier allocation"
  for fuel in List.range (spent+2) do
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "reconstruction is not a runtime-world guard"
    match genuine : Core.runStateful fuel (.initial core env s) with
    | .outOfFuel cp => have _ := Core.runStateful_resume genuine spent; check (decide (fuel<spent ∧ Core.runStateful spent cp=failed)) "all pre-fault resumptions"
    | result => check (decide (spent≤fuel ∧ result=failed)) "first fault and unchanged later results"
end ParsedComputationArgumentEffects
open ParsedComputationArgumentEffects in
def frontendParsedComputationArgumentEffectTests : IO Unit := do
  let source ← parsed; let c ← compile source
  for (location,value) in [(0,w 41),(1,w 99),(2,w 14)] do
    let _ ← verify source c allocator (reader location) [w 41,w 99] [w 41,w 99,w 14] [w 41,w 99,w 14] [w 41,w 99,w 14] (w 15) value value 8
  let original ← verify source c allocator (writer 0) [w 41,w 99] [w 41,w 99,w 14] [w 14,w 99,w 14] [w 14,w 99,w 14] (w 15) (w 14) (w 14) 15
  let permuted ← verify source c (writer 0) allocator [w 41,w 99] [w 14,w 99] [w 14,w 99,w 14] [w 14,w 99,w 14,w 15] (w 14) (w 15) (w 16) 15
  have _ : original.1.toCompiled=permuted.1.toCompiled := original.2.down.trans permuted.2.down.symm
  check (decide (original.1.inputs.environment.values≠permuted.1.inputs.environment.values)) "same compiled projection and same cost52 do not equate different same-typed supplied closures"
  let _ ← verify source c allocator (reader 0) [.bool false,w 99] [.bool false,w 99,w 14] [.bool false,w 99,w 14] [.bool false,w 99,w 14] (w 15) (.bool false) (.bool false) 8
  let _ ← verify source c allocator (writer 0) [.bool false,w 99] [.bool false,w 99,w 14] [w 14,w 99,w 14] [w 14,w 99,w 14] (w 15) (w 14) (w 14) 15
  for mode in [0,1,2,3] do fault source c mode
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationRuntimeSafety
/-! Original mixed bodies, sparse caller rows, independently counted source rules
and literal Core scripts connect actual effects to same-world runtime safety. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationRuntimeSafety
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RuntimeMixed",by decide⟩],by decide⟩⟩,68⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",id 4,.word⟩,⟨"f",foreign,.function .word .word⟩,⟨"g",id 9,.function .word .word⟩,
  ⟨"a",id 12,.function .word (.cell .word)⟩,⟨"c",id 15,.bool⟩,⟨"f",id 30,.bool⟩],
  by change [id 4,foreign,id 9,id 12,id 15,id 30].Nodup; decide⟩
private def types : TypeNameTable := [(["W"],.word),(["C"],.cell .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def reader : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word 0]
private def writer : Core.Value := .closure .word .word
  (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
private def env (x : Nat) (choice swap : Bool) : Resolved.Environment :=
  [(id 4,w x),(foreign,if swap then writer else reader),(id 9,if swap then reader else writer),
    (id 12,allocator),(id 15,.bool choice),(id 30,.bool false)]
private theorem envTyped (x : Nat) (choice swap : Bool) :
    Core.RuntimeEnvironmentHasTypes [.word] (env x choice swap).values inputs.context.values := by
  have r : Core.RuntimeValueHasType [.word] reader (.function .word .word) :=
    .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl))
  have g : Core.RuntimeValueHasType [.word] writer (.function .word .word) :=
    .closure (.cons (.cellRef rfl) .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))
  have a : Core.RuntimeValueHasType [.word] allocator (.function .word (.cell .word)) :=
    .closure .nil (.newCell (.var rfl))
  cases swap
  · exact .cons .word (.cons r (.cons g (.cons a (.cons .bool (.cons .bool .nil)))))
  · exact .cons .word (.cons g (.cons r (.cons a (.cons .bool (.cons .bool .nil)))))
private def parsed (body : String) : IO Syntax.Block := do
  let text := "function mixed(){" ++ body ++ "}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-runtime-safety.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original function parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original full bytes"
  return source.value.body
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .unit => return ⟨.unit,s,1,fun _ => by rw [original]; exact .cons .unit .refl⟩
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual callee shape")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | .newCell .word (.var i) =>
        match found : env[i]? with
        | some v => return ⟨.cellRef .word s.length,s ++ [v],3,fun _ => by rw [original]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
        | none => throw (IO.userError "manual allocation argument")
    | .ifE condition yes no =>
        let c ← path n condition env s
        match choice : c.value with
        | .bool true => let b ← path n yes env c.final; return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifTrue (choice ▸ c.evidence _) (b.evidence _)⟩
        | .bool false => let b ← path n no env c.final; return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifFalse (choice ▸ c.evidence _) (b.evidence _)⟩
        | _ => throw (IO.userError "manual Bool guard")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Certificate (Elaborates : Core.Expr → Core.Ty → Prop) (Evaluates : Core.Value → Core.Store → Nat → Prop) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : Elaborates core type
  raw : Evaluates value final cost
private abbrev Child (i : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) :=
  Certificate (RecursiveLocalComputationElaborates i.names i.context source) (RecursiveLocalComputationEvaluatesWithCost i.names e s source)
private def child (i : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) : IO (Child i e s source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some id =>
          match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id, actual : e.lookup? id with
          | some t,some n,some v => return ⟨.var n,t,v,s,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row")
      | none => throw (IO.userError "original first name")
  | ⟨_,.group inner⟩ =>
      let a ← child i e s inner
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .group a.elaboration,by rw [original]; exact .group a.raw⟩
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte≤argsSpan.startByte)) "original child ranges/order"
      let f ← child i e s fn; let a ← child i e f.final arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) a.final
            return ⟨.apply f.core a.core,output,b.value,b.final,f.cost+a.cost+b.cost+3,
              by rw [original]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
              by rw [original]; exact .application (fv ▸ f.raw) a.raw (b.evidence [])⟩
          else throw (IO.userError "original argument type")
      | _,_ => throw (IO.userError "original/actual Function")
  | _ => throw (IO.userError "outside independent child")
termination_by sizeOf source
private abbrev Tree (i : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (source : Syntax.Block) :=
  Certificate (RecursiveComputationReturnTreeElaborates types owner i source) (RecursiveComputationReturnTreeEvaluatesWithCost owner i.names e s source)
private def tree (i : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (source : Syntax.Block) : IO (Tree i e s source) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement ranges"
  match original : source with
  | ⟨_,[⟨rs,.returnStmt (some expression)⟩]⟩ =>
      check (rs.contains expression.span) "original return range"; let a ← child i e s expression
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | ⟨_,[⟨bs,.block statements⟩]⟩ =>
      let a ← tree i e s ⟨bs,statements⟩
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .block a.elaboration,by rw [original]; exact .block a.raw⟩
  | ⟨bs,⟨ls,.letDecl name annotation (some initializer)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span && decide (name.span.endByte≤initializer.span.startByte)) "original binding ranges/order"
      if unused : name.value ∉ i.names.map Prod.fst then
        let a ← child i e s initializer; let fresh := Resolved.freshLocalId owner i.ids
        let b ← tree (i.bindFresh owner name.value a.type) ((fresh,a.value)::e) a.final ⟨bs,rest⟩
        have tail : RecursiveComputationReturnTreeEvaluatesWithCost owner
            ((name.value,Resolved.freshLocalId owner (i.names.map Prod.snd))::i.names)
            ((Resolved.freshLocalId owner (i.names.map Prod.snd),a.value)::e) a.final ⟨bs,rest⟩ b.value b.final b.cost := by
          simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw
        match ann : annotation with
        | none => return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,
            by rw [original,ann]; exact .inferred a.elaboration b.elaboration,
            by rw [original,ann]; exact .inferred a.raw tail⟩
        | some written =>
            check (ls.contains written.span) "original type range"
            match atType : written with
            | ⟨_,.named name none⟩ =>
                if found : types.lookup? (qualifiedTypeNameKey name)=some a.type then
                  have meaning : StructuralTypeDenotes types written a.type := by rw [atType]; exact .named (TypeNameTable.lookup?_iff.mp found)
                  return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,
                    by rw [original,ann]; exact .binding meaning a.elaboration b.elaboration,
                    by rw [original,ann]; exact .binding a.raw tail⟩
                else throw (IO.userError "original annotation")
            | _ => throw (IO.userError "annotation shape")
      else throw (IO.userError "original shadow")
  | ⟨bs,⟨_,.expression expression true⟩::rest⟩ =>
      let a ← child i e s expression; let b ← tree i e a.final ⟨bs,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,b.value,b.final,a.cost+b.cost+2,
        by rw [original]; exact .discard a.elaboration b.elaboration,by rw [original]; exact .discard a.raw b.raw⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (i.names.map Prod.fst) yes=true then pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child i e s guard; let a ← tree i e c.final yes; let b ← tree i e c.final no
      if ct : c.type=.bool then
        if same : b.type=a.type then
          match cv : c.value with
          | .bool true => return ⟨.ifE c.core a.core b.core,a.type,a.value,a.final,c.cost+a.cost+2,
              by rw [original]; exact .conditional (ct ▸ c.elaboration) protection.down a.elaboration (same ▸ b.elaboration),
              by rw [original]; exact .ifTrue (cv ▸ c.raw) a.raw⟩
          | .bool false => return ⟨.ifE c.core a.core b.core,a.type,b.value,b.final,c.cost+b.cost+2,
              by rw [original]; exact .conditional (ct ▸ c.elaboration) protection.down a.elaboration (same ▸ b.elaboration),
              by rw [original]; exact .ifFalse (cv ▸ c.raw) b.raw⟩
          | _ => throw (IO.userError "actual Bool")
        else throw (IO.userError "both original branches")
      else throw (IO.userError "original Bool")
  | _ => throw (IO.userError "outside original mixed body")
termination_by sizeOf source
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def fixed : Core.Expr := .letE (call 1 0) (.letE (call 3 1)
  (.ifE (.var 6) (.letE (call 5 1) (.apply (.var 4) (call 5 2))) (call 3 2)))
private def verify (text : String) (x old : Nat) (choice swap : Bool) : IO Unit := do
  let source ← parsed text; let e := env x choice swap; let s := [w old]
  let a ← tree inputs e s source; let manual ← path 100 fixed e.values s
  let value := w (if swap || !choice then x else old)
  let final := if choice then [value,value] else [w x]
  let cost := if choice then 62 else if swap then 45 else 38
  if shape : a.core=fixed ∧ a.type=.word then
    have elaboration : RecursiveComputationReturnTreeElaborates types owner inputs source fixed .word := by simpa only [shape.1,shape.2] using a.elaboration
    have ids : e.ids=inputs.context.ids := rfl
    have st : Core.StoreHasTypes [.word] s := Core.StoreHasTypes.nil.allocate .word .word
    have et := envTyped x choice swap
    check (decide (a.value=value ∧ a.final=final ∧ a.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent exact values/stores/costs"
    check (decide (elaborateRecursiveComputationReturnTree? types owner inputs source=some (fixed,.word) ∧
      inputs.names.lookup? "f"=some foreign ∧ (inputs.bindFresh owner "r" .word).names.lookup? "r"=some (id 31) ∧
      ((inputs.bindFresh owner "r" .word).bindFresh owner "p" (.cell .word)).names.lookup? "p"=some (id 32))) "exact checker, first match and owner-filtered freshness"
    have identified : ∃ fw, Core.WorldExtends [.word] fw ∧ Core.RuntimeStoreHasTypes fw manual.final ∧ Core.RuntimeValueHasType fw manual.value .word ∧
        RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names e s source manual.value manual.final manual.cost := by
      obtain ⟨fw,fs,v,n,extension,storeTyped,valueTyped,originalCost,paths,_⟩ :=
        ComputationReturnTreeElaborates.runtime_typed_execution (F := RecursiveLocalComputationFragment)
          (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates)
          (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
          RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment
          RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
          RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost
          RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaboration ids et st
          ⟨manual.value, manual.final, Core.steps_from_initial_sound (manual.evidence [])⟩
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique (manual.evidence [])
      exact ⟨fw,extension,storeTyped,valueTyped,originalCost⟩
    have counted := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
      RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation a.raw a.elaboration ids
    have _ := (by simpa only [shape.1,Core.State.initial,Core.State.final] using counted [] : Core.Steps a.cost (.initial fixed e.values s) (.final a.value a.final)).final_unique (manual.evidence [])
    let k := [Core.Frame.pairApply (w 7)]
    have kt : Core.ContinuationHasType [.word] k .word (.product .word .word) := .cons (.pairApply .word) .nil
    have safety := ComputationReturnTreeElaborates.runtime_checkpoint_safety (ChildElab := RecursiveLocalComputationElaborates)
      RecursiveLocalComputationElaborates.core_hasType elaboration et st kt
    if choice then
      let bound := w (if swap then x else old)
      let saved := w x::bound::e.values
      let after := [w x,bound]
      check (decide (Core.runStateful 39 ⟨.eval fixed e.values,k,s⟩=
        .outOfFuel ⟨.ret (.cellRef .word 1),.letBody (.apply (.var 4) (call 5 2)) saved::k,after⟩ ∧
        Core.runStateful 40 ⟨.eval fixed e.values,k,s⟩=
        .outOfFuel ⟨.eval (.apply (.var 4) (call 5 2)) (.cellRef .word 1::saved),k,after⟩)) "allocation and hidden discard slot literal checkpoints"
    for fuel in List.range (cost+2) do
      match closed : Core.runStateful fuel (.initial fixed e.values s) with
      | .done v fs => check (decide (cost≤fuel ∧ v=value ∧ fs=final)) "exact closed result"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel closed
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final)) "exact closed residual"
      | .fault _ _ => throw (IO.userError "independent manual path faulted")
      match stopped : Core.runStateful fuel ⟨.eval fixed e.values,k,s⟩ with
      | .done v fs => check (decide (cost+1≤fuel ∧ v=.pair (w 7) value ∧ fs=final)) "typed pending completion"
      | .outOfFuel cp =>
          have _ := safety.2.2 stopped
          have _ := Core.runStateful_resume stopped (cost+1-fuel)
          check (decide (fuel≤cost ∧ Core.runStateful (cost+1-fuel) cp=.done (.pair (w 7) value) final ∧
            Core.runStateful 1 cp=Core.runStateful (fuel+1) ⟨.eval fixed e.values,k,s⟩)) "exact typed saved state/full resume"
      | .fault error state => False.elim (safety.2.1 fuel error state stopped)
    check (decide (Core.runStateful cost ⟨.eval fixed e.values,k,s⟩=.outOfFuel ⟨.ret value,k,final⟩)) "actual endpoint not closed completion"
  else throw (IO.userError "original lowering differs from literal Core")
end ParsedComputationRuntimeSafety
open ParsedComputationRuntimeSafety
def frontendParsedComputationRuntimeSafetyTests : IO Unit := do
  for choice in [true,false] do
    for swap in [true,false] do
      for x in [11,14] do
        for old in [23,91] do
          for annotation in ["",":W"] do
            for wrapper in [false,true] do
              let body := "let r"++annotation++"=f(x);g(x);if(c){{let p:C=a(r);return f(g(r));}}else{return f(x);}"
              verify (if wrapper then "{"++body++"}" else body) x old choice swap
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationRuntimeSafetyEntries
/-! Original mixed declarations and actual argument worlds are independent of
checking. Literal Core scripts fix observations before the runtime theorem. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationRuntimeSafetyEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"SafeEntries",by decide⟩],by decide⟩⟩,68⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-runtime-safety.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original declaration")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) ("complete original parse: "++text)
  check (decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span &&
    source.span.contains source.value.signature.span) "original file/header/body spans"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match shape : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "named fixture annotation")
private def parameters (types : TypeNameTable) (initial : LocalInputs) (ps : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Σ final, PLift (RuntimeParametersBindFrom types owner initial ps args final)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨initial,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter ranges"
      let m ← meaning types annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let next ← parameters types (initial.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused next.2.down⟩⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "actual argument type")
  | _,_ => throw (IO.userError "parameter arity/profile")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) :
    IO (Static (RecursiveLocalComputationElaborates inputs.names inputs.context source)) := do
  match shape : source with
  | ⟨_,.identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          match typed : inputs.context.lookup? id, indexed : Resolved.LocalScope.index? inputs.context.ids id with
          | some type,some index => return ⟨.var index,type,by
              rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _,_ => throw (IO.userError "original static row")
      | none => throw (IO.userError "original name")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call spans"
      let f ← child inputs fn; let a ← child inputs arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "call argument")
      | _ => throw (IO.userError "callee")
  | _ => throw (IO.userError "fixture child shape")
termination_by sizeOf source
private def body (types : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) :
    IO (Static (RecursiveComputationReturnTreeElaborates types owner inputs source)) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement ranges"
  match shape : source with
  | ⟨_,[⟨_,.returnStmt (some expression)⟩]⟩ =>
      let a ← child inputs expression; return ⟨a.core,a.type,by rw [shape]; exact .expression a.evidence⟩
  | ⟨_,[⟨innerSpan,.block statements⟩]⟩ =>
      let a ← body types inputs ⟨innerSpan,statements⟩; return ⟨a.core,a.type,by rw [shape]; exact .block a.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some initializer)⟩::rest⟩ =>
      if unused : name.value ∉ inputs.names.map Prod.fst then
        let a ← child inputs initializer
        let b ← body types (inputs.bindFresh owner name.value a.type) ⟨span,rest⟩
        match annotationShape : annotation with
        | none => return ⟨.letE a.core b.core,b.type,by rw [shape,annotationShape]; exact .inferred a.evidence b.evidence⟩
        | some annotation =>
            let m ← meaning types annotation
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,by rw [shape,annotationShape]; exact .binding (same ▸ m.2.down) a.evidence b.evidence⟩
            else throw (IO.userError "initializer annotation")
      else throw (IO.userError "fresh original binding")
  | ⟨span,⟨_,.expression expression true⟩::rest⟩ =>
      let a ← child inputs expression; let b ← body types inputs ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,by rw [shape]; exact .discard a.evidence b.evidence⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (inputs.names.map Prod.fst) yes=true then pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child inputs condition; let a ← body types inputs yes; let b ← body types inputs no
      if valid : c.type=.bool ∧ b.type=a.type then return ⟨.ifE c.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ c.evidence) protection.down a.evidence (valid.2 ▸ b.evidence)⟩
      else throw (IO.userError "whole guard/branch types")
  | _ => throw (IO.userError "original mixed body")
termination_by sizeOf source
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual lookup")
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .ifE condition yes no =>
        let c ← path n condition env s
        match decision : c.value with
        | .bool true => let a ← path n yes env c.final; return ⟨a.value,a.final,c.cost+a.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (decision ▸ c.evidence _) (a.evidence _)⟩
        | .bool false => let b ← path n no env c.final; return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (decision ▸ c.evidence _) (b.evidence _)⟩
        | _ => throw (IO.userError "manual Bool")
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .newCell .word (.var i) =>
        match found : env[i]? with
        | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
        | none => throw (IO.userError "allocation operand")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual read")
        | _ => throw (IO.userError "manual reference")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write")
        | _,_ => throw (IO.userError "manual store operands")
    | _ => throw (IO.userError "literal Core script")
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) :
    IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.1=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.2.down)⟩⟩
        else throw (IO.userError "header profile")
      else throw (IO.userError "return meaning")
  | _ => throw (IO.userError "singleton return clause")
private def verify (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr)
    (world : Core.StoreTyping) (s final : Core.Store) (value : Core.Value) (cost : Nat)
    (typed : ∀ a ∈ args, Core.RuntimeValueHasType world a.value a.type) (stored : Core.StoreHasTypes world s) : IO PreparedRuntimeFunction := do
  let f::g::_ := args | throw (IO.userError "fixture arguments")
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],.word),(["Y"],.word),(["C"],.bool),(["R"],output)]
  let ps ← parameters types .empty source.value.signature.parameters.elements args
  let inputs := ps.1; let env := inputs.environment.values
  let b ← body types inputs.toTypeInputs source.value.body
  let manual ← path 100 core env s
  check (decide (env=args.reverse.map (·.value) ∧ inputs.ids=(List.range args.length).reverse.map (fun i => ⟨owner,i⟩))) "exact actual rows/reverse once"
  check (decide (manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independently fixed observations"
  if fixed : b.core=core ∧ b.type=output then
    let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    let h ← header types source output
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared :=
      ⟨h.down,ps.2.down,by simpa only [fixed.1,fixed.2] using b.evidence⟩
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost
      RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
      elaborateRecursiveLocalComputation?_iff preparation typed stored
      ⟨manual.value, manual.final, Core.steps_from_initial_sound (manual.evidence [])⟩
    have agreement : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future manual.final ∧
        Core.RuntimeValueHasType future manual.value output ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names inputs.environment s source.value.body manual.value manual.final manual.cost := by
      obtain ⟨future,final,value,cost,ext,st,vt,raw,paths,_⟩ := safe.2
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique (manual.evidence [])
      exact ⟨future,ext,st,vt,raw⟩
    if grows : s.length < manual.final.length then
      have allocationExtends : ∃ future, Core.WorldExtends world future ∧
          world.length < future.length ∧ Core.RuntimeStoreHasTypes future manual.final := by
        obtain ⟨future,ext,st,_,_⟩ := agreement
        exact ⟨future,ext,by simpa only [stored.length_eq,st.length_eq] using grows,st⟩
      have _ := allocationExtends
      check (decide (s.length < final.length)) "allocation grows the actual store and runtime world"
    match shape : core with
    | .letE initializer (.letE discarded tail) =>
        let a ← path 100 initializer env s
        let d ← path 100 discarded (a.value::env) a.final
        let first : Core.State := ⟨.ret a.value,[.letBody (.letE discarded tail) env],a.final⟩
        let second : Core.State := ⟨.ret d.value,[.letBody tail (a.value::env)],d.final⟩
        have firstPath : Core.Steps (a.cost+1) (.initial core env s) first := by
          rw [shape]; simpa [first,Core.State.initial,Nat.add_comm] using Core.Steps.cons Core.Transition.enterLet (a.evidence [.letBody (.letE discarded tail) env])
        have secondPath : Core.Steps (a.cost+d.cost+3) (.initial core env s) second := by
          rw [shape]
          simpa [second,Core.State.initial,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Core.Steps.cons Core.Transition.enterLet
            ((a.evidence [.letBody (.letE discarded tail) env]).trans (.cons .bindLet (.cons .enterLet (d.evidence [.letBody tail (a.value::env)]))))
        have _ := Core.runStateful_outOfFuel_complete firstPath (Core.advance_next_iff.mpr .bindLet)
        have _ := Core.runStateful_outOfFuel_complete secondPath (Core.advance_next_iff.mpr .bindLet)
        for (spent,cp) in [(a.cost+1,first),(a.cost+d.cost+3,second)] do
          check (decide (Core.runStateful spent (.initial core env s)=.outOfFuel cp ∧
            Core.runStateful (cost-spent) cp=.done value final)) "named binding and discard retain actual saved environment/store"
    | _ => throw (IO.userError "literal named/discard let checkpoints")
    have whole (fuel) : runRecursiveComputationFunction? types owner source args fuel s =
        some (output,Core.runStateful fuel (.initial core env s)) := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,runs⟩ := safe.2
      exact runs fuel
    have _ := safe.1
    for fuel in List.range (cost+2) do
      have _ := whole fuel
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core env s)))) "full result including actual checkpoints"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact successful threshold"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted
          have _ := Core.runStateful_resume exhausted 3
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧ runRecursiveComputationFunction? types owner source args (fuel+3) s=some (output,Core.runStateful 3 cp))) "every genuine checkpoint fully resumes"
      | .fault _ _ => throw (IO.userError "world/store typed execution faulted")
    return prepared
  else throw (IO.userError "independent exact Core/type")
private def reader (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word location],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def allocator : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl))⟩
private def arg (n : Nat) : TypedRuntimeArgument := ⟨.word,w n,.word⟩
private def choice (b : Bool) : TypedRuntimeArgument := ⟨.bool,.bool b,.bool⟩
private theorem readerTyped {world : Core.StoreTyping} {location : Nat} (found : world[location]?=some .word) :
    Core.RuntimeValueHasType world (reader location).value (reader location).type := .closure (.cons (.cellRef found) .nil) (.loadCell (.var rfl))
private theorem writerTyped {world : Core.StoreTyping} (found : world[0]?=some .word) :
    Core.RuntimeValueHasType world writer.value writer.type :=
  .closure (.cons (.cellRef found) .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))
private theorem wordStore (n : Nat) : Core.StoreHasTypes [.word] [w n] :=
  Core.StoreHasTypes.nil.allocate .word .word
private theorem argumentsTyped {world : Core.StoreTyping} {f g : TypedRuntimeArgument}
    (ft : Core.RuntimeValueHasType world f.value f.type) (gt : Core.RuntimeValueHasType world g.value g.type) (x y : Nat) (c : Bool) :
    ∀ a ∈ [f,g,arg x,arg y,choice c], Core.RuntimeValueHasType world a.value a.type := by
  intro a member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl; exact ft; exact gt; exact .word; exact .word; exact .bool
end ParsedComputationRuntimeSafetyEntries
open ParsedComputationRuntimeSafetyEntries
def frontendParsedComputationRuntimeSafetyEntryTests : IO Unit := do
  let core := Core.Expr.letE (.apply (.var 4) (.var 2))
    (.letE (.apply (.var 4) (.var 2)) (.ifE (.var 2) (.var 1) (.apply (.var 6) (.var 3))))
  for annotated in [false,true] do
    let binding := if annotated then "let a:R=f(x);" else "let a=f(x);"
    let source ← parsed ("function safe(f:F,g:G,x:X,y:Y,c:C) returns(R){"++binding++"g(y);{if(c){return a;}else{return f(y);}}}")
    for c in [true,false] do
      let args := [reader 0,writer,arg 11,arg 14,choice c]
      let one ← verify source args .word core [.word] [w 23] [w 14] (w (if c then 23 else 14)) (if c then 31 else 38)
        (argumentsTyped (readerTyped rfl) (writerTyped rfl) 11 14 c) (wordStore 23)
      let two ← verify source args .word core [.word] [w 7] [w 14] (w (if c then 7 else 14)) (if c then 31 else 38)
        (argumentsTyped (readerTyped rfl) (writerTyped rfl) 11 14 c) (wordStore 7)
      let three ← verify source args .word core [.word,.word] [w 23,w 7] [w 14,w 7] (w (if c then 23 else 14)) (if c then 31 else 38)
        (argumentsTyped (readerTyped rfl) (writerTyped rfl) 11 14 c) ((wordStore 23).allocate .word .word)
      check (decide (one.core=two.core ∧ one.returnType=two.returnType ∧
        one.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=two.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) ∧
        one.core=three.core ∧ one.returnType=three.returnType ∧
        one.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=three.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)))) "same prepared fields with distinct typed stores/worlds"
      discard <| verify source [writer,reader 0,arg 11,arg 14,choice c] .word core [.word] [w 23] [w (if c then 11 else 14)] (w (if c then 11 else 14)) (if c then 31 else 45)
        (argumentsTyped (writerTyped rfl) (readerTyped rfl) 11 14 c) (wordStore 23)
      discard <| verify source [reader 1,writer,arg 11,arg 14,choice c] .word core [.word,.word] [w 23,w 7] [w 14,w 7] (w 7) (if c then 31 else 38)
        (argumentsTyped (readerTyped rfl) (writerTyped rfl) 11 14 c) ((wordStore 23).allocate .word .word)
      discard <| verify source [allocator,writer,arg 11,arg 14,choice c] (.cell .word) core [.word] [w 23]
        (if c then [w 14,w 11] else [w 14,w 11,w 14]) (.cellRef .word (if c then 1 else 2)) (if c then 31 else 38)
        (argumentsTyped (.closure .nil (.newCell (.var rfl))) (writerTyped rfl) 11 14 c) (wordStore 23)

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationTypeTableBoundaries
/-! A selected raw success does not license rejection preservation when an
unselected original annotation gains or changes its first-match meaning. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationTypeTableBoundaries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TypeTableBoundary", by decide⟩], by decide⟩⟩, 127⟩
private def base : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def repaired : TypeNameTable := base ++ [(["Missing"], .word)]
private def changed : TypeNameTable := (["Missing"], .bool) :: repaired
private def word := Core.Value.word (Core.Word.ofNatModulo 17)
private def args (c : Bool) : List TypedRuntimeArgument := [⟨.bool, .bool c, .bool⟩, ⟨.word, word, .word⟩]
private def core : Core.Expr := .ifE (.var 1) (.var 0) (.letE (.var 0) (.var 0))
private def cost (c : Bool) : Nat := if c then 4 else 7
private def payload (p : PreparedRuntimeFunction) :=
  (p.inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)), p.core, p.returnType)
private theorem changed_not_extension : ¬ TypeNameTable.Extends repaired changed := by
  intro extension
  have found : TypeNameTable.Lookup repaired ["Missing"] .word := .tail (by decide) (.tail (by decide) .head)
  have impossible := TypeNameTable.lookup?_iff.mpr (extension found)
  cases impossible
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function boundary(c:Bool,x:Word) returns(Word){if(c){return x;}else{let x:Missing=x;return x;}}"
  let file : Syntax.SourceFile := ⟨⟨.main, "computation-type-table-boundary.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lex")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original complete bytes"
  return source
private def meaning (s : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes repaired s t)) := do
  match shape : s with
  | ⟨_, .named name none⟩ =>
      match found : repaired.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t, ⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original named meaning")
  | _ => throw (IO.userError "original annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (as : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom repaired owner s ps statics
  bound : RuntimeParametersBindFrom repaired owner a ps as actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (as : List TypedRuntimeArgument) : IO (Parameters s a ps as) := do
  match shape : ps, supplied : as with
  | [], [] => return ⟨s, a, by rw [shape]; exact .nil, by rw [shape, supplied]; exact .nil⟩
  | ⟨span, .typed none name ann⟩ :: rest, arg :: tail =>
      check (span.contains name.span && span.contains ann.span) "original parameter fields"
      let m ← meaning ann
      if same : m.1 = arg.type then
        if fresh : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let n ← parameters (s.bindFresh owner name.value arg.type)
            (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨n.statics, n.actual, by rw [shape]; exact .cons (same ▸ m.2.down) fresh.1 n.declared,
            by rw [shape, supplied]; exact .cons (same ▸ m.2.down) fresh.2 n.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "actual argument type")
  | _, _ => throw (IO.userError "original arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context s)) := do
  match shape : s with
  | ⟨_, .identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some id =>
          match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
          | some t, some n => return ⟨.var n, t, by
              rw [shape]
              exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _, _ => throw (IO.userError "original row")
      | none => throw (IO.userError "original name")
  | _ => throw (IO.userError "child fixture")
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates repaired owner i b)) := do
  check (b.value.all fun s => b.span.contains s.span) "original statement ranges"
  match shape : b with
  | ⟨_, [⟨_, .returnStmt (some s)⟩]⟩ => let c ← child i s; return ⟨c.core, c.type, by rw [shape]; exact .expression c.evidence⟩
  | ⟨span, ⟨ls, .letDecl name (some ann) (some init)⟩ :: rest⟩ =>
      check (ls.contains name.span && ls.contains ann.span && ls.contains init.span) "original annotation and initializer"
      let c ← child i init; let m ← meaning ann
      if same : m.1 = c.type then
        let n ← body (i.bindFresh owner name.value c.type) ⟨span, rest⟩
        return ⟨.letE c.core n.core, n.type, by rw [shape]; exact .binding (same ▸ m.2.down) c.evidence n.evidence⟩
      else throw (IO.userError "typed initializer")
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let c ← child i condition; let a ← body i yes; let d ← body i no
      if same : c.type = .bool ∧ d.type = a.type then
        match arm : yes with
        | ⟨_, [⟨_, .returnStmt _⟩]⟩ =>
            have protection : ComputationNamesProtected (i.names.map Prod.fst) yes := by
              intro name exposed; rw [arm] at exposed; cases exposed with | tail impossible => cases impossible
            return ⟨.ifE c.core a.core d.core, a.type, by rw [shape]; exact .conditional (same.1 ▸ c.evidence) protection a.evidence (same.2 ▸ d.evidence)⟩
        | _ => throw (IO.userError "original return-only then")
      else throw (IO.userError "branch types")
  | _ => throw (IO.userError "body fixture")
termination_by sizeOf b
private def preparation (source : Syntax.FunctionDecl) (as : List TypedRuntimeArgument) :
    IO (Σ p, PLift (RecursiveComputationFunctionPrepares repaired owner source as p ∧ p.core = core ∧ p.returnType = .word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements as
  let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1 = .word ∧ b.core = core ∧ b.type = .word then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          have header : RuntimeFunctionHeader repaired source.value.signature .word :=
            ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compiled : RecursiveComputationFunctionCompiles repaired owner source ⟨ps.statics, core, .word⟩ :=
            ⟨header, ps.declared, by simpa only [erased, same.2.1, same.2.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compiled
          check (decide (ps.actual.environment.values = as.reverse.map (·.value) ∧
            ps.actual.names = [("x", ⟨owner, 1⟩), ("c", ⟨owner, 0⟩)])) "exact declaration order and actual values"
          return ⟨⟨ps.actual, core, .word⟩, ⟨⟨⟨header, ps.bound, by simpa only [same.2.1, same.2.2] using b.evidence⟩, rfl, rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "separately written Core")
  | _ => throw (IO.userError "original return clause")
private def atom (table : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Expr) :
    IO (Σ v, PLift (∀ store, RecursiveLocalComputationEvaluatesWithCost table env store s v store 1)) := do
  match shape : s with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | some id => match found : env.lookup? id with
        | some v => return ⟨v, ⟨fun _ => by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩⟩
        | none => throw (IO.userError "raw row")
      | none => throw (IO.userError "raw name")
  | _ => throw (IO.userError "raw atom")
private structure Raw (table : LocalNameTable) (env : Resolved.Environment) (b : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner table env store b value store cost
private def raw (table : LocalNameTable) (env : Resolved.Environment) (b : Syntax.Block) : IO (Raw table env b) := do
  match shape : b with
  | ⟨_, [⟨_, .returnStmt (some s)⟩]⟩ => let v ← atom table env s; return ⟨v.1, 1, fun _ => by rw [shape]; exact .expression (v.2.down _)⟩
  | ⟨span, ⟨_, .letDecl name (some _) (some init)⟩ :: rest⟩ =>
      let v ← atom table env init; let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← raw ((name.value, fresh) :: table) ((fresh, v.1) :: env) ⟨span, rest⟩
      return ⟨r.value, 1 + r.cost + 2, fun _ => by rw [shape]; exact .binding (v.2.down _) (r.evidence _)⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let c ← atom table env condition
      match selected : c.1 with
      | .bool true => let r ← raw table env yes; return ⟨r.value, 1 + r.cost + 2, fun _ => by rw [shape]; exact .ifTrue (selected ▸ c.2.down _) (r.evidence _)⟩
      | .bool false => let r ← raw table env no; return ⟨r.value, 1 + r.cost + 2, fun _ => by rw [shape]; exact .ifFalse (selected ▸ c.2.down _) (r.evidence _)⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private theorem path (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (cost c) ⟨.eval core [word, .bool c], k, store⟩ ⟨.ret word, k, store⟩ := by
  cases c
  · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl)
      (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))
  · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
end ParsedComputationTypeTableBoundaries
open ParsedComputationTypeTableBoundaries
def frontendParsedComputationTypeTableBoundaryTests : IO Unit := do
  let source ← parsed
  have extension : TypeNameTable.Extends base repaired := TypeNameTable.Extends.append_right _ _
  have _ := changed_not_extension
  check (decide (base.lookup? ["Missing"] = none ∧ repaired.lookup? ["Missing"] = some .word ∧
    changed.lookup? ["Missing"] = some .bool)) "unknown repair and changed first match are different boundaries"
  for c in [true, false] do
    let p ← preparation source (args c); let prepared := p.1; let evidence := p.2.down.1
    have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr evidence
    have _ := evidence.extend_types (TypeNameTable.Extends.append_right repaired [(["Word"], .bool)])
    have _ : TypeNameTable.Lookup repaired ["Word"] .word := extension .head
    let r ← raw prepared.inputs.names prepared.inputs.environment source.value.body
    if expected : r.value = word ∧ r.cost = cost c then
      if rejected : elaborateRecursiveComputationReturnTree? base owner prepared.inputs.toTypeInputs source.value.body = none then
        have absent : ¬ ∃ e t, RecursiveComputationReturnTreeElaborates base owner prepared.inputs.toTypeInputs source.value.body e t := by
          rintro ⟨e, t, provenance⟩
          have contradiction := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr provenance
          change elaborateRecursiveComputationReturnTree? base owner prepared.inputs.toTypeInputs source.value.body = some (e, t) at contradiction
          rw [rejected] at contradiction; cases contradiction
        have _ := absent
      else throw (IO.userError "old whole body accepted its unknown unselected annotation")
      for table in [base, changed] do
        check ((compileRecursiveComputationFunction? table owner source).isNone &&
          (prepareRecursiveComputationFunction? table owner source (args c)).isNone) "whole source rejection cannot follow the selected path"
      for store in [[], [Core.Value.bool true, .cellRef .word 999]] do
        have sourceCost : RecursiveComputationReturnTreeEvaluatesWithCost owner prepared.inputs.names prepared.inputs.environment store source.value.body word store (cost c) := by
          simpa only [expected.1, expected.2] using r.evidence store
        have _ := sourceCost
        for fuel in List.range (cost c + 2) do
          have _ := (path c store []).runStateful_done_iff (fuel := fuel)
          let result := Core.runStateful fuel (.initial core [word, .bool c] store)
          check (decide (runRecursiveComputationFunction? repaired owner source (args c) fuel store = some (.word, result))) "complete repaired result equals independent literal path"
          check (decide (runRecursiveComputationFunction? base owner source (args c) fuel store = none ∧
            runRecursiveComputationFunction? changed owner source (args c) fuel store = none)) "rejected original annotations stay rejected at every fuel"
          check (decide (result = .done word store) == decide (cost c ≤ fuel)) "independent exact source cost"
          match result with
          | .outOfFuel cp => check (decide (Core.runStateful (cost c - fuel) cp = .done word store)) "genuine residual retains original values/store"
          | .done _ _ => pure ()
          | .fault _ _ => throw (IO.userError "unexpected fault")
    else throw (IO.userError "independent selected raw value and cost")
    check (decide ((prepareRecursiveComputationFunction? repaired owner source (args c)).map payload = some (payload prepared))) "original independent preparation"
    have _ := accepted
  for badArgs in [[], [⟨.bool, .bool true, .bool⟩], [⟨.bool, .bool true, .bool⟩, ⟨.bool, .bool false, .bool⟩]] do
    check ((prepareRecursiveComputationFunction? repaired owner source badArgs).isNone) "repair does not repair wrong actual arity or types"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationTypeTableEffects
/-! Table transport preserves actual closures, allocation, faults and complete saved states. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationTypeTableEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationTypeTableEffects",by decide⟩],by decide⟩⟩,125⟩
private def types : TypeNameTable := [(["Word"],.word),(["Bool"],.bool),(["Word"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def reader (l : Nat) : Core.Value := .closure .word .word (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.loadCell (.var 2)) (.var 1))) [.cellRef .word l]
private def branchCore : Core.Expr := .letE (.apply (.var 1) (.var 0)) (.var 0)
private def afterCore : Core.Expr := .ifE (.var 2) branchCore (.var 0)
private def tailCore : Core.Expr := .letE (.apply (.var 0) (.var 2)) afterCore
private def core : Core.Expr := .letE (.var 2) tailCore
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:function(Word) returns(Word),x:Word,c:Bool) returns(Word){let f:function(Word) returns(Word)=f;let x:Word=f(x);if(c){{let x:Word=f(x);return x;}}else{return x;}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-type-table-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple [a]⟩ => let x ← meaning a; return ⟨x.1,⟨by rw [shape]; exact .single x.2.down⟩⟩
  | ⟨_,.function _ ⟨_,[a]⟩ (some ⟨span,results⟩)⟩ => let x ← meaning a; let y ← meaning ⟨span,.tuple results⟩; return ⟨.function x.1 y.1,⟨by rw [shape]; exact .functionReturns x.2.down y.2.down⟩⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf e
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "actual argument type")
  | _,_ => throw (IO.userError "original arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← body i ⟨span,statements⟩; return ⟨r.core,r.type,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.length=i.ids.length+1 ∧ next.ids.head?=some (Resolved.freshLocalId owner i.ids))) "same fresh IDs retain every original row"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← child i c; let t ← body i yes; let e ← body i no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protection : ComputationNamesProtected (i.names.map Prod.fst) yes := by intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : a.type=.bool ∧ t.type=e.type then return ⟨.ifE a.core t.core e.core,t.type,by rw [shape]; exact .conditional (same.1 ▸ a.evidence) protection t.evidence (same.2.symm ▸ e.evidence)⟩ else throw (IO.userError "branch type")
      | _ => throw (IO.userError "original explicit then scope barrier")
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core ∧ b.type=.word then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature (.word) := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2.1,same.2.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("c",⟨owner,2⟩),("x",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original declarations and actual reverse once"
          return ⟨⟨ps.actual,core,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2.1,same.2.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core and outer single annotation")
  | _ => throw (IO.userError "outer single return policy")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .binary .wordAdd a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : Core.BinaryOp.wordAdd.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual Word addition fault")
    | .ifE c a b =>
        let condition ← path n c env s
        match cv : condition.value with
        | .bool true => let r ← path n a env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (cv ▸ condition.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (cv ▸ condition.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual condition")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← rawBody table env s ⟨span,statements⟩; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← rawChild table env s c
      match cv : a.value with
      | .bool true => let r ← rawBody table env a.final yes; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifTrue (cv ▸ a.evidence) r.evidence⟩
      | .bool false => let r ← rawBody table env a.final no; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifFalse (cv ▸ a.evidence) r.evidence⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b

private def duplicates : TypeNameTable := types++[(["Word"],.unit),(["Bool"],.word)]
private theorem backwards : TypeNameTable.Extends duplicates types := by
  intro key type found
  have same : duplicates.lookup? key=types.lookup? key := by
    by_cases a : ["Word"]=key <;> by_cases b : ["Bool"]=key <;> simp [duplicates,types,TypeNameTable.lookup?,a,b]
  exact TypeNameTable.lookup?_iff.mp (same ▸ TypeNameTable.lookup?_iff.mpr found)
private def variants : List (Σ next, PLift (TypeNameTable.Extends types next)) :=
  [⟨duplicates,⟨TypeNameTable.Extends.append_right _ _⟩⟩,
   ⟨(["Fresh"],Core.Ty.unit)::types,⟨TypeNameTable.Extends.cons_fresh _ _ _ (by decide)⟩⟩]
private def view (p : PreparedRuntimeFunction) :=
  (p.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),p.core,p.returnType)
private def arguments (l : Nat) (c : Bool) : IO (List TypedRuntimeArgument) :=
  [reader l,w 14,.bool c].mapM fun v => do
    match built : buildRuntimeArgument? v with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=v ∧ a.type=v.type)) "same constructed closure/captures"; return a
    | none => throw (IO.userError "original actual argument")
private def transport (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (p : PreparedRuntimeFunction)
    (provenance : RecursiveComputationFunctionPrepares types owner source args p) (s : Core.Store) (limit : Nat) : IO Unit := do
  have old := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr provenance
  have compilation : RecursiveComputationFunctionCompiles types owner source p.toCompiled := ⟨provenance.header,provenance.parameters.erase_values,provenance.body⟩
  have oldCompile := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
  have oldBody := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr provenance.body
  have typing := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,provenance.body⟩
  have exactRun (fuel) : runRecursiveComputationFunction? types owner source args fuel s=some (p.returnType,Core.runStateful fuel (.initial p.core p.inputs.environment.values s)) := by simp only [runRecursiveComputationFunction?,runComputationFunction?,old,bind,Option.bind_some,pure]
  for ⟨next,extension⟩ in variants do
    have changed := provenance.extend_types extension.down; have _ := compilation.extend_types extension.down
    have _ := provenance.body.extend_types extension.down; have _ := typing.extend_types extension.down
    have _ := elaborateComputationReturnTree?_some_of_extends extension.down oldBody
    have _ := compileComputationFunction?_some_of_extends extension.down oldCompile
    have exactPrepared := prepareComputationFunction?_some_of_extends extension.down old
    have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr changed
    check (decide ((prepareRecursiveComputationFunction? next owner source args).map view=some (view p))) "entire actual binding rows, captures, Core and return tag"
    for fuel in List.range limit do
      have _ := runComputationFunction?_some_of_extends extension.down (exactRun fuel)
      have _ := runComputationFunction?_eq_of_mutual_extends (checkChild := elaborateRecursiveLocalComputation?) (TypeNameTable.Extends.append_right _ _) backwards owner source args fuel s
      check (decide (runRecursiveComputationFunction? next owner source args fuel s=some (p.returnType,Core.runStateful fuel (.initial p.core p.inputs.environment.values s)))) "transport retains done/fault/complete genuine checkpoint"
    have _ := exactPrepared
  have _ := elaborateComputationReturnTree?_eq_of_mutual_extends (checkChild := elaborateRecursiveLocalComputation?) (TypeNameTable.Extends.append_right _ _) backwards owner p.inputs.toTypeInputs source.value.body
  have _ := compileComputationFunction?_eq_of_mutual_extends (checkChild := elaborateRecursiveLocalComputation?) (TypeNameTable.Extends.append_right _ _) backwards owner source
  for bad in [[],args.drop 1,args.reverse] do
    have _ := prepareComputationFunction?_eq_of_mutual_extends (checkChild := elaborateRecursiveLocalComputation?) (TypeNameTable.Extends.append_right _ _) backwards owner source bad
    check ((prepareRecursiveComputationFunction? types owner source bad).isNone && (prepareRecursiveComputationFunction? duplicates owner source bad).isNone) "mutual equality includes wrong-argument rejection"
private def verify (l base : Nat) (c : Bool) : IO Unit := do
  let source ← parsed; let s := [w 41,w 99]; let first := w (base+14); let value := if c then w (base+base+14) else first
  let final := s++[w 14]++(if c then [first] else []); let cost := if c then 45 else 26
  let manual ← path 80 core [.bool c,w 14,reader l] s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal Core cost/value and actual allocation"
  let args ← arguments l c; let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actual : env=[.bool c,w 14,reader l] then
    have literal (k) : Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actual]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have allK (k) : Core.Steps raw.cost ⟨.eval core env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original (by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds) k
    have _ := (allK []).final_unique (literal [])
    check (decide (raw.value=value ∧ raw.cost=cost ∧ raw.final=final ∧ validateRuntimeInputs [.word,.word] args s=true)) "independent original source cost and separate valid-world boundary"
    transport source args p.1 p.2.down.1 s (cost+2)
    for fuel in List.range (cost+2) do
      have _ := (literal []).runStateful_done_iff (fuel := fuel)
      match genuine : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "independent full fuel threshold"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel genuine
          for more in [0,1,cost] do
            have _ := Core.runStateful_resume genuine more
            check (decide (fuel<cost ∧ Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "same genuine checkpoint/full resumed state"
      | .fault _ _ => throw (IO.userError "successful path fault")
    let retained := reader l::env; let allocated := s++[w 14]
    let cps : List (Nat × Core.State) := [(20,⟨.ret (w 14),[.binaryApply .wordAdd (w base),.letBody afterCore retained],allocated⟩),(21,⟨.ret first,[.letBody afterCore retained],allocated⟩),(24,⟨.ret (.bool c),[.ifBranches branchCore (.var 0) (first::retained)],allocated⟩)]
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env s)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        have ready := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
        have stopped : runComputationFunction? elaborateRecursiveLocalComputation? types owner source args spent s=some (.word,.outOfFuel cp) := by simp only [runComputationFunction?,ready,bind,Option.bind_some,pure,p.2.down.2.1,p.2.down.2.2]; exact congrArg (fun r => some (Core.Ty.word,r)) genuine
        for ⟨next,extension⟩ in variants do
          have _ := runComputationFunction?_some_of_extends extension.down stopped
          check (decide (runRecursiveComputationFunction? next owner source args spent s=some (.word,.outOfFuel cp))) "literal saved environment/capture/store transported without erasure"
        check (decide (Core.runStateful (cost-spent) cp=.done value final)) "literal actual operands/captured callee/old rows are retained"
      else throw (IO.userError "literal checkpoint")
    have _ := literal [.pairApply .unit]
    check (decide (Core.runStateful cost ⟨.eval core env,[.pairApply .unit],s⟩=.outOfFuel ⟨.ret value,[.pairApply .unit],final⟩)) "caller continuation is outside source cost"
  else throw (IO.userError "actual argument reverse once")
private def fault (missing c : Bool) : IO Unit := do
  let l := if missing then 700 else 0; let s := if missing then [w 41,w 99] else [Core.Value.bool false,w 99]
  let source ← parsed; let args ← arguments l c; let p ← prepare source args; let env := p.1.inputs.environment.values
  let caller := reader l::env; let captured : Core.Environment := [.cellRef .word s.length,w 14,.cellRef .word l]
  let allocated := s++[w 14]; let spent := if missing then 17 else 20
  let frames : List Core.Frame := if missing then [.loadCellApply,.binaryRight .wordAdd (.var 1) captured,.letBody afterCore caller] else [.binaryApply .wordAdd (.bool false),.letBody afterCore caller]
  let v := if missing then Core.Value.cellRef .word l else w 14
  let error := if missing then Core.MachineFault.invalidCellLocation l else .invalidBinaryOperands .wordAdd (.bool false) (w 14)
  let failed : Core.StatefulRunResult := .fault error ⟨.ret v,frames,allocated⟩
  let before : Core.State := ⟨.eval (.var (if missing then 2 else 1)) captured,frames,allocated⟩
  check (decide (validateRuntimeInputs [.word,.word] args s=false ∧ Core.runStateful (spent-1) (.initial core env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "missing/corrupt actual reference retains allocation before fault"
  transport source args p.1 p.2.down.1 s (spent+2)
  for fuel in List.range (spent+2) do
    match genuine : Core.runStateful fuel (.initial core env s) with
    | .outOfFuel cp => have _ := Core.runStateful_resume genuine spent; check (decide (fuel<spent ∧ Core.runStateful spent cp=failed)) "every pre-fault checkpoint and exact resumed fault"
    | result => check (decide (spent≤fuel ∧ result=failed)) "same first fault and all later fuels"
end ParsedComputationTypeTableEffects
open ParsedComputationTypeTableEffects
def frontendParsedComputationTypeTableEffectTests : IO Unit := do
  for (l,base) in [(0,41),(1,99)] do for c in [false,true] do verify l base c
  for missing in [false,true] do for c in [false,true] do fault missing c
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedSourceLambdaEffects
set_option autoImplicit false
namespace Tests
namespace ParsedSourceLambdaEffects
open Solcore Solcore.Frontend
private abbrev Store := List RuntimeValue
private abbrev Captures := Resolved.LocalScope RuntimeValue
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def w (n : Nat) : RuntimeValue := .word ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def savedOwner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"SourceLambdaCallbacks",by decide⟩],by decide⟩⟩,153⟩
private def sid (index : Nat) : Resolved.LocalId := ⟨savedOwner,index⟩
private def callerOwner : Resolved.DeclarationId := {savedOwner with declarationIndex:=154}
private def cid (index : Nat) : Resolved.LocalId := ⟨callerOwner,index⟩
private def foreign : Resolved.LocalId := ⟨{savedOwner with declarationIndex:=900},700⟩
private def savedNames : LocalNameTable := [("x",sid 7),("r",sid 31),("x",foreign),("extra",sid 2)]
private def savedCaptured : Captures :=
  [(sid 32,.bool false),(sid 31,.cellRef .word 0),(sid 7,w 5),(sid 31,w 99),(foreign,.unit)]
private def callerNames : LocalNameTable := [("fetch",cid 7),("argument",cid 900),("r",cid 42)]
private def callerCaptured (source : Syntax.Expr) (argument : RuntimeValue) : Captures :=
  [(cid 900,argument),(cid 7,.sourceClosure source savedOwner savedNames savedCaptured),(cid 42,.cellRef .word 999)]
private theorem fresh : Resolved.freshLocalId savedOwner (savedNames.map Prod.snd) = sid 32 := by decide
private structure Original (source : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source name body
private def original : (source : Syntax.Expr) → Option (Original source)
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred name⟩]⟩ _ body⟩ => some ⟨name,body,.inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none name _⟩]⟩ _ body⟩ => some ⟨name,body,.typed⟩
  | _ => none
private def emptyCall (spelling : String) (source : Syntax.Expr) : Bool :=
  match source.value with
  | .call ⟨_,.identifier name⟩ ⟨_,[]⟩ => name.value == spelling
  | _ => false
private def touchReadSyntax (body : Syntax.Block) : Bool :=
  match body.value with
  | [⟨_,.expression touch true⟩,⟨_,.returnStmt (some ⟨_,.tuple ⟨_,
      [⟨_,.identifier parameter⟩,⟨_,.call ⟨_,.identifier load⟩ ⟨_,[⟨_,.identifier reference⟩]⟩⟩]⟩⟩)⟩] =>
      emptyCall "touch" touch && parameter.value == "x" && load.value == "load" && reference.value == "r"
  | _ => false

/- Independently supplied, deliberately limited callback semantics for these original calls.
They are neither the new relation recursively closed nor a canonical/general source evaluator. -/
private inductive Child (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Captures) :
    Store → Syntax.Expr → RuntimeValue → Store → Prop where
  | fetch {store source value target} (callSyntax : emptyCall "fetch" source = true)
      (named : LocalNameTable.Lookup names "fetch" target) (found : Resolved.LocalScope.Lookup captured target value) :
      Child owner names captured store source value (store ++ [.unit])
  | argument {store source value target} (callSyntax : emptyCall "argument" source = true)
      (named : LocalNameTable.Lookup names "argument" target) (found : Resolved.LocalScope.Lookup captured target value) :
      Child owner names captured store source value (store.set 0 (w 41))
private inductive Body (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Captures) :
    Store → Syntax.Block → RuntimeValue → Store → Prop where
  | touchRead {store source parameterId referenceId argument location value}
      (bodySyntax : touchReadSyntax source = true)
      (parameterName : LocalNameTable.Lookup names "x" parameterId)
      (parameter : Resolved.LocalScope.Lookup captured parameterId argument)
      (referenceName : LocalNameTable.Lookup names "r" referenceId)
      (reference : Resolved.LocalScope.Lookup captured referenceId (.cellRef .word location))
      (read : (store ++ [.bool true])[location]? = some value) :
      Body owner names captured store source (.pair argument value) (store ++ [.bool true])
private def noChild (_ : Resolved.DeclarationId) (_ : LocalNameTable) (_ : Captures)
    (_ : Store) (_ : Syntax.Expr) (_ : RuntimeValue) (_ : Store) : Prop := False
private def noBody (_ : Resolved.DeclarationId) (_ : LocalNameTable) (_ : Captures)
    (_ : Store) (_ : Syntax.Block) (_ : RuntimeValue) (_ : Store) : Prop := False
private theorem create (source : Syntax.Expr) (header : Original source) (store : Store) :
    SourceLambdaEvaluates noChild noBody savedOwner savedNames savedCaptured store source
      (.sourceClosure source savedOwner savedNames savedCaptured) store := .creation header.shape
private theorem call (source callee argument : Syntax.Expr) (header : Original source)
    (parameter : header.name.value = "x") (bodySyntax : touchReadSyntax header.body = true)
    (fetch : emptyCall "fetch" callee = true) (arg : emptyCall "argument" argument = true)
    (value : RuntimeValue) (span argumentsSpan : Syntax.SourceSpan) :
    SourceLambdaEvaluates Child Body callerOwner callerNames (callerCaptured source value)
      [w 23] ⟨span,.call callee ⟨argumentsSpan,[argument]⟩⟩ (.pair value (w 41)) [w 41,.unit,.bool true] := by
  have first : Child callerOwner callerNames (callerCaptured source value) [w 23] callee
      (.sourceClosure source savedOwner savedNames savedCaptured) [w 23,.unit] :=
    .fetch fetch .head (.tail (by decide) .head)
  have second : Child callerOwner callerNames (callerCaptured source value) [w 23,.unit] argument value [w 41,.unit] :=
    .argument arg (.tail (by decide) .head) .head
  have third : Body savedOwner (("x",sid 32)::savedNames) ((sid 32,value)::savedCaptured)
      [w 41,.unit] header.body (.pair value (w 41)) [w 41,.unit,.bool true] :=
    .touchRead bodySyntax .head .head (.tail (by decide) (.tail (by decide) .head))
      (.tail (by decide) (.tail (by decide) .head)) rfl
  exact .call header.shape first second (by simpa only [parameter,fresh] using third)
private theorem exact_rows (value : RuntimeValue) :
    ((("x",sid 32)::savedNames).map Prod.snd) = [sid 32,sid 7,sid 31,foreign,sid 2] ∧
    (((sid 32,value)::savedCaptured).map Prod.fst) = [sid 32,sid 32,sid 31,sid 7,sid 31,foreign] ∧
    Resolved.LocalScope.Lookup ((sid 32,value)::savedCaptured) (sid 32) value := ⟨rfl,rfl,.head⟩

private def parsed (text : String) (diagnostics : Nat := 0) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"source-lambda-callbacks.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && decide
        (source.span=Syntax.SourceSpan.fullFile file ∧ next.diagnostics.length=diagnostics)) "complete original Expr and diagnostics"
      if text="lam(x:comptime<A>)->comptime<B>{return x;}" then
        let [⟨diagnosticSpan,.constraintViolation .comptimeTypeInParameter⟩] := next.diagnostics
          | throw (IO.userError "actual comptime parameter diagnostic")
        check (decide (diagnosticSpan=⟨file.id,6,17⟩)) "diagnostics do not replace the preserved raw parameter syntax"
      if let .lambda keyword parameters returns body := source.value then
        check (source.span.contains keyword && source.span.contains parameters.span &&
          source.span.contains body.span && parameters.elements.all (fun p => parameters.span.contains p.span) &&
          returns.toList.all (fun annotation => source.span.contains annotation.span) &&
          body.value.all (fun statement => body.span.contains statement.span)) "all original lambda subranges"
      return source
  | .reject _ _ => throw (IO.userError "parser rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
private def inspectShape (text : String) (expected : Bool) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics
  match original source with
  | some header =>
      check expected "independent original unary shape"
      have decoded := sourceUnaryLambdaShape?_iff.mpr header.shape
      have _ : SourceUnaryLambdaShape source header.name header.body := sourceUnaryLambdaShape?_iff.mp decoded
      check (sourceUnaryLambdaShape? source == some (header.name,header.body)) "exact original name/body decoder"
      have created := create source header [w 5]
      have retained := (SourceLambdaEvaluates.creation_iff header.shape).mp created
      have _ := (SourceLambdaEvaluates.creation_iff (ChildEval:=noChild) (BodyEval:=noBody) header.shape).mpr retained
      check (decide (([w 5] : Store).map RuntimeValue.toCore? = [some (.word ⟨5,by decide⟩)]))
        "creation with empty body/child relations and unchanged actual store"
  | none => check (!expected && (sourceUnaryLambdaShape? source).isNone) "outside this unary shape only, not a language fault"
private def inspectCall (source callSource : Syntax.Expr) (value : RuntimeValue) : IO Unit := do
  let some header := original source | throw (IO.userError "saved original unary source")
  have generated := create source header [w 5]
  have _ := (SourceLambdaEvaluates.creation_iff header.shape).mp generated
  check (decide ((([w 5] : Store).map RuntimeValue.toCore?) ≠ ([w 23] : Store).map RuntimeValue.toCore?))
    "the same saved closure data is invoked with a different store, not a stored heap snapshot"
  match shape : callSource with
  | ⟨span,.call callee ⟨argumentsSpan,[argument]⟩⟩ =>
      if parameter : header.name.value = "x" then
        if bodySyntax : touchReadSyntax header.body = true then
          if fetch : emptyCall "fetch" callee = true then
            if arg : emptyCall "argument" argument = true then
              have evaluated := call source callee argument header parameter bodySyntax fetch arg value span argumentsSpan
              have decomposed := SourceLambdaEvaluates.call_iff.mp evaluated
              have rebuilt := SourceLambdaEvaluates.call_iff.mpr decomposed
              have _ : SourceLambdaEvaluates Child Body callerOwner callerNames (callerCaptured source value)
                  [w 23] callSource (.pair value (w 41)) [w 41,.unit,.bool true] := by
                rw [shape]; exact rebuilt
              have rows := exact_rows value
              check (decide ((((sid 32,value)::savedCaptured).map Prod.fst)=
                [sid 32,sid 32,sid 31,sid 7,sid 31,foreign])) "actual parameter prepended; old colliding capture remains"
              have _ : Resolved.LocalScope.Lookup ((sid 32,value)::savedCaptured) (sid 32) value := rows.2.2
              check (decide (savedOwner ≠ callerOwner ∧
                Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)=sid 32 ∧
                Resolved.freshLocalId callerOwner (callerNames.map Prod.snd)=cid 901)) "saved owner and names-only freshness"
              check (decide (([w 23,.unit] : Store).map RuntimeValue.toCore?=
                [some (.word ⟨23,by decide⟩),some .unit] ∧
                ([w 41,.unit] : Store).map RuntimeValue.toCore?=
                [some (.word ⟨41,by decide⟩),some .unit] ∧
                ([w 41,.unit,.bool true] : Store).map RuntimeValue.toCore?=
                [some (.word ⟨41,by decide⟩),some .unit,some (.bool true)])) "distinct callee, argument and body store effects"
              check (decide (value.toCore?=none ∧ (RuntimeValue.pair value (w 41)).toCore?=none))
                "actual nonprojectable argument/result passed directly, never projected by the raw rules"
            else throw (IO.userError "argument callback syntax")
          else throw (IO.userError "callee callback syntax")
        else throw (IO.userError "independent saved original body syntax")
      else throw (IO.userError "original parameter spelling")
  | _ => throw (IO.userError "original unary outer call")
end ParsedSourceLambdaEffects

open ParsedSourceLambdaEffects in
/-- Original source rules consume supplied callback witnesses; no closed evaluator or typing claim. -/
def frontendParsedSourceLambdaEffectTests : IO Unit := do
  inspectShape "lam(x){return x;}" true
  inspectShape "lam(x:A)->B{let x:A=x;return saved;}" true
  inspectShape "lam(x,)->A{return saved;}" true
  inspectShape "lam(){return saved;}" false
  inspectShape "lam(x,y){return x;}" false
  inspectShape "lam(comptime x:A){return x;}" false
  inspectShape "lam(comptime){return comptime;}" true 1
  inspectShape "lam(comptime:A){return comptime;}" true 1
  inspectShape "lam(comptime x){return x;}" false 1
  inspectShape "lam(x){let ;}" true 1
  inspectShape "lam(x:Missing)->Missing{return absent;}" true
  inspectShape "lam(x){return lam(y){return x;};}" true
  inspectShape "saved" false
  inspectShape "saved(x)" false
  inspectShape "(lam(x){return x;})" false
  inspectShape "let" false 2
  let staged := "lam(x:comptime<A>)->comptime<B>{return x;}"
  inspectShape staged true 1
  let stagedSource ← parsed staged 1
  let .lambda _ ⟨_,[⟨_,.typed none _ ⟨_,.comptime _ _ _⟩⟩]⟩ _ _ := stagedSource.value
    | throw (IO.userError "unmarked comptime type is raw uninterpreted data, not staging admission")
  let text := "lam(x:Unknown)->comptime<B>{touch();return (x,load(r));}"
  inspectShape text true
  let source ← parsed text
  let callSource ← parsed "fetch()(argument())"
  let payloadSource ← parsed "lam(){return saved;}"
  let value := Solcore.Frontend.RuntimeValue.sourceClosure payloadSource callerOwner [] [(sid 99,.bool true)]
  inspectCall source callSource value
  inspectCall source callSource (.coreClosure .bool .unit (.var 99) [value,.cellRef .word 700])

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendSourceLambdaBoundaryProperties
/-! Deliberately small callback models isolate raw success from body availability
and from each independent determinism premise. They are not a closed evaluator. -/
set_option autoImplicit false
namespace Tests.SourceLambdaBoundaries
open Solcore Solcore.Frontend
private abbrev Names := List (String × Resolved.LocalId)
private abbrev Captures := List (Resolved.LocalId × RuntimeValue)
private abbrev Store := List RuntimeValue
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"RawLambdaBoundaries",by decide⟩],by decide⟩⟩,153⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"raw-lambda-boundaries.sol"⟩,0,37⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def body : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref "x"))⟩]⟩
private def original : Syntax.Expr :=
  ⟨span,.lambda span ⟨span,[⟨span,.inferred ⟨span,"x"⟩⟩]⟩ none body⟩
private def invocation : Syntax.Expr := ⟨span,.call (ref "callee") ⟨span,[ref "argument"]⟩⟩
private def NoExpr (_ : Resolved.DeclarationId) (_ : Names) (_ : Captures)
    (_ : Store) (_ : Syntax.Expr) (_ : RuntimeValue) (_ : Store) : Prop := False
private def NoBody (_ : Resolved.DeclarationId) (_ : Names) (_ : Captures)
    (_ : Store) (_ : Syntax.Block) (_ : RuntimeValue) (_ : Store) : Prop := False

theorem creation_is_possible_when_both_callbacks_are_empty
    (source : Syntax.Expr) (name : Syntax.Identifier) (block : Syntax.Block)
    (shape : SourceUnaryLambdaShape source name block)
    (caller : Resolved.DeclarationId) (names : Names) (captured : Captures) (store : Store) :
    SourceLambdaEvaluates NoExpr NoBody caller names captured store source
      (.sourceClosure source caller names captured) store := .creation shape

theorem raw_creation_keeps_any_annotations_and_unevaluated_body
    (parameterAnnotation : Syntax.TypeExpr) (returnAnnotation : Option Syntax.TypeExpr)
    (block : Syntax.Block) (names : Names) (captured : Captures) (store : Store) :
    let source : Syntax.Expr :=
      ⟨span,.lambda span ⟨span,[⟨span,.typed none ⟨span,"x"⟩ parameterAnnotation⟩]⟩ returnAnnotation block⟩
    sourceUnaryLambdaShape? source = some (⟨span,"x"⟩,block) ∧
    SourceLambdaEvaluates NoExpr NoBody owner names captured store source
      (.sourceClosure source owner names captured) store := by
  exact ⟨sourceUnaryLambdaShape?_iff.mpr .typed,.creation .typed⟩

theorem absent_body_evidence_prevents_every_successful_unary_call
    (ChildEval : Resolved.DeclarationId → Names → Captures → Store → Syntax.Expr → RuntimeValue → Store → Prop)
    (caller : Resolved.DeclarationId) (names : Names) (captured : Captures)
    (initial finalStore : Store) (callee argument : Syntax.Expr) (value : RuntimeValue) :
    ¬ SourceLambdaEvaluates ChildEval NoBody caller names captured initial
      ⟨span,.call callee ⟨span,[argument]⟩⟩ value finalStore := by
  intro evaluated
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,impossible⟩ := SourceLambdaEvaluates.call_iff.mp evaluated
  exact impossible

/- The child fixture reads only these two literal identifiers; its argument
choice is explicitly controlled by a supplied set of Boolean outcomes. -/
private inductive ChoiceChild (allowed : Bool → Prop)
    (_caller : Resolved.DeclarationId) (_names : Names) (_captured : Captures) :
    Store → Syntax.Expr → RuntimeValue → Store → Prop where
  | callee {store : Store} : ChoiceChild allowed _ _ _ store (ref "callee")
      (.sourceClosure original owner [] []) store
  | argument {store : Store} {bit : Bool} : allowed bit →
      ChoiceChild allowed _ _ _ store (ref "argument") (.bool bit) store
private def fixedOutcome (source : Syntax.Expr) : Option RuntimeValue :=
  match source.value with
  | .identifier name =>
      if name.value = "callee" then some (.sourceClosure original owner [] [])
      else if name.value = "argument" then some (.bool false) else none
  | _ => none
private theorem fixedChild_outcome
    {caller : Resolved.DeclarationId} {names : Names} {captured : Captures}
    {initial finalStore : Store} {source : Syntax.Expr} {value : RuntimeValue}
    (evaluated : ChoiceChild (fun bit => bit = false) caller names captured initial source value finalStore) :
    fixedOutcome source = some value ∧ finalStore = initial := by
  cases evaluated with
  | callee => exact ⟨rfl,rfl⟩
  | argument bitFalse => cases bitFalse; exact ⟨rfl,rfl⟩
private theorem fixedChild_deterministic
    {caller : Resolved.DeclarationId} {names : Names} {captured : Captures}
    {initial : Store} {source : Syntax.Expr} {left right : RuntimeValue} {leftStore rightStore : Store}
    (first : ChoiceChild (fun bit => bit = false) caller names captured initial source left leftStore)
    (second : ChoiceChild (fun bit => bit = false) caller names captured initial source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  have firstResult := fixedChild_outcome first
  have secondResult := fixedChild_outcome second
  exact ⟨Option.some.inj (firstResult.1.symm.trans secondResult.1),
    firstResult.2.trans secondResult.2.symm⟩

/- This body has an intentional nondeterministic outcome, not source truth. -/
private inductive ChoiceBody (_caller : Resolved.DeclarationId) (_names : Names) (_captured : Captures) :
    Store → Syntax.Block → RuntimeValue → Store → Prop where
  | bit {store : Store} (value : Bool) : ChoiceBody _ _ _ store body (.bool value) store

private theorem bodyChoice (store : Store) (bit : Bool) :
    SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) ChoiceBody owner [] []
      store invocation (.bool bit) store :=
  .call .inferred .callee (.argument rfl) (.bit bit)

theorem deterministic_children_do_not_supply_body_determinism (store : Store) :
    (∀ {caller names captured initial source left leftStore right rightStore},
      ChoiceChild (fun bit => bit = false) caller names captured initial source left leftStore →
      ChoiceChild (fun bit => bit = false) caller names captured initial source right rightStore →
      left = right ∧ leftStore = rightStore) ∧
    SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) ChoiceBody owner [] []
      store invocation (.bool false) store ∧
    SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) ChoiceBody owner [] []
      store invocation (.bool true) store ∧
    (RuntimeValue.bool false ≠ .bool true) :=
  ⟨fixedChild_deterministic,bodyChoice store false,bodyChoice store true,by intro same; cases same⟩

/- A separate deterministic original return-x body reads the matching first
parameter name and value row, with arbitrary actual mixed value and suffix. -/
private inductive HeadBody (_caller : Resolved.DeclarationId) :
    Names → Captures → Store → Syntax.Block → RuntimeValue → Store → Prop where
  | returned {names : Names} {captured : Captures} {id : Resolved.LocalId}
      {value : RuntimeValue} {store : Store} :
      HeadBody _ (("x",id)::names) ((id,value)::captured) store body value store
private theorem headBody_deterministic
    {caller : Resolved.DeclarationId} {names : Names} {captured : Captures}
    {initial : Store} {source : Syntax.Block} {left right : RuntimeValue} {leftStore rightStore : Store}
    (first : HeadBody caller names captured initial source left leftStore)
    (second : HeadBody caller names captured initial source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases first
  cases second
  exact ⟨rfl,rfl⟩
private theorem argumentChoice (store : Store) (bit : Bool) :
    SourceLambdaEvaluates (ChoiceChild (fun _ => True)) HeadBody owner [] []
      store invocation (.bool bit) store :=
  .call .inferred .callee (.argument True.intro) .returned

theorem deterministic_bodies_do_not_supply_child_determinism (store : Store) :
    (∀ {caller names captured initial source left leftStore right rightStore},
      HeadBody caller names captured initial source left leftStore →
      HeadBody caller names captured initial source right rightStore →
      left = right ∧ leftStore = rightStore) ∧
    SourceLambdaEvaluates (ChoiceChild (fun _ => True)) HeadBody owner [] []
      store invocation (.bool false) store ∧
    SourceLambdaEvaluates (ChoiceChild (fun _ => True)) HeadBody owner [] []
      store invocation (.bool true) store ∧
    (RuntimeValue.bool false ≠ .bool true) :=
  ⟨headBody_deterministic,argumentChoice store false,argumentChoice store true,by intro same; cases same⟩

theorem separate_callback_determinism_laws_recover_exact_call_results
    (store : Store) {value : RuntimeValue} {finalStore : Store}
    (evaluated : SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) HeadBody
      owner [] [] store invocation value finalStore) : value = .bool false ∧ finalStore = store := by
  have exactCall : SourceLambdaEvaluates (ChoiceChild (fun bit => bit = false)) HeadBody
      owner [] [] store invocation (.bool false) store :=
    .call .inferred .callee (.argument rfl) .returned
  exact SourceLambdaEvaluates.deterministic
    (ChildEval := ChoiceChild (fun bit => bit = false)) (BodyEval := HeadBody)
    fixedChild_deterministic headBody_deterministic evaluated exactCall

end Tests.SourceLambdaBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendSourceLambdaEvaluationProperties
/-! These independently supplied callbacks only read original local references and
return through explicit blocks. They are not a closed source-language evaluator.
Mixed values, duplicate rows and raw stores need no typing or Core projection. -/
set_option autoImplicit false
namespace Tests.FrontendSourceLambdaEvaluation
open Solcore Solcore.Frontend

private inductive Child (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) :
    List RuntimeValue → Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | reference {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {name : Syntax.Identifier} {id : Resolved.LocalId} {value : RuntimeValue}
      (named : LocalNameTable.Lookup names name.value id)
      (found : Resolved.LocalScope.Lookup captured id value) :
      Child owner names captured store ⟨span,.identifier name⟩ value store
private inductive Body (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) :
    List RuntimeValue → Syntax.Block → RuntimeValue → List RuntimeValue → Prop where
  | returned {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {source : Syntax.Expr} {value : RuntimeValue}
      (evaluated : Child owner names captured store source value store) :
      Body owner names captured store ⟨span,[⟨span,.returnStmt (some source)⟩]⟩ value store
  | block {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {value : RuntimeValue}
      (evaluated : Body owner names captured store ⟨span,statements⟩ value store) :
      Body owner names captured store ⟨span,[⟨span,.block statements⟩]⟩ value store
private theorem childDet {o names captured store source value final other otherStore}
    (first : Child o names captured store source value final)
    (second : Child o names captured store source other otherStore) :
    value=other ∧ final=otherStore := by
  cases first with
  | reference named found =>
      cases second with
      | reference otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound,rfl⟩
private theorem bodyDet {o names captured store source value final other otherStore}
    (first : Body o names captured store source value final)
    (second : Body o names captured store source other otherStore) :
    value=other ∧ final=otherStore := by
  induction first with
  | returned evaluated => cases second with | returned other => exact childDet evaluated other
  | block evaluated ih => cases second with | block other => exact ih other

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def returned (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Nat → Syntax.Block
  | 0 => ⟨span,[⟨span,.returnStmt (some (reference span name))⟩]⟩
  | n+1 => ⟨span,[⟨span,.block (returned span name n).value⟩]⟩
private theorem returnedPath (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) (n : Nat) :
    Body o names captured store (returned span name n) value store := by
  induction n with
  | zero => exact .returned (.reference named found)
  | succ n ih => cases n <;> exact .block ih
private def lambda (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨span,.lambda span ⟨span,[⟨name.span,match annotation with
    | none => .inferred name | some type => .typed none name type⟩]⟩ returns body⟩
private theorem originalShape (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda span name annotation returns body) name body := by
  cases annotation <;> first | exact .inferred | exact .typed
private def call (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span,.call (reference span ⟨span,"f"⟩) ⟨span,[reference span ⟨span,"argument"⟩]⟩⟩
private def callerNames (f x : Resolved.LocalId) (tail : LocalNameTable) : LocalNameTable :=
  ("f",f)::("argument",x)::tail
private def callerValues (f x : Resolved.LocalId) (closure argument : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (f,closure)::(x,argument)::tail
private theorem invoke (span : Syntax.SourceSpan) (caller saved : Resolved.DeclarationId)
    (names callerTail : LocalNameTable) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (f x : Resolved.LocalId) (different : f≠x) (store : List RuntimeValue)
    (source : Syntax.Expr) (name : Syntax.Identifier) (body : Syntax.Block)
    (argument result : RuntimeValue) (shape : SourceUnaryLambdaShape source name body)
    (path : Body saved ((name.value,Resolved.freshLocalId saved (names.map Prod.snd))::names)
      ((Resolved.freshLocalId saved (names.map Prod.snd),argument)::captured) store body result store) :
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure source saved names captured) argument callerSuffix)
      store (call span) result store :=
  .call shape (.reference .head .head)
    (.reference (.tail (by change "f" ≠ "argument"; decide) .head) (.tail different .head)) path
private theorem freshNe {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {spelling : String} {id : Resolved.LocalId} (named : LocalNameTable.Lookup names spelling id) :
    Resolved.freshLocalId owner (names.map Prod.snd) ≠ id := by
  intro equal
  have member : id ∈ names.map Prod.snd := List.mem_map_of_mem named.mem
  exact Resolved.freshLocalId_not_mem owner _ (equal ▸ member)

theorem original_creation_retains_every_row_and_uninterpreted_annotation
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (body : Syntax.Block) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    sourceUnaryLambdaShape? (lambda span name annotation returns body)=some (name,body) ∧
    SourceLambdaEvaluates Child Body owner names captured store (lambda span name annotation returns body)
      (.sourceClosure (lambda span name annotation returns body) owner names captured) store := by
  have shape := originalShape span name annotation returns body
  exact ⟨sourceUnaryLambdaShape?_iff.mpr shape,.creation shape⟩
theorem creation_iff_preserves_the_whole_original_source_and_actual_store
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (body : Syntax.Block) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store final : List RuntimeValue) (value : RuntimeValue) :
    SourceLambdaEvaluates Child Body owner names captured store (lambda span name annotation returns body) value final ↔
      value=.sourceClosure (lambda span name annotation returns body) owner names captured ∧ final=store :=
  SourceLambdaEvaluates.creation_iff (originalShape span name annotation returns body)

theorem arbitrary_depth_parameter_shadow_returns_the_actual_mixed_argument
    (span : Syntax.SourceSpan) (parameter : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (f x : Resolved.LocalId) (different : f≠x)
    (store : List RuntimeValue) (argument : RuntimeValue) :
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter annotation returns (returned span parameter n))
        saved names captured) argument callerSuffix) store (call span) argument store :=
  invoke span caller saved names callerTail captured callerSuffix f x different store _ _ _ argument argument
    (originalShape _ _ _ _ _) (returnedPath _ _ _ _ _ _ _ _ .head .head n)

theorem captured_reference_uses_saved_rows_not_the_caller_scope
    (span : Syntax.SourceSpan) (parameter selected : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (notParameter : parameter.value≠selected.value)
    (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (f x id : Resolved.LocalId) (different : f≠x)
    (store : List RuntimeValue) (argument result : RuntimeValue)
    (named : LocalNameTable.Lookup names selected.value id) (found : Resolved.LocalScope.Lookup captured id result) :
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter annotation returns (returned span selected n))
        saved names captured) argument callerSuffix) store (call span) result store :=
  invoke span caller saved names callerTail captured callerSuffix f x different store _ _ _ argument result
    (originalShape _ _ _ _ _) (returnedPath _ _ _ _ _ _ _ _
      (.tail notParameter named) (.tail (freshNe named) found) n)

theorem all_successful_reference_callback_runs_are_value_and_store_deterministic
    {owner names captured store source left leftStore right rightStore}
    (first : SourceLambdaEvaluates Child Body owner names captured store source left leftStore)
    (second : SourceLambdaEvaluates Child Body owner names captured store source right rightStore) :
    left=right ∧ leftStore=rightStore :=
  SourceLambdaEvaluates.deterministic (ChildEval := Child) (BodyEval := Body)
    (fun a b => childDet a b) (fun a b => bodyDet a b) first second

theorem actual_calls_expose_the_saved_scope_and_all_three_store_edges
    {owner names captured store span result final}
    (evaluated : SourceLambdaEvaluates Child Body owner names captured store (call span) result final) :
    ∃ source saved savedNames savedCaptured parameter body calleeStore argument argumentStore,
      SourceUnaryLambdaShape source parameter body ∧
      Child owner names captured store (reference span ⟨span,"f"⟩)
        (.sourceClosure source saved savedNames savedCaptured) calleeStore ∧
      Child owner names captured calleeStore (reference span ⟨span,"argument"⟩) argument argumentStore ∧
      Body saved ((parameter.value,Resolved.freshLocalId saved (savedNames.map Prod.snd))::savedNames)
        ((Resolved.freshLocalId saved (savedNames.map Prod.snd),argument)::savedCaptured)
        argumentStore body result final := SourceLambdaEvaluates.call_iff.mp evaluated

theorem environment_only_fresh_collision_keeps_both_literal_rows_but_selects_argument
    (span : Syntax.SourceSpan) (parameter : Syntax.Identifier) (n : Nat)
    (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (f x : Resolved.LocalId) (different : f≠x)
    (store : List RuntimeValue) (argument old : RuntimeValue) :
    let fresh := Resolved.freshLocalId saved (names.map Prod.snd)
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter none none (returned span parameter n))
        saved names ((fresh,old)::captured)) argument callerSuffix) store (call span) argument store ∧
    Resolved.LocalScope.Lookup ((fresh,argument)::(fresh,old)::captured) fresh argument ∧
    ((fresh,argument)::(fresh,old)::captured).tail=(fresh,old)::captured ∧
    fresh.owner=saved ∧ fresh∉names.map Prod.snd := by
  dsimp only
  exact ⟨arbitrary_depth_parameter_shadow_returns_the_actual_mixed_argument
    span parameter none none n caller saved names callerTail _ callerSuffix f x different store argument,
    .head,rfl,Resolved.freshLocalId_owner _ _,Resolved.freshLocalId_not_mem _ _⟩

theorem first_captured_duplicate_wins_even_under_arbitrary_unselected_suffix
    (span : Syntax.SourceSpan) (n : Nat) (caller saved : Resolved.DeclarationId)
    (names callerTail : LocalNameTable) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (f x id : Resolved.LocalId) (different : f≠x) (store : List RuntimeValue)
    (argument first second : RuntimeValue) :
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span ⟨span,"parameter"⟩ none none
        (returned span ⟨span,"saved"⟩ n)) saved (("saved",id)::("saved",x)::names)
        ((id,first)::(id,second)::captured)) argument callerSuffix) store (call span) first store :=
  captured_reference_uses_saved_rows_not_the_caller_scope span _ _ none none n
    (by change "parameter" ≠ "saved"; decide)
    caller saved _ callerTail _ callerSuffix f x id different store argument first .head .head

theorem source_closure_argument_needs_no_core_projection_to_be_returned
    (span : Syntax.SourceSpan) (parameter : Syntax.Identifier) (n : Nat)
    (caller saved actualOwner : Resolved.DeclarationId) (names callerTail actualNames : LocalNameTable)
    (captured callerSuffix actualCaptured : Resolved.LocalScope RuntimeValue)
    (f x : Resolved.LocalId) (different : f≠x) (store : List RuntimeValue) (actualSource : Syntax.Expr) :
    let actual := RuntimeValue.sourceClosure actualSource actualOwner actualNames actualCaptured
    actual.toCore?=none ∧
    SourceLambdaEvaluates Child Body caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter none none (returned span parameter n))
        saved names captured) actual callerSuffix) store (call span) actual store :=
  ⟨by simp [RuntimeValue.toCore?],arbitrary_depth_parameter_shadow_returns_the_actual_mixed_argument
    span parameter none none n caller saved names callerTail captured callerSuffix f x different store _⟩

private def otherOwner (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {owner with declarationIndex:=owner.declarationIndex+1}
theorem different_caller_owner_and_foreign_high_ids_preserve_actual_core_closure_argument
    (span : Syntax.SourceSpan) (n high : Nat) (saved foreign : Resolved.DeclarationId)
    (foreignOwner : foreign≠saved) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (a b : Core.Ty) (core : Core.Expr) (actualCaptures : List RuntimeValue) :
    otherOwner saved≠saved ∧
    Resolved.freshLocalId saved [⟨foreign,high⟩,⟨saved,7⟩]=Resolved.freshLocalId saved [⟨saved,7⟩] ∧
    SourceLambdaEvaluates Child Body (otherOwner saved)
      (callerNames ⟨otherOwner saved,0⟩ ⟨otherOwner saved,1⟩ [])
      (callerValues ⟨otherOwner saved,0⟩ ⟨otherOwner saved,1⟩
        (.sourceClosure (lambda span ⟨span,"p"⟩ none none (returned span ⟨span,"p"⟩ n)) saved
          [("foreign",⟨foreign,high⟩),("p",⟨saved,7⟩)] captured)
        (.coreClosure a b core actualCaptures) callerSuffix) store (call span)
      (.coreClosure a b core actualCaptures) store := by
  refine ⟨?_,?_,?_⟩
  · intro equal
    have index := congrArg Resolved.DeclarationId.declarationIndex equal
    simp [otherOwner] at index
  · exact Resolved.freshLocalId_cons_of_ne_owner saved _ ⟨foreign,high⟩ foreignOwner
  · apply arbitrary_depth_parameter_shadow_returns_the_actual_mixed_argument
    intro equal
    have index := congrArg Resolved.LocalId.binderIndex equal
    cases index

end Tests.FrontendSourceLambdaEvaluation
end
