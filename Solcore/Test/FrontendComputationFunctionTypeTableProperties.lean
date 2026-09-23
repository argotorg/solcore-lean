import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

/-! Original symbolic headers, parameter binding and same-name lets have independent
meaning before checker transport. Arbitrary actual records retain every capture.
The deliberately incorrect checker below tests equations, not source soundness. -/
set_option autoImplicit false
namespace Tests.FrontendComputationFunctionTypeTable
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s,.named ⟨s,⟨⟨⟨s,"Payload"⟩,[]⟩⟩⟩ none⟩
private def types (a : Core.Ty) : TypeNameTable := [(["Payload"],a),(["Payload"],.bool)]
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"x"⟩⟩
private def body (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,
  [⟨s,.letDecl ⟨s,"x"⟩ (some (named s)) (some (ref s))⟩,⟨s,.returnStmt (some (ref s))⟩]⟩
private def parameter (s : Syntax.SourceSpan) : Syntax.FunctionParameter := ⟨s,.typed none ⟨s,"x"⟩ (named s)⟩
private def entry (s : Syntax.SourceSpan) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"transported"⟩,none,⟨s,[parameter s]⟩,⟨none,none⟩,
    some ⟨s,⟨s,[named s]⟩⟩,none⟩,body s⟩⟩
private def initial (o : Resolved.DeclarationId) (a : Core.Ty) := LocalTypeInputs.empty.bindFresh o "x" a
private def core : Core.Expr := .letE (.var 0) (.var 0)
private def compiled (o : Resolved.DeclarationId) (a : Core.Ty) : CompiledRuntimeFunction := ⟨initial o a,core,a⟩
private def inputs (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :=
  LocalInputs.empty.bindFresh o "x" arg.type arg.value arg.valueTyped
private def prepared (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) : PreparedRuntimeFunction :=
  ⟨inputs o arg,core,arg.type⟩
private theorem header (s : Syntax.SourceSpan) (a : Core.Ty) : RuntimeFunctionHeader (types a) (entry s).value.signature a :=
  ⟨rfl,rfl,rfl,rfl,.single (.named .head)⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RuntimeParametersDeclare (types a) o [parameter s] (initial o a) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty,LocalTypeInputs.names]) .nil
private theorem provenance (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types a) o (initial o a) (body s) core a :=
  .binding (.named .head) (.pure (.identifier .head) (.var .head) (.var .head))
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem compilation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RecursiveComputationFunctionCompiles (types a) o (entry s) (compiled o a) :=
  ⟨header s a,declared s o a,provenance s o a⟩
private theorem bound (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    RuntimeParametersBind (types arg.type) o [parameter s] [arg] (inputs o arg) :=
  .cons (.named .head) (by simp [LocalInputs.empty,LocalInputs.names]) .nil
private theorem preparation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    RecursiveComputationFunctionPrepares (types arg.type) o (entry s) [arg] (prepared o arg) :=
  ⟨header s arg.type,bound s o arg,provenance s o arg.type⟩
private theorem raw (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost o (inputs o arg).names (inputs o arg).environment
      store (body s) arg.value store 4 := by
  change ComputationReturnTreeEvaluatesWithCost RecursiveLocalComputationEvaluatesWithCost o
    [("x",_)] [(_,arg.value)] store (body s) arg.value store 4
  refine ComputationReturnTreeEvaluatesWithCost.binding (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    (initializerCost := 1) (tailCost := 1) (boundValue := arg.value) (middleStore := store) ?_ ?_
  · exact .pure (.identifier .head .head)
  · exact .expression (.pure (.identifier .head .head))
private theorem manual (value : Core.Value) (retained : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 4 ⟨.eval core (value::retained),k,store⟩ ⟨.ret value,k,store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
private theorem compileSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    compileRecursiveComputationFunction? (types a) o (entry s)=some (compiled o a) :=
  (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr (compilation s o a)
private theorem prepareSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    prepareRecursiveComputationFunction? (types arg.type) o (entry s) [arg]=some (prepared o arg) :=
  (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr (preparation s o arg)

theorem independent_original_records_survive_every_meaning_extension
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types arg.type) next) :
    RecursiveComputationFunctionCompiles next o (entry s) (compiled o arg.type) ∧
    RecursiveComputationFunctionPrepares next o (entry s) [arg] (prepared o arg) :=
  ⟨(compilation s o arg.type).extend_types extension,(preparation s o arg).extend_types extension⟩
theorem complete_compilation_and_value_bearing_preparation_survive_append
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (extras : TypeNameTable) :
    compileRecursiveComputationFunction? (types arg.type++extras) o (entry s)=some (compiled o arg.type) ∧
    prepareRecursiveComputationFunction? (types arg.type++extras) o (entry s) [arg]=some (prepared o arg) :=
  ⟨compileComputationFunction?_some_of_extends (TypeNameTable.Extends.append_right _ _) (compileSome s o arg.type),
    prepareComputationFunction?_some_of_extends (TypeNameTable.Extends.append_right _ _) (prepareSome s o arg)⟩
theorem independent_raw_cost_and_literal_pending_path
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (store : Core.Store) (k : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost o (inputs o arg).names (inputs o arg).environment
      store (body s) arg.value store 4 ∧
    Core.Steps 4 ⟨.eval core (inputs o arg).environment.values,k,store⟩ ⟨.ret arg.value,k,store⟩ :=
  ⟨raw s o arg store,manual arg.value [] store k⟩
theorem every_full_run_preserves_exact_actual_values_and_store
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types arg.type) next) (fuel : Nat) (store : Core.Store) :
    runRecursiveComputationFunction? next o (entry s) [arg] fuel store=
      some (arg.type,Core.runStateful fuel (.initial core [arg.value] store)) := by
  apply runComputationFunction?_some_of_extends extension
  simp only [runComputationFunction?,prepareSome s o arg]; rfl
theorem exact_completion_and_all_genuine_resumptions_survive_append
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (extras : TypeNameTable) (fuel extra : Nat) (store : Core.Store) :
    (runRecursiveComputationFunction? (types arg.type++extras) o (entry s) [arg] fuel store=
      some (arg.type,.done arg.value store) ↔ 4≤fuel) ∧
    ∀ cp, runRecursiveComputationFunction? (types arg.type++extras) o (entry s) [arg] fuel store=
      some (arg.type,.outOfFuel cp) →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial core [arg.value] store) := by
  rw [every_full_run_preserves_exact_actual_values_and_store s o arg _ (TypeNameTable.Extends.append_right _ _) fuel store]
  simp only [Option.some.injEq,Prod.mk.injEq,true_and]
  exact ⟨(manual arg.value [] store []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
private theorem hiddenMutual (a hidden : Core.Ty) :
    TypeNameTable.Extends (types a) [(["Payload"],a),(["Payload"],hidden)] ∧
    TypeNameTable.Extends [(["Payload"],a),(["Payload"],hidden)] (types a) := by
  constructor <;> intro key type found <;> cases found with
  | head => exact .head
  | tail different found => cases found with
    | head => exact False.elim (different rfl)
    | tail _ found => cases found
theorem hidden_rows_keep_all_optional_records_for_an_arbitrary_fixed_checker
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (a hidden : Core.Ty) (o : Resolved.DeclarationId) (source : Syntax.FunctionDecl)
    (args : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    compileComputationFunction? checkChild (types a) o source=
      compileComputationFunction? checkChild [(["Payload"],a),(["Payload"],hidden)] o source ∧
    prepareComputationFunction? checkChild (types a) o source args=
      prepareComputationFunction? checkChild [(["Payload"],a),(["Payload"],hidden)] o source args ∧
    runComputationFunction? checkChild (types a) o source args fuel store=
      runComputationFunction? checkChild [(["Payload"],a),(["Payload"],hidden)] o source args fuel store :=
  ⟨compileComputationFunction?_eq_of_mutual_extends (hiddenMutual a hidden).1 (hiddenMutual a hidden).2 o source,
    prepareComputationFunction?_eq_of_mutual_extends (hiddenMutual a hidden).1 (hiddenMutual a hidden).2 o source args,
    runComputationFunction?_eq_of_mutual_extends (hiddenMutual a hidden).1 (hiddenMutual a hidden).2 o source args fuel store⟩

private def bogus (a : Core.Ty) (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  some (.var 99,a)
private def graph (a : Core.Ty) (names : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) (expression : Core.Expr) (type : Core.Ty) := bogus a names context source=some (expression,type)
private def badCore : Core.Expr := .letE (.var 99) (.var 99)
private def badPrepared (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) : PreparedRuntimeFunction :=
  ⟨inputs o arg,badCore,arg.type⟩
private theorem bogusSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    prepareComputationFunction? (bogus arg.type) (types arg.type) o (entry s) [arg]=some (badPrepared o arg) :=
  (prepareComputationFunction?_iff (ChildElab := graph arg.type) Iff.rfl).mpr
    ⟨header s arg.type,bound s o arg,.binding (.named .head) rfl (.expression rfl)⟩
private def badState (arg : TypedRuntimeArgument) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 99) [arg.value],[.letBody (.var 99) [arg.value]],store⟩
private theorem bogusRun (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types arg.type) next) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) next o (entry s) [arg] fuel store=
      some (arg.type,Core.runStateful fuel (.initial badCore [arg.value] store)) := by
  apply runComputationFunction?_some_of_extends extension
  simp only [runComputationFunction?,bogusSome s o arg]; rfl
theorem incorrect_checker_exhaustion_is_transported_without_becoming_safety
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (extras : TypeNameTable) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (types arg.type++extras) o (entry s) [arg] 0 store=
      some (arg.type,.outOfFuel (.initial badCore [arg.value] store)) := by
  rw [bogusRun s o arg _ (TypeNameTable.Extends.append_right _ _)]; rfl
theorem incorrect_checker_fault_keeps_the_exact_saved_state_for_all_positive_fuel
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (extras : TypeNameTable) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (types arg.type++extras) o (entry s) [arg] (fuel+1) store=
      some (arg.type,.fault (.unboundVariable 99) (badState arg store)) := by
  rw [bogusRun s o arg _ (TypeNameTable.Extends.append_right _ _)]
  simp [Core.runStateful,Core.advance,badCore,badState,Core.State.initial]
end Tests.FrontendComputationFunctionTypeTable
