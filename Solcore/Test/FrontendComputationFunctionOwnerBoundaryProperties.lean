import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties

/-! Covariance is an equation, not child-checker correctness. The graph below
is explicitly an artificial interface, never original-source elaboration.
An injective nonsurjective owner map alone does not supply that equation. -/
set_option autoImplicit false
namespace Tests.FrontendComputationFunctionOwnerBoundary
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,"A"⟩,[]⟩⟩⟩ none⟩
private def table (a : Core.Ty) : TypeNameTable := [(["A"],a)]
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"x"⟩⟩
private def parameter (s : Syntax.SourceSpan) : Syntax.FunctionParameter := ⟨s,.typed none ⟨s,"x"⟩ (named s)⟩
private def entry (s : Syntax.SourceSpan) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"checkerBoundary"⟩,none,⟨s,[parameter s]⟩,⟨none,none⟩,some ⟨s,⟨s,[named s]⟩⟩,none⟩,
    ⟨s,[⟨s,.letDecl ⟨s,"x"⟩ (some (named s)) (some (ref s))⟩,⟨s,.returnStmt (some (ref s))⟩]⟩⟩⟩
private def staticInputs (o : Resolved.DeclarationId) (a : Core.Ty) := LocalTypeInputs.empty.bindFresh o "x" a
private def inputs (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :=
  LocalInputs.empty.bindFresh o "x" arg.type arg.value arg.valueTyped
private theorem header (s : Syntax.SourceSpan) (a : Core.Ty) : RuntimeFunctionHeader (table a) (entry s).value.signature a :=
  ⟨rfl,rfl,rfl,rfl,.single (.named .head)⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RuntimeParametersDeclare (table a) o [parameter s] (staticInputs o a) := .cons (.named .head) (by simp) .nil
private theorem bound (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    RuntimeParametersBind (table arg.type) o [parameter s] [arg] (inputs o arg) := .cons (.named .head) (by simp) .nil
private def bogus (a : Core.Ty) (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) := some (.var 99,a)
private def graph (a : Core.Ty) (names : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) := bogus a names context source=some (core,type)
private def badCore : Core.Expr := .letE (.var 99) (.var 99)
private def badCompiled (o : Resolved.DeclarationId) (a : Core.Ty) : CompiledRuntimeFunction := ⟨staticInputs o a,badCore,a⟩
private def badPrepared (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) : PreparedRuntimeFunction := ⟨inputs o arg,badCore,arg.type⟩
private theorem bogusSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    prepareComputationFunction? (bogus arg.type) (table arg.type) o (entry s) [arg]=some (badPrepared o arg) :=
  (prepareComputationFunction?_iff (ChildElab := graph arg.type) Iff.rfl).mpr
    ⟨header s arg.type,bound s o arg,.binding (.named .head) rfl (.expression rfl)⟩
private theorem bogusRun (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (table arg.type) (mapping o) (entry s) [arg] fuel store=
      some (arg.type,Core.runStateful fuel (.initial badCore [arg.value] store)) := by
  rw [runComputationFunction?_mapOwner mapping injective _ (by intros; rfl)]
  simp only [runComputationFunction?,bogusSome s o arg]; rfl
private def badState (arg : TypedRuntimeArgument) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 99) [arg.value],[.letBody (.var 99) [arg.value]],store⟩

theorem all_three_whole_option_laws_require_covariance_but_no_soundness
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (a : Core.Ty) (types : TypeNameTable) (o : Resolved.DeclarationId) (source : Syntax.FunctionDecl)
    (args : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    compileComputationFunction? (bogus a) types (mapping o) source=
      (compileComputationFunction? (bogus a) types o source).map (fun c => {c with inputs := (c.inputs.mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))}) ∧
    prepareComputationFunction? (bogus a) types (mapping o) source args=
      (prepareComputationFunction? (bogus a) types o source args).map (fun p => {p with inputs := (p.inputs.mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))}) ∧
    runComputationFunction? (bogus a) types (mapping o) source args fuel store=
      runComputationFunction? (bogus a) types o source args fuel store :=
  ⟨compileComputationFunction?_mapOwner mapping injective _ (by intros; rfl) types o source,
   prepareComputationFunction?_mapOwner mapping injective _ (by intros; rfl) types o source args,
   runComputationFunction?_mapOwner mapping injective _ (by intros; rfl) types o source args fuel store⟩
theorem original_source_is_well_typed_but_the_covariant_checker_is_not_correct
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    RecursiveComputationFunctionCompiles (table arg.type) o (entry s) ⟨staticInputs o arg.type,.letE (.var 0) (.var 0),arg.type⟩ ∧
    prepareComputationFunction? (bogus arg.type) (table arg.type) o (entry s) [arg]=some (badPrepared o arg) ∧
    ¬ Core.HasType [arg.type] (.var 99) arg.type := by
  refine ⟨⟨header s _,declared s o _,.binding (.named .head)
    (.pure (.identifier .head) (.var .head) (.var .head))
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))⟩,bogusSome s o arg,?_⟩
  intro h
  cases h with | var impossible => simp at impossible
theorem the_bad_checker_preserves_genuine_exhaustion_and_full_resumption
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (table arg.type) (mapping o) (entry s) [arg] 0 store=
      some (arg.type,.outOfFuel (.initial badCore [arg.value] store)) ∧
    ∀ extra,Core.runStateful extra (.initial badCore [arg.value] store)=Core.runStateful (0+extra) (.initial badCore [arg.value] store) := by
  rw [bogusRun mapping injective s o arg]
  exact ⟨rfl,Core.runStateful_resume (show Core.runStateful 0 (.initial badCore [arg.value] store)=.outOfFuel _ from rfl)⟩
theorem every_positive_fuel_keeps_the_same_actual_fault_state
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (table arg.type) (mapping o) (entry s) [arg] (fuel+1) store=
      some (arg.type,.fault (.unboundVariable 99) (badState arg store)) := by
  rw [bogusRun mapping injective s o arg]
  simp [Core.runStateful,Core.advance,badCore,badState,Core.State.initial]

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"FunctionOwnerBoundary",by decide⟩],by decide⟩⟩,138⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private def sensitive (a : Core.Ty) (names : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if names.lookup? "x"=some ⟨owner,0⟩ then some (.var 0,a) else none
private def direct (s : Syntax.SourceSpan) : Syntax.FunctionDecl :=
  {(entry s) with value := {(entry s).value with body := ⟨s,[⟨s,.returnStmt (some (ref s))⟩]⟩}}
private def sensitiveGraph (a : Core.Ty) (names : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) := sensitive a names context source=some (core,type)
private theorem sensitiveSome (s : Syntax.SourceSpan) (arg : TypedRuntimeArgument) :
    prepareComputationFunction? (sensitive arg.type) (table arg.type) owner (direct s) [arg]=some ⟨inputs owner arg,.var 0,arg.type⟩ :=
  (prepareComputationFunction?_iff (ChildElab := sensitiveGraph arg.type) Iff.rfl).mpr
    ⟨header s _,bound s owner arg,.expression (by simp [sensitiveGraph,sensitive,inputs,LocalNameTable.lookup?,Resolved.freshLocalId_empty])⟩
private theorem sensitiveNone (s : Syntax.SourceSpan) (arg : TypedRuntimeArgument) :
    prepareComputationFunction? (sensitive arg.type) (table arg.type) (shift owner) (direct s) [arg]=none := by
  have checkedHeader : interpretRuntimeFunctionHeader? (table arg.type) (direct s).value.signature=some arg.type :=
    interpretRuntimeFunctionHeader?_iff.mpr (header s arg.type)
  have checkedParameters : bindRuntimeParameters? (table arg.type) (shift owner)
      (direct s).value.signature.parameters.elements [arg]=some (inputs (shift owner) arg) := (bound s (shift owner) arg).complete
  simp only [prepareComputationFunction?,checkedHeader,checkedParameters,bind,Option.bind_some]
  simp [elaborateComputationReturnTree?,direct,entry,sensitive,inputs,LocalInputs.toTypeInputs,
    LocalTypeInputs.names,LocalInputs.bindFresh,LocalInputs.empty,LocalInputs.ids,LocalNameTable.lookup?,owner,shift,Resolved.freshLocalId_empty]
theorem injective_nonsurjective_maps_do_not_replace_checker_covariance
    (s : Syntax.SourceSpan) (arg : TypedRuntimeArgument) :
    Function.Injective shift ∧ (¬ Function.Surjective shift) ∧
    prepareComputationFunction? (sensitive arg.type) (table arg.type) owner (direct s) [arg]=some ⟨inputs owner arg,.var 0,arg.type⟩ ∧
    prepareComputationFunction? (sensitive arg.type) (table arg.type) (shift owner) (direct s) [arg]=none := by
  refine ⟨injective,?_,sensitiveSome s arg,sensitiveNone s arg⟩
  intro surjective
  obtain ⟨id,same⟩ := surjective {owner with declarationIndex := 0}
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change id.declarationIndex+10=0 at impossible
  omega
theorem failed_child_covariance_is_an_actual_unequal_option
    (s : Syntax.SourceSpan) (a : Core.Ty) :
    sensitive a (LocalNameTable.mapIds (ownerLocalIdMap shift) (staticInputs owner a).names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) (staticInputs owner a).context) (ref s) ≠
      sensitive a (staticInputs owner a).names (staticInputs owner a).context (ref s) := by
  simp [sensitive,staticInputs,LocalTypeInputs.bindFresh_names,LocalNameTable.mapIds,LocalNameTable.lookup?,
    ownerLocalIdMap,owner,shift,Resolved.freshLocalId_empty]
end Tests.FrontendComputationFunctionOwnerBoundary
