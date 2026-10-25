import Solcore.Frontend.RustHull.LifecycleBuiltinInputs
import Solcore.Frontend.RustHull.AccountLifecycleDestroyCorrespondence
import Solcore.Frontend.RustHull.RuntimeLifecycleStateCorrespondence

/-! SELFDESTRUCT follows the actual static guard, account update and stopping
branch. Shared state, catalog identities and installed callbacks remain related. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
open Core Correspondence ScalarExecution PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout CallPassive)
open RuntimeCallModeEffectsCorrespondence (ModeHandlers model base_related)
open RuntimeChildCallEffectsCorrespondence (Anchors Context)

private def destruction (state : RuntimeLifecycleSemantics.State) (beneficiary : Word) :
    Except Word (StorageSemantics.World × StorageSemantics.Words) :=
  AccountLifecycleSemantics.destroy state.runtime.runtime.runtime.runtime.runtime.storage.world
    state.runtime.runtime.balances state.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
    state.runtime.runtime.runtime.runtime.runtime.storage.complete

private def afterDestruction (state : RuntimeLifecycleSemantics.State) :
    Except Word (StorageSemantics.World × StorageSemantics.Words) → RuntimeLifecycleSemantics.State
  | .error _ => state
  | .ok next => RuntimeLifecycleSemantics.updated state next.1 next.2

private theorem Inputs.destroy_evaluates
    {references : References} {mapping : Renaming} {environment : Environment} {store : Store}
    {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout}
    {world : World} {state : Semantics.State RuntimeLifecycleSemantics.State}
    {beneficiary : Word} {beneficiaryExpr : Core.Expr}
    (inputs : Inputs references mapping environment store layout state.external)
    (passive : CallPassive layout slots)
    (before : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (supplied : Evaluates environment store beneficiaryExpr (.word beneficiary) store) :
    ∃ final, Evaluates environment store
      (AccountLifecycle.destroy (references.world.rename mapping) (references.balances.rename mapping)
        ((Core.Expr.loadCell references.address).rename mapping) beneficiaryExpr
        ((Core.Expr.loadCell references.complete).rename mapping))
      (StorageCorrespondence.unitResult (destruction state.external beneficiary)) final ∧
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := afterDestruction state.external (destruction state.external beneficiary)} final ∧
      ClosuresPreserved store final := by
  obtain ⟨accounts, same, linked, worldRead⟩ := RuntimeChildCallEffectsCorrespondence.linked_related before
  have shared := (RuntimeCallEffectsCorrespondence.shared_resources (base_related before)).1
  have separate : layout.storage.world ≠ layout.balances := by
    have distinct := shared.distinct
    simp only [AccountCallCorrespondence.SharedLocations.all, RuntimeCallEffectsCorrespondence.sharedLocations,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
    exact distinct.1.2.2.1
  obtain ⟨final, evaluated, finalWorld, finalBalances, frame⟩ :=
    AccountLifecycleCorrespondence.destroy_preserves accounts state.external.runtime.runtime.balances
      layout.storage.world layout.balances state.external.runtime.runtime.runtime.runtime.runtime.storage.address
      beneficiary state.external.runtime.runtime.runtime.runtime.runtime.storage.complete
      (.pair inputs.world (.pair inputs.balances (.pair inputs.address (.pair supplied inputs.complete))))
      worldRead shared.balances separate
  have projected := AccountLifecycleCorrespondence.destroy_source accounts state.external.runtime.runtime.balances
    state.external.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
    state.external.runtime.runtime.runtime.runtime.runtime.storage.complete
  change accounts.map Prod.fst = state.external.runtime.runtime.runtime.runtime.runtime.storage.world at same
  rw [same] at projected
  change _ = destruction state.external beneficiary at projected
  have finalLinked := AccountLifecycleCorrespondence.destroy_links linked state.external.runtime.runtime.balances
    state.external.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
    state.external.runtime.runtime.runtime.runtime.runtime.storage.complete
  cases outcome : AccountLifecycleCorrespondence.destroyAccounts accounts state.external.runtime.runtime.balances
      state.external.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
      state.external.runtime.runtime.runtime.runtime.runtime.storage.complete with
  | error reason =>
      have source : destruction state.external beneficiary = .error reason := by simpa only [outcome, Except.map] using projected.symm
      simp only [outcome, AccountLifecycleCorrespondence.nextAccounts, AccountLifecycleCorrespondence.nextBalances] at evaluated finalWorld finalBalances finalLinked
      obtain ⟨related, retained⟩ := RuntimeLifecycleCorrespondence.updated_preserves passive before
        ⟨accounts, same, finalLinked, finalWorld⟩ finalBalances frame
      refine ⟨final, ?_, ?_, retained⟩
      · simpa only [source, Core.Expr.rename, StorageCorrespondence.unitResult] using evaluated
      · simpa only [source, afterDestruction, RuntimeLifecycleSemantics.updated, RuntimeCallEffectsSemantics.withShared, RuntimeCallEffectsSemantics.shared] using related
  | ok next =>
      rcases next with ⟨nextAccounts, nextBalances⟩
      have source : destruction state.external beneficiary = .ok (nextAccounts.map Prod.fst, nextBalances) := by
        simpa only [outcome, Except.map] using projected.symm
      simp only [outcome, AccountLifecycleCorrespondence.nextAccounts, AccountLifecycleCorrespondence.nextBalances] at evaluated finalWorld finalBalances finalLinked
      obtain ⟨related, retained⟩ := RuntimeLifecycleCorrespondence.updated_preserves passive before
        ⟨nextAccounts, rfl, finalLinked, finalWorld⟩ finalBalances frame
      refine ⟨final, ?_, ?_, retained⟩
      · simpa only [source, StorageCorrespondence.unitResult, Core.Expr.rename] using evaluated
      · simpa only [source, afterDestruction, RuntimeLifecycleSemantics.updated, RuntimeCallEffectsSemantics.withShared, RuntimeCallEffectsSemantics.shared] using related

/-- Actual lowering, source destruction and evaluated arguments determine the
Core result and the complete related runtime state. -/
theorem preserves {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    {beneficiary : Word} {result : Semantics.Result Semantics.Value} {finalState : RuntimeLifecycleSemantics.State}
    {targets : List Core.Value} {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {layout : Layout} {baseline : Nat → Option Value}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout}
    {world : World} {state : Semantics.State RuntimeLifecycleSemantics.State}
    (compiled : lowerBuiltin scope "selfdestruct" expected arguments = .ok lowered)
    (computed : RuntimeLifecycleSemantics.Destroy beneficiary state.external result finalState)
    (related : ArgumentsRel arguments [.word beneficiary] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (balancesMember : ⟨"balances", WordMapping.type, layout.balances⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components rfl compiled
  have arity : arguments.length = 1 := by
    simpa only [List.length_map, List.length_range] using inner_arity rawCompiled
  obtain ⟨beneficiaryExpr, input, rfl, same, rfl⟩ := one_word related words arity
  cases same
  obtain ⟨references, invalid, stopped, referencesCompiled, invalidCompiled, stoppedCompiled, rfl⟩ := inner_components rawCompiled
  cases typed
  cases loweredEqual
  have runtime' := runtime.temporary .word (.word beneficiary)
  have observed := inputs referencesCompiled runtime' worldMember balancesMember addressMember completeMember staticMember stateRelated
  have supplied : Evaluates (.word beneficiary :: environment) store
      ((projectArgument 0 1 (.var 0)).rename mapping.lift) (.word beneficiary) store := .var rfl
  cases computed with
  | staticFrame isStatic =>
      obtain ⟨target, final, resultRelated, evaluated, finalRelated, retained⟩ :=
        RuntimeLifecycleCorrespondence.terminate_preserves invalidCompiled runtime' passive
          memorySizeMember exitMember offsetMember sizeMember stateRelated
      refine ⟨target, final, resultRelated, ?_, finalRelated, retained⟩
      apply LanguageResult.bind_success .unit packed
      rw [expression_rename]
      exact .ifTrue (by simpa only [isStatic, Core.Expr.rename, References.rename, bundleValues] using observed.isStatic) evaluated
  | rejected reason notStatic destroyed =>
      obtain ⟨final, evaluated, finalRelated, retained⟩ := observed.destroy_evaluates callPassive stateRelated supplied
      change destruction state.external beneficiary = .error reason at destroyed
      simp only [destroyed, afterDestruction, StorageCorrespondence.unitResult] at evaluated finalRelated
      refine ⟨.inLeft .unit (.word reason), final, .language _, ?_, finalRelated, retained⟩
      apply LanguageResult.bind_success .unit packed
      rw [expression_rename]
      apply Evaluates.ifFalse (by simpa only [notStatic, Core.Expr.rename, References.rename, bundleValues] using observed.isStatic)
      exact LocalSequence.discard_failure .unit evaluated
  | completed nextWorld nextBalances notStatic destroyed =>
      obtain ⟨middle, evaluated, middleRelated, firstRetained⟩ := observed.destroy_evaluates callPassive stateRelated supplied
      change destruction state.external beneficiary = .ok (nextWorld, nextBalances) at destroyed
      simp only [destroyed, afterDestruction, StorageCorrespondence.unitResult] at evaluated middleRelated
      obtain ⟨target, final, resultRelated, stoppedEvaluated, finalRelated, secondRetained⟩ :=
        RuntimeLifecycleCorrespondence.terminate_preserves stoppedCompiled (runtime'.prepend [.unit]) passive
          memorySizeMember exitMember offsetMember sizeMember middleRelated
      refine ⟨target, final, resultRelated, ?_, finalRelated, firstRetained.trans secondRetained⟩
      apply LanguageResult.bind_success .unit packed
      rw [expression_rename]
      apply Evaluates.ifFalse (by simpa only [notStatic, Core.Expr.rename, References.rename, bundleValues] using observed.isStatic)
      apply LocalSequence.discard_success .unit evaluated
      rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
      have shifted : ((Renaming.insertion 0).comp mapping.lift) = (fun index => 1 + mapping.lift index) := by
        funext index
        simp [Renaming.comp, Renaming.insertion, Nat.add_comm]
      rw [shifted]
      exact stoppedEvaluated

end Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
