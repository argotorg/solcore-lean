import Solcore.Frontend.RustHull.LifecycleBuiltinCompiler
import Solcore.Frontend.RustHull.RuntimeCallModeStateCorrespondence

/-! SELFDESTRUCT references use the actual caller account, world and ledger
cells supplied by runtime initialization. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
open Core Correspondence ScalarExecution EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout)
open RuntimeCallModeEffectsCorrespondence (ModeHandlers model base_related)
open RuntimeChildCallEffectsCorrespondence (Anchors Context)

structure Inputs (references : References) (mapping : Renaming) (environment : Environment)
    (store : Store) (layout : Layout) (state : RuntimeCallEffectsSemantics.State) : Prop where
  world : Evaluates environment store (references.world.rename mapping) (.cellRef AccountState.type layout.storage.world) store
  balances : Evaluates environment store (references.balances.rename mapping) (.cellRef WordMapping.type layout.balances) store
  address : Evaluates environment store ((Core.Expr.loadCell references.address).rename mapping)
    (.word state.runtime.runtime.runtime.runtime.runtime.storage.address) store
  complete : Evaluates environment store ((Core.Expr.loadCell references.complete).rename mapping)
    (.bool state.runtime.runtime.runtime.runtime.runtime.storage.complete) store
  isStatic : Evaluates environment store ((Core.Expr.loadCell references.isStatic).rename mapping)
    (.bool state.runtime.runtime.runtime.runtime.runtime.storage.isStatic) store

theorem inputs {scope : Scope} {references : References} (compiled : CompiledReferences scope references)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {layout : Layout} {baseline : Nat → Option Value} {image : Option (List UInt8)} {handlers : ModeHandlers layout}
    {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Store}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (balancesMember : ⟨"balances", WordMapping.type, layout.balances⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    Inputs references mapping environment store layout state.external := by
  have storage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeCallEffectsCorrespondence.account_related (base_related related)))))
  exact ⟨reference_evaluates runtime worldMember compiled.world store,
    reference_evaluates runtime balancesMember compiled.balances store,
    .loadCell (reference_evaluates runtime addressMember compiled.address store) storage.address,
    .loadCell (reference_evaluates runtime completeMember compiled.complete store) storage.complete,
    .loadCell (reference_evaluates runtime staticMember compiled.isStatic store) storage.isStatic⟩

end Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
