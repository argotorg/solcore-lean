import Solcore.Frontend.RustHull.LinkedStorageBuiltinCorrespondence
import Solcore.Frontend.RustHull.RuntimeEffectsCorrespondence

/-! A separate, deterministic execution witness carries exact catalog links
through a builtin. It can be combined with ordinary effect preservation without
changing the existing source or runtime models. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedBuiltinWorldCorrespondence
open Correspondence ScalarExecution PureCallCorrespondence

abbrev Anchors := List CatalogWorldCorrespondence.Anchor

def ExternalWorldPreservation {σ : Type} (supported : String → Prop)
    (model : StateModel σ) (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ)
    (anchors : Anchors) (location : Nat) (sourceWorld : σ → StorageSemantics.World) : Prop :=
  ∀ {functions name type sources initial final result}, supported name →
    functions.find? (·.name == name) = none →
    Semantics.EvalCall functions effects name type sources initial result final →
    ∀ {typeFuel expected}, lowerType typeFuel type = .ok expected →
    ∀ {scope arguments lowered}, lowerBuiltin scope name expected arguments = .ok lowered →
    ∀ {world mapping environment initialStore argumentStore targets codes locations captured},
      ArgumentsRel arguments sources targets →
      Core.Evaluates environment initialStore ((packArguments arguments).expression.rename mapping)
        (.inRight .word (bundleValues targets)) argumentStore →
      EffectEnvironmentRel slots scope mapping environment →
      StateRel model world initial argumentStore →
      InstalledGlobals codes locations captured argumentStore →
      RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld initial.external) location argumentStore →
      ∃ target finalStore, Core.Evaluates environment initialStore (lowered.expression.rename mapping) target finalStore ∧
        RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld final.external) location finalStore

theorem memory_frame {layout : RuntimeEffectsCorrespondence.Layout}
    {anchors : Anchors} {source : StorageSemantics.World} {initial final : Core.Store}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors source layout.storage.world initial)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors source layout.storage.world final := by
  have distinct := layout.distinct
  simp [StorageBuiltinCorrespondence.Locations.all] at distinct
  exact linked.read_preserved (fun _ found => frame.read _ _
    (by intro same; simp_all) (by intro same; simp_all) found)

end Solcore.Frontend.RustHull.LinkedBuiltinWorldCorrespondence
