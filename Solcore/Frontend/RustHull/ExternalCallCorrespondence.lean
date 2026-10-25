import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport

/-! The operation boundary used by the common recursive proof. Concrete effect
implementations discharge this interface using their independent state model
and the actual accepted builtin code. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence ScalarExecution PureCallCorrespondence

def ExternalCallPreservation {σ : Type} (supported : String → Prop)
    (model : StateModel σ) (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) : Prop :=
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
      ∃ target finalStore,
        ResultRel lowered.type result target ∧
        Core.Evaluates environment initialStore (lowered.expression.rename mapping) target finalStore ∧
        StateRel model world final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧
        ClosuresPreserved argumentStore finalStore

theorem ExternalCallPreservation.empty {σ : Type} (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) :
    ExternalCallPreservation (fun _ => False) model slots effects := by
  intro functions name type sources initial final result impossible
  cases impossible

end Solcore.Frontend.RustHull.DerivationCorrespondence
