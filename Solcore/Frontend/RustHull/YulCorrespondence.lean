import Solcore.Frontend.RustHull.ExternalCallCorrespondence

/-! The assembly boundary used by the common recursive proof. An eligible
inline Yul block is an external effect: the effect specification of the block
simulates the actual `YulLowering.lowerStatements` code of the statement. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence ScalarExecution

def AssemblyPreservation {σ : Type} (supported : String → Prop) (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) : Prop :=
  ∀ {functions : List Function} {sourceEnvironment : Semantics.Environment} {body : List YulStmt}
    {initial : Semantics.State σ} {control : Semantics.Control} {final : Semantics.State σ},
    YulFragment.Eligible supported body →
    effects.assembly functions sourceEnvironment body initial control final →
    ∀ {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat}
      {captured : Core.Environment} {span : Option Span},
      StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
        ⟨.assembly body, span⟩ initial control final

theorem AssemblyPreservation.empty {σ : Type} (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) :
    AssemblyPreservation (fun _ => False) model slots effects := by
  intro functions sourceEnvironment body initial control final eligible
  exact (YulFragment.Eligible.empty eligible).elim

/-- Effects without an assembly rule meet the obligation vacuously. -/
theorem AssemblyPreservation.unreachable {σ : Type} {supported : String → Prop} {model : StateModel σ}
    {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ}
    (unreachable : ∀ functions environment body initial control final,
      effects.assembly functions environment body initial control final → False) :
    AssemblyPreservation supported model slots effects := by
  intro functions sourceEnvironment body initial control final _ assembled
  exact (unreachable _ _ _ _ _ _ assembled).elim

end Solcore.Frontend.RustHull.DerivationCorrespondence
