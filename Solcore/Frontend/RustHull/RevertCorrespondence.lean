import Solcore.Frontend.RustHull.ExternalCallCorrespondence

/-! The revert boundary used by the common recursive proof. Hull's explicit
revert is an external effect: the effect specification of the statement
simulates the actual `Effects.revertMessage` code, which writes the message
and exits through the revert termination. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence ScalarExecution

def RevertPreservation {σ : Type} (supported : String → Prop) (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) : Prop :=
  ∀ {message : String} {initial : Semantics.State σ} {control : Semantics.Control} {final : σ},
    supported "revert" → effects.revert message initial.external control final →
    ∀ {scope exit}, Effects.revertMessage scope message = .ok exit →
    ∀ {world mapping environment store},
      EffectEnvironmentRel slots scope mapping environment → StateRel model world initial store →
      ∃ reason finalStore, control = .fault (.language reason) ∧
        Core.Evaluates environment store (exit.rename mapping) (.inLeft .unit (.word reason)) finalStore ∧
        StateRel model world {initial with external := final} finalStore ∧ ClosuresPreserved store finalStore

theorem RevertPreservation.empty {σ : Type} (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) :
    RevertPreservation (fun _ => False) model slots effects := by
  intro message initial control final impossible
  cases impossible

/-- Effects without a revert rule meet the obligation vacuously. -/
theorem RevertPreservation.unreachable {σ : Type} {supported : String → Prop} {model : StateModel σ}
    {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ}
    (unreachable : ∀ message state control final, effects.revert message state control final → False) :
    RevertPreservation supported model slots effects := by
  intro message initial control final _ reverted
  exact (unreachable _ _ _ _ reverted).elim

/-- An eligible revert statement simulates its lowering: the actual exit code
fails with the termination reason and the statement propagates it. -/
theorem RevertPreservation.statement {supported : String → Prop} {σ : Type} {model : StateModel σ}
    {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {sourceEnvironment : Semantics.Environment}
    (reverting : RevertPreservation supported model slots effects) {span : Option Span} {message : String}
    {state : Semantics.State σ} {control : Semantics.Control} {final : σ}
    (available : supported "revert") (executed : effects.revert message state.external control final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨.revert message, span⟩ state control {state with external := final} := by
  intro fuel scope result loops expression compiled covered world mapping environment store _ _ runtime heap installed
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨exit, exitCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨reason, finalStore, rfl, exitEvaluated, finalHeap, closures⟩ :=
        reverting available executed exitCompiled runtime heap
      exact ⟨[], _, finalStore, .language reason, Core.LanguageResult.bind_failure _ exitEvaluated,
        by simpa only [List.append_nil] using finalHeap, installed.preserved closures, closures⟩

end Solcore.Frontend.RustHull.DerivationCorrespondence
