import Solcore.SourceSemantics.SourceCompiledStatementPrivacyResume

/-! The same selected checker invocation supplies every entry condition for
a statement position and its exact continuation through the whole body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledGeneralizedSoundness

theorem Selected.statementResume {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source) :
    Nonempty (StatementPrivacyResume (checkingContext selected.toBodySelection) source
      (Ty.productMany selected.signature.returnTypes)
      (initial selected.signature selected.body.declaration) selected.body.body
      (ResumeEntryInvariant selected (Ty.productMany selected.signature.returnTypes))) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    Ty.variablesBelow_productMany
      ((formation.functions selected.signature selected.signatureMember).2.1.variablesBelow 0)
  have bodyOwner := Detail.inferStatementsFuel_preserves_owner selected.body.inferred
  have returnOwner := congrArg State.Header.owner (Detail.unify_state_header selected.body.unified)
  have owner : (initial selected.signature selected.body.declaration).owner =
      (evidenceSource selected.toBodySelection).owner := bodyOwner.symm.trans returnOwner.symm
  apply selected_statement_privacy_resume checked (.refl selected.toBodySelection) progress.initialReady
    (State.initial_nodesBelowNextOccurrence _ _ _) _ progress.returnBelow
    (by rw [selected.body.returned_nodes]; exact List.prefix_refl _)
    progress.final_substitution selected.body.inferred position
  refine ⟨?_,fun binder member => safe_closed _ _ closed,owner⟩
  apply GeneralizedActualStateInvariant.initial
  intro entry present
  obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp present
  rfl

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
