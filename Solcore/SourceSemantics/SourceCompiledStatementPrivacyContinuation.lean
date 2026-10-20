import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceInferenceStatementPrivacyContinuation
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyReturnFinalization

/-! Original selected syntax positions carry their real later inference and
finalization. Only privacy of the newly chosen quantifiers at the declaration
boundary remains for the generalization proof to establish. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

/-- The actual checker result supplies the continuation through all later
statements, return unification and finalization for a selected source position. -/
theorem BodySelection.statementPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source) :
    ∃ occurrence : StatementPrivacyOccurrence
        (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
        source (Ty.productMany selected.signature.returnTypes)
        (initial selected.signature selected.body.declaration) selected.body.body.state,
      ∀ protectedVars : List TypeVarId,
        (∀ v ∈ protectedVars, v.index < occurrence.result.state.inference.next) →
        LiveBindersSafe protectedVars occurrence.result.state →
        (∀ type, Safe protectedVars occurrence.result.state type →
          Avoids protectedVars (selected.body.finalized.substitution.apply type)) ∧
        (∀ requirement ∈ selected.body.body.state.requirements,
          requirement ∉ occurrence.result.state.requirements →
          ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
            Avoids protectedVars (selected.body.finalized.substitution.apply type)) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence⟩ := statementPrivacyOccurrence_of_position progress.initialReady
    (State.initial_requirementsWellFormed _ _ _) (State.initial_nodesBelowNextOccurrence _ _ _)
    catalog formation canonical progress.returnBelow selected.body.inferred position
  refine ⟨occurrence,?_⟩
  intro protectedVars bound live
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    selected.returns_closed checked
  have continuation := occurrence.privacy protectedVars bound live
    (safe_closed protectedVars occurrence.result.state closed)
  constructor
  · intro type safe
    exact selected.finishPrivacy checked protectedVars type (continuation.1 type safe)
  · intro requirement member fresh type typeMember
    exact selected.finishPrivacy checked protectedVars type
      (continuation.2 requirement member fresh type typeMember)

/-- A successful public compilation chooses the original body and all its
actual statement continuations; no whole-program body typing is assumed. -/
theorem compile_statement_privacy {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∃ occurrence : StatementPrivacyOccurrence
            (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
            source (Ty.productMany selected.signature.returnTypes)
            (initial selected.signature selected.body.declaration) selected.body.body.state,
          ∀ protectedVars : List TypeVarId,
            (∀ v ∈ protectedVars, v.index < occurrence.result.state.inference.next) →
            LiveBindersSafe protectedVars occurrence.result.state →
            (∀ type, Safe protectedVars occurrence.result.state type →
              Avoids protectedVars (selected.body.finalized.substitution.apply type)) ∧
            (∀ requirement ∈ selected.body.body.state.requirements,
              requirement ∉ occurrence.result.state.requirements →
              ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
                Avoids protectedVars (selected.body.finalized.substitution.apply type)) := by
  obtain ⟨selected⟩ := of_compile accepted member
  exact ⟨selected,fun position => selected.toBodySelection.statementPrivacy
    (SourceCoreCompiler.compile_checked_source accepted) position⟩


theorem Selected.statementPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source) :
    ∃ occurrence : StatementPrivacyOccurrence
        (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
        source (Ty.productMany selected.signature.returnTypes)
        (initial selected.signature selected.body.declaration) selected.body.body.state,
      ∀ protectedVars : List TypeVarId,
        (∀ v ∈ protectedVars, v.index < occurrence.result.state.inference.next) →
        LiveBindersSafe protectedVars occurrence.result.state →
        (∀ type, Safe protectedVars occurrence.result.state type →
          Avoids protectedVars (selected.body.finalized.substitution.apply type)) ∧
        (∀ requirement ∈ selected.body.body.state.requirements,
          requirement ∉ occurrence.result.state.requirements →
          ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
            Avoids protectedVars (selected.body.finalized.substitution.apply type)) :=
  selected.toBodySelection.statementPrivacy checked position

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
