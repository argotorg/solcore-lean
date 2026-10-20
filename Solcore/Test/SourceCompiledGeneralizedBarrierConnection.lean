import Solcore.SourceSemantics.SourceCompiledGeneralizedBarrierConnection
import Solcore.Test.SourceSelectedTemplateInventory

/-! The unchanged public-compilation fixture checks template scope in the
original checked function, including a nonempty flexible template predicate.
The proof consumer retains that exact original and its rigid specialization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledGeneralizedBarrierConnection
open Solcore Frontend SourceInference SourceSemantics TypeSystem
open SourceCompiledLocalFinalization

private theorem original_scope {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) :
    ∃ original ∈ compiled.program.functions,
      row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution original ∧
      (∀ owner, ContainsLocalSchemeTemplate original.typedBody owner →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
          metavariable ∈ owner.binder.scheme.quantified) := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  refine ⟨selected.original, selected.originalMember, selected.specialized, ?_⟩
  intro owner contains
  rw [selected.body.source] at contains
  exact SourceCompiledGeneralizedBarrierConnection.original_template_scoped accepted member selected contains

def main : IO Unit := do
  let workspace := Tests.SourceSelectedTemplateInventory.workspace
  let .ok checked := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some entry := checked.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut rows := 0
    let mut templates := 0
    let mut variables := 0
    for row in compiled.plan.specializations.attach do
      have _actualOriginal := original_scope compiledEq row.property
      let some original := compiled.program.functions.find?
          (fun function => function.declaration == row.val.function.declaration)
        | throw (IO.userError "missing original checked function")
      for owner in localSchemeTemplateOwners original.typedBody do
        let free := TypedTraitResolution.predicateVariables owner.requirement.predicate
        unless free.all owner.binder.scheme.quantified.contains do
          throw (IO.userError "original finalized predicate escapes its complete owner")
        let some solved := original.solvedRequirements.find?
            (fun solved => solved.id == owner.requirement.templateRequirement)
          | throw (IO.userError "original finalized template has no solved row")
        unless solved.predicate == owner.requirement.predicate do
          throw (IO.userError "original finalized predicate changed in solved ledger")
        templates := templates + 1
        variables := variables + free.length
      rows := rows + 1
    unless rows == 2 && templates == 1 && variables > 0 do
      throw (IO.userError "original template scope coverage is empty or changed")
    IO.println s!"PASS original selected template scope: rows={rows}, templates={templates}, flexible variables={variables}"

end Tests.SourceCompiledGeneralizedBarrierConnection
