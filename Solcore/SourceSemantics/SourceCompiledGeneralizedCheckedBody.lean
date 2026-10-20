import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedBodyEntry

/-! The actual recursive result supplies one body-facts witness for every
compatible input context of the same checked declaration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

private theorem input_context_unique {owner : Resolved.DeclarationId}
    {base left right : SourceSemantics.Context} {binders : List TypedBinder} {types : List Ty}
    (first : MonoBindersExtend owner base binders types left)
    (second : MonoBindersExtend owner base binders types right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons _ head _ ih =>
      cases second with
      | cons _ otherHead otherTail =>
          cases head
          cases otherHead
          exact ih otherTail

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head tail ih =>
      cases right with
      | nil => simp at same
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at same
          have equal := NodeId.statement.inj same.1
          subst other
          exact congrArg (List.cons head) (ih same.2)

theorem checked_statements_of_recursive_of_interfaces_for {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    {callProvenance : CallIndex → Prop}
    (rootHere : callProvenance selected.inferenceCall)
    (sound : StatementsRootedSoundnessFor callProvenance selected fuel) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original := by
  obtain ⟨target, entry, finalContext, facts, _, _, _, typed, matching⟩ :=
    body_of_recursive_of_interfaces_for selected checked interfaces rootHere sound
  have header := selected_body_header selected checked
  have returnFixed : selected.body.finalized.substitution.apply
      (Ty.productMany selected.signature.returnTypes) = Ty.productMany selected.signature.returnTypes := by
    have typeEq : selected.body.finalized.type = Ty.productMany selected.signature.returnTypes := by
      simpa only [selected.body.checkedResult] using header.result_type
    exact (Detail.finalize_type selected.body.finalization).symm.trans typeEq
  have factsType : facts.type = Ty.productMany selected.signature.returnTypes := by
    calc
      facts.type = selected.body.finalized.substitution.apply selected.body.body.type := matching.type_eq
      _ = selected.body.finalized.substitution.apply (Ty.productMany selected.signature.returnTypes) :=
        Detail.unify_then_finalize_eq selected.body.unified selected.body.finalization
      _ = _ := returnFixed
  have actualRoots : selected.original.typedBody.roots =
      selected.body.body.statements.map NodeId.statement := by
    rw [selected.body.source]
    exact finalize_statementRoots selected.body.finalization
  intro statements roots
  have same := roots_injective (roots.symm.trans actualRoots)
  subst statements
  refine ⟨facts, factsType, ?_⟩
  intro lexicalContext extension
  have contextEq := input_context_unique extension entry.inputs
  subst lexicalContext
  refine ⟨finalContext, ?_⟩
  simpa only [selected.body.source, returnFixed, checkingContext, context] using typed


theorem checked_statements_of_recursive_of_interfaces {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (sound : StatementsRootedSoundness selected fuel) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original := by
  exact checked_statements_of_recursive_of_interfaces_for (callProvenance := fun _ => True) selected checked interfaces True.intro
    (statementsRootedSoundnessFor_true sound)

/-- This is the original checked body's complete declarative judgment.
The caller supplies the recursive assembly at the same selected receipt. -/
theorem checked_body_of_recursive_of_interfaces {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (sound : StatementsRootedSoundness selected fuel) :
    CheckedBodyHasType compiled.program.signatures selected.signature selected.original :=
  checkedBodyHasType_ofStatements selected.body.accepted
    (checked_statements_of_recursive_of_interfaces selected checked interfaces sound)

theorem checked_statements_of_recursive {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (sound : StatementsRootedSoundness selected fuel) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original :=
  checked_statements_of_recursive_of_interfaces selected checked
    (selected_original_interfaces selected member) sound

theorem checked_body_of_recursive {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (sound : StatementsRootedSoundness selected fuel) :
    CheckedBodyHasType compiled.program.signatures selected.signature selected.original :=
  checked_body_of_recursive_of_interfaces selected checked
    (selected_original_interfaces selected member) sound

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
