import Solcore.Frontend.SourceInference.CatalogedDirectCallInference
import Solcore.SourceSemantics.SourceCompiledTemplateCallOrigins
import Solcore.SourceSemantics.SourceCompiledSelectedFinalization

/-! The actual selected declaration catalog follows every finalized template
emitter through solving and specialization. No source body typing is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledCatalogedCallOrigins
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceCompiledLocalFinalization CatalogedDirectCallEvents

variable {catalog : List Resolved.DeclarationId}

theorem solved_call {nodes : List Node} {requirement : RequirementId}
    (emitter : HasCall catalog nodes requirement) (substitution : Substitution) :
    HasCall catalog (nodes.map (Node.applySubstitution substitution)) requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged⟩ := emitter
  refine ⟨node.applySubstitution substitution,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, instantiation.applySubstitution substitution, ?_, issued, cataloged⟩
  change node.form.applySubstitution substitution = _
  rw [form]
  rfl

theorem specialized_call {source : TypedSource} {requirement : RequirementId}
    (emitter : HasCall catalog source.nodes requirement) (substitution : ParameterSubstitution) :
    HasCall catalog (SourceSpecialization.applyTypedSource substitution source).nodes requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged⟩ := emitter
  refine ⟨SourceSpecialization.applyExpressionNode substitution node,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, SourceSpecialization.applyInstantiation substitution instantiation, ?_, issued, cataloged⟩
  change SourceSpecialization.applyExpressionForm substitution node.form = _
  rw [form]
  rfl

namespace BodyReceipt
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}

theorem direct_origins (receipt : BodyReceipt environment signatures signature fuel checked) :
    Origins (signatures.functions.map (·.id)) receipt.returned :=
  Progress.unify receipt.unified (initializedStatements_origins receipt.inferred)

theorem finalized_template_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    HasCall (signatures.functions.map (·.id)) receipt.finalized.typedSource.nodes id := by
  have emitter := direct_origins receipt id (SourceCompiledTemplateCallOrigins.BodyReceipt.finalized_template_direct receipt member)
  rw [receipt.resources.source_eq]
  exact solved_call emitter receipt.finalized.substitution

end BodyReceipt

/-- The same actual selected receipt supplies all source-template emitters,
including templates owned by nested local binders. -/
theorem selected_template_emitter
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) {id : RequirementId}
    (member : id ∈ sourceLocalSchemeTemplateIds row.function.typedBody) :
    HasCall (compiled.program.signatures.functions.map (·.id)) row.function.typedBody.nodes id := by
  rw [selected.source] at member ⊢
  have original : id ∈ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource := by
    change id ∈ sourceLocalSchemeTemplateIds (StructuralSubstitution.applyTypedSource row.parameterSubstitution selected.body.finalized.typedSource) at member
    simpa only [StructuralSubstitution.sourceLocalSchemeTemplateIds_applyTypedSource] using member
  exact specialized_call
    (BodyReceipt.finalized_template_emitter selected.body original) row.parameterSubstitution

theorem receipt_ready_origins
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins (context.signatures.functions.map (·.id)) initial) :
    Origins (context.signatures.functions.map (·.id)) receipt.ready :=
  inferExprFuel_origins_progress receipt.child origins

/-- Raw public compilation itself supplies the checked body and provenance;
there is no direct-ID, body-typing, or ownership premise. -/
theorem compile_template_emitters
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∀ id ∈ sourceLocalSchemeTemplateIds row.function.typedBody,
      HasCall (compiled.program.signatures.functions.map (·.id)) row.function.typedBody.nodes id := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  exact fun _ present => selected_template_emitter selected present

end Solcore.SourceSemantics.SourceCompiledCatalogedCallOrigins
