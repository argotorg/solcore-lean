import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
import Solcore.SourceSemantics.Staging.RecursiveErasure

/-! Actual named specialization views select the global body's own staging
scope. This connects independent recursively staged body runs to independent
global applications. Original source instantiation, full evidence and ordered
allocation stay explicit. Native body meaning and full expression admission
are separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStagedCalls
open Frontend SourceInference SourceCoreStageContracts
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedPreparedStageScopes
open Staging.Recursive

namespace Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)

theorem global_view : prepared.view = globalView
    (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
    prepared.view.evidence prepared.compilation.statements := by
  dsimp only [RecursiveNamedPublicSpecializationMeaning.Prepared.view, RecursiveNamedPreparedSourceFrames.view,
    globalView, RecursiveNamedSpecializationBodyFacts.bodyInstance]
  rw [prepared.same]

variable {native : SourceCoreGeneralFunctions.CallableContext}
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan row.key = .ok row)

include prepared actual record in
/-- The same descriptor-authenticated sidecar selects the actual global view.
No dictionary is emptied and no stage marker is copied from the caller. -/
theorem selected_global
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named row.key)) :
    ∃ sidecar : Sidecar,
      prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar ∧ sidecar.caller = row ∧
      (registry actual).Closure
        (globalView (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
          prepared.view.evidence prepared.compilation.statements)
        (RecursiveStageRegistry.scope sidecar [] prepared.view) := by
  obtain ⟨sidecar, issued, same, selected⟩ := selected_of_descriptor actual prepared record descriptor
  refine ⟨sidecar, issued, same, ?_⟩
  rw [← global_view prepared]
  exact selected

include prepared actual record in
/-- A real source body run enters the named callee's original scope and
ordered parameter allocation. Its entire heap and failure scope are retained. -/
theorem applies
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {sidecar : Sidecar} (issued : prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar)
    {caller : Scope} {context bodyContext finalContext : Context}
    {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    {types : List TypeSystem.Ty} {outcome : BodyOutcome} {result : Outcome}
    (parameters : MonoBindersExtend row.function.typedBody.owner
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context
      row.function.typedBody.inputs types bodyContext)
    (allocate : Dynamic.BindersAllocate [] before row.function.typedBody.inputs arguments environment bound)
    (body : Statements (Program.ofChecked compiled.sourceProgram) (registry actual)
      (RecursiveStageRegistry.scope sidecar [] prepared.view) bodyContext environment bound
      prepared.compilation.statements finalContext outcome after)
    (converted : BodyResult row.function.inferredBodyType outcome result) :
    Applies (Program.ofChecked compiled.sourceProgram) (registry actual) caller context before
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments result after := by
  have frame := prepared.source_frame wellFormed range
  have same := sidecar_caller issued record
  have selected : (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) :=
    .named prepared sidecar issued same
  refine Applies.global (function := ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩)
    frame.instantiated frame.covers frame.roots ?_ parameters allocate body converted
  change (registry actual).Closure
    (globalView (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      prepared.view.evidence prepared.compilation.statements)
    (RecursiveStageRegistry.scope sidecar [] prepared.view)
  rw [← global_view prepared]
  exact selected

include prepared actual in
/-- Arity failure is independent of body staging and changes no heap. It
requires the actual source instantiation rather than native packed arity. -/
theorem arity_failure
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {caller : Scope} {context : Context} {heap : Dynamic.Heap} {arguments : List Dynamic.Value}
    (mismatch : row.function.typedBody.inputs.length ≠ arguments.length) :
    Applies (Program.ofChecked compiled.sourceProgram) (registry actual) caller context heap
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments
      (.fault (.semantic (.argumentArityMismatch row.function.typedBody.inputs.length arguments.length))) heap :=
  Applies.globalArity (function := ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩)
    (bodyInstance := RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
    (prepared.instantiated wellFormed range) mismatch
end Prepared
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStagedCalls
