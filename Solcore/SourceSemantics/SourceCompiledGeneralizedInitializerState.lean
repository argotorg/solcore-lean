import Solcore.SourceSemantics.SourceCompiledGeneralizedInitializer
import Solcore.SourceSemantics.SourceInferenceRetainedInitializerState

/-! The selected initializer's semantic and operational continuations share
the same receipt and finalizer. Only its own retained binder is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.RetainedInitializer
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel} {source : Syntax.Statement}

theorem operational (continuation : RetainedInitializer selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (signatures : continuation.inferenceContext.signatures = compiled.program.signatures)
    (ready : continuation.entry.InferenceReady)
    (entering : GeneralizedActualStateInvariant continuation.entry
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))) :
    GeneralizedActualStateInvariant continuation.result.state
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) := by
  have formation : ProgramSignatureFormationValidated continuation.inferenceContext.signatures :=
    signatures.symm ▸ Frontend.checkProgram_success_signature_formation checked
  have catalog : SignatureCatalogWellFormed continuation.inferenceContext.signatures :=
    signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical : ∀ signature ∈ continuation.inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes) := by
    intro signature member
    rw [signatures] at member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  apply entering.ofRetainedInitializer continuation.receipt selected.body.resources ready catalog formation canonical
    continuation.privacy.retained
  rw [continuation.receipt.inference_eq]
  exact continuation.privacy.extension

theorem statement_of_child_with_state
    {raw : Workspace.RawWorkspace} {control : ControlContext}
    (continuation : RetainedInitializer selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (signatures : continuation.inferenceContext.signatures = compiled.program.signatures)
    (entering : GeneralizedActualStateInvariant continuation.entry
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)))
    (invariant : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry target)
    (actual : ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized frames target)
    (covered : ActualContext.Covers selected.body.finalized frames
      (.statement continuation.entry.allocateStatementId.1))
    (barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
      selected.body.finalized.substitution target
      (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (child :
      RecursiveExpressionInvariant
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized continuation.entry.allocateStatementId.2
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized (frames ++ [continuation.initializerBinding])
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
        (.expression continuation.receipt.value.id) →
      ExpressionHasType selected.body.finalized.typedSource
        (localSchemeInitializerContext target continuation.initializerBinding.binder)
        continuation.receipt.value.id
        (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    ∃ finalContext,
      ActiveLocalContextInvariant continuation.result.state selected.body.finalized.substitution finalContext ∧
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized frames finalContext ∧
      GeneralizedActualStateInvariant continuation.result.state
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) ∧
      StatementHasType selected.body.finalized.typedSource control target continuation.result.id finalContext {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution continuation.result {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
  obtain ⟨finalContext,active,actualFinal,typed,matching⟩ :=
    continuation.statement_of_child checked invariant actual covered barrier child
  exact ⟨finalContext,active,actualFinal,
    continuation.operational checked signatures invariant.ready entering,typed,matching⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.RetainedInitializer
