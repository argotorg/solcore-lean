import Solcore.SourceSemantics.SourceCompiledMethodNormalizedFormation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInterfaces

/-! Complete actual method-checking inputs for a shared generalized body
consumer, recovered from the same cached method and raw compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledMethodFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceNormalizedCoercionFormation

namespace CachedMethodBody
variable {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
  {retained : CheckedImplementationMethod} {fuel : Nat}

/-- The executable cache validates the actual method specialization; reversing
that exact structural substitution supplies the original body's interfaces. -/
theorem interfaces (actual : CachedMethodBody compiled cached retained fuel) :
    ExecutableCoercionInterfaces.BodyInterfaces compiled.program.signatures retained.checked := by
  obtain ⟨index, named, method, atIndex, same, selection, _member, _identity, original⟩ := actual.selected
  have accepted : SourceSpecialization.specializeFunction
      (selection.implementation.functionSignatureOfMethodWithTrait selection.trait selection.declaration)
      retained.checked selection.supplied = .ok named.specialized := by
    simpa only [original, same] using selection.specialized
  have recorded := CoreLowering.SelectedCompilationCoercionInterfaces.cached cached atIndex
  rw [(CoreLowering.CallableCoercionBodyProvenance.specialization_fields accepted).1] at recorded
  have originalInterfaces := CoreLowering.SelectedCompilationCoercionInterfaces.of_applied recorded
  simpa only [(compiled.artifact_fields actual.artifact).1] using originalInterfaces

end CachedMethodBody

/-- All formation and continuation facts belong to this receipt's original
method and finalizer. Semantic body typing and generalized barriers are not
fields of this input record. -/
structure MethodBodyInputs {program : CheckedProgram} {retained : CheckedImplementationMethod} {fuel : Nat}
    (receipt : MethodBodyReceipt program retained fuel) : Prop where
  header : CheckedBodyHeaderWellFormed program.signatures receipt.signature retained.checked
  canonical : SignatureParametersWellFormed receipt.signature.id receipt.signature.scheme.parameters
  predicates : PredicatesWellFormed
    (signatureContext program.signatures receipt.signature.id
      receipt.signature.scheme.parameters receipt.signature.scheme.predicates)
    receipt.signature.scheme.predicates
  predicatesFixed : receipt.signature.scheme.predicates.map
    (TypedTraitResolution.applySubstitution retained.checked.substitution) = receipt.signature.scheme.predicates
  progress : BodyInferenceProgress receipt.body
  normalized : TypeAdmissible receipt.normalizedContext
      (receipt.body.finalized.substitution.apply receipt.body.body.type) ∧
    NormalizedStateFormation receipt.normalizedContext receipt.body.finalized.substitution receipt.body.body.state

theorem MethodBodyReceipt.inputs {raw : Workspace.RawWorkspace} {program : CheckedProgram}
    {retained : CheckedImplementationMethod} {fuel : Nat}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program) : MethodBodyInputs receipt :=
  ⟨receipt.header checked, receipt.canonical checked, receipt.predicates_formed checked,
    receipt.predicates_fixed checked retained.checked.substitution, receipt.inferenceProgress checked,
    receipt.normalizedBodyFormation checked rfl rfl rfl rfl⟩

/-- Public compiler success supplies the original method-checking carrier,
its executable interfaces and the complete normalized inference inputs. -/
theorem compile_cached_method_inputs {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
    {retained : CheckedImplementationMethod}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    (artifact : compiled.artifact? = some cached)
    (selected : CoreLowering.SelectedCompilationBodyTyping.MethodSource cached retained) :
    ∃ actual : CachedMethodBody compiled cached retained options.checkingFuel,
      MethodBodyInputs actual.receipt ∧
      ExecutableCoercionInterfaces.BodyInterfaces compiled.program.signatures retained.checked := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  obtain ⟨actual⟩ := cached_method_body checked artifact selected
  exact ⟨actual, actual.receipt.inputs checked, actual.interfaces⟩

end Solcore.SourceSemantics.SourceCompiledMethodFinalization
