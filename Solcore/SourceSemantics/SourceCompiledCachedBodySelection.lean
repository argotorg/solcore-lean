import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation

/-! Actual method cache positions supply the shared body carrier. The method
receipt and executable specialization remain attached to the same source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledMethodFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

namespace MethodBodyReceipt
variable {compiled : SourceCoreCompiler.Compiled} {retained : CheckedImplementationMethod}
  {fuel : Nat} {row : SourceSpecialization.SpecializedFunction}

def toBodySelection (receipt : MethodBodyReceipt compiled.program retained fuel)
    (member : retained ∈ compiled.program.methods)
    (specialized : row.function =
      SourceSpecialization.applyCheckedFunction row.parameterSubstitution retained.checked) :
    BodySelection compiled row fuel := {
  original := retained.checked
  signature := receipt.signature
  body := receipt.body
  origin := .method member receipt.implementationMember receipt.methodMember receipt.traitLookup receipt.methodId
  specialized }

theorem toBodySelection_body (receipt : MethodBodyReceipt compiled.program retained fuel)
    (member : retained ∈ compiled.program.methods)
    (specialized : row.function =
      SourceSpecialization.applyCheckedFunction row.parameterSubstitution retained.checked) :
    (receipt.toBodySelection member specialized).body = receipt.body := rfl

end MethodBodyReceipt

theorem CachedMethodBody.bodySelection
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
    {retained : CheckedImplementationMethod} {fuel : Nat}
    (actual : CachedMethodBody compiled cached retained fuel) :
    ∃ (row : SourceSpecialization.SpecializedFunction)
      (selected : BodySelection compiled row fuel),
      selected.original = retained.checked ∧
      selected.signature = actual.receipt.signature ∧
      HEq selected.body actual.receipt.body ∧
      (∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
        cached.indexed.base.functions[index]? = some named ∧ named.specialized = row) ∧
      ExecutableCoercionInterfaces.SourceInterfaces compiled.program.signatures
        selected.body.finalized.solvedRequirements selected.body.finalized.typedSource := by
  obtain ⟨index, named, method, atIndex, same, selection, member, _identity, original⟩ := actual.selected
  have accepted : SourceSpecialization.specializeFunction
      (selection.implementation.functionSignatureOfMethodWithTrait selection.trait selection.declaration)
      retained.checked selection.supplied = .ok named.specialized := by
    simpa only [original, same] using selection.specialized
  have retainedMember : retained ∈ compiled.program.methods := by
    rw [← (compiled.artifact_fields actual.artifact).1]
    exact member
  let selected := actual.receipt.toBodySelection retainedMember
    (CoreLowering.CallableCoercionBodyProvenance.specialization_fields accepted).1
  refine ⟨named.specialized, selected, rfl, rfl, HEq.rfl, ⟨index, named, atIndex, rfl⟩, ?_⟩
  change ExecutableCoercionInterfaces.SourceInterfaces compiled.program.signatures
    actual.receipt.body.finalized.solvedRequirements actual.receipt.body.finalized.typedSource
  rw [← actual.receipt.body.solved, ← actual.receipt.body.source]
  exact actual.interfaces

end Solcore.SourceSemantics.SourceCompiledMethodFinalization
