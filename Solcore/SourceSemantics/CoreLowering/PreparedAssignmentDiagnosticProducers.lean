import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentProvenance

/-! The actual named and cached diagnostic producers authenticate projected
place tokens for the complete retained Source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
open Core Frontend SourceInference
open PreparedAssignmentDiagnosticAuthority

 theorem named {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    Nonempty (SourcePort compiled header.function.source
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared)) := by
  obtain ⟨issuer, present, lowered⟩ := diagnostic.actual
  refine ⟨{
    owner := prepared.named.signature.key
    row := prepared.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook
    sourceEq := by rw [aligned.function]; rfl
    unique := header.unique
    issuer := issuer
    present := present
    invalidToken := ?_
    missingToken := ?_ }⟩
  · intro site root
    simp only [RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection, lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  · intro site root raw
    simp only [RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault, lowered]
    cases compiled.indexed.base.callableContext <;> rfl

 theorem cached {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
    (cached : CallablePreparedMethodSelection.Cached compiled row)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt cached)
    {source : TypedSource} (sourceEq : source = cached.named.specialized.function.typedBody)
    (unique : NodeOccurrencesUnique source) :
    Nonempty (SourcePort compiled source
      (fun site root => cached.diagnostics.placeReason cached.named.signature.key site root none)
      (fun site root raw => cached.diagnostics.placeReason cached.named.signature.key site root (some raw))) := by
  obtain ⟨issuer, present, lowered⟩ := diagnostic.actual
  refine ⟨{
    owner := cached.named.signature.key
    row := cached.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook
    sourceEq := sourceEq
    unique := unique
    issuer := issuer
    present := present
    invalidToken := ?_
    missingToken := ?_ }⟩
  · intro site root
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  · intro site root raw
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl

end Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
