import Solcore.SourceSemantics.CoreLowering.GenericAssignmentUnaryDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes

/-! The existing exact issued Compilation and receiving diagnostic table also
retain original bit-not entries. No additional issuance field is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
open Core Frontend SourceInference
open GenericAssignmentUnaryDiagnostics
open CallableIndexedOwnedPublicFaultReceiverTables
open RecursiveNamedPublicSpecializationMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}

theorem receiver_unary (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {own : SourceCoreProgramFaultSites.Function} (member : own ∈ issued.program.base.functions)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : UnaryRep own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  cases reason <;> simp only [UnaryRep] at represented
  next operator =>
    cases operator <;> simp only at represented
    next =>
      obtain ⟨diagnostic, decoded, error⟩ := represented
      apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
      refine ⟨diagnostic, CallableIndexedOwnedPublicAssignmentDiagnostics.receiver_assignment_diagnostic
        compiled receiver present member decoded, ?_⟩
      rw [error]
      exact .unary

theorem prepared_unary {row : SourceSpecialization.SpecializedFunction}
    (prepared : Prepared compiled row)
    (receipt : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : UnaryRep prepared.compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ :=
    CallableIndexedOwnedPublicAssignmentDiagnostics.prepared_member prepared receipt
  exact receiver_unary compiled receiver present member represented

theorem cached_unary {row : SourceSpecialization.SpecializedFunction}
    (cached : CallablePreparedMethodSelection.Cached compiled row)
    (receipt : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt cached)
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : UnaryRep cached.compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ := CallableIndexedOwnedAssignmentProvenance.cached_member cached receipt
  exact receiver_unary compiled receiver present member represented

/-- A closure's same retained Compilation supplies the original unary table. -/
theorem compilation_unary {named : CallableIndexedNamedGeneration.Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)
    (receipt : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : UnaryRep compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ :=
    CallableIndexedOwnedIssuedAssignmentRecipes.compilation_member compilation receipt
  exact receiver_unary compiled receiver present member represented

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
