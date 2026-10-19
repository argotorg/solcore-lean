import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDiagnosticIssuer
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts

/-! The actual named preparation retains its diagnostic inventory and callback.
Every generalized initializer receives that same issuer before it is allocated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedDiagnosticIssuer
open Core Frontend SourceInference

variable {whole : SourceCoreUnifiedCompilation.Compiled}

def Named (prepared : SourceCoreCallableIndexedPrograms.Prepared whole.compatible.checked)
    (named : SourceCoreGeneralFunctions.Function) (reasonAt : ExpressionId → Word) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial whole.compatible.checked),
    prepared.base.diagnostics = some issued ∧
    reasonAt = issued.program.reasonAt named.signature.key ∧
    ∃ own : SourceCoreProgramFaultSites.Function,
      issued.program.base.find? named.signature.key = some own

theorem Named.initializer {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
    {reasonAt : ExpressionId → Word} (issuer : Named whole.indexed named reasonAt)
    (rootFuel budget : Nat) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) :
    GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
      (GeneralizedLocalInitializerCompilation.namedInputs compiled rootFuel budget
        (CallableIndexedNamedGeneration.context whole.indexed named) scope id reasonAt) := issuer

theorem of_prepared {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    Named whole.indexed header.named header.reasonAt := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  have sameBase : prepared.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases whole.indexed.base.callableContext <;> rfl
  have ownFound := prepared.compilation.diagnostic
  rw [sameBase] at ownFound
  refine ⟨issued, present, ?_, prepared.compilation.own, ?_⟩
  · rw [aligned.reasonAt, aligned.named, lowered]
    cases whole.indexed.base.callableContext <;> rfl
  · simpa only [aligned.named] using ownFound

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedDiagnosticIssuer
