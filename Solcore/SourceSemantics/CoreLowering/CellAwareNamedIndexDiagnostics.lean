import Solcore.SourceSemantics.CoreLowering.CellAwareNamedDiagnosticIssuer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority

/-! Actual named compilation supplies each index occurrence's original issuer.
The current public receiver supplies its missing-default diagnostic only when
that lookup is reached. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedIndexDiagnostics
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority

def Ready (compiled : SourceCoreUnifiedCompilation.Compiled) (source : TypedSource)
    (reasonAt : ExpressionId → Word) : Prop :=
  ∀ {id base node baseNode layout comparison first second}
    (header : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second),
    Nonempty (Port compiled header (reasonAt id))

theorem ready {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {reasonAt : ExpressionId → Word}
    (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named reasonAt)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {source : TypedSource} (sourceEq : source = CallableIndexedNamedGeneration.source named)
    (unique : NodeOccurrencesUnique source) : Ready compiled source reasonAt := by
  intro id base node baseNode layout comparison first second header
  obtain ⟨issued,present,callback,_own,_ownFound⟩ := issuer
  exact ⟨{
    owner := named.signature.key
    row := named.specialized
    record := record
    sourceEq := sourceEq
    unique := unique
    issuer := issued
    present := present
    token := congrFun callback id }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedIndexDiagnostics
