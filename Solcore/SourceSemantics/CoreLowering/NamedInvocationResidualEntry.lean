import Solcore.Frontend.ResidualLexicalScopes
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames

/-! Named invocation roots are the exact statement roots extracted by the
real compiler. Their initial residual scope is empty. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering
open Frontend SourceInference TypeSystem SourceSpecializationWorklist

namespace CallableIndexedNamedGeneration

theorem Compilation.residual_entry
    {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (receipt : Compilation prepared named diagnostics code) :
    ResidualEntryCovered (source named) (receipt.statements.map NodeId.statement) [] := by
  have covered := ResidualEntryCovered.named (source named) []
  have roots := RecursiveNamedPreparedSourceFrames.compiled_roots_eq receipt
  change (source named).roots = receipt.statements.map NodeId.statement at roots
  rwa [roots] at covered

end CallableIndexedNamedGeneration

namespace ActualBodyInvocation

theorem Index.named_residual_entry
    {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}
    {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (receipt : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
    (selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      named.signature.key = .ok named.specialized) :
    let index : Index compiled bodyRelation := .named receipt selected
    ResidualEntryCovered index.source (index.statements.map NodeId.statement) index.active.domain := by
  exact receipt.residual_entry

end ActualBodyInvocation
end Solcore.SourceSemantics.CoreLowering
