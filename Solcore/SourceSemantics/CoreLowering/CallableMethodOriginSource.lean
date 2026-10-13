import Solcore.SourceSemantics.CoreLowering.RecursiveMethodOriginIdentity
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection

/-! Authentic compiler selection produces the same ordered roots used by
independent Source dictionary assembly at the reached lexical context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodOriginSource
open Core Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallablePreparedMethodSelection
open CallableNamedMetadata (evidence environment)

theorem roots_produced
    {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
    {receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output}
    (selected : SourceReceipt receipt)
    {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    RecursiveMethodOriginIdentity.RootsProduced context (environment receipt.available)
      receipt.requirements
      ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map evidence) := by
  have head := CallableCoercionSourceSelection.requirement_produces signatures ledger assumptions
    receipt.resolved selected.certificate.roots.primarySelected selected.certificate.roots.primaryValid
  have tail := CallableCoercionSourceSelection.requirements_produce signatures ledger assumptions
    receipt.resolved selected.certificate.roots.methodsSelected selected.certificate.roots.methodsValid
  have result : RecursiveMethodOriginIdentity.RootsProduced context (environment receipt.available)
      (receipt.selection.primaryRequirement :: selected.methodIds)
      ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map evidence) := by
    simpa only [environment, List.map_map, List.map_cons, Function.comp_def] using
      RecursiveMethodOriginIdentity.RootsProduced.intro head tail
  exact (congrArg (fun ids => RecursiveMethodOriginIdentity.RootsProduced context
    (environment receipt.available) ids
    ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map evidence))
    selected.requirements).mpr result

end Solcore.SourceSemantics.CoreLowering.CallableMethodOriginSource
