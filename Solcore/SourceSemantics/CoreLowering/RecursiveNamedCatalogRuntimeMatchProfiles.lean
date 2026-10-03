import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMatchProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates

/-! Runtime profiles retain the same accepted body, emitted flow and native
Tree, with actual literal receipts attached to each expression occurrence.
Initial context validity is static and indexed by the actual Header context.
This unit does not close body execution or weaken Header.valid. Source syntax,
child compilation receipts, native typing and assignment diagnostics remain
inputs to the same Tree/extractor boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

abbrev RuntimeMatchProfileForWith (authenticated : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  MatchProfileWith
    (fun context => CompatibleRuntimeContextValidity.Valid header.solved context header.function.evidence)
    (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation
      expressionFuel header.function.source context header.solved header.reasonAt)
    diagnosticPolicy header expressionSyntax administrative registry faults

abbrev RuntimeMatchProfileFor (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  RuntimeMatchProfileForWith false diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults

def RuntimeMatchProfileForWith.of_extracted (authenticated : Bool) {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (valid : CompatibleRuntimeContextValidity.Valid header.solved header.context header.function.evidence)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  MatchProfileWith.of_extracted valid accepted projection generated tree errors


def RuntimeMatchProfileFor.of_extracted {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (valid : CompatibleRuntimeContextValidity.Valid header.solved header.context header.function.evidence)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    RuntimeMatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  RuntimeMatchProfileForWith.of_extracted false valid accepted projection generated tree errors

/-- The actual independent source frame supplies the initial runtime condition;
no Header.valid or template-empty premise is used here. -/
def RuntimeMatchProfileForWith.of_frame (authenticated : Bool) {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  RuntimeMatchProfileForWith.of_extracted authenticated
    (CompatibleRuntimeContextValidity.of_frame header.frame header.extended programTyped sameLedger)
    accepted projection generated tree errors

def RuntimeMatchProfileFor.of_frame {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    RuntimeMatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  RuntimeMatchProfileForWith.of_frame false programTyped sameLedger accepted projection generated tree errors


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
