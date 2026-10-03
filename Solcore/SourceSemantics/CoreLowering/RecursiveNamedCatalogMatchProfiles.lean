import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfiles
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding

/-! Static match profiles retain the actual body and flow compiler equations.
They carry the existing Match Tree and its site-specific diagnostic/catalog
receipt, without execution laws. Original For profiles embed with identical
code and administrative context, without a new catalog-validity premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

/-- Shared static body receipts use the actual source context. The condition P
contains no execution law and the expression family indexes this same Tree. -/
structure MatchProfileWith (P : SourceSemantics.Context → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (header : Header prepared values ambient.definitions program)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where private mk ::
  initialValid : P header.context
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
    header.onError values header.function.source expressionSyntax
    certificates
    ambient.definitions administrative header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output flow
  errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree

structure MatchProfileFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) extends MatchProfileWith
      (fun context => CompatibleExpressionLiterals.ContextValid header.solved context header.function.evidence)
      (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      diagnosticPolicy header expressionSyntax administrative registry faults where private mk ::

def ProfileFor.to_match
    {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (certificate : ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    MatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  ⟨⟨header.valid, certificate.accepted, certificate.projection, certificate.flow, certificate.generated, certificate.emitted, GenericImperativeMatch.Tree.of_for certificate.tree,
    GenericImperativeMatch.Tree.CatalogSites.of_for certificate.errors⟩⟩

def MatchProfileWith.of_extracted
    {P : SourceSemantics.Context → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {header : Header prepared values ambient.definitions program}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (valid : P header.context)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      certificates
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    MatchProfileWith P certificates diagnosticPolicy header expressionSyntax administrative registry faults := by
  have emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [generated] at accepted
    exact Except.ok.inj accepted.symm
  exact ⟨valid, accepted, projection, flow, generated, emitted, tree, errors⟩

def MatchProfileFor.of_extracted {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    MatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  ⟨MatchProfileWith.of_extracted header.valid accepted projection generated tree errors⟩

def MatchProfileFor.of_ready {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (errors : GenericImperativeMatch.Tree.ReadyFor diagnosticPolicy registry faults tree) :
    MatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  MatchProfileFor.of_extracted accepted projection generated tree
    (GenericImperativeMatch.Tree.CatalogSites.of_catalog catalog errors)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
