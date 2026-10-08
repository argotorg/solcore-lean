import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSamePolicyCompilerLeafReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates

/-! A finite static call head retains the genuine named, prepared lambda or
indirect compiler receipt at one root policy and its actual child positions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles

def extraForm : ExpressionForm → Prop
  | .lambda _ _ _ | .call _ _ (.indirect _) => True
  | _ => False

def extraChildren : ExpressionForm → List ExpressionId
  | .call callee ids (.indirect _) => callee :: ids
  | _ => []

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
  {reasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel (source caller.named) scope rootId reasonAt rootLowered)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
    (source caller.named) sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) certificates)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

/-- Prepared alternatives keep their literal factory and the supplied compiler
certificate. The named alternative retains its original dictionary variants. -/
inductive Head
    (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
      rootFuel (source caller.named) scope rootId reasonAt rootLowered)
    (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
      (source caller.named) sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) certificates)
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | named {childScope id lowered}
      (head : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
        (context compiled.indexed caller.named) (source caller.named) sourceContext children childScope id lowered) :
      Head root factory headers children childScope id lowered
  | prepared_lambda {childFuel id lowered node parameters result statements reported}
      (found : (source caller.named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) (source caller.named) scope id node parameters result statements reported reasonAt lowered)
      (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
        sourceContext evidence scope id lowered)
      (samePolicy : receipt.formation.produced.site.code.policy = root.selected.policy)
      (sameBody : receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody)
      (sameFuel : receipt.formation.produced.site.code.fuel = childFuel)
      (sameView : receipt.formation.produced.site.code.view = source caller.named)
      (sameReason : receipt.formation.produced.site.code.reasonAt = reasonAt)
      (sameCertificate : HEq receipt.formation.produced.site.code.receipt certificate)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type) :
      Head root factory headers children scope id lowered
  | prepared_indirect {childFuel id lowered node callee ids metadata}
      (found : (source caller.named).lookupExpression? id = some node)
      (form : node.form = .call callee ids (.indirect metadata))
      (receipt : CallableIndexedOwnedIndirectCompilerReceipts.Receipt compiled.indexed.ancestry.graph.inputs.callable [] factory
        (policy := root.selected.policy) (body := root.selected.lowerBody) (fuel := childFuel)
        (id := id) (callee := callee) (ids := ids) (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered))
      (ordered : ∀ child code, (child, code) ∈ receipt.compiler.entries → children scope child code) :
      Head root factory headers children scope id lowered

/-- Existing genuine named heads enter this finite family without alteration. -/
theorem include_named {children childScope id lowered}
    (head : RecursiveNamedCallEvidenceHeads.Calls (some evidence) headers
      (context compiled.indexed caller.named) (source caller.named) sourceContext children childScope id lowered) :
    Head root factory headers children childScope id lowered := .named head

/-- Projection follows the same parent metadata and emitted annotation. -/
theorem projected {children childScope id lowered node}
    (head : Head root factory headers children childScope id lowered)
    (found : (source caller.named).lookupExpression? id = some node) :
    compiled.compatible.checked.catalog.project node.type = .ok lowered.type := by
  cases head with
  | named actual => exact RecursiveNamedCallEvidenceHeads.projected actual found
  | prepared_lambda actualFound _ _ _ _ _ _ _ _ _ metadata =>
    have same := Option.some.inj (actualFound.symm.trans found)
    exact same ▸ metadata.projected
  | prepared_indirect _ _ receipt _ =>
    have same := Option.some.inj (receipt.compiler.found.symm.trans found)
    have emitted := congrArg SourceCoreBasic.LoweredExpr.type receipt.compiler.output
    simpa only [same, emitted] using receipt.parentMetadata.projected

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerHeads
