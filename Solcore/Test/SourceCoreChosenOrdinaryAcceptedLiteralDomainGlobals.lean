import Solcore.Test.SourceCoreChosenOrdinaryAcceptedCatalogFacts
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedStaticInventory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralPlaceDiagnosticShells

/-! Actual Header and inventory receipts populate the literal body's static
compiler domain. The same supplied root policy and current context are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralDomainGlobals
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

private def transport_root
    {compiled : SourceCoreUnifiedCompilation.Compiled} {named target : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {fuel : Nat} {rootSource : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) named diagnostics namedCode compilation fuel rootSource scope id reasonAt lowered)
    (same : named = target) :=
  Eq.rec (motive := fun actual (identity : named = actual) =>
    CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) actual diagnostics namedCode (identity ▸ compilation)
      fuel rootSource scope id reasonAt lowered) root same

private theorem transport_policy
    {compiled : SourceCoreUnifiedCompilation.Compiled} {named target : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {fuel : Nat} {rootSource : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) named diagnostics namedCode compilation fuel rootSource scope id reasonAt lowered)
    (same : named = target) :
    (transport_root root same).selected.policy = root.selected.policy := by
  cases same
  rfl

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel rootSource rootScope rootId
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      rootLowered)

include atHeader selected checked inventory in
/-- The actual catalog and complete builtin inventory supply every global field.
Lexical variables and residual mode remain those of the supplied current context. -/
theorem globals_at (currentContext : SourceSemantics.Context) (currentScope : SourceCoreLocalCell.Scope)
    (signatures : currentContext.signatures = fixture.packet.compiled.sourceProgram.signatures) :
    LiteralDomainGlobals root currentContext currentScope
      (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) := by
  let originalRoot := transport_root root.root atHeader.named
  have samePolicy := transport_policy root.root atHeader.named
  have sameSource : source caller.named = source fixture.packet.named := congrArg source atHeader.named
  have sameContext : context fixture.packet.compiled.indexed caller.named =
      context fixture.packet.compiled.indexed fixture.packet.named :=
    congrArg (context fixture.packet.compiled.indexed) atHeader.named
  refine {
    namedLedger := by simpa only [atHeader.named] using SourceCoreChosenOrdinaryAcceptedCatalogFacts.named_ledger atHeader
    headerOrder := SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers_order checked atHeader
    sourceTypes := SourceCoreChosenOrdinaryAcceptedCatalogFacts.source_types_at selected checked atHeader
      currentContext signatures
    fragmentValid := ?_
    fragmentCoercions := ?_
    fragmentSpecial := ?_
    fragmentRead := ?_
    profile := inventory.contracts }
  · simpa only [atHeader.named] using
      inventory.constructor_law currentContext (CompatibleExpressionBuiltins.Syntax (source fixture.packet.named))
  · intro candidate node tree found
    exact inventory.fragment_coercions (atHeader.named ▸ tree) (atHeader.named ▸ found)
  · intro candidate tree child budget
    have pointwise := inventory.builtin_policy originalRoot currentScope (atHeader.named ▸ tree)
    have special := pointwise.special child budget
    rw [samePolicy] at special
    rw [sameContext, sameSource]
    exact special
  · intro candidate tree
    have pointwise := inventory.builtin_policy originalRoot currentScope (atHeader.named ▸ tree)
    have read := pointwise.read
    rw [samePolicy] at read
    rw [sameSource]
    exact read

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := fixture.packet.compiled) caller.named parameters result statements
      sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      id lowered)
    (inputs : PlaceDiagnosticBodyInputs produced root)

include atHeader selected checked inventory in
/-- The actual literal inputs and constructed globals feed the original bounded
compiler domain once at the fixed indexed read budget. -/
theorem domain_at (currentContext : SourceSemantics.Context) (currentScope : SourceCoreLocalCell.Scope)
    (signatures : currentContext.signatures = fixture.packet.compiled.sourceProgram.signatures) :
    CallableIndexedOwnedPreparedMixedBodyCompilerFactory.DomainAt root.root
      (approved produced root inputs) fixture.packet.compiled.indexed.fuel currentContext evidence currentScope
      (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) := by
  exact literal_domain produced root inputs
    (globals_at fixture atHeader selected checked inventory root currentContext currentScope signatures)

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralDomainGlobals
