import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralFactory
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralDomainGlobals

/-! The selected initializer retains its original lambda indices and factory.
The actual literal inventory constructs local domains at current contexts;
existing compiler coverage consumes the same recaptured Support certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralSupport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := fixture.packet.compiled) caller.named parameters result statements
      (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      (expressionId fixture.packet 1) lowered)

include atHeader produced in
/-- The retained original lookup fixes the selected lambda's three indices. -/
theorem produced_shape : parameters = fixture.graph.parameters ∧ result = wordType ∧
    statements = [statementId fixture.packet 2] := by
  have found : (source caller.named).lookupExpression? (expressionId fixture.packet 1) =
      some fixture.graph.lambdaNode := by
    simpa only [atHeader.named] using fixture.graph.lambdaFound
  have sameNode := Produced.source_node caller produced found
  have form := produced.site.code.sourceForm
  rw [sameNode, fixture.graph.lambdaForm] at form
  change ExpressionForm.lambda fixture.graph.parameters wordType [statementId fixture.packet 2] =
    .lambda parameters result statements at form
  injection form with sameParameters sameResult sameStatements
  exact ⟨sameParameters.symm, sameResult.symm, sameStatements.symm⟩

variable (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    {rootFuel : Nat}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      lowered)

include atHeader shape metadata inventory in
/-- Only local index binders are substituted. The returned inputs retain the
original Produced value and its original diagnostic issuer. -/
theorem body_inputs_at_produced
    (diagnosticsEq : produced.diagnostics = effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named) :
    Nonempty (PlaceDiagnosticBodyInputs produced root) := by
  obtain ⟨sameParameters, sameResult, sameStatements⟩ := produced_shape fixture atHeader produced
  subst parameters
  subst result
  subst statements
  exact SourceCoreChosenOrdinaryAcceptedIssuedShell.body_inputs fixture atHeader shape metadata inventory
    root produced diagnosticsEq samePolicy sameView

include atHeader in
/-- Every genuine singleton return input identifies the same approved literal. -/
theorem approved_is_literal (inputs : PlaceDiagnosticBodyInputs produced root) :
    approved produced root inputs = SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture := by
  obtain ⟨sameParameters, sameResult, sameStatements⟩ := produced_shape fixture atHeader produced
  subst parameters
  subst result
  subst statements
  exact SourceCoreChosenOrdinaryAcceptedLiteralFactory.inputs_syntax fixture atHeader root produced inputs

include atHeader in
/-- The approved occurrence excludes indirect calls while the outer parent
remains an actual indirect call in the same Source. -/
theorem no_indirect_on :
    CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn (source caller.named)
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture (source caller.named)) := by
  intro id node callee ids resolution allowed found
  change id = expressionId fixture.packet 3 at allowed
  have original : (source fixture.packet.named).lookupExpression? id = some node := by
    simpa only [atHeader.named] using found
  exact fixture.graph.body_no_indirect allowed original

variable
    (selected : OriginalSelection fixture.packet) (checked : Metadata fixture.packet)
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)
    (samePolicy : receipt.formation.produced.site.code.policy = root.root.selected.policy)
    (sameView : receipt.formation.produced.site.code.view = source caller.named)
    (readFuelEq : receipt.formation.body.readFuel = fixture.packet.compiled.indexed.fuel)

include atHeader shape metadata inventory selected checked samePolicy sameView readFuelEq in
/-- Runtime signatures at the actual current context supply the catalog field.
The selected Support's read budget is the original fixed indexed budget. -/
theorem domain_at_support (environment : Dynamic.Environment)
    (currentContext : SourceSemantics.Context) (currentScope : SourceCoreLocalCell.Scope)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked fixture.packet.compiled.sourceProgram)
      currentContext (receipt.formation.function environment).source) :
    DomainAt root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
      (receipt.formation.support environment).body.readFuel currentContext [] currentScope
      (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) := by
  obtain ⟨inputs⟩ := body_inputs_at_produced fixture atHeader receipt.formation.produced shape metadata inventory
    root receipt.diagnostics_eq samePolicy sameView
  have literal := approved_is_literal fixture atHeader receipt.formation.produced root inputs
  have domain := SourceCoreChosenOrdinaryAcceptedLiteralDomainGlobals.domain_at fixture atHeader selected checked
    inventory root receipt.formation.produced inputs currentContext currentScope runtime.signatures
  rw [literal] at domain
  change DomainAt root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    receipt.formation.body.readFuel currentContext [] currentScope _
  rw [readFuelEq]
  exact domain

variable
    (chosen : ChosenFactory root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) receipt)

include chosen readFuelEq in
/-- Recapture retains the selected expression factory and its fixed read fuel. -/
theorem recaptured_factories (environment : Dynamic.Environment) :
    (receipt.formation.support environment).expressionSyntax =
      SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture ∧
    (receipt.formation.support environment).certificates =
      certificates root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) ∧
    (receipt.formation.support environment).body.readFuel = fixture.packet.compiled.indexed.fuel := by
  have actual := recaptured_factory root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    receipt chosen environment
  exact ⟨actual.1, actual.2.1, actual.2.2.trans readFuelEq⟩

include atHeader shape metadata inventory selected checked samePolicy sameView readFuelEq chosen in
/-- The original compiler coverage consumes one actual accepted child from
the same recaptured Support; no completed expression or body law is supplied. -/
theorem tree_at_support (environment : Dynamic.Environment)
    (currentContext : SourceSemantics.Context) (currentScope : SourceCoreLocalCell.Scope)
    (valid : CompatibleRuntimeContextValidity.Valid
      (context fixture.packet.compiled.indexed caller.named).solvedRequirements currentContext [])
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked fixture.packet.compiled.sourceProgram)
      currentContext (receipt.formation.function environment).source)
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support environment).certificates
      (receipt.formation.support environment).body.readFuel (receipt.formation.function environment).source
      currentContext currentScope child output) :
    let domain := domain_at_support fixture atHeader shape metadata inventory root selected checked receipt
      samePolicy sameView readFuelEq environment currentContext currentScope runtime
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (ScopedBodyCalls root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
        (indirect_factory root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
          (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) domain valid)
        (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller))
      receipt.formation.body.readFuel (.initial fixture.packet.compiled.compatible.checked)
      (source caller.named) currentContext (context fixture.packet.compiled.indexed caller.named).solvedRequirements
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      currentScope child output := by
  let domain := domain_at_support fixture atHeader shape metadata inventory root selected checked receipt
    samePolicy sameView readFuelEq environment currentContext currentScope runtime
  exact support_cover_for root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    receipt true chosen environment (SourceCoreChosenOrdinaryAcceptedCatalogFacts.headers caller) domain valid runtime actual

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralSupport
