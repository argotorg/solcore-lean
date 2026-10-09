import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralInputs
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedStaticInventory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralIssuedSourceReceipts

/-! The actual fixture supplies its original diagnostic issuer at the chosen
Produced. Its inventory closes diagnostic typing before the literal shell is built. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedIssuedShell
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named diagnostics namedCode}
    {rootFuel : Nat} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named diagnostics namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet)
      (expressionId fixture.packet 1) rootReasonAt rootLowered)
    {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := fixture.packet.compiled) caller.named fixture.graph.parameters wordType
      [statementId fixture.packet 2] (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial fixture.packet.compiled.compatible.checked) caller)
      (expressionId fixture.packet 1) lowered)

include atHeader inventory in
/-- The unchanged node inventory supplies diagnostic typing at the actual Header. -/
theorem diagnostic_typing :
    EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named) := by
  simpa only [atHeader.named] using inventory.typing

include atHeader inventory in
/-- Original preparation and the selected compilation issue the same assignments.
The optional callable root table changes only the effective diagnostic table. -/
theorem issued_at_produced
    (diagnosticsEq : produced.diagnostics =
      effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) :
    ∃ issued : IssuedSource fixture.packet.compiled produced.site.code.compilation.owner (source caller.named),
      issued.assignments = produced.compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program produced.diagnostics := by
  exact CallableIndexedOwnedLiteralIssuedSourceReceipts.at_produced caller produced
    fixture.packet.diagnosticsFound diagnosticsEq (diagnostic_typing fixture atHeader inventory)

include atHeader inventory in
/-- The original callback identities retain the same assignment row and places.
No new compilation or contextual selection is performed. -/
theorem issued_at_callback
    {callbackCode : Expr}
    (callback : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) callbackCode)
    (diagnosticsEq : produced.diagnostics =
      effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    (codeEq : produced.namedCode = callbackCode)
    (compilationEq : HEq produced.compilation callback) :
    ∃ issued : IssuedSource fixture.packet.compiled produced.site.code.compilation.owner (source caller.named),
      issued.assignments = callback.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program
        (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) := by
  exact CallableIndexedOwnedLiteralIssuedSourceReceipts.at_callback caller produced callback
    diagnosticsEq codeEq compilationEq fixture.packet.diagnosticsFound rfl
    (diagnostic_typing fixture atHeader inventory)

include atHeader shape metadata inventory in
/-- The real issuer and Source facts populate the chosen Produced's literal inputs. -/
theorem body_inputs
    (diagnosticsEq : produced.diagnostics =
      effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named) :
    Nonempty (PlaceDiagnosticBodyInputs produced root) := by
  obtain ⟨issued, assignments, places⟩ :=
    issued_at_produced fixture atHeader inventory produced diagnosticsEq
  exact SourceCoreChosenOrdinaryAcceptedLiteralInputs.body_inputs
    fixture atHeader shape metadata root produced issued assignments places samePolicy sameView

include atHeader shape metadata inventory in
/-- One original issuer and the actual static inputs construct the same body's shell. -/
theorem shell
    (diagnosticsEq : produced.diagnostics =
      effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    (samePolicy : produced.site.code.policy = root.root.selected.policy)
    (sameView : produced.site.code.view = source caller.named)
    (readFuel : Nat) :
    ∃ inputs : PlaceDiagnosticBodyInputs produced root,
      Nonempty (CallableIndexedOwnedPreparedMixedBodyCompilerFactory.SiteShell
        (approved produced root inputs) produced) := by
  obtain ⟨inputs⟩ := body_inputs fixture atHeader shape metadata inventory root produced
    diagnosticsEq samePolicy sameView
  exact ⟨inputs, literal_shell produced root inputs readFuel⟩

end Tests.SourceCoreChosenOrdinaryAcceptedIssuedShell
