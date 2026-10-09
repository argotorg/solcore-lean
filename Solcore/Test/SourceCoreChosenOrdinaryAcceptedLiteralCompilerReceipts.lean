import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSingletonReturnCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenWordLiteralExpressionBounds

/-! The retained initializer supplies the actual singleton-return compiler
receipt. Its approved child has admitted Word meaning at the same chosen
support, using the fixture's genuine numeric row and current runtime ledger. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedLiteralPlaceDiagnosticShells
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
    (atHeader : HeaderAt fixture caller)

include atHeader in
/-- The same Source lookup and original initializer inventory supply every
Word-literal field; no expression or body meaning is assumed. -/
theorem word_facts :
    CallableIndexedOwnedChosenWordLiteralExpressionBounds.WordNodeFacts
      (caller := caller) (expressionId fixture.packet 3) fixture.graph.literal := by
  refine ⟨?_, Or.inr ⟨_, _, fixture.graph.literalForm⟩, fixture.graph.literalType,
    fixture.graph.literalCoercions, ⟨_, fixture.graph.literalOwned⟩,
    Or.inr ⟨_, _, fixture.graph.literalForm⟩, ?_⟩
  · simpa only [atHeader.named] using fixture.graph.literalFound
  · simpa only [atHeader.named, context, CompatibleNamedBody.bodyContext] using fixture.calls.literalOrdinary

variable {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    {rootFuel : Nat}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      lowered)
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)

include atHeader in
/-- The actual selected return is identified with occurrence 3 before its
original accepted body is inverted once. The result retains compiler fuel. -/
theorem compiler_receipt
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (metadata : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph)
    (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
    (samePolicy : receipt.formation.produced.site.code.policy = root.root.selected.policy)
    (sameView : receipt.formation.produced.site.code.view = source caller.named) :
    Nonempty (CallableIndexedOwnedSingletonReturnCompilerReceipts.Receipt
      receipt.formation.produced (expressionId fixture.packet 3)) := by
  obtain ⟨inputs⟩ := SourceCoreChosenOrdinaryAcceptedLiteralSupport.body_inputs_at_produced
    fixture atHeader receipt.formation.produced shape metadata inventory root
    receipt.diagnostics_eq samePolicy sameView
  have literal := SourceCoreChosenOrdinaryAcceptedLiteralSupport.approved_is_literal
    fixture atHeader receipt.formation.produced root inputs
  have sameExpression : inputs.expression = expressionId fixture.packet 3 := by
    have allowed : approved receipt.formation.produced root inputs (source caller.named) inputs.expression := rfl
    rw [literal] at allowed
    exact allowed
  have read : (bodyPolicy receipt.formation.produced.compilation receipt.formation.produced.site.code).readStatement
      receipt.formation.produced.site.code.view inputs.statement = .ok (inputs.statementNode, inputs.statementCore) := by
    rw [read_policy, inputs.canonical]
    simp [SourceCoreCompatibleDataExpressions.readStatement, inputs.statementOwner,
      inputs.statementFound, inputs.statementProjected]
    rfl
  have accepted := CallableIndexedOwnedSingletonReturnCompilerReceipts.of_return
    receipt.formation.produced inputs.singleton read inputs.statementForm
  rw [sameExpression] at accepted
  exact accepted

variable (chosen : ChosenFactory root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) receipt)

include atHeader chosen in
/-- A real accepted child at the same recaptured support supplies the original
literal runtime certificate, with its fixed approved occurrence. -/
theorem certificate_at_support (environment : Dynamic.Environment)
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support environment).certificates
      (receipt.formation.support environment).body.readFuel (receipt.formation.function environment).source
      currentContext childScope child output) :
    child = expressionId fixture.packet 3 ∧ CompatibleExpressionLiteralRuntime.Certificate
      (context fixture.packet.compiled.indexed caller.named).solvedRequirements
      (receipt.formation.function environment).source child output := by
  exact CallableIndexedOwnedChosenWordLiteralExpressionBounds.certificate_at_support
    root (expressionId fixture.packet 3) fixture.graph.literal receipt chosen environment
    (word_facts fixture atHeader) actual

section Admitted
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (currentContext : SourceSemantics.Context) (currentEvidence : Dynamic.EvidenceEnvironment)
    (ledger : currentContext.solvedRequirements = (context fixture.packet.compiled.indexed caller.named).solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid currentContext)

include atHeader chosen ledger runtime in
/-- The original literal producer consumes the actual Source child once and
retains the same current state, all rows and successful Word admission. -/
theorem preserves_at_support (environment : Dynamic.Environment)
    (unique : NodeOccurrencesUnique (receipt.formation.function environment).source) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      currentContext currentEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates
        (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source currentContext) faults size := by
  exact CallableIndexedOwnedChosenWordLiteralExpressionBounds.preserves_at_support
    root (expressionId fixture.packet 3) fixture.graph.literal receipt chosen environment
    (word_facts fixture atHeader) bridge functions currentContext currentEvidence ledger runtime unique size

include atHeader chosen ledger runtime in
/-- Native reflection preserves the same actual tuple and reconstructs its
independently sized Source trace through the original literal producer once. -/
theorem reflects_at_support (environment : Dynamic.Environment) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      currentContext currentEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates
        (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source currentContext) faults size := by
  exact CallableIndexedOwnedChosenWordLiteralExpressionBounds.reflects_at_support
    root (expressionId fixture.packet 3) fixture.graph.literal receipt chosen environment
    (word_facts fixture atHeader) bridge functions currentContext currentEvidence ledger runtime size

end Admitted
end Tests.SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts
