import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinarySelectedCallReceipts
import Solcore.SourceSemantics.CoreLowering.CallStageGuard

/-! The original selected closure contract admits the actual singleton pair
argument and Word result. Caller stages and the authentic dispatch remain
unchanged; no verdict or execution premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralCallGuard
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts

variable (fixture : AcceptedFixture) (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)

/-- The retained parameter is an ordinary physical pair, independently of
its native projection or the caller's expression stages. -/
theorem parameter_runtime :
    ¬ Staging.CallGuard.RequiresComptime false shape.parameter := by
  rintro (force | staged | type)
  · cases force
  · rw [shape.ordinary] at staged
    cases staged
  · rw [shape.scheme] at type
    cases type

include shape in
/-- Source order and the original singleton parameter close the argument
stage judgment for every authentic caller frame. -/
theorem arguments_accept (frame : Staging.CallGuard.Frame) :
    Staging.CallGuard.ArgumentsAccept frame false 0 fixture.graph.parameters
      [expressionId fixture.packet 6] := by
  rw [shape.parameters]
  exact .cons (.ordinary (parameter_runtime fixture shape)) (.nil _)

include shape in
/-- The actual ordinary contract is accepted even when the caller itself
has an effectful stage. No stage lookup or replacement contract is used. -/
theorem contract_accepts (frame : Staging.CallGuard.Frame) (call : ExpressionId) :
    Staging.CallGuard.Accepts frame ⟨fixture.graph.parameters, false⟩ call
      [expressionId fixture.packet 6] := by
  classical
  by_cases effectful : Staging.CallGuard.Effectful frame
  · exact .effectful effectful
  · exact .ordinary effectful (arguments_accept fixture shape frame) (.ordinary rfl)

include shape in
/-- Binding the selected original contract to this Source closure supplies
its actual parameter list and ordinary Word result flag. -/
theorem stage_accepts {sidecar : SourceCoreStageContracts.Sidecar}
    {function : Dynamic.Closure} {contract : Staging.CallGuard.Contract}
    (parameters : function.parameters = fixture.graph.parameters)
    (result : function.resultType = wordType)
    (bound : (CallableLedger.frame sidecar).Binds (.closure function) contract)
    (call : ExpressionId) :
    Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) call
      [expressionId fixture.packet 6] (.closure function) := by
  have raw : CallableLedger.Binds sidecar.plan (.closure function) contract := bound
  cases raw with
  | closure actualParameters actualResult =>
      have ordinary : contract.stagedResult = false := by
        cases staged : contract.stagedResult with
        | false => rfl
        | true =>
            have impossible := actualResult.mp staged
            rw [result] at impossible
            cases impossible
      have same : contract = ⟨fixture.graph.parameters, false⟩ := by
        cases contract
        simp only at actualParameters ordinary
        cases actualParameters.trans parameters
        cases ordinary
        rfl
      exact .contract bound (same ▸ contract_accepts fixture shape _ call)

variable {caller : ActualHeader fixture} (atHeader : HeaderAt fixture caller)
    {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {carrier : Value}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call
      [expressionId fixture.packet 6] (.closure (receipt.formation.function [])) carrier)

include atHeader shape in
/-- The original lambda lookup identifies the actual physical count. -/
theorem physical_arity :
    (receipt.formation.function []).parameters.length = [expressionId fixture.packet 6].length := by
  rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []).1,
    shape.parameters]
  rfl

include atHeader shape in
/-- The exact sealed row accepts before arguments from the authentic bound
contract. Acceptance is proved rather than supplied as a gate verdict. -/
theorem before_arguments : dispatch.row.beforeArguments = .ok () := by
  have actual := SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []
  exact dispatch.accepted (stage_accepts fixture shape actual.1 actual.2.1 dispatch.bound site.call)

include atHeader shape in
/-- The same selected row accepts its physical arity and application gates.
The original codebook, sidecar and selected entry remain genuine inputs. -/
theorem accepted_at_selected {callee : ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee
      [expressionId fixture.packet 6] metadata node dispatch.row) (unknown : Word) :
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch unknown := by
  have actual := SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []
  exact CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.accepted_at_row dispatch selected unknown
    (stage_accepts fixture shape actual.1 actual.2.1 dispatch.bound site.call)
    (physical_arity fixture shape atHeader receipt)

end Tests.SourceCoreChosenOrdinaryAcceptedLiteralCallGuard
