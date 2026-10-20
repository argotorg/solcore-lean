import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
variable {bridge context}
theorem after_expression_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType invocation.source context id type)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last := by
  have stable := StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame
  cases outcome with
  | value value =>
    have preserved := Staging.Recursive.SelectedPreservation.expression selectedBodies
      runtime covers locals admitted.heap typed trace
    exact ⟨stable, by intro found same; cases same; exact ⟨preserved.value_typed _ rfl, preserved.heap_typed⟩⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨stable, by intro value same; cases same⟩
    | stage origin call reason => exact stable

end Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
