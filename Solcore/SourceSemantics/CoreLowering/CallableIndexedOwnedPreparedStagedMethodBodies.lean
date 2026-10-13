import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport

/-! Both method body forms retain their actual compiler packet and SourceAt.
The alternatives contain static receipts only. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedMethodPrincipal (Principal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}

inductive Packet (principal : Principal compiled method) where
  | terminal : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal → Packet principal
  | scoped : CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Packet principal → Packet principal

def Packet.sourceAt {principal : Principal compiled method} (packet : Packet principal) :
    CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary :=
  match packet with
  | .terminal packet => packet.sourceAt
  | .scoped packet => packet.sourceAt

def Support (principal : Principal compiled method) (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep) : Prop :=
  match packet with
  | .terminal packet => CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support
      principal packet headers stages semanticFaults
  | .scoped packet => CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Support
      principal packet headers stages semanticFaults

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies
