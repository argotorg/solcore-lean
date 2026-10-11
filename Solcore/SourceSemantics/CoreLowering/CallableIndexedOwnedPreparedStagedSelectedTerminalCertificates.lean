import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch

/-! Static restriction to the terminal compiler's actual used child.
The closure restriction reuses the checked same-Code used-child producers.
The new named restriction uses its accepted action to expose a single point.
These producers contain no execution, body meaning or runtime state.
Original Source compiler authority remains separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (code : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point scope id code

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {stages : Staging.Recursive.Registry}

/-- Keep the same Code/selected scope and narrow only its child certificate. -/
def closure {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (code : Code compiled.indexed function scope administrative)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages :=
  CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow (code := code) terminal

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Specialize the restriction through the actual ordinary/principal Code. -/
def closureFor
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages :=
  CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrowFor association terminal

/-- Keep this Header's actual receipt/alignment and expose its unique used child. -/
def named (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header) :
    CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header :=
  { terminal with
    certificate := Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child
    certifies := by
      intro lowered accepted
      exact ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans terminal.receipt.generated)⟩ }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates
