import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds

/-! The actual discard compiler issuer constructs the mixed support at each
genuine selected Source scope. Its original frame, parameter context, full
LocalView/Avoids transport and proof-indexed CallsReady remain explicit static
inputs. No expression or body meaning is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Discard DiscardSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {changed : List ExpressionId} {roots : List NodeId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}

/-- Each child receives a static issuer for this same whole receipt and the
actual BodyWith parameter inputs. Varying selected scopes are not collapsed
to source equality or one packet-selected scope. -/
def of_static (packet : Discard code stages)
    (packets : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
      CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Static
        (compiled := compiled) (function := function) (context := inputs.context)
        (types := inputs.types) (invocation := child) (changed := changed) (roots := roots)
        (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
        (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
        (native := native) (active := active) packet.receipt)
    (ready : ∀ (child : Staging.Recursive.Scope) (selected : stages.Closure function child),
      CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Ready
        (packets child selected)) :
    DiscardSupport code inputs stages packet semanticFaults where
  heads := fun child selected =>
    ⟨packet.receipt.shape.node,
      packet.receipt.source_head (packets child selected).edited.metadata⟩
  roots := fun child selected =>
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.rootPair
      (packets child selected) (ready child selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport
