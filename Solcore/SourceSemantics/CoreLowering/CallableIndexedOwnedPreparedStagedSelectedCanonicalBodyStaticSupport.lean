import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport

/-! Canonical terminal closure roots retain the same compiler, original Source
and parameter context. Actual captured global values are supplied later by the
real parameter entry, and are not a static support premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues

structure SelectedCanonicalBody {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function localScope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages)
    (semanticFaults : FunctionCalls.FaultRep) where
  point : packet.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
    packet.expression packet.receipt.child
  readFuel : Nat
  «prefix» : code.compilation.administrativePrefix = 1
  roots : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CanonicalRoot compiled code.policy code.lowerBody code.compilation readFuel inputs.context child
      code.reasonAt
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child function.resultType semanticFaults headers

def SelectedCanonicalBody.rootAt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    {code : Code compiled.indexed function localScope administrative}
    {inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
    {stages : Staging.Recursive.Registry}
    {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
    {semanticFaults : FunctionCalls.FaultRep}
    (support : SelectedCanonicalBody (headers := headers) code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    CanonicalRootAt compiled headers inputs.context child
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child semanticFaults :=
  CanonicalRootAt.ofRoot (support.roots child selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
