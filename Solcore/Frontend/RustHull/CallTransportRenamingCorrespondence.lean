import Solcore.Frontend.RustHull.CallTransportCorrespondence

/-! CALL transport builders preserve the variable renaming introduced by the
outer argument compiler. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem invoke_rename
    (memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      callerAddress currentDepth staticFlag suppliedGas address transferredValue
      sourceOffset sourceLength destinationOffset destinationLength : Core.Expr) (mapping : Renaming) :
    (Calls.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      callerAddress currentDepth staticFlag suppliedGas address transferredValue
      sourceOffset sourceLength destinationOffset destinationLength).rename mapping =
    Calls.invoke (memoryReference.rename mapping) (sizeReference.rename mapping)
      (returnDataReference.rename mapping) (returnSizeReference.rename mapping) (callbackReference.rename mapping)
      (callerAddress.rename mapping) (currentDepth.rename mapping) (staticFlag.rename mapping)
      (suppliedGas.rename mapping) (address.rename mapping) (transferredValue.rename mapping)
      (sourceOffset.rename mapping) (sourceLength.rename mapping)
      (destinationOffset.rename mapping) (destinationLength.rename mapping) := by
  simp only [Calls.invoke, bundle, Core.Expr.rename]
  congr 1
  simp [Calls.callCode, Calls.dispatch, Calls.finish, Calls.bind, Calls.bindResult,
    Calls.copy, MemoryCopyCorrespondence.copyPackedFrom_rename,
    Calls.touch, Memory.touch, Memory.packet, Memory.field, Memory.number, Memory.add, Calls.store, Calls.load, Calls.allocate, Calls.empty,
    Calls.choose, Calls.binary, Calls.success, Calls.number, Calls.part, Calls.arg,
    Calls.memory, Calls.memorySize, Calls.returnData, Calls.returnSize, Calls.callback,
    Calls.caller, Calls.depth, Calls.childStatic, Calls.gas, Calls.target, Calls.value,
    Calls.inputOffset, Calls.inputLength, Calls.outputOffset, Calls.outputLength,
    Calls.responseField, projectArgument, bundle,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OptionalCell.read, WordMapping.empty, Core.Expr.rename, Core.Renaming.lift]
  all_goals rfl

end Solcore.Frontend.RustHull.CallTransportCorrespondence
