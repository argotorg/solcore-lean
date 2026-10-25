import Solcore.Frontend.RustHull.CallBuiltinCompiler

/-! Successful mode-specific lowering supplies the actual handler, caller and
inherited-value references, together with the ordered stipend guard. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallModeBuiltinCorrespondence
open Core Correspondence ScalarExecution PureCallCorrespondence EffectBuiltinCorrespondence
open CallBuiltinCorrespondence (References invoke)

structure CompiledReferences (scope : Scope) (handlerName callerName : String) (references : References) : Prop where
  isStatic : Effects.reference scope "isStatic" .bool = .ok references.isStatic
  memory : Effects.reference scope "memory" WordMapping.type = .ok references.memory
  memorySize : Effects.reference scope "memorySize" .word = .ok references.memorySize
  returnData : Effects.reference scope "returnData" WordMapping.type = .ok references.returnData
  returnDataSize : Effects.reference scope "returnDataSize" .word = .ok references.returnDataSize
  handler : Effects.reference scope handlerName (OptionalCell.cellType Calls.callbackType) = .ok references.handler
  caller : Effects.reference scope callerName .word = .ok references.caller
  depth : Effects.reference scope "callDepth" .word = .ok references.depth

def callCodeExpression (references : References)
    (gas target value inputOffset inputLength outputOffset outputLength : Core.Expr) : Core.Expr :=
  let zeroValue := Core.Expr.binary .wordEq value (.word Word.zero)
  let supplied := Core.Expr.ifE zeroValue gas (.binary .wordAdd gas (.word (Word.ofNatModulo 2300)))
  let called := invoke references (.loadCell references.isStatic) supplied target value inputOffset inputLength outputOffset outputLength
  .ifE zeroValue called
    (.ifE (.binary .wordGt gas (.word (Word.ofNatModulo (wordModulus - 2301))))
      (LanguageResult.failure .word (.word (Word.ofNatModulo 13))) called)

theorem callCode_components {scope : Scope} {gas target value inputOffset inputLength outputOffset outputLength : Core.Expr}
    {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "callcode" [gas, target, value, inputOffset, inputLength, outputOffset, outputLength] = .ok lowered) :
    ∃ references invalid, CompiledReferences scope "callCodeHandler" "address" references ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      lowered = ⟨.word, callCodeExpression references gas target value inputOffset inputLength outputOffset outputLength⟩ := by
  change (Except.bind (Effects.call scope .callCode gas target value inputOffset inputLength outputOffset outputLength) Except.ok) = .ok lowered at compiled
  obtain ⟨actual, compiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases Except.ok.inj returned
  unfold Effects.call at compiled
  obtain ⟨static, staticCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨data, dataCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨dataSize, dataSizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨handler, handlerCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨caller, callerCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨depth, depthCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨invalid, invalidCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  refine ⟨⟨static, memory, size, data, dataSize, handler, caller, depth⟩, invalid,
    ⟨staticCompiled, memoryCompiled, sizeCompiled, dataCompiled, dataSizeCompiled,
      handlerCompiled, callerCompiled, depthCompiled⟩, invalidCompiled, ?_⟩
  exact (Except.ok.inj returned).symm

theorem delegate_components {scope : Scope} {gas target inputOffset inputLength outputOffset outputLength : Core.Expr}
    {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "delegatecall" [gas, target, inputOffset, inputLength, outputOffset, outputLength] = .ok lowered) :
    ∃ references value, CompiledReferences scope "delegateCallHandler" "caller" references ∧
      Effects.reference scope "callvalue" .word = .ok value ∧
      lowered = ⟨.word, invoke references (.loadCell references.isStatic) gas target (.loadCell value)
        inputOffset inputLength outputOffset outputLength⟩ := by
  change (Except.bind (Effects.reference scope "callvalue" .word) fun value =>
    Except.bind (Effects.call scope .delegateCall gas target (.loadCell value) inputOffset inputLength outputOffset outputLength)
      Except.ok) = .ok lowered at compiled
  obtain ⟨value, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨actual, compiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases Except.ok.inj returned
  unfold Effects.call at compiled
  obtain ⟨static, staticCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨data, dataCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨dataSize, dataSizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨handler, handlerCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨caller, callerCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨depth, depthCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  refine ⟨⟨static, memory, size, data, dataSize, handler, caller, depth⟩, value,
    ⟨staticCompiled, memoryCompiled, sizeCompiled, dataCompiled, dataSizeCompiled,
      handlerCompiled, callerCompiled, depthCompiled⟩, valueCompiled, ?_⟩
  exact (Except.ok.inj returned).symm

end Solcore.Frontend.RustHull.CallModeBuiltinCorrespondence
