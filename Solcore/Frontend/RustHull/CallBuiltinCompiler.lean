import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
import Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport

/-! Actual call lowering exposes the reserved references and the two ordered
ordinary-call guards. These are compiler facts, not source execution premises. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

structure References where
  isStatic : Core.Expr
  memory : Core.Expr
  memorySize : Core.Expr
  returnData : Core.Expr
  returnDataSize : Core.Expr
  handler : Core.Expr
  caller : Core.Expr
  depth : Core.Expr

structure CompiledReferences (scope : Scope) (references : References) : Prop where
  isStatic : Effects.reference scope "isStatic" .bool = .ok references.isStatic
  memory : Effects.reference scope "memory" WordMapping.type = .ok references.memory
  memorySize : Effects.reference scope "memorySize" .word = .ok references.memorySize
  returnData : Effects.reference scope "returnData" WordMapping.type = .ok references.returnData
  returnDataSize : Effects.reference scope "returnDataSize" .word = .ok references.returnDataSize
  handler : Effects.reference scope "callHandler" (OptionalCell.cellType Calls.callbackType) = .ok references.handler
  caller : Effects.reference scope "address" .word = .ok references.caller
  depth : Effects.reference scope "callDepth" .word = .ok references.depth

def invoke (references : References) (isStatic gas target value inputOffset inputLength outputOffset outputLength : Core.Expr) : Core.Expr :=
  Calls.invoke references.memory references.memorySize references.returnData references.returnDataSize
    references.handler (.loadCell references.caller) (.loadCell references.depth) isStatic
    gas target value inputOffset inputLength outputOffset outputLength

def ordinaryExpression (references : References) (invalid gas target value inputOffset inputLength outputOffset outputLength : Core.Expr) : Core.Expr :=
  let zeroValue := Core.Expr.binary .wordEq value (.word Word.zero)
  let supplied := Core.Expr.ifE zeroValue gas (.binary .wordAdd gas (.word (Word.ofNatModulo 2300)))
  let called := invoke references (.loadCell references.isStatic) supplied target value inputOffset inputLength outputOffset outputLength
  let invalidWord := LanguageResult.bind .word invalid (LanguageResult.success (.word Word.zero))
  let stipend := Core.Expr.ifE zeroValue called
    (.ifE (.binary .wordGt gas (.word (Word.ofNatModulo (wordModulus - 2301))))
      (LanguageResult.failure .word (.word (Word.ofNatModulo 13))) called)
  .ifE (.loadCell references.isStatic) (.ifE zeroValue called invalidWord) stipend

theorem ordinary_components {scope : Scope} {gas target value inputOffset inputLength outputOffset outputLength : Core.Expr}
    {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "call" [gas, target, value, inputOffset, inputLength, outputOffset, outputLength] = .ok lowered) :
    ∃ references invalid, CompiledReferences scope references ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      lowered = ⟨.word, ordinaryExpression references invalid gas target value inputOffset inputLength outputOffset outputLength⟩ := by
  change (Except.bind (Effects.call scope .ordinary gas target value inputOffset inputLength outputOffset outputLength) Except.ok) = .ok lowered at compiled
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

theorem static_components {scope : Scope} {gas target inputOffset inputLength outputOffset outputLength : Core.Expr}
    {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "staticcall" [gas, target, inputOffset, inputLength, outputOffset, outputLength] = .ok lowered) :
    ∃ references, CompiledReferences scope references ∧
      lowered = ⟨.word, invoke references (.bool true) gas target (.word Word.zero) inputOffset inputLength outputOffset outputLength⟩ := by
  change (Except.bind (Effects.call scope .staticCall gas target (.word Word.zero) inputOffset inputLength outputOffset outputLength) Except.ok) = .ok lowered at compiled
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
  refine ⟨⟨static, memory, size, data, dataSize, handler, caller, depth⟩,
    ⟨staticCompiled, memoryCompiled, sizeCompiled, dataCompiled, dataSizeCompiled,
      handlerCompiled, callerCompiled, depthCompiled⟩, ?_⟩
  exact (Except.ok.inj returned).symm

end Solcore.Frontend.RustHull.CallBuiltinCorrespondence
