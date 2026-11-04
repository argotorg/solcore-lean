import Solcore.Frontend.RustHull.Semantics.Layers
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.EffectBuiltins
import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Frontend.RustHull.Semantics.Accounts
import Solcore.Frontend.RustHull.Effects
import Solcore.Frontend.RustHull.Internal.MemoryState
import Solcore.Frontend.RustHull.Internal.NamedFunctions
import Solcore.Frontend.RustHull.AccountRuntime
import Solcore.Frontend.RustHull.Internal.Digests

/-!
# Call transport

Caller-frame transport and the identity precompile, with the call builtin compiler facts.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.CallBuiltinCompiler
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallBuiltinArguments
/-! Successful call lowering fixes the arity and the packed word shapes used
by the concrete call guards and transport evaluator. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull

def RuntimeCallEffectsSemantics.Operation.arity : RuntimeCallEffectsSemantics.Operation → Nat
  | .ordinary => 7
  | .staticCall => 6

namespace CallBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallEffectsSemantics (Operation)

theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation with
  | ordinary =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, _ | ⟨seventh, _ | ⟨eighth, rest⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled
  | staticCall =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, _ | ⟨seventh, rest⟩⟩⟩⟩⟩⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled

private theorem five_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 5) :
    ∃ first second third fourth fifth one two three four five,
      arguments = [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩, ⟨.word, fourth⟩, ⟨.word, fifth⟩] ∧
      sources = [.word one, .word two, .word three, .word four, .word five] ∧
      targets = [.word one, .word two, .word three, .word four, .word five] := by
  cases related with
  | nil => cases length
  | @cons first rest source sources target targets head tail =>
      obtain ⟨second, third, fourth, fifth, two, three, four, five, rfl, rfl, rfl⟩ := AccountObservationBuiltinCorrespondence.four_words tail
        (fun argument member => words argument (.tail _ member)) (Nat.succ.inj length)
      have typed := words first (.head _)
      cases first with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word one => exact ⟨expression, second, third, fourth, fifth, one, two, three, four, five, rfl, rfl, rfl⟩

theorem six_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 6) :
    ∃ first second third fourth fifth sixth one two three four five six,
      arguments = [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩, ⟨.word, fourth⟩, ⟨.word, fifth⟩, ⟨.word, sixth⟩] ∧
      sources = [.word one, .word two, .word three, .word four, .word five, .word six] ∧
      targets = [.word one, .word two, .word three, .word four, .word five, .word six] := by
  cases related with
  | nil => cases length
  | @cons first rest source sources target targets head tail =>
      obtain ⟨second, third, fourth, fifth, sixth, two, three, four, five, six, rfl, rfl, rfl⟩ := five_words tail
        (fun argument member => words argument (.tail _ member)) (Nat.succ.inj length)
      have typed := words first (.head _)
      cases first with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word one => exact ⟨expression, second, third, fourth, fifth, sixth, one, two, three, four, five, six, rfl, rfl, rfl⟩

theorem seven_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 7) :
    ∃ first second third fourth fifth sixth seventh one two three four five six seven,
      arguments = [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩, ⟨.word, fourth⟩, ⟨.word, fifth⟩, ⟨.word, sixth⟩, ⟨.word, seventh⟩] ∧
      sources = [.word one, .word two, .word three, .word four, .word five, .word six, .word seven] ∧
      targets = [.word one, .word two, .word three, .word four, .word five, .word six, .word seven] := by
  cases related with
  | nil => cases length
  | @cons first rest source sources target targets head tail =>
      obtain ⟨second, third, fourth, fifth, sixth, seventh, two, three, four, five, six, seven, rfl, rfl, rfl⟩ := six_words tail
        (fun argument member => words argument (.tail _ member)) (Nat.succ.inj length)
      have typed := words first (.head _)
      cases first with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word one => exact ⟨expression, second, third, fourth, fifth, sixth, seventh, one, two, three, four, five, six, seven, rfl, rfl, rfl⟩

end CallBuiltinCorrespondence
end Solcore.Frontend.RustHull
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallModeBuiltinArguments
set_option autoImplicit false
namespace Solcore.Frontend.RustHull

def RuntimeCallModeSemantics.Operation.arity : RuntimeCallModeSemantics.Operation → Nat
  | .ordinary | .callCode => 7
  | .staticCall | .delegateCall => 6

namespace CallModeBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallModeSemantics (Operation)

theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation with
  | ordinary | callCode =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, _ | ⟨seventh, _ | ⟨eighth, rest⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled
  | staticCall | delegateCall =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, _ | ⟨seventh, rest⟩⟩⟩⟩⟩⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled

end CallModeBuiltinCorrespondence
end Solcore.Frontend.RustHull
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallModeBuiltinCompiler
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallTransportValues
/-! The caller and account dispatcher agree on the actual callback packets. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

def requestValues (request : Request) : List Core.Value :=
  [.word request.target, .word request.caller, .word request.value, .bool request.isStatic,
    .word request.depth, .word request.gas, WordMapping.encode request.calldata, .word request.calldataSize]
def requestValue (request : Request) : Core.Value := bundleValues (requestValues request)
def responseValues (response : Response) : List Core.Value :=
  [.bool response.success, WordMapping.encode response.data, .word response.size]
def responseValue (response : Response) : Core.Value := bundleValues (responseValues response)

inductive ResponseRel : Semantics.Result Response → Core.Value → Prop where
  | returned (response : Response) : ResponseRel (.value response) (.inRight .word (responseValue response))
  | language (reason : Word) : ResponseRel (.fault (.language reason)) (.inLeft Calls.responseType (.word reason))

end Solcore.Frontend.RustHull.CallTransportCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallTransportStateCorrespondence
/-! Caller-local memory and return data occupy four distinct cells. The same
four-cell frame rules used for event storage apply after renaming the two
mapping fields; no event behavior is involved in this representation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

structure Locations where
  memory : Nat
  memorySize : Nat
  returnData : Nat
  returnDataSize : Nat

def Locations.all (locations : Locations) : List Nat :=
  [locations.memory, locations.memorySize, locations.returnData, locations.returnDataSize]
def Locations.resources (locations : Locations) : LogsCorrespondence.Locations :=
  ⟨locations.memory, locations.memorySize, locations.returnData, locations.returnDataSize⟩
def resources (state : CallTransportSemantics.State) : LogsSemantics.State :=
  {memory := state.memory, words := state.returnData, cursor := state.returnDataSize}
abbrev StateRel (locations : Locations) (state : CallTransportSemantics.State) (store : Store) :=
  LogsCorrespondence.StateRel locations.resources (resources state) store
abbrev Frame (locations : Locations) (initial final : Store) :=
  LogsCorrespondence.Frame locations.resources initial final

theorem memory_related {locations : Locations} {state : CallTransportSemantics.State} {store : Store}
    (related : StateRel locations state store) :
    MemoryCorrespondence.StateRel locations.memory locations.memorySize state.memory store := by
  refine ⟨?_, related.memory, related.memorySize⟩
  have distinct := related.distinct
  simp [LogsCorrespondence.Locations.all, Locations.resources] at distinct
  exact distinct.1.1

theorem memory_updated {locations : Locations} {state : CallTransportSemantics.State} {memory : MemorySemantics.State} {initial final : Store}
    (related : StateRel locations state initial)
    (updated : MemoryCorrespondence.StateRel locations.memory locations.memorySize memory final)
    (frame : MemoryCorrespondence.Frame locations.memory locations.memorySize initial final) :
    StateRel locations {state with memory := memory} final := by
  have distinct := related.distinct
  simp [LogsCorrespondence.Locations.all, Locations.resources] at distinct
  refine ⟨related.distinct, updated.memory, updated.size, ?_, ?_⟩
  · exact frame.read locations.returnData _ (by intro same; simp_all) (by intro same; simp_all) related.logs
  · exact frame.read locations.returnDataSize _ (by intro same; simp_all) (by intro same; simp_all) related.logSize

theorem memory_frame {locations : Locations} {initial final : Store}
    (frame : MemoryCorrespondence.Frame locations.memory locations.memorySize initial final) :
    Frame locations initial final := by
  refine ⟨frame.length, ?_⟩
  intro location value outside found
  apply frame.read location value _ _ found
  · intro same
    exact outside (by simp [Locations.resources, LogsCorrespondence.Locations.all, same])
  · intro same
    exact outside (by simp [Locations.resources, LogsCorrespondence.Locations.all, same])

theorem frame_closures {locations : Locations} {state : CallTransportSemantics.State} {initial final : Store}
    (related : StateRel locations state initial) (frame : Frame locations initial final) :
    ClosuresPreserved initial final := by
  intro location parameter result body environment found
  apply frame.read location _ _ found
  intro member
  simp only [Locations.resources, LogsCorrespondence.Locations.all, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · have same := Option.some.inj (related.memory.symm.trans found)
    cases entries : state.memory.words <;> simp only [resources, entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (related.memorySize.symm.trans found)
    cases same
  · have same := Option.some.inj (related.logs.symm.trans found)
    cases entries : state.returnData <;> simp only [resources, entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (related.logSize.symm.trans found)
    cases same

def publishStore (locations : Locations) (store : Store) (data : MemorySemantics.Entries) (size : Word) : Store :=
  LogsCorrespondence.publishStore locations.resources store data size

theorem published {locations : Locations} {state : CallTransportSemantics.State} {store : Store}
    (related : StateRel locations state store) (data : MemorySemantics.Entries) (size : Word) :
    StateRel locations {state with returnData := data, returnDataSize := size} (publishStore locations store data size) :=
  related.publish data size

def argumentValues (locations : Locations) (callback : Nat) (arguments : Arguments) : List Core.Value :=
  [.cellRef WordMapping.type locations.memory, .cellRef .word locations.memorySize,
    .cellRef WordMapping.type locations.returnData, .cellRef .word locations.returnDataSize,
    .cellRef (OptionalCell.cellType Calls.callbackType) callback,
    .word arguments.caller, .word arguments.depth, .bool arguments.isStatic, .word arguments.gas,
    .word arguments.target, .word arguments.value, .word arguments.inputOffset, .word arguments.inputLength,
    .word arguments.outputOffset, .word arguments.outputLength]

abbrev Inputs (depth : Nat) (environment : Environment) (locations : Locations) (callback : Nat) (arguments : Arguments) :=
  CodeValue depth environment Calls.arg (bundleValues (argumentValues locations callback arguments))

theorem input_part {depth : Nat} {environment : Environment} {locations : Locations} {callback : Nat} {arguments : Arguments}
    (related : Inputs depth environment locations callback arguments) {index : Nat} {value : Core.Value}
    (found : (argumentValues locations callback arguments)[index]? = some value) :
    CodeValue depth environment (Calls.part index) value := related.part found

theorem input_initial (locations : Locations) (callback : Nat) (arguments : Arguments) (environment : Environment) :
    Inputs 0 (bundleValues (argumentValues locations callback arguments) :: environment) locations callback arguments := by
  intro extra store
  exact .var (by simp)

end Solcore.Frontend.RustHull.CallTransportCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallTransportFinishCorrespondence
/-! Child responses update complete return data before copying the requested
prefix into caller memory. The copied bytes and the returned success word come
from the independent response. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

private theorem response_part {depth : Nat} {environment : Environment} {code : Calls.Code} {response : Response}
    (related : CodeValue depth environment code (responseValue response)) {index : Nat} {value : Core.Value}
    (found : (responseValues response)[index]? = some value) :
    CodeValue depth environment (fun depth => Calls.responseField index (code depth)) value := related.part found

theorem finish_preserves {depth : Nat} {environment : Environment} {store : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    {response : Response} {memory : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    {responseCode : Calls.Code}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (responseRelated : CodeValue depth environment responseCode (responseValue response))
    (copied : MemoryCopySemantics.From response.data arguments.outputOffset Word.zero
      (copiedLength arguments response) state.memory result memory) :
    ∃ target final,
      ResultRel .word (finishResult response result) target ∧
      Evaluates environment store (Calls.finish responseCode depth) target final ∧
      StateRel locations ⟨memory, response.data, response.size⟩ final ∧ Frame locations store final := by
  let writtenData : Store := store.set locations.returnData (WordMapping.encode response.data)
  let publishedStore := publishStore locations store response.data response.size
  have distinct := related.distinct
  simp [Locations.resources, LogsCorrespondence.Locations.all] at distinct
  have dataWritten : store.write? locations.returnData (WordMapping.encode response.data) = some writtenData :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp related.logs).1, rfl⟩
  have sizeFound : writtenData.read? locations.returnDataSize = some (.word state.returnDataSize) := by
    rw [Store.write?_preserves_other dataWritten (by intro same; simp_all)]
    exact related.logSize
  have sizeWritten : writtenData.write? locations.returnDataSize (.word response.size) = some publishedStore :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeFound).1, rfl⟩
  have publishedRelated := published related response.data response.size
  have input' := inputs.prepend [Core.Value.unit, .unit]
  have response' := responseRelated.prepend [Core.Value.unit, .unit]
  have lengthEvaluated : Evaluates ([Core.Value.unit, .unit] ++ environment) publishedStore
      (Calls.choose (Calls.binary .wordGt (fun depth => Calls.responseField 2 (responseCode depth)) Calls.outputLength)
        Calls.outputLength (fun depth => Calls.responseField 2 (responseCode depth)) (depth + 2))
      (.word (copiedLength arguments response)) publishedStore := by
    have left := (response_part response' (index := 2) rfl).evaluates publishedStore
    have right := (input_part input' (index := 14) rfl).evaluates publishedStore
    by_cases long : response.size > arguments.outputLength
    · simp only [copiedLength, long, ↓reduceIte]
      exact .ifTrue (.binary left right (by simp [BinaryOp.apply, long])) right
    · simp only [copiedLength, long, ↓reduceIte]
      exact .ifFalse (.binary left right (by simp [BinaryOp.apply, long])) left
  obtain ⟨copyTarget, final, copyRelated, evaluated, memoryFinal, copiedFrame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves copied (memory_related (state := {state with returnData := response.data, returnDataSize := response.size}) publishedRelated)
      ((input_part input' (index := 0) rfl).evaluates publishedStore)
      ((input_part input' (index := 1) rfl).evaluates publishedStore)
      ((input_part input' (index := 13) rfl).evaluates publishedStore)
      ((response_part response' (index := 1) rfl).evaluates publishedStore) .word lengthEvaluated
  have finalRelated := memory_updated publishedRelated memoryFinal copiedFrame
  have frame := (LogsCorrespondence.Frame.publish locations.resources store response.data response.size).trans
    (memory_frame copiedFrame)
  have enter : ∀ target,
      Evaluates ([Core.Value.unit, .unit] ++ environment) publishedStore
        (Calls.bindResult (Calls.copy Calls.memory Calls.memorySize Calls.outputOffset
          (fun depth => Calls.responseField 1 (responseCode depth)) (Calls.number 0)
          (Calls.choose (Calls.binary .wordGt (fun depth => Calls.responseField 2 (responseCode depth)) Calls.outputLength)
            Calls.outputLength (fun depth => Calls.responseField 2 (responseCode depth))))
          (fun _ => Calls.success (Calls.choose (fun depth => Calls.responseField 0 (responseCode depth))
            (Calls.number 1) (Calls.number 0))) (depth + 2)) target final →
      Evaluates environment store (Calls.finish responseCode depth) target final := by
    intro target completed
    unfold Calls.finish Calls.bind
    apply Evaluates.letE (bodyStore := writtenData)
    · exact .storeCell ((input_part inputs (index := 2) rfl).evaluates store) related.logs
        ((response_part responseRelated (index := 1) rfl).evaluates store) dataWritten
    · apply Evaluates.letE (bodyStore := publishedStore)
      · exact .storeCell ((input_part (inputs.prepend [.unit]) (index := 3) rfl).evaluates writtenData)
          sizeFound ((response_part (responseRelated.prepend [.unit]) (index := 2) rfl).evaluates writtenData) sizeWritten
      · exact completed
  cases copied with
  | overflow _ =>
      cases copyRelated
      refine ⟨.inLeft .word (.word (Word.ofNatModulo 6)), final, .language _, enter _ ?_, finalRelated, frame⟩
      exact LanguageResult.bind_failure .word evaluated
  | done _ _ =>
      cases copyRelated with
      | value copiedValue =>
          cases copiedValue
          refine ⟨.inRight .word (.word (Word.ofNatModulo (if response.success then 1 else 0))), final,
            .value (.word _), enter _ ?_, finalRelated, frame⟩
          apply LanguageResult.bind_success .word evaluated
          apply Evaluates.inRight
          have succeeded := (response_part (responseRelated.prepend [.unit, .unit, .unit]) (index := 0) rfl).evaluates final
          cases success : response.success
          · exact .ifFalse (by simpa only [success, List.length_cons, List.length_nil, List.cons_append, List.nil_append, Nat.add_assoc] using succeeded) .word
          · exact .ifTrue (by simpa only [success, List.length_cons, List.length_nil, List.cons_append, List.nil_append, Nat.add_assoc] using succeeded) .word

end Solcore.Frontend.RustHull.CallTransportCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallTransportSnapshotCorrespondence
/-! The emitted dispatch copies caller input into two fresh scratch cells.
Every pre-existing cell is retained before the callback is selected. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

def dispatchTail (input : Calls.Code) : Calls.Code :=
  Calls.bindResult (fun depth => OptionalCell.read Calls.callbackType (Calls.callback depth) Calls.unavailableReason) fun function =>
  Calls.bindResult (fun depth => .apply (function depth) (bundle [
    Calls.binary .wordAnd Calls.target (Calls.number (2 ^ 160 - 1)) depth,
    Calls.binary .wordAnd Calls.caller (Calls.number (2 ^ 160 - 1)) depth,
    Calls.value depth, Calls.childStatic depth, Calls.binary .wordAdd Calls.depth (Calls.number 1) depth,
    Calls.gas depth, Calls.load input depth, Calls.inputLength depth])) Calls.finish

theorem state_retained {locations : Locations} {state : CallTransportSemantics.State} {initial final : Store}
    (related : StateRel locations state initial) (retained : StoreRetains initial final) : StateRel locations state final := by
  refine ⟨related.distinct, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact (retained.read _ (List.getElem?_eq_some_iff.mp related.memory).1).trans related.memory
    | exact (retained.read _ (List.getElem?_eq_some_iff.mp related.memorySize).1).trans related.memorySize
    | exact (retained.read _ (List.getElem?_eq_some_iff.mp related.logs).1).trans related.logs
    | exact (retained.read _ (List.getElem?_eq_some_iff.mp related.logSize).1).trans related.logSize

theorem retained_frame (locations : Locations) {initial final : Store} (retained : StoreRetains initial final) :
    Frame locations initial final :=
  ⟨retained.length_le, fun _ _ _ found => (retained.read _ (List.getElem?_eq_some_iff.mp found).1).trans found⟩

theorem snapshot_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    {input : MemorySemantics.State}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (copied : MemoryCopySemantics.From state.memory.words Word.zero arguments.inputOffset arguments.inputLength
      {} (.value .unit) input) :
    ∃ extra copiedStore inputCode,
      extra.length = 4 ∧ StoreRetains store copiedStore ∧
      Inputs (depth + 4) (extra ++ environment) locations callback arguments ∧
      CodeValue (depth + 4) (extra ++ environment) inputCode (.cellRef WordMapping.type store.length) ∧
      copiedStore.read? store.length = some (WordMapping.encode input.words) ∧
      ∀ target final,
        Evaluates (extra ++ environment) copiedStore (dispatchTail inputCode (depth + 4)) target final →
        Evaluates environment store (Calls.dispatch depth) target final := by
  let snapshot := WordMapping.encode state.memory.words
  let inputRef := Value.cellRef WordMapping.type store.length
  let sizeRef := Value.cellRef .word (store.length + 1)
  let allocated : Store := store ++ [WordMapping.encode [], .word Word.zero]
  let inputCode : Calls.Code := fun here => .var (here - (depth + 1) - 1)
  let sizeCode : Calls.Code := fun here => .var (here - (depth + 2) - 1)
  let snapshotCode : Calls.Code := fun here => .var (here - depth - 1)
  have snapshotRelated := CodeValue.bound depth environment snapshot
  have inputRelated := CodeValue.bound (depth + 1) (snapshot :: environment) inputRef
  have sizeRelated := CodeValue.bound (depth + 2) (inputRef :: snapshot :: environment) sizeRef
  have scratchRelated : MemoryCorrespondence.StateRel store.length (store.length + 1) {} allocated := by
    refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
  let extraInput : Environment := [sizeRef, inputRef, snapshot]
  obtain ⟨target, copiedStore, resultRelated, evaluated, inputMemory, frame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves copied scratchRelated
      ((inputRelated.prepend [sizeRef]).evaluates allocated) (sizeRelated.evaluates allocated) .word
      ((snapshotRelated.prepend [sizeRef, inputRef]).evaluates allocated)
      ((input_part (inputs.prepend extraInput) (index := 11) rfl).evaluates allocated)
      ((input_part (inputs.prepend extraInput) (index := 12) rfl).evaluates allocated)
  cases resultRelated with
  | value valueRelated =>
      cases valueRelated
      have retained : StoreRetains store copiedStore := by
        constructor
        · have length := frame.length
          simp only [allocated, List.length_append, List.length_cons, List.length_nil] at length
          omega
        · intro location bounded
          have found : store.read? location = some store[location] := List.getElem?_eq_getElem bounded
          have after : copiedStore.read? location = some store[location] :=
            frame.read location _ (by omega) (by omega)
              (by simpa only [allocated, Store.read?, List.getElem?_append_left bounded] using found)
          exact after.trans found.symm
      refine ⟨.unit :: extraInput, copiedStore, inputCode, rfl, retained, inputs.prepend (.unit :: extraInput),
        inputRelated.prepend [.unit, sizeRef], inputMemory.memory, ?_⟩
      intro target final completed
      unfold Calls.dispatch Calls.bind
      apply Evaluates.letE (.loadCell ((input_part inputs (index := 0) rfl).evaluates store) related.memory)
      apply Evaluates.letE (bodyStore := store ++ [WordMapping.encode []])
      · exact .newCell (.construct .unit)
      · apply Evaluates.letE (bodyStore := allocated)
        · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc, List.cons_append, List.nil_append, inputRef, snapshot, resources, Calls.allocate, Calls.number, show Word.ofNatModulo 0 = Word.zero from rfl] using
            (Evaluates.newCell (elementType := .word) (environment := inputRef :: snapshot :: environment)
              (initialStore := store ++ [WordMapping.encode []]) Evaluates.word (initialValue := .word Word.zero))
        · exact LanguageResult.bind_success .word evaluated completed

end Solcore.Frontend.RustHull.CallTransportCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallTransportCallbackCorrespondence
/-! Account callbacks may change shared resources while preserving the four
caller cells. Their store relation composes with ordinary transport frames. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

structure Model (Shared : Type) (locations : Locations) where
  related : Shared → Store → Prop
  frame : ∀ {state initial final}, Frame locations initial final → related state initial → related state final
  retains : Store → Store → Prop
  retainedFrame : ∀ {initial final}, Frame locations initial final → retains initial final
  retainedTrans : ∀ {initial middle final}, retains initial middle → retains middle final → retains initial final

def CallbackPreservation {Shared : Type} {locations : Locations}
    (model : Model Shared locations)
    (callback : Request → Shared → Semantics.Result Response → Shared → Prop) (function : Core.Value) : Prop :=
  ∀ {request shared finalShared result}, callback request shared result finalShared →
    ∀ {state environment store functionExpr requestExpr},
      model.related shared store → StateRel locations state store →
      Evaluates environment store functionExpr function store →
      Evaluates environment store requestExpr (requestValue request) store →
      ∃ target final, ResponseRel result target ∧
        Evaluates environment store (.apply functionExpr requestExpr) target final ∧
        StateRel locations state final ∧ model.related finalShared final ∧ model.retains store final

def requestExpression (input : Calls.Code) : Calls.Code := fun depth => bundle [
  Calls.binary .wordAnd Calls.target (Calls.number (2 ^ 160 - 1)) depth,
  Calls.binary .wordAnd Calls.caller (Calls.number (2 ^ 160 - 1)) depth,
  Calls.value depth, Calls.childStatic depth, Calls.binary .wordAdd Calls.depth (Calls.number 1) depth,
  Calls.gas depth, Calls.load input depth, Calls.inputLength depth]

theorem request_evaluates {depth : Nat} {environment : Environment} {store : Store} {locations : Locations}
    {callback inputLocation : Nat} {arguments : Arguments} {entries : MemorySemantics.Entries} {input : Calls.Code}
    (inputs : Inputs depth environment locations callback arguments)
    (inputRelated : CodeValue depth environment input (.cellRef WordMapping.type inputLocation))
    (inputRead : store.read? inputLocation = some (WordMapping.encode entries)) :
    Evaluates environment store (requestExpression input depth) (requestValue (request arguments entries)) store := by
  refine .pair (.binary ((input_part inputs (index := 9) rfl).evaluates store) .word rfl) ?_
  refine .pair (.binary ((input_part inputs (index := 5) rfl).evaluates store) .word rfl) ?_
  refine .pair ((input_part inputs (index := 10) rfl).evaluates store) ?_
  refine .pair ((input_part inputs (index := 7) rfl).evaluates store) ?_
  refine .pair (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word rfl) ?_
  refine .pair ((input_part inputs (index := 8) rfl).evaluates store) ?_
  exact .pair (.loadCell (inputRelated.evaluates store) inputRead) ((input_part inputs (index := 12) rfl).evaluates store)

def callbackValue (available : Bool) (function : Core.Value) : Core.Value :=
  if available then .inRight .unit function else .inLeft Calls.callbackType .unit

theorem dispatch_preserves {Shared : Type} {locations : Locations} (model : Model Shared locations)
    {callback : Request → Shared → Semantics.Result Response → Shared → Prop}
    {available : Bool} {arguments : Arguments}
    {state finalState : CallTransportSemantics.State} {shared finalShared : Shared}
    {result : Semantics.Result Semantics.Value}
    (dispatched : Dispatch callback available arguments state shared result finalState finalShared)
    {depth : Nat} {environment : Environment} {store : Store} {callbackLocation : Nat} {function : Core.Value}
    (inputs : Inputs depth environment locations callbackLocation arguments)
    (related : StateRel locations state store)
    (sharedRelated : model.related shared store)
    (handler : store.read? callbackLocation = some (callbackValue available function))
    (preserved : CallbackPreservation model callback function) :
    ∃ target final, ResultRel .word result target ∧
      Evaluates environment store
        (Calls.choose (Calls.binary .wordGt Calls.depth (Calls.number (Calls.depthLimit - 1)))
          (Calls.success (Calls.number 0)) Calls.dispatch depth) target final ∧
      StateRel locations finalState final ∧ model.related finalShared final ∧ model.retains store final := by
  cases dispatched with
  | depth _ exceeded =>
      refine ⟨.inRight .word (.word Word.zero), store, .value (.word _), ?_, related, sharedRelated,
        model.retainedFrame (.refl _ _)⟩
      exact .ifTrue (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word
        (by simp [BinaryOp.apply, Calls.depthLimit, exceeded])) (.inRight .word)
  | unavailable _ allowed copied missing =>
      subst available
      obtain ⟨extra, copiedStore, inputCode, length, retained, inputs', _, _, entered⟩ := snapshot_evaluates inputs related copied
      have frame := retained_frame locations retained
      have read := (retained.read callbackLocation (List.getElem?_eq_some_iff.mp handler).1).trans handler
      refine ⟨.inLeft .word (.word (Word.ofNatModulo 7)), copiedStore, .language _, ?_,
        state_retained related retained, model.frame frame sharedRelated, model.retainedFrame frame⟩
      apply Evaluates.ifFalse (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word
        (by simp [BinaryOp.apply, Calls.depthLimit, allowed]))
      apply entered
      exact LanguageResult.bind_failure .word
        (OptionalCell.read_failure Calls.unavailableReason ((input_part inputs' (index := 4) rfl).evaluates copiedStore) read)
  | fault allowed copied present called =>
      subst available
      obtain ⟨extra, copiedStore, inputCode, length, retained, inputs', inputRelated, inputRead, entered⟩ := snapshot_evaluates inputs related copied
      have frame := retained_frame locations retained
      have read := (retained.read callbackLocation (List.getElem?_eq_some_iff.mp handler).1).trans handler
      have functionRead := OptionalCell.read_success Calls.unavailableReason
        ((input_part inputs' (index := 4) rfl).evaluates copiedStore) read
      have requestRead := request_evaluates (inputs'.prepend [function]) (inputRelated.prepend [function]) inputRead
      obtain ⟨target, after, responseRelated, evaluated, afterRelated, sharedAfter, retainedAfter⟩ :=
        preserved called (model.frame frame sharedRelated) (state_retained related retained)
          ((CodeValue.bound (depth + 4) (extra ++ environment) function).evaluates copiedStore) requestRead
      cases responseRelated with
      | language reason =>
          refine ⟨.inLeft .word (.word reason), after, .language _, ?_, afterRelated, sharedAfter,
            model.retainedTrans (model.retainedFrame frame) retainedAfter⟩
          apply Evaluates.ifFalse (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word
            (by simp [BinaryOp.apply, Calls.depthLimit, allowed]))
          apply entered
          exact LanguageResult.bind_success .word functionRead (LanguageResult.bind_failure .word evaluated)
  | returned allowed copied present called output =>
      rename_i input memory response result
      subst available
      obtain ⟨extra, copiedStore, inputCode, length, retained, inputs', inputRelated, inputRead, entered⟩ := snapshot_evaluates inputs related copied
      have frame := retained_frame locations retained
      have read := (retained.read callbackLocation (List.getElem?_eq_some_iff.mp handler).1).trans handler
      have functionRead := OptionalCell.read_success Calls.unavailableReason
        ((input_part inputs' (index := 4) rfl).evaluates copiedStore) read
      have requestRead := request_evaluates (inputs'.prepend [function]) (inputRelated.prepend [function]) inputRead
      obtain ⟨target, after, responseRelated, evaluated, afterRelated, sharedAfter, retainedAfter⟩ :=
        preserved called (model.frame frame sharedRelated) (state_retained related retained)
          ((CodeValue.bound (depth + 4) (extra ++ environment) function).evaluates copiedStore) requestRead
      cases responseRelated with
      | returned =>
          obtain ⟨target, final, resultRelated, finished, finalRelated, finishFrame⟩ := finish_preserves
            (inputs'.prepend [responseValue response, function]) afterRelated
            (CodeValue.bound (depth + 4 + 1) (function :: extra ++ environment) (responseValue response)) output
          refine ⟨target, final, resultRelated, ?_, finalRelated, model.frame finishFrame sharedAfter,
            model.retainedTrans (model.retainedTrans (model.retainedFrame frame) retainedAfter) (model.retainedFrame finishFrame)⟩
          apply Evaluates.ifFalse (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word
            (by simp [BinaryOp.apply, Calls.depthLimit, allowed]))
          apply entered
          exact LanguageResult.bind_success .word functionRead (LanguageResult.bind_success .word evaluated finished)

end Solcore.Frontend.RustHull.CallTransportCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallTransportCorrespondence
/-! The complete CALL transport follows the independent range checks, data
reset, depth decision, copied input, callback, and copied response. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

private theorem clear_evaluates {depth : Nat} {environment : Environment} {store final : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    {target : Core.Value} {body : Calls.Code}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (continued : Evaluates ([Core.Value.unit, .unit] ++ environment)
      (publishStore locations store [] Word.zero) (body (depth + 2)) target final) :
    Evaluates environment store
      (Calls.bind (Calls.store Calls.returnData Calls.empty) (fun _ =>
        Calls.bind (Calls.store Calls.returnSize (Calls.number 0)) (fun _ => body)) depth) target final := by
  let writtenData : Store := store.set locations.returnData (WordMapping.encode [])
  have distinct := related.distinct
  simp [Locations.resources, LogsCorrespondence.Locations.all] at distinct
  have dataWritten : store.write? locations.returnData (WordMapping.encode []) = some writtenData :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp related.logs).1, rfl⟩
  have sizeFound : writtenData.read? locations.returnDataSize = some (.word state.returnDataSize) := by
    rw [Store.write?_preserves_other dataWritten (by intro same; simp_all)]
    exact related.logSize
  have sizeWritten : writtenData.write? locations.returnDataSize (.word Word.zero) =
      some (publishStore locations store [] Word.zero) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeFound).1, rfl⟩
  apply Evaluates.letE (bodyStore := writtenData)
  · exact .storeCell ((input_part inputs (index := 2) rfl).evaluates store) related.logs (.construct .unit) dataWritten
  · apply Evaluates.letE (bodyStore := publishStore locations store [] Word.zero)
    · exact .storeCell ((input_part (inputs.prepend [.unit]) (index := 3) rfl).evaluates writtenData)
        sizeFound .word sizeWritten
    · exact continued

theorem callCode_preserves {Shared : Type} {locations : Locations} (model : Model Shared locations)
    {callback : Request → Shared → Semantics.Result Response → Shared → Prop}
    {available : Bool} {arguments : Arguments}
    {state finalState : CallTransportSemantics.State} {shared finalShared : Shared}
    {result : Semantics.Result Semantics.Value}
    (executed : Execute callback available arguments state shared result finalState finalShared)
    {depth : Nat} {environment : Environment} {store : Store} {callbackLocation : Nat} {function : Core.Value}
    (inputs : Inputs depth environment locations callbackLocation arguments)
    (related : StateRel locations state store)
    (sharedRelated : model.related shared store)
    (handler : store.read? callbackLocation = some (callbackValue available function))
    (outside : callbackLocation ∉ locations.all)
    (preserved : CallbackPreservation model callback function) :
    ∃ target final, ResultRel .word result target ∧
      Evaluates environment store (Calls.callCode depth) target final ∧
      StateRel locations finalState final ∧ model.related finalShared final ∧ model.retains store final := by
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  cases executed with
  | inputOverflow _ invalid =>
      simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at touched
      refine ⟨.inLeft .word (.word Memory.overflowReason), store, .language _, ?_, related,
        sharedRelated, model.retainedFrame (.refl _ _)⟩
      exact LanguageResult.bind_failure .word touched
  | outputOverflow _ input invalid =>
      simp only [MemoryCorrespondence.touchResult, input] at touched
      let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size arguments.inputOffset arguments.inputLength
      have inputRelated := related.touch input
      have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size arguments.inputOffset arguments.inputLength
      have inputs' := inputs.prepend [.unit]
      have outputTouched := MemoryCorrespondence.touch_evaluates
        ((input_part inputs' (index := 1) rfl).evaluates inputStore)
        ((input_part inputs' (index := 13) rfl).evaluates inputStore)
        ((input_part inputs' (index := 14) rfl).evaluates inputStore) inputRelated.memorySize
      simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at outputTouched
      refine ⟨.inLeft .word (.word Memory.overflowReason), inputStore, .language _, ?_, inputRelated,
        model.frame inputFrame sharedRelated, model.retainedFrame inputFrame⟩
      exact LanguageResult.bind_success .word touched (LanguageResult.bind_failure .word outputTouched)
  | @ready _ _ _ inputSize outputSize _ input output dispatched =>
      simp only [MemoryCorrespondence.touchResult, input] at touched
      let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size arguments.inputOffset arguments.inputLength
      let outputStore := MemoryCorrespondence.touchStore inputStore locations.memorySize inputSize arguments.outputOffset arguments.outputLength
      have inputRelated := related.touch input
      have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size arguments.inputOffset arguments.inputLength
      have inputs' := inputs.prepend [.unit]
      have outputTouched := MemoryCorrespondence.touch_evaluates
        ((input_part inputs' (index := 1) rfl).evaluates inputStore)
        ((input_part inputs' (index := 13) rfl).evaluates inputStore)
        ((input_part inputs' (index := 14) rfl).evaluates inputStore) inputRelated.memorySize
      simp only [MemoryCorrespondence.touchResult, output] at outputTouched
      have outputRelated : StateRel locations {state with memory := {state.memory with size := outputSize}} outputStore :=
        inputRelated.touch output
      have outputFrame := LogsCorrespondence.Frame.touch locations.resources inputStore inputSize arguments.outputOffset arguments.outputLength
      have clearedRelated := published outputRelated [] Word.zero
      have clearFrame := LogsCorrespondence.Frame.publish locations.resources outputStore [] Word.zero
      have framed := (inputFrame.trans outputFrame).trans clearFrame
      have handler' := framed.read callbackLocation _ outside handler
      obtain ⟨target, final, resultRelated, evaluated, finalRelated, sharedFinal, retained⟩ :=
        dispatch_preserves model dispatched (inputs.prepend [.unit, .unit, .unit, .unit])
          clearedRelated (model.frame framed sharedRelated) handler' preserved
      refine ⟨target, final, resultRelated, ?_, finalRelated, sharedFinal,
        model.retainedTrans (model.retainedFrame framed) retained⟩
      apply LanguageResult.bind_success .word touched
      apply LanguageResult.bind_success .word outputTouched
      exact clear_evaluates (inputs.prepend [.unit, .unit]) outputRelated evaluated

theorem invoke_preserves {Shared : Type} {locations : Locations} (model : Model Shared locations)
    {callback : Request → Shared → Semantics.Result Response → Shared → Prop}
    {available : Bool} {arguments : Arguments}
    {state finalState : CallTransportSemantics.State} {shared finalShared : Shared}
    {result : Semantics.Result Semantics.Value}
    (executed : Execute callback available arguments state shared result finalState finalShared)
    {environment : Environment} {initial store : Store} {callbackLocation : Nat} {function : Core.Value}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      callerAddress currentDepth staticFlag suppliedGas address transferredValue
      sourceOffset sourceLength destinationOffset destinationLength : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, callerAddress, currentDepth, staticFlag, suppliedGas, address,
        transferredValue, sourceOffset, sourceLength, destinationOffset, destinationLength])
      (bundleValues (argumentValues locations callbackLocation arguments)) store)
    (related : StateRel locations state store)
    (sharedRelated : model.related shared store)
    (handler : store.read? callbackLocation = some (callbackValue available function))
    (outside : callbackLocation ∉ locations.all)
    (preserved : CallbackPreservation model callback function) :
    ∃ target final, ResultRel .word result target ∧
      Evaluates environment initial
        (Calls.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
          callerAddress currentDepth staticFlag suppliedGas address transferredValue
          sourceOffset sourceLength destinationOffset destinationLength) target final ∧
      StateRel locations finalState final ∧ model.related finalShared final ∧ model.retains store final := by
  obtain ⟨target, final, resultRelated, evaluated, finalRelated, sharedFinal, retained⟩ :=
    callCode_preserves model executed (input_initial locations callbackLocation arguments environment)
      related sharedRelated handler outside preserved
  exact ⟨target, final, resultRelated, .letE packed evaluated, finalRelated, sharedFinal, retained⟩

end Solcore.Frontend.RustHull.CallTransportCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallTransportRenamingCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.PrecompileCallCorrespondence
/-! The implemented identity, SHA-256 and RIPEMD-160 precompiles preserve their
independent gas, byte-copy and digest meaning. `Precompiles` keeps its builders
private, so `staticCall_shape` restates the implemented expression with public
builders and proves the restatement by `rfl`. Only these three branches are
spelled out; the elliptic-curve branches remain opaque. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.PrecompileCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

namespace Implementation

def integer (value : Nat) : Code := fun _ => .integer (Int.ofNat value)
def unary (op : UnaryOp) (value : Code) : Code := fun depth => .unary op (value depth)
/-- Field `index` of the ten-field call packet bound at depth zero. -/
def input (index : Nat) : Code := part index 10 (fun depth => .var depth)
def touch (size offset length : Code) : Code := fun depth =>
  Memory.touch (size depth) (offset depth) (length depth)
def copy (memory size destination mapping source length : Code) : Code := fun depth =>
  Memory.copyPackedFrom (memory depth) (size depth) (destination depth)
    (mapping depth) (source depth) (length depth)

def enoughGas (base perWord : Nat) : Code :=
  unary .boolNot (binary .integerLt (unary .wordToInteger (input 4))
    (binary .integerAdd (integer base)
      (binary .integerMul (integer perWord)
        (binary .integerDiv
          (binary .integerAdd (unary .wordToInteger (input 7)) (integer 31)) (integer 32)))))

def finish (mapping length : Code) : Code :=
  bind mapping fun snapshot =>
  bind (store (input 2) snapshot) fun _ =>
  bind (store (input 3) length) fun _ =>
  bindResult .word (copy (input 0) (input 1) (input 8) snapshot (number 0)
    (choose (binary .wordGt length (input 9)) (input 9) length)) fun _ =>
  success (number 1)

def identity (snapshot : Code) : Code :=
  bind (allocate WordMapping.type empty) fun resultMemory =>
  bind (allocate .word (number 0)) fun resultSize =>
  bindResult .word (copy resultMemory resultSize (number 0) snapshot (input 6) (input 7)) fun _ =>
  finish (load resultMemory) (input 7)

def finishWord (value : Code) : Code :=
  bindResult .word (fun depth => WordMapping.insert WordMapping.empty (number 0 depth) (value depth)) fun mapping =>
  finish mapping (number 32)

def hashCall (operation : Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr) (snapshot : Code) : Code :=
  bind (allocate WordMapping.type snapshot) fun sourceMemory =>
  bind (allocate .word (number 0)) fun sourceSize =>
  bindResult .word (fun depth => operation (sourceMemory depth) (sourceSize depth) (input 6 depth) (input 7 depth))
    finishWord

def select (recover p256 : Core.Expr) (snapshot address : Code) : Code :=
  choose (binary .wordEq address (number 1)) (constant recover) <|
  choose (binary .wordEq address (number 2))
    (choose (enoughGas 60 12) (hashCall Sha256.hash snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 3))
    (choose (enoughGas 600 120) (hashCall Ripemd160.hash snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 4))
    (choose (enoughGas 15 3) (identity snapshot) (success (number 0))) (constant p256)

def dispatch (recover p256 : Core.Expr) (snapshot : Code) : Code :=
  bind (binary .wordAnd (input 5) (number (2 ^ 160 - 1))) fun address =>
  select recover p256 snapshot address

def callCode (recover p256 : Core.Expr) : Code :=
  bindResult .word (touch (input 1) (input 6) (input 7)) fun _ =>
  bindResult .word (touch (input 1) (input 8) (input 9)) fun _ =>
  bind (load (input 0)) fun snapshot =>
  bind (store (input 2) empty) fun _ =>
  bind (store (input 3) (number 0)) fun _ =>
  dispatch recover p256 snapshot

end Implementation

/-- The actual precompile expression, with its other branches left opaque. -/
theorem staticCall_shape : ∃ recover p256 : Core.Expr,
    ∀ a b c d e f g h i j : Core.Expr, Precompiles.staticCall a b c d e f g h i j =
      .letE (bundle [a, b, c, d, e, f, g, h, i, j]) (Implementation.callCode recover p256 0) :=
  ⟨_, _, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩

/-- Cells below `boundary` keep their values; later cells may change. -/
structure RetainsBelow (boundary : Nat) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location, location < boundary → final.read? location = initial.read? location

theorem RetainsBelow.refl (boundary : Nat) (store : Core.Store) : RetainsBelow boundary store store :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem RetainsBelow.trans {boundary : Nat} {initial middle final : Core.Store}
    (first : RetainsBelow boundary initial middle) (second : RetainsBelow boundary middle final) :
    RetainsBelow boundary initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun location below => by
    rw [second.read location below, first.read location below]⟩

theorem RetainsBelow.append {boundary : Nat} {store : Core.Store} (bounded : boundary ≤ store.length)
    (suffix : Core.Store) : RetainsBelow boundary store (store ++ suffix) :=
  ⟨by simp, fun location below => List.getElem?_append_left (by omega)⟩

theorem RetainsBelow.set {boundary location : Nat} (above : boundary ≤ location)
    (store : Core.Store) (value : Core.Value) :
    RetainsBelow boundary store (store.set location value) :=
  ⟨by simp, fun other below => by
    simp only [Store.read?]
    exact List.getElem?_set_ne (by omega)⟩

theorem RetainsBelow.ofFrame {boundary memoryLocation sizeLocation : Nat} {initial final : Core.Store}
    (framed : MemoryCorrespondence.Frame memoryLocation sizeLocation initial final)
    (memoryAbove : boundary ≤ memoryLocation) (sizeAbove : boundary ≤ sizeLocation)
    (bounded : boundary ≤ initial.length) : RetainsBelow boundary initial final :=
  ⟨framed.length, fun location below => by
    obtain ⟨value, found⟩ : ∃ value, initial.read? location = some value :=
      ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le below bounded)⟩
    rw [found]
    exact framed.read location value (by omega) (by omega) found⟩

theorem RetainsBelow.touch {boundary location : Nat} (above : boundary ≤ location)
    (store : Core.Store) (size offset length : Core.Word) :
    RetainsBelow boundary store (MemoryCorrespondence.touchStore store location size offset length) :=
  ⟨Nat.le_of_eq (MemoryCorrespondence.touchStore_length ..).symm, fun other below =>
    MemoryCorrespondence.touchStore_other store (by omega) size offset length⟩

theorem RetainsBelow.retains {initial final : Core.Store}
    (retained : RetainsBelow initial.length initial final) : StoreRetains initial final :=
  ⟨retained.length_le, retained.read⟩

theorem enoughGas_evaluates {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {gas length : Core.Word} (base perWord : Nat)
    (gasCode : CodeValue depth environment (Implementation.input 4) (.word gas))
    (lengthCode : CodeValue depth environment (Implementation.input 7) (.word length)) :
    Core.Evaluates environment store (Implementation.enoughGas base perWord depth)
      (.bool (decide (AccountCallSemantics.linearCost base perWord length ≤ gas.val))) store := by
  apply Core.Evaluates.unary
  · apply Core.Evaluates.binary (.unary (gasCode.evaluates store) rfl)
    · exact .binary .integer (.binary .integer (.binary (.binary (.unary (lengthCode.evaluates store) rfl)
        .integer rfl) .integer rfl) rfl) rfl
    · rfl
  · have divided : Integer.divide (Int.ofNat length.val + Int.ofNat 31) (Int.ofNat 32) =
        Int.ofNat ((length.val + 31) / 32) := by
      simp only [Integer.divide, Int.ofNat_eq_natCast]
      omega
    have total : Int.ofNat base + Int.ofNat perWord * Int.ofNat ((length.val + 31) / 32) =
        Int.ofNat (AccountCallSemantics.linearCost base perWord length) := by
      simp only [AccountCallSemantics.linearCost, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
    rw [divided, total]
    simp only [UnaryOp.apply, Option.some.injEq, Value.bool.injEq, Int.ofNat_eq_natCast]
    by_cases enough : AccountCallSemantics.linearCost base perWord length ≤ gas.val
    · simp only [enough, decide_true, Bool.not_eq_true', decide_eq_false_iff_not]
      omega
    · simp only [enough, decide_false, Bool.not_eq_false', decide_eq_true_eq]
      omega

/-- The ten packet fields received by the precompile body: four fresh cells,
then the forwarded gas, target, input range and the empty output range. -/
def packetValues (memory size data dataSize : Nat) (request : AccountCallSemantics.Request) : List Core.Value :=
  [.cellRef WordMapping.type memory, .cellRef .word size, .cellRef WordMapping.type data, .cellRef .word dataSize,
   .word request.gas, .word request.target, .word Word.zero, .word request.calldataSize, .word Word.zero, .word Word.zero]

def packetValue (memory size data dataSize : Nat) (request : AccountCallSemantics.Request) : Core.Value :=
  bundleValues (packetValues memory size data dataSize request)

theorem packet_field {environment : Core.Environment} {memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} {index : Nat} {value : Core.Value}
    (found : (packetValues memory size data dataSize request)[index]? = some value) :
    CodeValue 0 (packetValue memory size data dataSize request :: environment) (Implementation.input index) value := by
  have packetCode : CodeValue 0 (packetValue memory size data dataSize request :: environment)
      (fun depth => .var depth) (packetValue memory size data dataSize request) := by
    intro extra store
    exact .var (by simp)
  exact packetCode.part found

/-- The environment of a selected branch: the masked address, two discarded
updates, the input snapshot, two discarded touches and the call packet. -/
def branchEnvironment (address memory size data dataSize : Nat) (request : AccountCallSemantics.Request)
    (environment : Core.Environment) : Core.Environment :=
  [.word (Word.ofNatModulo address), .unit, .unit, WordMapping.encode request.calldata, .unit, .unit,
    packetValue memory size data dataSize request] ++ environment

theorem branch_field {environment : Core.Environment} {address memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} {index : Nat} {value : Core.Value}
    (found : (packetValues memory size data dataSize request)[index]? = some value) :
    CodeValue 6 (branchEnvironment address memory size data dataSize request environment)
      (Implementation.input index) value :=
  (packet_field found).prepend [.word (Word.ofNatModulo address), .unit, .unit, WordMapping.encode request.calldata,
    .unit, .unit]

theorem branch_snapshot {environment : Core.Environment} {address memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} :
    CodeValue 6 (branchEnvironment address memory size data dataSize request environment)
      (fun here => .var (here - 2 - 1)) (WordMapping.encode request.calldata) :=
  (CodeValue.bound 2 ([.unit, .unit, packetValue memory size data dataSize request] ++ environment)
    (WordMapping.encode request.calldata)).prepend [.word (Word.ofNatModulo address), .unit, .unit]

theorem branch_address {environment : Core.Environment} {address memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} :
    CodeValue 6 (branchEnvironment address memory size data dataSize request environment)
      (fun here => .var (here - 5 - 1)) (.word (Word.ofNatModulo address)) :=
  CodeValue.bound 5 ([.unit, .unit, WordMapping.encode request.calldata, .unit, .unit,
    packetValue memory size data dataSize request] ++ environment) (.word (Word.ofNatModulo address))

/-- Both range touches, the return-data reset and target masking reach the
actual selection among the implemented precompiles. -/
theorem callCode_prefix {recover p256 : Core.Expr} {environment : Core.Environment}
    {store : Core.Store} {memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {inputSize : Core.Word} {address : Nat} {flag : Core.Value} {final : Core.Store}
    (masked : request.target.bitAnd (Word.ofNatModulo (2 ^ 160 - 1)) = Word.ofNatModulo address)
    (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some inputSize)
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word Word.zero))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size)
    (continued : Core.Evaluates (branchEnvironment address memory size data dataSize request environment)
      (((MemoryCorrespondence.touchStore store size Word.zero Word.zero request.calldataSize).set data
        (WordMapping.encode [])).set dataSize (.word Word.zero))
      (Implementation.select recover p256 (fun here => .var (here - 2 - 1)) (fun here => .var (here - 5 - 1)) 6)
      flag final) :
    Core.Evaluates (packetValue memory size data dataSize request :: environment) store
      (Implementation.callCode recover p256 0) flag final := by
  let first := MemoryCorrespondence.touchStore store size Word.zero Word.zero request.calldataSize
  have touched := MemoryCorrespondence.touch_evaluates
    (environment := packetValue memory size data dataSize request :: environment)
    ((packet_field (index := 1) rfl).evaluates store) ((packet_field (index := 6) rfl).evaluates store)
    ((packet_field (index := 7) rfl).evaluates store) sizeRead
  simp only [MemoryCorrespondence.touchResult, valid] at touched
  apply LanguageResult.bind_success .word touched
  have firstSize : first.read? size = some (.word inputSize) := MemoryCorrespondence.touchStore_read sizeRead valid
  have touchedOutput := MemoryCorrespondence.touch_evaluates
    (environment := .unit :: packetValue memory size data dataSize request :: environment)
    (((packet_field (index := 1) rfl).prepend [.unit]).evaluates first)
    (((packet_field (index := 8) rfl).prepend [.unit]).evaluates first)
    (((packet_field (index := 9) rfl).prepend [.unit]).evaluates first) firstSize
  have unchanged : MemoryCorrespondence.touchStore first size inputSize Word.zero Word.zero = first := by
    simp [MemoryCorrespondence.touchStore]
  simp only [MemoryCorrespondence.touchResult, MemorySemantics.touchSize?, beq_self_eq_true, ↓reduceIte,
    unchanged] at touchedOutput
  apply LanguageResult.bind_success .word touchedOutput
  have firstMemory : first.read? memory = some (WordMapping.encode request.calldata) :=
    (MemoryCorrespondence.touchStore_other store memorySize _ _ _).trans memoryRead
  apply Core.Evaluates.letE (.loadCell (((packet_field (index := 0) rfl).prepend [.unit, .unit]).evaluates first)
    firstMemory)
  have firstLength : first.length = store.length := MemoryCorrespondence.touchStore_length ..
  have dataFirst : data < first.length := by rw [firstLength]; exact dataBound
  have dataOld : first.read? data = some (first[data]'dataFirst) := List.getElem?_eq_getElem _
  apply Core.Evaluates.letE (.storeCell
    (((packet_field (index := 2) rfl).prepend [WordMapping.encode request.calldata, .unit, .unit]).evaluates first)
    dataOld ((CodeValue.empty _ _).evaluates first) (Store.write?_eq_some_iff.mpr ⟨dataFirst, rfl⟩))
  let second : Store := first.set data (WordMapping.encode [])
  have dataSizeSecond : dataSize < second.length := by
    simp only [second, List.length_set, firstLength]; exact dataSizeBound
  have dataSizeOld : second.read? dataSize = some (second[dataSize]'dataSizeSecond) := List.getElem?_eq_getElem _
  apply Core.Evaluates.letE (.storeCell
    (((packet_field (index := 3) rfl).prepend [.unit, WordMapping.encode request.calldata, .unit, .unit]).evaluates second)
    dataSizeOld .word (Store.write?_eq_some_iff.mpr ⟨dataSizeSecond, rfl⟩))
  apply Core.Evaluates.letE (boundValue := .word (Word.ofNatModulo address)) (.binary
    (((packet_field (index := 5) rfl).prepend [.unit, .unit, WordMapping.encode request.calldata, .unit, .unit]).evaluates _)
    .word (by
      show some (Value.word (request.target.bitAnd (Word.ofNatModulo (2 ^ 160 - 1)))) = _
      rw [masked]))
  exact continued

/-- Address 4 selects the identity branch. -/
theorem select_identity {recover p256 : Core.Expr} {environment : Core.Environment}
    {store final : Core.Store} {memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {flag : Core.Value}
    (continued : Core.Evaluates (branchEnvironment 4 memory size data dataSize request environment) store
      (choose (Implementation.enoughGas 15 3) (Implementation.identity (fun here => .var (here - 2 - 1)))
        (success (number 0)) 6) flag final) :
    Core.Evaluates (branchEnvironment 4 memory size data dataSize request environment) store
      (Implementation.select recover p256 (fun here => .var (here - 2 - 1)) (fun here => .var (here - 5 - 1)) 6)
      flag final := by
  have addressCode := branch_address (environment := environment) (address := 4) (memory := memory) (size := size)
    (data := data) (dataSize := dataSize) (request := request)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  exact .ifTrue (.binary (addressCode.evaluates _) .word rfl) continued

/-- Address 2 selects the SHA-256 branch. -/
theorem select_sha256 {recover p256 : Core.Expr} {environment : Core.Environment}
    {store final : Core.Store} {memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {flag : Core.Value}
    (continued : Core.Evaluates (branchEnvironment 2 memory size data dataSize request environment) store
      (choose (Implementation.enoughGas 60 12) (Implementation.hashCall Sha256.hash (fun here => .var (here - 2 - 1)))
        (success (number 0)) 6) flag final) :
    Core.Evaluates (branchEnvironment 2 memory size data dataSize request environment) store
      (Implementation.select recover p256 (fun here => .var (here - 2 - 1)) (fun here => .var (here - 5 - 1)) 6)
      flag final := by
  have addressCode := branch_address (environment := environment) (address := 2) (memory := memory) (size := size)
    (data := data) (dataSize := dataSize) (request := request)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  exact .ifTrue (.binary (addressCode.evaluates _) .word rfl) continued

/-- Address 3 selects the RIPEMD-160 branch. -/
theorem select_ripemd160 {recover p256 : Core.Expr} {environment : Core.Environment}
    {store final : Core.Store} {memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {flag : Core.Value}
    (continued : Core.Evaluates (branchEnvironment 3 memory size data dataSize request environment) store
      (choose (Implementation.enoughGas 600 120)
        (Implementation.hashCall Ripemd160.hash (fun here => .var (here - 2 - 1)))
        (success (number 0)) 6) flag final) :
    Core.Evaluates (branchEnvironment 3 memory size data dataSize request environment) store
      (Implementation.select recover p256 (fun here => .var (here - 2 - 1)) (fun here => .var (here - 5 - 1)) 6)
      flag final := by
  have addressCode := branch_address (environment := environment) (address := 3) (memory := memory) (size := size)
    (data := data) (dataSize := dataSize) (request := request)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  exact .ifTrue (.binary (addressCode.evaluates _) .word rfl) continued


theorem read_set_other {store : Core.Store} {location other : Nat} {value : Core.Value}
    (different : other ≠ location) : Store.read? (store.set location value) other = store.read? other := by
  simp only [Store.read?]
  exact List.getElem?_set_ne (Ne.symm different)

theorem read_set_self {store : Core.Store} {location : Nat} {value : Core.Value}
    (bound : location < store.length) : Store.read? (store.set location value) location = some value := by
  simp only [Store.read?]
  exact List.getElem?_set_self bound

/-- Sufficient gas copies the complete input into fresh result memory through
the actual copy loop, then publishes that mapping and the input length as
return data. The empty output range leaves caller memory unchanged. -/
theorem identity_evaluates {environment : Core.Environment} {store : Core.Store}
    {boundary memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {inputSize : Core.Word} {output : MemorySemantics.Entries}
    (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some inputSize)
    (copied : MemoryCopySemantics.Copy request.calldata Word.zero Word.zero request.calldataSize [] output)
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word inputSize))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size) (memoryData : memory ≠ data) (memoryDataSize : memory ≠ dataSize)
    (sizeData : size ≠ data) (sizeDataSize : size ≠ dataSize) (dataDataSize : data ≠ dataSize)
    (memoryAbove : boundary ≤ memory) (sizeAbove : boundary ≤ size)
    (dataAbove : boundary ≤ data) (dataSizeAbove : boundary ≤ dataSize) :
    ∃ final, Core.Evaluates (branchEnvironment 4 memory size data dataSize request environment) store
        (Implementation.identity (fun here => .var (here - 2 - 1)) 6)
        (.inRight .word (.word (Word.ofNatModulo 1))) final ∧
      final.read? data = some (WordMapping.encode output) ∧
      final.read? dataSize = some (.word request.calldataSize) ∧ RetainsBelow boundary store final := by
  let base := branchEnvironment 4 memory size data dataSize request environment
  have memoryBound : memory < store.length := (List.getElem?_eq_some_iff.mp memoryRead).1
  have sizeBound : size < store.length := (List.getElem?_eq_some_iff.mp sizeRead).1
  let resultSize := (store ++ [WordMapping.encode []]).length
  let allocated : Core.Store := (store ++ [WordMapping.encode []]) ++ [.word (Word.ofNatModulo 0)]
  have freshRelated : MemoryCorrespondence.StateRel store.length resultSize ⟨[], Word.zero⟩ allocated :=
    ⟨by simp [resultSize], by simp [allocated, Store.read?], by simp [allocated, resultSize, Store.read?]; rfl⟩
  let resultMemoryValue := Core.Value.cellRef WordMapping.type store.length
  let resultSizeValue := Core.Value.cellRef .word resultSize
  have memoryCode := CodeValue.bound 6 base resultMemoryValue
  have sizeCode := CodeValue.bound 7 (resultMemoryValue :: base) resultSizeValue
  obtain ⟨copyTarget, copiedStore, copyRelated, copyEvaluated, copiedRelated, copiedFrame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves (environment := [resultSizeValue, resultMemoryValue] ++ base)
      (MemoryCopySemantics.From.done (initial := ⟨[], Word.zero⟩) valid copied) freshRelated
      ((memoryCode.prepend [resultSizeValue]).evaluates allocated) (sizeCode.evaluates allocated) .word
      ((branch_snapshot.prepend [resultSizeValue, resultMemoryValue]).evaluates allocated)
      (((branch_field (index := 6) rfl).prepend [resultSizeValue, resultMemoryValue]).evaluates allocated)
      (((branch_field (index := 7) rfl).prepend [resultSizeValue, resultMemoryValue]).evaluates allocated)
  cases copyRelated with
  | value unitRelated =>
  cases unitRelated
  have allocatedLength : allocated.length = store.length + 2 := by simp [allocated]
  have copiedLength : store.length + 2 ≤ copiedStore.length := allocatedLength ▸ copiedFrame.length
  have retainedAllocated : ∀ location, location < store.length →
      copiedStore.read? location = store.read? location := by
    intro location below
    have found : allocated.read? location = store.read? location := by
      simp only [allocated, Store.read?, List.append_assoc]
      exact List.getElem?_append_left below
    obtain ⟨value, stored⟩ : ∃ value, store.read? location = some value :=
      ⟨_, List.getElem?_eq_getElem below⟩
    rw [stored] at found ⊢
    exact copiedFrame.read location value (by omega) (by simp [resultSize]; omega) found
  let published : Core.Store := copiedStore.set data (WordMapping.encode output)
  let sized : Core.Store := published.set dataSize (.word request.calldataSize)
  have callerRelated : MemoryCorrespondence.StateRel memory size ⟨request.calldata, inputSize⟩ sized := by
    refine ⟨memorySize, ?_, ?_⟩
    · simp only [sized, published]
      rw [read_set_other memoryDataSize, read_set_other memoryData, retainedAllocated memory memoryBound]
      exact memoryRead
    · simp only [sized, published]
      rw [read_set_other sizeDataSize, read_set_other sizeData, retainedAllocated size sizeBound]
      exact sizeRead
  let outputValue := WordMapping.encode output
  let finishEnvironment := [Core.Value.unit, .unit, outputValue, .unit, resultSizeValue, resultMemoryValue] ++ base
  have finishField {index : Nat} {value : Core.Value}
      (found : (packetValues memory size data dataSize request)[index]? = some value) :
      CodeValue 12 finishEnvironment (Implementation.input index) value :=
    (branch_field found).prepend [.unit, .unit, outputValue, .unit, resultSizeValue, resultMemoryValue]
  have snapshotCode := (CodeValue.bound 9 (.unit :: [resultSizeValue, resultMemoryValue] ++ base) outputValue).prepend
    [.unit, .unit]
  have lengthEvaluated : Core.Evaluates finishEnvironment sized
      (.ifE (.binary .wordGt (Implementation.input 7 12) (Implementation.input 9 12))
        (Implementation.input 9 12) (Implementation.input 7 12)) (.word Word.zero) sized := by
    by_cases positive : request.calldataSize > Word.zero
    · exact .ifTrue (.binary ((finishField (index := 7) rfl).evaluates sized) ((finishField (index := 9) rfl).evaluates sized)
        (by simp [BinaryOp.apply, positive])) ((finishField (index := 9) rfl).evaluates sized)
    · have zero : request.calldataSize = Word.zero := by
        apply Fin.ext
        simp only [GT.gt, Fin.lt_def, Word.zero, Nat.not_lt] at positive
        simpa [Word.zero] using positive
      apply Core.Evaluates.ifFalse (.binary ((finishField (index := 7) rfl).evaluates sized)
        ((finishField (index := 9) rfl).evaluates sized) (by simp [BinaryOp.apply, positive]))
      simpa only [zero] using (finishField (index := 7) rfl).evaluates sized
  obtain ⟨finishTarget, final, finishRelated, finishEvaluated, finalRelated, finalFrame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves (environment := finishEnvironment)
      (MemoryCopySemantics.From.done (initial := ⟨request.calldata, inputSize⟩) (size := inputSize)
        (by simp [MemorySemantics.touchSize?]) (.empty output request.calldata Word.zero Word.zero)) callerRelated
      ((finishField (index := 0) rfl).evaluates sized) ((finishField (index := 1) rfl).evaluates sized)
      ((finishField (index := 8) rfl).evaluates sized) (snapshotCode.evaluates sized) .word lengthEvaluated
  cases finishRelated with
  | value unitRelated =>
  cases unitRelated
  have dataCopied : data < copiedStore.length := by omega
  have dataSizePublished : dataSize < published.length := by simp only [published, List.length_set]; omega
  have dataOld : copiedStore.read? data = some (copiedStore[data]'dataCopied) := List.getElem?_eq_getElem _
  have dataSizeOld : Store.read? published dataSize = some (published[dataSize]'dataSizePublished) :=
    List.getElem?_eq_getElem _
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · apply Core.Evaluates.letE (.newCell ((CodeValue.empty _ _).evaluates store))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply LanguageResult.bind_success .word copyEvaluated
    apply Core.Evaluates.letE (.loadCell ((memoryCode.prepend [.unit, resultSizeValue]).evaluates copiedStore)
      copiedRelated.memory)
    apply Core.Evaluates.letE (.storeCell
      (((branch_field (index := 2) rfl).prepend [outputValue, .unit, resultSizeValue, resultMemoryValue]).evaluates copiedStore)
      dataOld ((CodeValue.bound 9 (.unit :: [resultSizeValue, resultMemoryValue] ++ base) outputValue).evaluates copiedStore)
      (Store.write?_eq_some_iff.mpr ⟨dataCopied, rfl⟩))
    apply Core.Evaluates.letE (.storeCell
      (((branch_field (index := 3) rfl).prepend [.unit, outputValue, .unit, resultSizeValue, resultMemoryValue]).evaluates published)
      dataSizeOld
      (((branch_field (index := 7) rfl).prepend [.unit, outputValue, .unit, resultSizeValue, resultMemoryValue]).evaluates published)
      (Store.write?_eq_some_iff.mpr ⟨dataSizePublished, rfl⟩))
    apply LanguageResult.bind_success .word finishEvaluated
    exact .inRight .word
  · have published : sized.read? data = some outputValue := by
      simp only [sized, published]
      rw [read_set_other dataDataSize, read_set_self dataCopied]
    exact finalFrame.read data _ (Ne.symm memoryData) (Ne.symm sizeData) published
  · have sizedRead : sized.read? dataSize = some (.word request.calldataSize) := read_set_self dataSizePublished
    exact finalFrame.read dataSize _ (Ne.symm memoryDataSize) (Ne.symm sizeDataSize) sizedRead
  · have bounded : boundary ≤ store.length := by omega
    have first : RetainsBelow boundary store allocated := by
      simpa only [allocated, List.append_assoc] using
        RetainsBelow.append bounded ([WordMapping.encode []] ++ [.word (Word.ofNatModulo 0)])
    have second := RetainsBelow.ofFrame (boundary := boundary) copiedFrame (by omega) (by simp [resultSize]; omega)
      (by simp [allocated]; omega)
    have third := RetainsBelow.set (boundary := boundary) dataAbove copiedStore (WordMapping.encode output)
    have fourth := RetainsBelow.set (boundary := boundary) dataSizeAbove published (.word request.calldataSize)
    have fifth := RetainsBelow.ofFrame (boundary := boundary) finalFrame memoryAbove sizeAbove
      (by simp only [sized, published, List.length_set]; omega)
    exact first.trans (second.trans (third.trans (fourth.trans fifth)))

/-- A digest expression that evaluates from fresh source cells holding `words`
to `digest`, changing only those two cells and appending helpers. -/
def HashPreserves (operation : Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr)
    (words : MemorySemantics.Entries) (length digest : Core.Word) : Prop :=
  ∀ {environment : Core.Environment} {store : Core.Store} {memoryLocation sizeLocation : Nat}
    {memoryRef sizeRef offsetExpr lengthExpr : Core.Expr},
    MemoryCorrespondence.StateRel memoryLocation sizeLocation ⟨words, Word.zero⟩ store →
    Core.Evaluates environment store memoryRef (.cellRef WordMapping.type memoryLocation) store →
    Core.Evaluates environment store sizeRef (.cellRef .word sizeLocation) store →
    Core.Evaluates environment store offsetExpr (.word Word.zero) store →
    Core.Evaluates environment store lengthExpr (.word length) store →
    ∃ final, Core.Evaluates environment store (operation memoryRef sizeRef offsetExpr lengthExpr)
        (.inRight .word (.word digest)) final ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store final

theorem sha256_preserves {words : MemorySemantics.Entries} {length size digest : Core.Word}
    (valid : MemorySemantics.touchSize? Word.zero Word.zero length = some size)
    (digested : Sha256Semantics.Digest words Word.zero length digest) :
    HashPreserves Sha256.hash words length digest := by
  intro environment store memoryLocation sizeLocation memoryRef sizeRef offsetExpr lengthExpr
    related memoryEvaluated sizeEvaluated offsetEvaluated lengthEvaluated
  obtain ⟨final, evaluated, _, framed⟩ := Sha256HashCorrespondence.hash_preserves (state := ⟨words, Word.zero⟩)
    valid digested related memoryEvaluated sizeEvaluated offsetEvaluated lengthEvaluated
  exact ⟨final, evaluated, framed⟩

theorem ripemd160_preserves {words : MemorySemantics.Entries} {length size digest : Core.Word}
    (valid : MemorySemantics.touchSize? Word.zero Word.zero length = some size)
    (digested : Ripemd160Semantics.Digest words Word.zero length digest) :
    HashPreserves Ripemd160.hash words length digest := by
  intro environment store memoryLocation sizeLocation memoryRef sizeRef offsetExpr lengthExpr
    related memoryEvaluated sizeEvaluated offsetEvaluated lengthEvaluated
  obtain ⟨final, evaluated, _, framed⟩ := Ripemd160HashCorrespondence.hash_preserves (state := ⟨words, Word.zero⟩)
    valid digested related memoryEvaluated sizeEvaluated offsetEvaluated lengthEvaluated
  exact ⟨final, evaluated, framed⟩

/-- Sufficient gas digests the complete input from a fresh copy of the input
snapshot through the actual digest expression, then publishes the 32-byte
result as return data. The empty output range leaves caller memory unchanged. -/
theorem hashCall_evaluates {operation : Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr}
    {environment : Core.Environment} {store : Core.Store}
    {address boundary memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {inputSize digest : Core.Word}
    (hashed : HashPreserves operation request.calldata request.calldataSize digest)
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word inputSize))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size) (memoryData : memory ≠ data) (memoryDataSize : memory ≠ dataSize)
    (sizeData : size ≠ data) (sizeDataSize : size ≠ dataSize) (dataDataSize : data ≠ dataSize)
    (memoryAbove : boundary ≤ memory) (sizeAbove : boundary ≤ size)
    (dataAbove : boundary ≤ data) (dataSizeAbove : boundary ≤ dataSize) :
    ∃ final, Core.Evaluates (branchEnvironment address memory size data dataSize request environment) store
        (Implementation.hashCall operation (fun here => .var (here - 2 - 1)) 6)
        (.inRight .word (.word (Word.ofNatModulo 1))) final ∧
      final.read? data = some (WordMapping.encode [(Word.zero, digest)]) ∧
      final.read? dataSize = some (.word (Word.ofNatModulo 32)) ∧ RetainsBelow boundary store final := by
  let base := branchEnvironment address memory size data dataSize request environment
  have memoryBound : memory < store.length := (List.getElem?_eq_some_iff.mp memoryRead).1
  have sizeBound : size < store.length := (List.getElem?_eq_some_iff.mp sizeRead).1
  let sourceSize := (store ++ [WordMapping.encode request.calldata]).length
  let allocated : Core.Store := (store ++ [WordMapping.encode request.calldata]) ++ [.word (Word.ofNatModulo 0)]
  have sourceRelated : MemoryCorrespondence.StateRel store.length sourceSize ⟨request.calldata, Word.zero⟩ allocated :=
    ⟨by simp [sourceSize], by simp [allocated, Store.read?], by simp [allocated, sourceSize, Store.read?]; rfl⟩
  let sourceMemoryValue := Core.Value.cellRef WordMapping.type store.length
  let sourceSizeValue := Core.Value.cellRef .word sourceSize
  have memoryCode := CodeValue.bound 6 base sourceMemoryValue
  have sizeCode := CodeValue.bound 7 (sourceMemoryValue :: base) sourceSizeValue
  obtain ⟨hashed, hashEvaluated, hashedFrame⟩ :=
    hashed (environment := [sourceSizeValue, sourceMemoryValue] ++ base) sourceRelated
      ((memoryCode.prepend [sourceSizeValue]).evaluates allocated) (sizeCode.evaluates allocated)
      (((branch_field (index := 6) rfl).prepend [sourceSizeValue, sourceMemoryValue]).evaluates allocated)
      (((branch_field (index := 7) rfl).prepend [sourceSizeValue, sourceMemoryValue]).evaluates allocated)
  have allocatedLength : allocated.length = store.length + 2 := by simp [allocated]
  have hashedLength : store.length + 2 ≤ hashed.length := allocatedLength ▸ hashedFrame.length
  have retainedAllocated : ∀ location, location < store.length →
      hashed.read? location = store.read? location := by
    intro location below
    have found : allocated.read? location = store.read? location := by
      simp only [allocated, Store.read?, List.append_assoc]
      exact List.getElem?_append_left below
    obtain ⟨value, stored⟩ : ∃ value, store.read? location = some value :=
      ⟨_, List.getElem?_eq_getElem below⟩
    rw [stored] at found ⊢
    exact hashedFrame.read location value (by omega) (by simp [sourceSize]; omega) found
  let digestValue := Core.Value.word digest
  let insertEnvironment := digestValue :: [sourceSizeValue, sourceMemoryValue] ++ base
  let mappingValue := WordMapping.encode [(Word.ofNatModulo 0, digest)]
  let inserted : Core.Store := WordMapping.installedStore hashed WordMapping.insertParameter WordMapping.type
    WordMapping.insertBody (.pair (WordMapping.encode []) (.pair (.word (Word.ofNatModulo 0)) (.word digest)))
    insertEnvironment
  have insertEvaluated : Core.Evaluates insertEnvironment hashed
      (WordMapping.insert WordMapping.empty (.word (Word.ofNatModulo 0)) (.var 0))
      (.inRight .word mappingValue) inserted :=
    WordMapping.insert_evaluates [] (Word.ofNatModulo 0) digest (.construct .unit) .word (.var rfl)
  have insertedRead : ∀ location, location < hashed.length → inserted.read? location = hashed.read? location :=
    fun location bound => List.getElem?_append_left bound
  have insertedLength : hashed.length ≤ inserted.length := by simp [inserted, WordMapping.installedStore]
  have dataInserted : data < inserted.length := by omega
  let published : Core.Store := inserted.set data mappingValue
  let sized : Core.Store := published.set dataSize (.word (Word.ofNatModulo 32))
  have dataSizePublished : dataSize < published.length := by simp only [published, List.length_set]; omega
  have callerRelated : MemoryCorrespondence.StateRel memory size ⟨request.calldata, inputSize⟩ sized := by
    refine ⟨memorySize, ?_, ?_⟩
    · simp only [sized, published]
      rw [read_set_other memoryDataSize, read_set_other memoryData, insertedRead memory (by omega),
        retainedAllocated memory memoryBound]
      exact memoryRead
    · simp only [sized, published]
      rw [read_set_other sizeDataSize, read_set_other sizeData, insertedRead size (by omega),
        retainedAllocated size sizeBound]
      exact sizeRead
  let finishEnvironment := [Core.Value.unit, .unit, mappingValue, mappingValue] ++ insertEnvironment
  have finishField {index : Nat} {value : Core.Value}
      (found : (packetValues memory size data dataSize request)[index]? = some value) :
      CodeValue 13 finishEnvironment (Implementation.input index) value :=
    (branch_field found).prepend [.unit, .unit, mappingValue, mappingValue, digestValue, sourceSizeValue, sourceMemoryValue]
  have snapshotCode := (CodeValue.bound 10 (mappingValue :: insertEnvironment) mappingValue).prepend [.unit, .unit]
  have lengthEvaluated : Core.Evaluates finishEnvironment sized
      (.ifE (.binary .wordGt (.word (Word.ofNatModulo 32)) (Implementation.input 9 13))
        (Implementation.input 9 13) (.word (Word.ofNatModulo 32))) (.word Word.zero) sized :=
    .ifTrue (.binary .word ((finishField (index := 9) rfl).evaluates sized) rfl)
      ((finishField (index := 9) rfl).evaluates sized)
  obtain ⟨finishTarget, final, finishRelated, finishEvaluated, finalRelated, finalFrame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves (environment := finishEnvironment)
      (MemoryCopySemantics.From.done (initial := ⟨request.calldata, inputSize⟩) (size := inputSize)
        (by simp [MemorySemantics.touchSize?]) (.empty [(Word.ofNatModulo 0, digest)] request.calldata Word.zero Word.zero))
      callerRelated
      ((finishField (index := 0) rfl).evaluates sized) ((finishField (index := 1) rfl).evaluates sized)
      ((finishField (index := 8) rfl).evaluates sized) (snapshotCode.evaluates sized) .word lengthEvaluated
  cases finishRelated with
  | value unitRelated =>
  cases unitRelated
  have dataOld : inserted.read? data = some (inserted[data]'dataInserted) := List.getElem?_eq_getElem _
  have dataSizeOld : Store.read? published dataSize = some (published[dataSize]'dataSizePublished) :=
    List.getElem?_eq_getElem _
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · apply Core.Evaluates.letE (.newCell (branch_snapshot.evaluates store))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply LanguageResult.bind_success .word hashEvaluated
    apply LanguageResult.bind_success .word insertEvaluated
    apply Core.Evaluates.letE (.var rfl)
    apply Core.Evaluates.letE (.storeCell
      (((branch_field (index := 2) rfl).prepend [mappingValue, mappingValue, digestValue, sourceSizeValue,
        sourceMemoryValue]).evaluates inserted)
      dataOld ((CodeValue.bound 10 (mappingValue :: insertEnvironment) mappingValue).evaluates inserted)
      (Store.write?_eq_some_iff.mpr ⟨dataInserted, rfl⟩))
    apply Core.Evaluates.letE (.storeCell
      (((branch_field (index := 3) rfl).prepend [.unit, mappingValue, mappingValue, digestValue, sourceSizeValue,
        sourceMemoryValue]).evaluates published)
      dataSizeOld .word (Store.write?_eq_some_iff.mpr ⟨dataSizePublished, rfl⟩))
    apply LanguageResult.bind_success .word finishEvaluated
    exact .inRight .word
  · have sizedRead : sized.read? data = some mappingValue := by
      simp only [sized, published]
      rw [read_set_other dataDataSize, read_set_self dataInserted]
    exact finalFrame.read data _ (Ne.symm memoryData) (Ne.symm sizeData) sizedRead
  · have sizedRead : sized.read? dataSize = some (.word (Word.ofNatModulo 32)) := read_set_self dataSizePublished
    exact finalFrame.read dataSize _ (Ne.symm memoryDataSize) (Ne.symm sizeDataSize) sizedRead
  · have bounded : boundary ≤ store.length := by omega
    have first : RetainsBelow boundary store allocated := by
      simpa only [allocated, List.append_assoc] using
        RetainsBelow.append bounded ([WordMapping.encode request.calldata] ++ [.word (Word.ofNatModulo 0)])
    have second := RetainsBelow.ofFrame (boundary := boundary) hashedFrame (by omega)
      (by simp [sourceSize]; omega) (by simp [allocated]; omega)
    have third : RetainsBelow boundary hashed inserted :=
      ⟨insertedLength, fun location below => insertedRead location (by omega)⟩
    have fourth := RetainsBelow.set (boundary := boundary) dataAbove inserted mappingValue
    have fifth := RetainsBelow.set (boundary := boundary) dataSizeAbove published (.word (Word.ofNatModulo 32))
    have sixth := RetainsBelow.ofFrame (boundary := boundary) finalFrame memoryAbove sizeAbove
      (by simp only [sized, published, List.length_set]; omega)
    exact first.trans (second.trans (third.trans (fourth.trans (fifth.trans sixth))))

/-- The body's flag, together with the response it leaves in the return-data
cells. -/
inductive Answered (data dataSize : Nat) (final : Core.Store) :
    Semantics.Result AccountCallSemantics.Response → Core.Value → Prop where
  | returned (response : AccountCallSemantics.Response)
      (dataRead : final.read? data = some (WordMapping.encode response.data))
      (sizeRead : final.read? dataSize = some (.word response.size)) :
      Answered data dataSize final (.value response)
        (.inRight .word (.word (Word.ofNatModulo (if response.success then 1 else 0))))
  | language (reason : Core.Word) :
      Answered data dataSize final (.fault (.language reason)) (.inLeft .word (.word reason))

/-- Every independent identity, SHA-256 and RIPEMD-160 outcome is produced by
the actual precompile body. Only its four fresh cells and later allocations
change. -/
theorem callCode_preserves {recover p256 : Core.Expr} {environment : Core.Environment}
    {store : Core.Store} {boundary memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Precompile request result)
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word Word.zero))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size) (memoryData : memory ≠ data) (memoryDataSize : memory ≠ dataSize)
    (sizeData : size ≠ data) (sizeDataSize : size ≠ dataSize) (dataDataSize : data ≠ dataSize)
    (memoryAbove : boundary ≤ memory) (sizeAbove : boundary ≤ size)
    (dataAbove : boundary ≤ data) (dataSizeAbove : boundary ≤ dataSize) :
    ∃ flag final, Core.Evaluates (packetValue memory size data dataSize request :: environment) store
        (Implementation.callCode recover p256 0) flag final ∧
      Answered data dataSize final result flag ∧ RetainsBelow boundary store final := by
  let first := MemoryCorrespondence.touchStore store size Word.zero Word.zero request.calldataSize
  let prepared : Core.Store := (first.set data (WordMapping.encode [])).set dataSize (.word Word.zero)
  have firstLength : first.length = store.length := MemoryCorrespondence.touchStore_length ..
  have dataFirst : data < first.length := by omega
  have dataSizeCleared : dataSize < (first.set data (WordMapping.encode [])).length := by
    simp only [List.length_set]; omega
  have preparedRetained : RetainsBelow boundary store prepared :=
    (RetainsBelow.touch sizeAbove store _ _ _).trans
      ((RetainsBelow.set dataAbove first _).trans (RetainsBelow.set dataSizeAbove _ _))
  have preparedData : prepared.read? data = some (WordMapping.encode []) := by
    simp only [prepared]
    rw [read_set_other dataDataSize, read_set_self dataFirst]
  have preparedDataSize : prepared.read? dataSize = some (.word Word.zero) := read_set_self dataSizeCleared
  have preparedMemory : prepared.read? memory = some (WordMapping.encode request.calldata) := by
    simp only [prepared]
    rw [read_set_other memoryDataSize, read_set_other memoryData,
      MemoryCorrespondence.touchStore_other store memorySize]
    exact memoryRead
  have preparedLength : prepared.length = store.length := by simp [prepared, firstLength]
  have preparedSize {inputSize : Core.Word}
      (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some inputSize) :
      prepared.read? size = some (.word inputSize) := by
    simp only [prepared]
    rw [read_set_other sizeDataSize, read_set_other sizeData]
    exact MemoryCorrespondence.touchStore_read sizeRead valid
  have enough (address base perWord : Nat) := enoughGas_evaluates (store := prepared) base perWord
    (branch_field (environment := environment) (address := address) (memory := memory) (size := size) (data := data)
      (dataSize := dataSize) (request := request) (index := 4) rfl)
    (branch_field (environment := environment) (address := address) (memory := memory) (size := size) (data := data)
      (dataSize := dataSize) (request := request) (index := 7) rfl)
  have overflowed (invalid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = none) :
      ∃ flag final, Core.Evaluates (packetValue memory size data dataSize request :: environment) store
        (Implementation.callCode recover p256 0) flag final ∧
      Answered data dataSize final (.fault (.language (Word.ofNatModulo 6))) flag ∧
      RetainsBelow boundary store final := by
    have touched := MemoryCorrespondence.touch_evaluates
      (environment := packetValue memory size data dataSize request :: environment)
      ((packet_field (index := 1) rfl).evaluates store) ((packet_field (index := 6) rfl).evaluates store)
      ((packet_field (index := 7) rfl).evaluates store) sizeRead
    simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at touched
    exact ⟨_, store, LanguageResult.bind_failure .word touched, .language _, .refl _ _⟩
  have maskedIdentity : (Word.ofNatModulo 4).bitAnd (Word.ofNatModulo (2 ^ 160 - 1)) = Word.ofNatModulo 4 := by
    decide +kernel
  have maskedSha256 : (Word.ofNatModulo 2).bitAnd (Word.ofNatModulo (2 ^ 160 - 1)) = Word.ofNatModulo 2 := by
    decide +kernel
  have maskedRipemd160 : (Word.ofNatModulo 3).bitAnd (Word.ofNatModulo (2 ^ 160 - 1)) = Word.ofNatModulo 3 := by
    decide +kernel
  cases computed with
  | identityOverflow _ invalid => exact overflowed invalid
  | sha256Overflow _ invalid => exact overflowed invalid
  | identityUnderfunded identity valid short =>
    refine ⟨_, prepared, callCode_prefix (by rw [identity]; exact maskedIdentity) valid memoryRead sizeRead dataBound
      dataSizeBound memorySize (select_identity ?_),
      .returned (AccountCallSemantics.emptyResponse false) preparedData preparedDataSize, preparedRetained⟩
    have checked := enough 4 15 3
    simp only [Nat.not_le.mpr short, decide_false] at checked
    exact .ifFalse checked (.inRight .word)
  | @identity inputSize output identity valid funded copied =>
    obtain ⟨final, evaluated, dataRead, dataSizeRead, retained⟩ := identity_evaluates (environment := environment)
      valid copied preparedMemory (preparedSize valid) (by omega) (by omega) memorySize memoryData memoryDataSize
      sizeData sizeDataSize dataDataSize memoryAbove sizeAbove dataAbove dataSizeAbove
    refine ⟨_, final, callCode_prefix (by rw [identity]; exact maskedIdentity) valid memoryRead sizeRead dataBound
      dataSizeBound memorySize (select_identity ?_),
      .returned ⟨true, output, request.calldataSize⟩ dataRead dataSizeRead, preparedRetained.trans retained⟩
    have checked := enough 4 15 3
    simp only [funded, decide_true] at checked
    exact .ifTrue checked evaluated
  | sha256Underfunded sha256 valid short =>
    refine ⟨_, prepared, callCode_prefix (by rw [sha256]; exact maskedSha256) valid memoryRead sizeRead dataBound
      dataSizeBound memorySize (select_sha256 ?_),
      .returned (AccountCallSemantics.emptyResponse false) preparedData preparedDataSize, preparedRetained⟩
    have checked := enough 2 60 12
    simp only [Nat.not_le.mpr short, decide_false] at checked
    exact .ifFalse checked (.inRight .word)
  | @sha256 inputSize digest sha256 valid funded digested =>
    obtain ⟨final, evaluated, dataRead, dataSizeRead, retained⟩ := hashCall_evaluates (environment := environment)
      (address := 2) (sha256_preserves valid digested) preparedMemory (preparedSize valid) (by omega) (by omega)
      memorySize memoryData memoryDataSize sizeData sizeDataSize dataDataSize memoryAbove sizeAbove dataAbove
      dataSizeAbove
    refine ⟨_, final, callCode_prefix (by rw [sha256]; exact maskedSha256) valid memoryRead sizeRead dataBound
      dataSizeBound memorySize (select_sha256 ?_),
      .returned ⟨true, [(Word.zero, digest)], Word.ofNatModulo 32⟩ dataRead dataSizeRead,
      preparedRetained.trans retained⟩
    have checked := enough 2 60 12
    simp only [funded, decide_true] at checked
    exact .ifTrue checked evaluated
  | ripemd160Overflow _ invalid => exact overflowed invalid
  | ripemd160Underfunded ripemd160 valid short =>
    refine ⟨_, prepared, callCode_prefix (by rw [ripemd160]; exact maskedRipemd160) valid memoryRead sizeRead
      dataBound dataSizeBound memorySize (select_ripemd160 ?_),
      .returned (AccountCallSemantics.emptyResponse false) preparedData preparedDataSize, preparedRetained⟩
    have checked := enough 3 600 120
    simp only [Nat.not_le.mpr short, decide_false] at checked
    exact .ifFalse checked (.inRight .word)
  | @ripemd160 inputSize digest ripemd160 valid funded digested =>
    obtain ⟨final, evaluated, dataRead, dataSizeRead, retained⟩ := hashCall_evaluates (environment := environment)
      (address := 3) (ripemd160_preserves valid digested) preparedMemory (preparedSize valid) (by omega) (by omega)
      memorySize memoryData memoryDataSize sizeData sizeDataSize dataDataSize memoryAbove sizeAbove dataAbove
      dataSizeAbove
    refine ⟨_, final, callCode_prefix (by rw [ripemd160]; exact maskedRipemd160) valid memoryRead sizeRead dataBound
      dataSizeBound memorySize (select_ripemd160 ?_),
      .returned ⟨true, [(Word.zero, digest)], Word.ofNatModulo 32⟩ dataRead dataSizeRead,
      preparedRetained.trans retained⟩
    have checked := enough 3 600 120
    simp only [funded, decide_true] at checked
    exact .ifTrue checked evaluated

/-- The actual precompile expression evaluates its ten arguments into the
packet and runs the precompile body. -/
theorem staticCall_preserves {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {memoryCode sizeCode dataCode dataSizeCode gasCode targetCode lengthCode : Code}
    {boundary memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Precompile request result)
    (memoryValue : CodeValue depth environment memoryCode (.cellRef WordMapping.type memory))
    (sizeValue : CodeValue depth environment sizeCode (.cellRef .word size))
    (dataValue : CodeValue depth environment dataCode (.cellRef WordMapping.type data))
    (dataSizeValue : CodeValue depth environment dataSizeCode (.cellRef .word dataSize))
    (gasValue : CodeValue depth environment gasCode (.word request.gas))
    (targetValue : CodeValue depth environment targetCode (.word request.target))
    (lengthValue : CodeValue depth environment lengthCode (.word request.calldataSize))
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word Word.zero))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size) (memoryData : memory ≠ data) (memoryDataSize : memory ≠ dataSize)
    (sizeData : size ≠ data) (sizeDataSize : size ≠ dataSize) (dataDataSize : data ≠ dataSize)
    (memoryAbove : boundary ≤ memory) (sizeAbove : boundary ≤ size)
    (dataAbove : boundary ≤ data) (dataSizeAbove : boundary ≤ dataSize) :
    ∃ flag final, Core.Evaluates environment store
        (Precompiles.staticCall (memoryCode depth) (sizeCode depth) (dataCode depth) (dataSizeCode depth)
          (gasCode depth) (targetCode depth) (number 0 depth) (lengthCode depth) (number 0 depth) (number 0 depth))
        flag final ∧
      Answered data dataSize final result flag ∧ RetainsBelow boundary store final := by
  obtain ⟨recover, p256, shape⟩ := staticCall_shape
  obtain ⟨flag, final, evaluated, answered, retained⟩ := callCode_preserves (recover := recover)
    (p256 := p256) (environment := environment) computed memoryRead sizeRead dataBound
    dataSizeBound memorySize memoryData memoryDataSize sizeData sizeDataSize dataDataSize memoryAbove sizeAbove
    dataAbove dataSizeAbove
  refine ⟨flag, final, ?_, answered, retained⟩
  rw [shape]
  apply Core.Evaluates.letE _ evaluated
  exact .pair (memoryValue.evaluates store) (.pair (sizeValue.evaluates store) (.pair (dataValue.evaluates store)
    (.pair (dataSizeValue.evaluates store) (.pair (gasValue.evaluates store) (.pair (targetValue.evaluates store)
      (.pair .word (.pair (lengthValue.evaluates store) (.pair .word .word))))))))

/-- The account runtime's private precompile call, restated with public
builders. `AccountCallCorrespondence.dispatch_precompile_eq` proves that it is
the implementation. -/
def precompileCode (request : Code) : Code :=
  bind (allocate WordMapping.type (part 6 8 request)) fun memory =>
  bind (allocate .word (number 0)) fun size =>
  bind (allocate WordMapping.type empty) fun data =>
  bind (allocate .word (number 0)) fun dataSize =>
  bindResult Calls.responseType (fun depth => Precompiles.staticCall
    (memory depth) (size depth) (data depth) (dataSize depth)
    (part 5 8 request depth) (part 0 8 request depth)
    (number 0 depth) (part 7 8 request depth) (number 0 depth) (number 0 depth)) fun flag =>
  AccountRuntime.callResult (binary .wordEq flag (number 1)) (load data) (load dataSize)

/-- The independent precompile result is the actual response. The fresh
precompile cells lie above every cell of the calling store. -/
theorem precompile_preserves {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {requestCode : Code} {request : AccountCallSemantics.Request}
    {result : Semantics.Result AccountCallSemantics.Response}
    (requestRelated : CodeValue depth environment requestCode (requestValue request))
    (computed : AccountCallSemantics.Precompile request result) :
    ∃ target final, Core.Evaluates environment store (precompileCode requestCode depth) target final ∧
      ResponseRel result target ∧ StoreRetains store final := by
  let memory := store.length
  let first : Core.Store := store ++ [WordMapping.encode request.calldata]
  let size := first.length
  let second : Core.Store := first ++ [.word (Word.ofNatModulo 0)]
  let data := second.length
  let third : Core.Store := second ++ [WordMapping.encode []]
  let dataSize := third.length
  let allocated : Core.Store := third ++ [.word (Word.ofNatModulo 0)]
  let memoryRef := Core.Value.cellRef WordMapping.type memory
  let sizeRef := Core.Value.cellRef .word size
  let dataRef := Core.Value.cellRef WordMapping.type data
  let dataSizeRef := Core.Value.cellRef .word dataSize
  let cells : Core.Environment := [dataSizeRef, dataRef, sizeRef, memoryRef]
  have lengths : size = store.length + 1 ∧ data = store.length + 2 ∧ dataSize = store.length + 3 ∧
      allocated.length = store.length + 4 := by
    simp [size, data, dataSize, allocated, third, second, first]
  have memoryRead : allocated.read? memory = some (WordMapping.encode request.calldata) := by
    simp [allocated, third, second, first, memory, Store.read?]
  have sizeRead : allocated.read? size = some (.word Word.zero) := by
    simp [allocated, third, second, first, size, Store.read?]; rfl
  have memoryValue : CodeValue (depth + 4) (cells ++ environment) (fun here => .var (here - depth - 1)) memoryRef :=
    (CodeValue.bound depth environment memoryRef).prepend [dataSizeRef, dataRef, sizeRef]
  have sizeValue : CodeValue (depth + 4) (cells ++ environment) (fun here => .var (here - (depth + 1) - 1)) sizeRef :=
    (CodeValue.bound (depth + 1) (memoryRef :: environment) sizeRef).prepend [dataSizeRef, dataRef]
  have dataValue : CodeValue (depth + 4) (cells ++ environment)
      (fun here => .var (here - (depth + 1 + 1) - 1)) dataRef :=
    (CodeValue.bound (depth + 1 + 1) (sizeRef :: memoryRef :: environment) dataRef).prepend [dataSizeRef]
  have dataSizeValue : CodeValue (depth + 4) (cells ++ environment)
      (fun here => .var (here - (depth + 1 + 1 + 1) - 1)) dataSizeRef :=
    CodeValue.bound (depth + 1 + 1 + 1) (dataRef :: sizeRef :: memoryRef :: environment) dataSizeRef
  have requestValue' := requestRelated.prepend cells
  obtain ⟨flag, final, evaluated, answered, retained⟩ := staticCall_preserves (boundary := store.length)
    computed memoryValue sizeValue dataValue dataSizeValue (requestValue'.part (index := 5) rfl)
    (requestValue'.part (index := 0) rfl) (requestValue'.part (index := 7) rfl) memoryRead sizeRead
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (Nat.le_refl _) (by omega) (by omega) (by omega)
  have allocatedRetained : StoreRetains store allocated := by
    simpa only [allocated, third, second, first, List.append_assoc] using StoreRetains.append store _
  have finalRetained : StoreRetains store final :=
    ⟨Nat.le_trans allocatedRetained.length_le retained.length_le, fun location below => by
      rw [retained.read location below, allocatedRetained.read location below]⟩
  cases answered with
  | returned response dataRead dataSizeRead =>
    refine ⟨.inRight .word (responseValue response), final, ?_, .returned response, finalRetained⟩
    apply Core.Evaluates.letE (.newCell ((requestRelated.part (index := 6) rfl).evaluates store))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply Core.Evaluates.letE (.newCell ((CodeValue.empty _ _).evaluates _))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply LanguageResult.bind_success Calls.responseType evaluated
    let flagValue := Core.Value.word (Word.ofNatModulo (if response.success then 1 else 0))
    have flagCode := CodeValue.bound (depth + 4) (cells ++ environment) flagValue
    have flagEquals : BinaryOp.wordEq.apply flagValue (.word (Word.ofNatModulo 1)) = some (.bool response.success) := by
      show BinaryOp.wordEq.apply (.word (Word.ofNatModulo (if response.success = true then 1 else 0)))
        (.word (Word.ofNatModulo 1)) = some (.bool response.success)
      cases response.success <;> rfl
    exact .inRight (.pair (.binary (flagCode.evaluates final) .word flagEquals)
      (.pair (.loadCell ((dataValue.prepend [flagValue]).evaluates final) dataRead)
        (.loadCell ((dataSizeValue.prepend [flagValue]).evaluates final) dataSizeRead)))
  | language reason =>
    refine ⟨.inLeft Calls.responseType (.word reason), final, ?_, .language reason, finalRetained⟩
    apply Core.Evaluates.letE (.newCell ((requestRelated.part (index := 6) rfl).evaluates store))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply Core.Evaluates.letE (.newCell ((CodeValue.empty _ _).evaluates _))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    exact LanguageResult.bind_failure Calls.responseType evaluated

end Solcore.Frontend.RustHull.PrecompileCorrespondence
end
