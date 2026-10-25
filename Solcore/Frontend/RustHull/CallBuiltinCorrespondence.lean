import Solcore.Frontend.RustHull.ChildCallBuiltinCorrespondence
import Solcore.Frontend.RustHull.RuntimeChildCallEmptyCorrespondence

/-! Ordinary and static calls preserve their independent source results through
actual argument packing, ordered guards, callback dispatch, and caller updates. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.CallBuiltinCorrespondence
open Core Correspondence ScalarExecution PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence

section
variable {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
variable {gas target value inputOffset inputLength outputOffset outputLength : Word}
variable {result : Semantics.Result Semantics.Value} {finalState : RuntimeCallEffectsSemantics.State}
variable {targets : List Core.Value} {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
variable {initial store : Store} {layout : Layout} {baseline : Nat → Option Value}
variable {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
variable {state : Semantics.State RuntimeCallEffectsSemantics.State}

theorem ordinary_preserves
    (compiled : lowerBuiltin scope "call" expected arguments = .ok lowered)
    (computed : RuntimeCallEffectsSemantics.Call (fun _ => AccountCallSemantics.noChildren) .ordinary
      gas target value inputOffset inputLength outputOffset outputLength state.external result finalState)
    (related : ArgumentsRel arguments [.word gas, .word target, .word value, .word inputOffset,
      .word inputLength, .word outputOffset, .word outputLength] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (handlerMember : ⟨"callHandler", OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers) world state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    ChildCallBuiltinCorrespondence.ordinary_preserves compiled computed related runtime passive callPassive
      memoryMember memorySizeMember dataMember dataSizeMember handlerMember addressMember depthMember staticMember
      exitMember offsetMember sizeMember (RuntimeChildCallEffectsCorrespondence.empty_state stateRelated)
      (RuntimeChildCallEffectsCorrespondence.empty_callback layout handlers state.external (source_eq stateRelated)) packed
  exact ⟨resultValue, final, resultRelated, evaluated,
    RuntimeChildCallEffectsCorrespondence.base_related finalRelated, retained⟩

theorem static_preserves
    (compiled : lowerBuiltin scope "staticcall" expected arguments = .ok lowered)
    (computed : RuntimeCallEffectsSemantics.Call (fun _ => AccountCallSemantics.noChildren) .staticCall
      gas target Word.zero inputOffset inputLength outputOffset outputLength state.external result finalState)
    (related : ArgumentsRel arguments [.word gas, .word target, .word inputOffset,
      .word inputLength, .word outputOffset, .word outputLength] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (_passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (handlerMember : ⟨"callHandler", OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (_exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (_offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (_sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers) world state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    ChildCallBuiltinCorrespondence.static_preserves compiled computed related runtime _passive callPassive
      memoryMember memorySizeMember dataMember dataSizeMember handlerMember addressMember depthMember staticMember
      _exitMember _offsetMember _sizeMember (RuntimeChildCallEffectsCorrespondence.empty_state stateRelated)
      (RuntimeChildCallEffectsCorrespondence.empty_callback layout handlers state.external (source_eq stateRelated)) packed
  exact ⟨resultValue, final, resultRelated, evaluated,
    RuntimeChildCallEffectsCorrespondence.base_related finalRelated, retained⟩

end
end Solcore.Frontend.RustHull.CallBuiltinCorrespondence
