import Solcore.Frontend.RustHull.AccountObservationSemantics
import Solcore.Frontend.RustHull.MemoryCopyBuiltinCorrespondence

/-! The actual account builtin compiler fixes the argument shapes and resolves
the runtime references used by account observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull

def AccountObservationSemantics.Operation.arity : AccountObservationSemantics.Operation → Nat
  | .selfbalance => 0
  | .copy => 4
  | _ => 1

namespace AccountObservationBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open AccountObservationSemantics (Operation)

theorem four_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 4) :
    ∃ first second third fourth left middle right last,
      arguments = [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩, ⟨.word, fourth⟩] ∧
      sources = [.word left, .word middle, .word right, .word last] ∧
      targets = [.word left, .word middle, .word right, .word last] := by
  cases related with
  | nil => cases length
  | @cons first rest source sources target targets head tail =>
      obtain ⟨second, third, fourth, middle, right, last, rfl, rfl, rfl⟩ :=
        MemoryCopyBuiltinCorrespondence.three_words tail
          (fun argument member => words argument (.tail _ member)) (Nat.succ.inj length)
      have typed := words first (.head _)
      cases first with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word left =>
              exact ⟨expression, second, third, fourth, left, middle, right, last, rfl, rfl, rfl⟩

theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation with
  | balance =>
      rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled
  | selfbalance =>
      rcases arguments with _ | ⟨first, rest⟩
      · rfl
      · change Except.error _ = Except.ok lowered at compiled
        cases compiled
  | size =>
      change AccountInspection.lowerBuiltin scope "extcodesize" arguments = .ok lowered at compiled
      unfold AccountInspection.lowerBuiltin at compiled
      obtain ⟨world, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨complete, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled
  | copy =>
      change AccountInspection.lowerBuiltin scope "extcodecopy" arguments = .ok lowered at compiled
      unfold AccountInspection.lowerBuiltin at compiled
      obtain ⟨world, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨complete, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, rest⟩⟩⟩⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled
  | hash =>
      change AccountInspection.lowerBuiltin scope "extcodehash" arguments = .ok lowered at compiled
      unfold AccountInspection.lowerBuiltin at compiled
      obtain ⟨world, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨complete, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled

theorem balance_components {scope : Scope} {target : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "balance" [target] = .ok lowered) :
    ∃ balances, Effects.reference scope "balances" WordMapping.type = .ok balances ∧
      lowered = ⟨.word, WordMapping.lookup (.loadCell balances)
        (.binary .wordAnd target (.word (Word.ofNatModulo (2 ^ 160 - 1))))⟩ := by
  change (do
    let balances ← Effects.reference scope "balances" WordMapping.type
    pure (Lowered.mk .word (WordMapping.lookup (.loadCell balances)
      (.binary .wordAnd target (.word (Word.ofNatModulo (2 ^ 160 - 1))))))) = .ok lowered at compiled
  obtain ⟨balances, found, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨balances, found, (Except.ok.inj returned).symm⟩

theorem selfbalance_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "selfbalance" [] = .ok lowered) :
    ∃ balances address, Effects.reference scope "balances" WordMapping.type = .ok balances ∧
      Effects.reference scope "address" .word = .ok address ∧
      lowered = ⟨.word, WordMapping.lookup (.loadCell balances) (.loadCell address)⟩ := by
  change (do
    let balances ← Effects.reference scope "balances" WordMapping.type
    let address ← Effects.reference scope "address" .word
    pure (Lowered.mk .word (WordMapping.lookup (.loadCell balances) (.loadCell address)))) = .ok lowered at compiled
  obtain ⟨balances, balancesCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨address, addressCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨balances, address, balancesCompiled, addressCompiled, (Except.ok.inj returned).symm⟩

theorem size_components {scope : Scope} {target : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "extcodesize" [target] = .ok lowered) :
    ∃ world complete, Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      lowered = ⟨.word, AccountInspection.size world (.loadCell complete) target⟩ := by
  change (do
    let world ← Effects.reference scope "world" AccountState.type
    let complete ← Effects.reference scope "worldComplete" .bool
    pure (Lowered.mk .word (AccountInspection.size world (.loadCell complete) target))) = .ok lowered at compiled
  obtain ⟨world, worldCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨complete, completeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨world, complete, worldCompiled, completeCompiled, (Except.ok.inj returned).symm⟩

theorem copy_components {scope : Scope} {target destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "extcodecopy" [target, destination, source, length] = .ok lowered) :
    ∃ world complete memory size, Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, AccountInspection.copy world (.loadCell complete) memory size target destination source length⟩ := by
  change (do
    let world ← Effects.reference scope "world" AccountState.type
    let complete ← Effects.reference scope "worldComplete" .bool
    let memory ← Effects.reference scope "memory" WordMapping.type
    let size ← Effects.reference scope "memorySize" .word
    pure (Lowered.mk .unit (AccountInspection.copy world (.loadCell complete) memory size target destination source length))) = .ok lowered at compiled
  obtain ⟨world, worldCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨complete, completeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨world, complete, memory, size, worldCompiled, completeCompiled, memoryCompiled, sizeCompiled,
    (Except.ok.inj returned).symm⟩

theorem hash_components {scope : Scope} {target : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "extcodehash" [target] = .ok lowered) :
    ∃ world complete balances, Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      Effects.reference scope "balances" WordMapping.type = .ok balances ∧
      lowered = ⟨.word, AccountInspection.hash world (.loadCell complete) balances target⟩ := by
  change (do
    let world ← Effects.reference scope "world" AccountState.type
    let complete ← Effects.reference scope "worldComplete" .bool
    let balances ← Effects.reference scope "balances" WordMapping.type
    pure (Lowered.mk .word (AccountInspection.hash world (.loadCell complete) balances target))) = .ok lowered at compiled
  obtain ⟨world, worldCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨complete, completeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨balances, balancesCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨world, complete, balances, worldCompiled, completeCompiled, balancesCompiled,
    (Except.ok.inj returned).symm⟩

end AccountObservationBuiltinCorrespondence
end Solcore.Frontend.RustHull
