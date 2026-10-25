import Solcore.Frontend.RustHull.CallBuiltinCompiler
import Solcore.Frontend.RustHull.AccountObservationBuiltinCompiler

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
