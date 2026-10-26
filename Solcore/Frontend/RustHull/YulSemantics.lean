import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics

/-! The connected fragment of inline Yul, independently of its lowering. An
assembly block holds one statement that calls `mstore`, `mstore8`, `return` or
`revert` on two literal words. Yul evaluates call arguments from right to left;
literals have no effect, so the order is not observable in this fragment.
Number and hexadecimal literals are words in the text of Hull word literals,
and `true` and `false` are one and zero. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulSemantics
open Core

/-- The word a literal denotes. String literals are outside the fragment. -/
def literalWord? : YulLit → Option Word
  | .number text | .hex text => Semantics.parseWord? text
  | .bool value => some (Word.ofNatModulo (if value then 1 else 0))
  | .string _ => none

/-- A builtin of the fragment on its two argument words: a memory write, or the
return or revert termination over a memory range. -/
inductive Builtin : String → Word → Word → RuntimeEffectsSemantics.State →
    Semantics.Result Semantics.Value → RuntimeEffectsSemantics.State → Prop where
  | mstore {frame : RuntimeEffectsSemantics.State} {offset value : Word} :
      Builtin "mstore" offset value frame (MemorySemantics.mstore frame.memory offset value).1
        {frame with memory := (MemorySemantics.mstore frame.memory offset value).2}
  | mstore8 {frame : RuntimeEffectsSemantics.State} {offset value : Word} :
      Builtin "mstore8" offset value frame (MemorySemantics.mstore8 frame.memory offset value).1
        {frame with memory := (MemorySemantics.mstore8 frame.memory offset value).2}
  | returned {frame : RuntimeEffectsSemantics.State} {offset length : Word} :
      Builtin "return" offset length frame (TerminationSemantics.terminate frame 1 offset length).1
        (TerminationSemantics.terminate frame 1 offset length).2
  | reverted {frame : RuntimeEffectsSemantics.State} {offset length : Word} :
      Builtin "revert" offset length frame (TerminationSemantics.terminate frame 2 offset length).1
        (TerminationSemantics.terminate frame 2 offset length).2

/-- A builtin that returns continues the block; a fault, including the
termination sentinel, stops it. -/
def control : Semantics.Result Semantics.Value → Semantics.Control
  | .value _ => .fallthrough
  | .fault reason => .fault reason

/-- The block's one call: the second argument, then the first, then the builtin
on the frame. -/
inductive Executed : List YulStmt → RuntimeCallEffectsSemantics.State → Semantics.Control →
    RuntimeCallEffectsSemantics.State → Prop where
  | call {name : YulName} {first second : YulLit} {firstSpan secondSpan callSpan statementSpan : Option Span}
      {state : RuntimeCallEffectsSemantics.State} {firstWord secondWord : Word}
      {result : Semantics.Result Semantics.Value} {frame : RuntimeEffectsSemantics.State}
      (secondEvaluated : literalWord? second = some secondWord)
      (firstEvaluated : literalWord? first = some firstWord)
      (computed : Builtin name.name firstWord secondWord state.runtime.runtime.runtime.runtime.runtime result frame) :
      Executed [⟨.expression ⟨.call name [⟨.literal first, firstSpan⟩, ⟨.literal second, secondSpan⟩], callSpan⟩,
          statementSpan⟩] state (control result)
        {state with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.runtime frame}

/-- An assembly block changes only the external state. -/
def Assembled {σ : Type} (executed : List YulStmt → σ → Semantics.Control → σ → Prop)
    (_functions : List Function) (_environment : Semantics.Environment) (body : List YulStmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  ∃ external, executed body initial.external control external ∧ final = {initial with external := external}

end Solcore.Frontend.RustHull.YulSemantics
