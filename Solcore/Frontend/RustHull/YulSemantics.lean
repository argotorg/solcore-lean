import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics

/-! The connected fragment of inline Yul, independently of its lowering. An
assembly block is a list of statements: `let` with one name and an optional
value, assignment to one name, and expression statements. Expressions are
literals, variables and calls of `mload`, `msize`, `mstore`, `mstore8`,
`return` and `revert`. A call evaluates its arguments from right to left, so
nested calls with effects observe the order. Yul locals live in the Hull heap
like Hull locals and are visible until the end of the block; a variable may
also name a Hull word local, which the block reads and assigns in place. Number
and hexadecimal literals are words in the text of Hull word literals, and
`true` and `false` are one and zero. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulSemantics
open Core

abbrev State := Semantics.State RuntimeCallEffectsSemantics.State

/-- The word a literal denotes. String literals are outside the fragment. -/
def literalWord? : YulLit → Option Word
  | .number text | .hex text => Semantics.parseWord? text
  | .bool value => some (Word.ofNatModulo (if value then 1 else 0))
  | .string _ => none

/-- The memory and termination frame of a state. -/
def frame (state : State) : RuntimeEffectsSemantics.State := state.external.runtime.runtime.runtime.runtime.runtime

def withFrame (state : State) (next : RuntimeEffectsSemantics.State) : State :=
  {state with external := {state.external with
    runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime next)}}

/-- The builtins of the fragment. -/
def builtins : List String := ["mload", "msize", "mstore", "mstore8", "return", "revert"]

/-- A builtin of the fragment on its argument words, in Yul order: a memory read
or size, a memory write, or the return or revert termination. -/
inductive Builtin : String → List Word → RuntimeEffectsSemantics.State →
    Semantics.Result Semantics.Value → RuntimeEffectsSemantics.State → Prop where
  | mload {frame : RuntimeEffectsSemantics.State} {offset : Word} :
      Builtin "mload" [offset] frame (MemorySemantics.mload frame.memory offset).1
        {frame with memory := (MemorySemantics.mload frame.memory offset).2}
  | msize {frame : RuntimeEffectsSemantics.State} :
      Builtin "msize" [] frame (.value (.word frame.memory.size)) frame
  | mstore {frame : RuntimeEffectsSemantics.State} {offset value : Word} :
      Builtin "mstore" [offset, value] frame (MemorySemantics.mstore frame.memory offset value).1
        {frame with memory := (MemorySemantics.mstore frame.memory offset value).2}
  | mstore8 {frame : RuntimeEffectsSemantics.State} {offset value : Word} :
      Builtin "mstore8" [offset, value] frame (MemorySemantics.mstore8 frame.memory offset value).1
        {frame with memory := (MemorySemantics.mstore8 frame.memory offset value).2}
  | returned {frame : RuntimeEffectsSemantics.State} {offset length : Word} :
      Builtin "return" [offset, length] frame (TerminationSemantics.terminate frame 1 offset length).1
        (TerminationSemantics.terminate frame 1 offset length).2
  | reverted {frame : RuntimeEffectsSemantics.State} {offset length : Word} :
      Builtin "revert" [offset, length] frame (TerminationSemantics.terminate frame 2 offset length).1
        (TerminationSemantics.terminate frame 2 offset length).2

mutual
  /-- An expression's value. A call evaluates the reversed argument list from
  left to right, which is Yul's right-to-left order, and passes the words to the
  builtin in source order. A fault in an argument stops a builtin call. -/
  inductive Eval : Semantics.Environment → YulExpr → State → Semantics.Result Semantics.Value → State → Prop where
    | literal {environment : Semantics.Environment} {literal : YulLit} {span : Option Span} {state : State}
        {word : Word} (evaluated : literalWord? literal = some word) :
        Eval environment ⟨.literal literal, span⟩ state (.value (.word word)) state
    | ident {environment : Semantics.Environment} {name : YulName} {span : Option Span} {state : State}
        {location : Nat} {word : Word}
        (found : Semantics.lookupLocation environment name.name = some location)
        (read : state.heap[location]? = some (.word word)) :
        Eval environment ⟨.ident name, span⟩ state (.value (.word word)) state
    | call {environment : Semantics.Environment} {name : YulName} {arguments : List YulExpr} {span : Option Span}
        {initial middle : State} {words : List Word} {result : Semantics.Result Semantics.Value}
        {next : RuntimeEffectsSemantics.State}
        (evaluated : Arguments environment arguments.reverse initial (.value words) middle)
        (computed : Builtin name.name words.reverse (frame middle) result next) :
        Eval environment ⟨.call name arguments, span⟩ initial result (withFrame middle next)
    | callFault {environment : Semantics.Environment} {name : YulName} {arguments : List YulExpr}
        {span : Option Span} {initial final : State} {reason : Semantics.Fault} (named : name.name ∈ builtins)
        (evaluated : Arguments environment arguments.reverse initial (.fault reason) final) :
        Eval environment ⟨.call name arguments, span⟩ initial (.fault reason) final

  /-- Argument words in evaluation order. -/
  inductive Arguments : Semantics.Environment → List YulExpr → State → Semantics.Result (List Word) → State → Prop where
    | nil {environment : Semantics.Environment} {state : State} :
        Arguments environment [] state (.value []) state
    | cons {environment : Semantics.Environment} {argument : YulExpr} {rest : List YulExpr}
        {initial middle final : State} {word : Word} {words : List Word}
        (head : Eval environment argument initial (.value (.word word)) middle)
        (tail : Arguments environment rest middle (.value words) final) :
        Arguments environment (argument :: rest) initial (.value (word :: words)) final
    | tailFault {environment : Semantics.Environment} {argument : YulExpr} {rest : List YulExpr}
        {initial middle final : State} {word : Word} {reason : Semantics.Fault}
        (head : Eval environment argument initial (.value (.word word)) middle)
        (tail : Arguments environment rest middle (.fault reason) final) :
        Arguments environment (argument :: rest) initial (.fault reason) final
    | headFault {environment : Semantics.Environment} {argument : YulExpr} {rest : List YulExpr}
        {initial final : State} {reason : Semantics.Fault}
        (head : Eval environment argument initial (.fault reason) final) :
        Arguments environment (argument :: rest) initial (.fault reason) final
end

/-- A statement list of the block. `let` allocates the local's heap cell, an
assignment writes the variable's cell, and a fault, including the termination
sentinel, stops the block. -/
inductive Run : Semantics.Environment → List YulStmt → State → Semantics.Control → State → Prop where
  | nil {environment : Semantics.Environment} {state : State} :
      Run environment [] state .fallthrough state
  | letValue {environment : Semantics.Environment} {name : YulName} {value : YulExpr} {span : Option Span}
      {rest : List YulStmt} {initial middle final : State} {control : Semantics.Control} {word : Word}
      (evaluated : Eval environment value initial (.value (.word word)) middle)
      (tail : Run ((name.name, middle.heap.length) :: environment) rest
        (Semantics.allocate middle (.word word)).2 control final) :
      Run environment (⟨.letDecl [name] (some value), span⟩ :: rest) initial control final
  | letZero {environment : Semantics.Environment} {name : YulName} {span : Option Span} {rest : List YulStmt}
      {initial final : State} {control : Semantics.Control}
      (tail : Run ((name.name, initial.heap.length) :: environment) rest
        (Semantics.allocate initial (.word Word.zero)).2 control final) :
      Run environment (⟨.letDecl [name] none, span⟩ :: rest) initial control final
  | letFault {environment : Semantics.Environment} {name : YulName} {value : YulExpr} {span : Option Span}
      {rest : List YulStmt} {initial final : State} {reason : Semantics.Fault}
      (evaluated : Eval environment value initial (.fault reason) final) :
      Run environment (⟨.letDecl [name] (some value), span⟩ :: rest) initial (.fault reason) final
  | assign {environment : Semantics.Environment} {name : YulName} {value : YulExpr} {span : Option Span}
      {rest : List YulStmt} {initial middle final : State} {control : Semantics.Control} {word : Word}
      {location : Nat}
      (evaluated : Eval environment value initial (.value (.word word)) middle)
      (found : Semantics.lookupLocation environment name.name = some location)
      (tail : Run environment rest {middle with heap := middle.heap.set location (.word word)} control final) :
      Run environment (⟨.assign [name] value, span⟩ :: rest) initial control final
  | assignFault {environment : Semantics.Environment} {name : YulName} {value : YulExpr} {span : Option Span}
      {rest : List YulStmt} {initial final : State} {reason : Semantics.Fault}
      (evaluated : Eval environment value initial (.fault reason) final) :
      Run environment (⟨.assign [name] value, span⟩ :: rest) initial (.fault reason) final
  | expression {environment : Semantics.Environment} {value : YulExpr} {span : Option Span}
      {rest : List YulStmt} {initial middle final : State} {control : Semantics.Control}
      (evaluated : Eval environment value initial (.value .unit) middle)
      (tail : Run environment rest middle control final) :
      Run environment (⟨.expression value, span⟩ :: rest) initial control final
  | expressionFault {environment : Semantics.Environment} {value : YulExpr} {span : Option Span}
      {rest : List YulStmt} {initial final : State} {reason : Semantics.Fault}
      (evaluated : Eval environment value initial (.fault reason) final) :
      Run environment (⟨.expression value, span⟩ :: rest) initial (.fault reason) final

/-- An assembly block runs in the Hull environment; its locals end with it. -/
def Assembled (_functions : List Function) (environment : Semantics.Environment) (body : List YulStmt)
    (initial : State) (control : Semantics.Control) (final : State) : Prop :=
  Run environment body initial control final

end Solcore.Frontend.RustHull.YulSemantics
