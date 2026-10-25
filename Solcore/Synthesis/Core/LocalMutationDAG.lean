import Solcore.Synthesis.Core.WordFunctionDAG

/-! A checked Word-function DAG with private mutable Word locals. Cell values
can only be introduced by direct let allocations and consumed by direct
loads/stores. They cannot escape, alias another binding or reach host functions. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.LocalMutation

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-local-mutation-dag-v1"

inductive Target where
  | word | bool | unit
  deriving Repr, BEq, DecidableEq

inductive Local where
  | word | bool | cellWord | unit
  deriving Repr, BEq, DecidableEq

def Target.toLocal : Target → Local
  | .word => .word
  | .bool => .bool
  | .unit => .unit

def Local.toTarget? : Local → Option Target
  | .word => some .word
  | .bool => some .bool
  | .unit => some .unit
  | .cellWord => none

private def scalarLocal : Solcore.Synthesis.Core.Target → Local
  | .word => .word
  | .bool => .bool

private def require (actual expected : Local) : Option Unit :=
  if actual == expected then some () else none

private def inferLocal? (locals : List Local) (priorFunctions : Nat) : Expr → Option Local
  | .word _ => some .word
  | .bool _ => some .bool
  | .unit => some .unit
  | .var index => do
      let kind ← locals[index]?
      if kind == .cellWord then none else some kind
  | .letE initializer body => do
      let kind ← inferLocal? locals priorFunctions initializer
      let result ← inferLocal? (kind :: locals) priorFunctions body
      if result == .cellWord then none else some result
  | .ifE condition yes no => do
      require (← inferLocal? locals priorFunctions condition) .bool
      let left ← inferLocal? locals priorFunctions yes
      let right ← inferLocal? locals priorFunctions no
      if left == right && left != .cellWord then some left else none
  | .unary operation operand => do
      match operation with
      | .integerNot | .integerToWord | .wordToInteger => none
      | _ =>
        require (← inferLocal? locals priorFunctions operand)
          (scalarLocal (Solcore.Synthesis.Core.Target.unaryOperand operation))
        return scalarLocal (Solcore.Synthesis.Core.Target.unaryResult operation)
  | .binary operation left right => do
      match operation with
      | .integerAdd | .integerSub | .integerMul | .integerDiv | .integerMod
      | .integerEq | .integerLt | .integerAnd | .integerOr | .integerXor => none
      | _ =>
        require (← inferLocal? locals priorFunctions left) .word
        require (← inferLocal? locals priorFunctions right) .word
        return scalarLocal (Solcore.Synthesis.Core.Target.binaryResult operation)
  | .ternary _ first second third => do
      require (← inferLocal? locals priorFunctions first) .word
      require (← inferLocal? locals priorFunctions second) .word
      require (← inferLocal? locals priorFunctions third) .word
      return .word
  | .apply (.var index) argument => do
      if locals.length ≤ index && index < locals.length + priorFunctions then
        require (← inferLocal? locals priorFunctions argument) .word
        return .word
      else none
  | .newCell .word initializer => do
      require (← inferLocal? locals priorFunctions initializer) .word
      return .cellWord
  | .loadCell (.var index) => do
      require (← locals[index]?) .cellWord
      return .word
  | .storeCell (.var index) value => do
      require (← locals[index]?) .cellWord
      require (← inferLocal? locals priorFunctions value) .word
      return .unit
  | _ => none

/-- Only a syntactically direct Word allocation can produce `cellWord`.
Unit bindings remain present in the context even when source printing elides them. -/
def initializerKind? (locals : List Local) (priorFunctions : Nat) (expression : Expr) : Option Local :=
  inferLocal? locals priorFunctions expression

/-- An expression cannot return a cell. The sole cell introduction position is
the initializer of a let, where `initializerKind?` supplies its local tag. -/
def infer? (locals : List Local) (priorFunctions : Nat) (expression : Expr) : Option Target := do
  (← inferLocal? locals priorFunctions expression).toTarget?

def acceptsAt (locals : List Local) (priorFunctions : Nat) (target : Target) (expression : Expr) : Bool :=
  infer? locals priorFunctions expression == some target

def features : Expr → List String
  | .word _ => ["wordLiteral"]
  | .bool _ => ["boolLiteral"]
  | .unit => ["unitLiteral"]
  | .var _ => ["local"]
  | .letE initializer body => "let" :: features initializer ++ features body
  | .ifE condition yes no => "if" :: features condition ++ features yes ++ features no
  | .unary operation operand => ("unary:" ++ reprStr operation) :: features operand
  | .binary operation left right => ("binary:" ++ reprStr operation) :: features left ++ features right
  | .ternary operation first second third =>
      ("ternary:" ++ reprStr operation) :: features first ++ features second ++ features third
  | .apply (.var _) argument => "functionCall" :: features argument
  | .newCell .word initializer => "newCell" :: features initializer
  | .loadCell (.var _) => ["loadCell"]
  | .storeCell (.var _) value => "storeCell" :: features value
  | _ => []

def helpersAccepted (helpers : List Expr) : Bool :=
  helpers.zipIdx.all fun (body, index) => acceptsAt [.word] index .word body

structure CheckedDAG where private mk ::
  helpers : List Expr
  entry : Expr
  count : 1 ≤ helpers.length ∧ helpers.length ≤ 3
  helperScopes : helpersAccepted helpers = true
  entryScope : acceptsAt [.word] helpers.length .word entry = true
  checked : (functionDAGProgram helpers entry).check = true

namespace CheckedDAG

def program (graph : CheckedDAG) : Program := functionDAGProgram graph.helpers graph.entry

def features (graph : CheckedDAG) : List String :=
  graph.helpers.flatMap LocalMutation.features ++ LocalMutation.features graph.entry

def ofParts? (helpers : List Expr) (entry : Expr) : Option CheckedDAG :=
  if count : 1 ≤ helpers.length ∧ helpers.length ≤ 3 then
    if helperScopes : helpersAccepted helpers = true then
      if entryScope : acceptsAt [.word] helpers.length .word entry = true then
        if checked : (functionDAGProgram helpers entry).check = true then
          some ⟨helpers, entry, count, helperScopes, entryScope, checked⟩
        else none
      else none
    else none
  else none

private def parts? : Expr → Option (List Expr × Expr)
  | .lambda .word .word entry => some ([], entry)
  | .letE (.lambda .word .word helper) rest => do
      let (helpers, entry) ← parts? rest
      return (helper :: helpers, entry)
  | _ => none

def ofProgram? : Program → Option CheckedDAG
  | {resultType := .function .word .word, dataDefinitions := [], body} => do
      let (helpers, entry) ← parts? body
      ofParts? helpers entry
  | _ => none

theorem wellTyped (graph : CheckedDAG) : graph.program.WellTyped :=
  Program.check_full_sound graph.checked

def instantiate (graph : CheckedDAG) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply graph.program.body (.word input)
}

theorem instantiate_wellTyped (graph : CheckedDAG) (input : Word) :
    (graph.instantiate input).WellTyped := by
  refine ⟨graph.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply graph.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (graph : CheckedDAG) (input : Word) :
    (graph.instantiate input).check = true :=
  Program.check_complete (graph.instantiate_wellTyped input)

end CheckedDAG
end Solcore.Synthesis.Core.LocalMutation

namespace Solcore.Synthesis.Core
abbrev CheckedLocalMutationDAG := LocalMutation.CheckedDAG
end Solcore.Synthesis.Core
