import Solcore.Synthesis.Core.WordFunction

/-! Checked acyclic Word-function graphs. The original Core program binds
one to three helper lambdas in declaration order, then returns an entry lambda.
Only calls to earlier helpers are admitted; recursion, escaping functions and
host references are outside this profile. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core

open Solcore.Core (Word)
open Solcore.Core.Wire

def wordFunctionDAGVersion : String := "core-word-function-dag-v1"

/-- Word locals are nearest first. Earlier helper functions immediately follow
that prefix, also nearest first. A helper may appear only as a direct callee. -/
def functionAcceptsAt (wordDepth priorFunctions : Nat) (target : Target) : Expr → Bool
  | .word _ => target == .word
  | .bool _ => target == .bool
  | .var index => target == .word && decide (index < wordDepth)
  | .letE initializer body =>
      functionAcceptsAt wordDepth priorFunctions .word initializer &&
        functionAcceptsAt (wordDepth + 1) priorFunctions target body
  | .ifE condition yes no =>
      functionAcceptsAt wordDepth priorFunctions .bool condition &&
        functionAcceptsAt wordDepth priorFunctions target yes &&
        functionAcceptsAt wordDepth priorFunctions target no
  | .unary operation operand =>
      match operation with
      | .integerNot | .integerToWord | .wordToInteger => false
      | _ => target == Target.unaryResult operation &&
          functionAcceptsAt wordDepth priorFunctions (Target.unaryOperand operation) operand
  | .binary operation left right =>
      match operation with
      | .integerAdd | .integerSub | .integerMul | .integerDiv | .integerMod
      | .integerEq | .integerLt | .integerAnd | .integerOr | .integerXor => false
      | _ => target == Target.binaryResult operation &&
          functionAcceptsAt wordDepth priorFunctions .word left &&
          functionAcceptsAt wordDepth priorFunctions .word right
  | .ternary _ first second third =>
      target == .word && functionAcceptsAt wordDepth priorFunctions .word first &&
        functionAcceptsAt wordDepth priorFunctions .word second &&
        functionAcceptsAt wordDepth priorFunctions .word third
  | .apply (.var index) argument =>
      target == .word && decide (wordDepth ≤ index ∧ index < wordDepth + priorFunctions) &&
        functionAcceptsAt wordDepth priorFunctions .word argument
  | _ => false

/-- Feature occurrences inside a scalar function body. Declaration lambdas,
their outer binding chain and the runtime-input application are not counted. -/
def functionFeatures : Expr → List String
  | .word _ => ["wordLiteral"]
  | .bool _ => ["boolLiteral"]
  | .var _ => ["local"]
  | .letE initializer body => "let" :: functionFeatures initializer ++ functionFeatures body
  | .ifE condition yes no =>
      "if" :: functionFeatures condition ++ functionFeatures yes ++ functionFeatures no
  | .unary operation operand =>
      ("unary:" ++ reprStr operation) :: functionFeatures operand
  | .binary operation left right =>
      ("binary:" ++ reprStr operation) :: functionFeatures left ++ functionFeatures right
  | .ternary operation first second third =>
      ("ternary:" ++ reprStr operation) ::
        functionFeatures first ++ functionFeatures second ++ functionFeatures third
  | .apply (.var _) argument => "functionCall" :: functionFeatures argument
  | _ => []

def functionDAGExpression (helpers : List Expr) (entry : Expr) : Expr :=
  helpers.foldr (fun body remaining => .letE (.lambda .word .word body) remaining)
    (.lambda .word .word entry)

def functionDAGProgram (helpers : List Expr) (entry : Expr) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := functionDAGExpression helpers entry
}

def functionHelpersAccepted (helpers : List Expr) : Bool :=
  helpers.zipIdx.all fun (body, index) => functionAcceptsAt 1 index .word body

/-- Helpers are stored oldest first. Every accepted graph has the exact
declaration shape, a closed scalar scope and full Core typing evidence. -/
structure CheckedWordFunctionDAG where private mk ::
  helpers : List Expr
  entry : Expr
  count : 1 ≤ helpers.length ∧ helpers.length ≤ 3
  helperScopes : functionHelpersAccepted helpers = true
  entryScope : functionAcceptsAt 1 helpers.length .word entry = true
  checked : (functionDAGProgram helpers entry).check = true

namespace CheckedWordFunctionDAG

def program (graph : CheckedWordFunctionDAG) : Program := functionDAGProgram graph.helpers graph.entry

def features (graph : CheckedWordFunctionDAG) : List String :=
  graph.helpers.flatMap functionFeatures ++ functionFeatures graph.entry

def ofParts? (helpers : List Expr) (entry : Expr) : Option CheckedWordFunctionDAG :=
  if count : 1 ≤ helpers.length ∧ helpers.length ≤ 3 then
    if helperScopes : functionHelpersAccepted helpers = true then
      if entryScope : functionAcceptsAt 1 helpers.length .word entry = true then
        if checked : (functionDAGProgram helpers entry).check = true then
          some ⟨helpers, entry, count, helperScopes, entryScope, checked⟩
        else none
      else none
    else none
  else none

private def parts? : Expr → Option (List Expr × Expr)
  | .lambda .word .word entry => some ([], entry)
  | .letE (.lambda .word .word helper) remaining => do
      let (helpers, entry) ← parts? remaining
      return (helper :: helpers, entry)
  | _ => none

/-- Parse only a let-of-lambdas chain ending in the Word entry lambda, then
seal the entire original program. Arbitrary function expressions are rejected. -/
def ofProgram? : Program → Option CheckedWordFunctionDAG
  | {resultType := .function .word .word, dataDefinitions := [], body} => do
      let (helpers, entry) ← parts? body
      ofParts? helpers entry
  | _ => none

theorem wellTyped (graph : CheckedWordFunctionDAG) : graph.program.WellTyped :=
  Program.check_full_sound graph.checked

/-- Execute the original Core binding chain and apply its entry closure. -/
def instantiate (graph : CheckedWordFunctionDAG) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply graph.program.body (.word input)
}

theorem instantiate_wellTyped (graph : CheckedWordFunctionDAG) (input : Word) :
    (graph.instantiate input).WellTyped := by
  refine ⟨graph.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply graph.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (graph : CheckedWordFunctionDAG) (input : Word) :
    (graph.instantiate input).check = true :=
  Program.check_complete (graph.instantiate_wellTyped input)

end CheckedWordFunctionDAG
end Solcore.Synthesis.Core
