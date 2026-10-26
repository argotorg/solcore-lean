import Solcore.Synthesis.Core.WordFunctionDAG
import Solcore.Synthesis.Core.Seed
import Solcore.Core.Wire.Codec.Program

/-! Direct, bounded generation of scalar expressions and acyclic helper calls.
The original Core graph is sealed by the existing full checker. The generator
does not choose a fixed graph template or substitute a literal for its input. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallGraph

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-call-graph-grammar-v1/" ++ Seed.algorithmId

structure Request where
  seed : Seed
  maxProgramNodes : Nat
  deriving Repr, BEq, DecidableEq

inductive Error where
  | budgetTooSmall
  | budgetTooLarge
  | checkerInvariant
  | budgetInvariant
  deriving Repr, BEq, DecidableEq

def callShapeVersion : String := "core-call-graph-shapes-v1"

def callShapeCatalog : List String :=
  ["skipped-helper", "multiple-callees", "shared-callee", "nested-call", "branch-call",
   "local-call", "diamond", "predicate-call", "primitive-operand-call"]

private def calls (depth prior : Nat) : Expr → List Nat
  | .letE value body => calls depth prior value ++ calls (depth + 1) prior body
  | .ifE condition yes no => calls depth prior condition ++ calls depth prior yes ++ calls depth prior no
  | .unary _ operand => calls depth prior operand
  | .binary _ left right => calls depth prior left ++ calls depth prior right
  | .ternary _ first second third => calls depth prior first ++ calls depth prior second ++ calls depth prior third
  | .apply (.var index) argument => (prior - 1 - (index - depth)) :: calls depth prior argument
  | _ => []

private def hasCall (expression : Expr) : Bool :=
  (functionFeatures expression).contains "functionCall"

private def nestedCall : Expr → Bool
  | .apply _ argument => hasCall argument
  | .letE value body => nestedCall value || nestedCall body
  | .ifE condition yes no => nestedCall condition || nestedCall yes || nestedCall no
  | .unary _ operand => nestedCall operand
  | .binary _ left right => nestedCall left || nestedCall right
  | .ternary _ first second third => nestedCall first || nestedCall second || nestedCall third
  | _ => false

private def branchCall : Expr → Bool
  | .ifE condition yes no => hasCall yes || hasCall no || branchCall condition
  | .letE value body => branchCall value || branchCall body
  | .unary _ operand => branchCall operand
  | .binary _ left right => branchCall left || branchCall right
  | .ternary _ first second third => branchCall first || branchCall second || branchCall third
  | .apply _ argument => branchCall argument
  | _ => false

private def localCall : Expr → Bool
  | .letE value body => hasCall body || localCall value
  | .ifE condition yes no => localCall condition || localCall yes || localCall no
  | .unary _ operand => localCall operand
  | .binary _ left right => localCall left || localCall right
  | .ternary _ first second third => localCall first || localCall second || localCall third
  | .apply _ argument => localCall argument
  | _ => false

private def predicateCall : Expr → Bool
  | .ifE condition yes no => hasCall condition || predicateCall yes || predicateCall no
  | .letE value body => predicateCall value || predicateCall body
  | .unary _ operand => predicateCall operand
  | .binary _ left right => predicateCall left || predicateCall right
  | .ternary _ first second third => predicateCall first || predicateCall second || predicateCall third
  | .apply _ argument => predicateCall argument
  | _ => false

private def primitiveOperandCall : Expr → Bool
  | .unary _ operand => hasCall operand
  | .binary _ left right => hasCall left || hasCall right
  | .ternary _ first second third => hasCall first || hasCall second || hasCall third
  | .ifE condition yes no => primitiveOperandCall condition || primitiveOperandCall yes || primitiveOperandCall no
  | .letE value body => primitiveOperandCall value || primitiveOperandCall body
  | .apply _ argument => primitiveOperandCall argument
  | _ => false

/-- Syntactic call shapes in all declared helper bodies and the entry. A helper
identity is its oldest-first declaration index, after removing the entire Word
local prefix. These observations do not claim that a call is executed. -/
def structuralShapes (graph : CheckedWordFunctionDAG) : List String := Id.run do
  let bodies := graph.helpers ++ [graph.entry]
  let edges := bodies.zipIdx.map fun (body, index) => calls 1 index body
  let mut found : List String := []
  if edges.zipIdx.any (fun (targets, source) => targets.any (fun target => target + 1 < source)) then
    found := "skipped-helper" :: found
  if edges.any (fun targets => targets.eraseDups.length ≥ 2) then
    found := "multiple-callees" :: found
  if (List.range graph.helpers.length).any (fun target =>
      (edges.filter (fun targets => targets.contains target)).length ≥ 2) then
    found := "shared-callee" :: found
  if bodies.any nestedCall then found := "nested-call" :: found
  if bodies.any branchCall then found := "branch-call" :: found
  if bodies.any localCall then found := "local-call" :: found
  if graph.helpers.length == 3 &&
      (edges[2]?.getD []).contains 0 && (edges[2]?.getD []).contains 1 &&
      (edges[1]?.getD []).contains 0 then found := "diamond" :: found
  if bodies.any predicateCall then found := "predicate-call" :: found
  if bodies.any primitiveOperandCall then found := "primitive-operand-call" :: found
  return found.reverse

/-- The measured minimum includes every helper binding, both lambda type
annotations, the entry closure, the runtime argument and the Program wrapper. -/
def minimumAppliedNodes (helperCount : Nat) : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (functionDAGExpression (List.replicate helperCount (.var 0)) (.var 0))
      (.word Word.zero) }

/-- Subtract only the one-node body of each helper and of the entry. -/
def appliedOverhead (helperCount : Nat) : Nat :=
  minimumAppliedNodes helperCount - (helperCount + 1)

structure Generated where private mk ::
  initialSeed : Seed
  finalSeed : Seed
  maxProgramNodes : Nat
  bodyBudgets : List Nat
  function : CheckedWordFunctionDAG
  bounded : programNodes (function.instantiate Word.zero) ≤ maxProgramNodes

namespace Generated

def program (generated : Generated) : Program := generated.function.program

def nodeCount (generated : Generated) : Nat :=
  programNodes (generated.function.instantiate Word.zero)

def features (generated : Generated) : List String := generated.function.features

theorem wellTyped (generated : Generated) : generated.program.WellTyped :=
  generated.function.wellTyped

end Generated

/-- Use the upper half of each full LCG draw. Consecutive low-bit parity choices
would correlate constructor selection with operation and variable selection. -/
private def choose (seed : Seed) (bound : Nat) : Nat × Seed :=
  let (value, next) := seed.draw
  if bound = 0 then (0, next) else ((value.toNat / 2 ^ 32) % bound, next)

private def edgeWord : Nat → Word
  | 0 => Word.zero
  | 1 => Word.ofNatModulo 1
  | 2 => Word.ofNatModulo 2
  | 3 => Word.ofNatModulo 31
  | 4 => Word.ofNatModulo 32
  | 5 => Word.ofNatModulo 255
  | 6 => Word.ofNatModulo 256
  | 7 => Word.ofNatModulo (2 ^ 255)
  | 8 => Word.ofNatModulo (2 ^ 255 - 1)
  | _ => Word.maximum

private def drawWord (seed : Seed) : Word × Seed :=
  let (kind, seed) := choose seed 3
  let (high, seed) := seed.draw
  let (next, seed) := seed.draw
  let (nextLow, seed) := seed.draw
  let (low, seed) := seed.draw
  let value := if kind < 2 then edgeWord ((high.toNat / 2 ^ 32) % 10) else
    Word.ofNatModulo (high.toNat * 2 ^ 192 + next.toNat * 2 ^ 128 +
      nextLow.toNat * 2 ^ 64 + low.toNat)
  (value, seed)

private def leaf (target : Target) (wordDepth : Nat) (seed : Seed) : Expr × Seed :=
  match target with
  | .bool =>
      let (value, seed) := choose seed 2
      (.bool (value == 1), seed)
  | .word =>
      let (kind, seed) := choose seed 3
      if wordDepth > 0 && kind < 2 then
        let (index, seed) := choose seed wordDepth
        (.var index, seed)
      else
        let (value, seed) := drawWord seed
        (.word value, seed)

private inductive Form where
  | leaf | unary | binary | ternary | letE | ifE | call

/-- Only constructors whose minimum cost fits are sampled. Call costs include
the direct callee variable as well as the application node. -/
private def forms (target : Target) (priorFunctions budget : Nat) : List Form :=
  [.leaf] ++
  (if budget ≥ 2 then [.unary] else []) ++
  (if budget ≥ 3 then [.binary, .binary, .letE, .letE] else []) ++
  (if budget ≥ 4 then [.ifE, .ifE] else []) ++
  (if target == .word && budget ≥ 4 then [.ternary] else []) ++
  (if target == .word && priorFunctions > 0 && budget ≥ 3 then [.call, .call] else [])

/-- Partition a budget into positive child budgets, in generation order. -/
private def partition : Nat → Nat → Seed → List Nat × Seed
  | 0, _, seed => ([], seed)
  | 1, total, seed => ([total], seed)
  | count + 2, total, seed =>
      let (extra, seed) := choose seed (total - (count + 2) + 1)
      let first := extra + 1
      let (remaining, seed) := partition (count + 1) (total - first) seed
      (first :: remaining, seed)

private def wordUnary : List UnaryOp := [.wordNot, .wordClz]
private def wordBinary : List BinaryOp :=
  [.wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod, .wordAnd, .wordOr, .wordXor,
   .wordShl, .wordShr, .wordByte, .wordSar, .wordPow, .wordSignExtend, .wordSdiv, .wordSmod]
private def boolBinary : List BinaryOp := [.wordEq, .wordGt, .wordSgt]

/-- Structural fuel is independent of arithmetic budget reasoning. Every body
starts with its actual Word parameter in scope; let adds another Word local. -/
private def expression : Nat → Target → Nat → Nat → Nat → Seed → Expr × Seed
  | 0, target, wordDepth, _, _, seed => leaf target wordDepth seed
  | fuel + 1, target, wordDepth, priorFunctions, budget, seed =>
      let available := forms target priorFunctions budget
      let (selected, seed) := choose seed available.length
      match available[selected]?.getD .leaf with
      | .leaf => leaf target wordDepth seed
      | .unary =>
          let (selected, seed) := choose seed (if target == .word then wordUnary.length else 1)
          let operation := if target == .word then wordUnary[selected]?.getD .wordNot else .boolNot
          let (operand, seed) := expression fuel target wordDepth priorFunctions (budget - 1) seed
          (.unary operation operand, seed)
      | .binary =>
          let operations := if target == .word then wordBinary else boolBinary
          let (selected, seed) := choose seed operations.length
          let operation := operations[selected]?.getD (if target == .word then .wordAdd else .wordEq)
          let (budgets, seed) := partition 2 (budget - 1) seed
          let (left, seed) := expression fuel .word wordDepth priorFunctions (budgets[0]?.getD 1) seed
          let (right, seed) := expression fuel .word wordDepth priorFunctions (budgets[1]?.getD 1) seed
          (.binary operation left right, seed)
      | .ternary =>
          let (selected, seed) := choose seed 2
          let operation := if selected == 0 then TernaryOp.wordAddMod else .wordMulMod
          let (budgets, seed) := partition 3 (budget - 1) seed
          let (first, seed) := expression fuel .word wordDepth priorFunctions (budgets[0]?.getD 1) seed
          let (second, seed) := expression fuel .word wordDepth priorFunctions (budgets[1]?.getD 1) seed
          let (third, seed) := expression fuel .word wordDepth priorFunctions (budgets[2]?.getD 1) seed
          (.ternary operation first second third, seed)
      | .letE =>
          let (budgets, seed) := partition 2 (budget - 1) seed
          let (value, seed) := expression fuel .word wordDepth priorFunctions (budgets[0]?.getD 1) seed
          let (body, seed) := expression fuel target (wordDepth + 1) priorFunctions
            (budgets[1]?.getD 1) seed
          (.letE value body, seed)
      | .ifE =>
          let (budgets, seed) := partition 3 (budget - 1) seed
          let (condition, seed) := expression fuel .bool wordDepth priorFunctions (budgets[0]?.getD 1) seed
          let (yes, seed) := expression fuel target wordDepth priorFunctions (budgets[1]?.getD 1) seed
          let (no, seed) := expression fuel target wordDepth priorFunctions (budgets[2]?.getD 1) seed
          (.ifE condition yes no, seed)
      | .call =>
          let (callee, seed) := choose seed priorFunctions
          let (argument, seed) := expression fuel .word wordDepth priorFunctions (budget - 2) seed
          (.apply (.var (wordDepth + callee)) argument, seed)

/-- Generate the complete graph directly, then validate both the scoped grammar
and the whole Core program. No evaluation or source result acts as its oracle.
Resource-limited execution and input-sensitivity filtering belong to Cases. -/
def generate (request : Request) : Except Error Generated := do
  if request.maxProgramNodes > 512 then throw .budgetTooLarge
  let counts := [1, 2, 3].filter (minimumAppliedNodes · ≤ request.maxProgramNodes)
  if counts.isEmpty then throw .budgetTooSmall
  let (selected, seed) := choose request.seed counts.length
  let count := counts[selected]?.getD 1
  let (budgets, seed) := partition (count + 1)
    (request.maxProgramNodes - appliedOverhead count) seed
  let mut seed := seed
  let mut helpers : List Expr := []
  for index in List.range count do
    let budget := budgets[index]?.getD 1
    let (body, next) := expression budget .word 1 index budget seed
    helpers := helpers ++ [body]
    seed := next
  let budget := budgets[count]?.getD 1
  let (entry, finalSeed) := expression budget .word 1 count budget seed
  let some function := CheckedWordFunctionDAG.ofParts? helpers entry |
    throw .checkerInvariant
  if bounded : programNodes (function.instantiate Word.zero) ≤ request.maxProgramNodes then
    return ⟨request.seed, finalSeed, request.maxProgramNodes, budgets, function, bounded⟩
  else throw .budgetInvariant

end Solcore.Synthesis.Core.CallGraph
