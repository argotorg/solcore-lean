import Solcore.Synthesis.Internal.Functions
import Solcore.Synthesis.Core.Seed
import Solcore.Core.Wire.Codec

/-!
# Profile: call graphs

The profile `runtime-call-graphs`: generator, renderer, emitter and cases.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.CallGraphGenerator
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
def choose (seed : Seed) (bound : Nat) : Nat × Seed :=
  let (value, next) := seed.draw
  if bound = 0 then (0, next) else ((value.toNat / 2 ^ 32) % bound, next)

def edgeWord : Nat → Word
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

def drawWord (seed : Seed) : Word × Seed :=
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

def wordUnary : List UnaryOp := [.wordNot, .wordClz]
def wordBinary : List BinaryOp :=
  [.wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod, .wordAnd, .wordOr, .wordXor,
   .wordShl, .wordShr, .wordByte, .wordSar, .wordPow, .wordSignExtend, .wordSdiv, .wordSmod]
def boolBinary : List BinaryOp := [.wordEq, .wordGt, .wordSgt]

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
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallGraphRenderer
/-! Scalar source rendering with direct calls to earlier named Word helpers.
The primitive formatting and operand snapshots match PrimitiveRenderer. Helper
indices follow the Word-local prefix; neither functions nor host values escape.
This tested printer does not assert source meaning preservation. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallGraphRenderer

open Solcore.Core.Wire
open Solcore.Synthesis.Core (Target)
open ScalarRenderer (Rendered)

def supportedUnary := PrimitiveRenderer.supportedUnary
def supportedBinary := PrimitiveRenderer.supportedBinary
def supportedTernary := PrimitiveRenderer.supportedTernary

/-- The G0 features this renderer renders, those of `PrimitiveRenderer`. -/
def support := PrimitiveRenderer.support

/-- Syntax support is separate from the existing checked function boundary. -/
def supported : Expr → Bool
  | .word _ | .bool _ | .var _ => true
  | .letE initializer body => supported initializer && supported body
  | .ifE condition yes no => supported condition && supported yes && supported no
  | .unary operation operand => supportedUnary operation && supported operand
  | .binary operation left right => supportedBinary operation && supported left && supported right
  | .ternary operation first second third =>
      supportedTernary operation && supported first && supported second && supported third
  | .apply (.var _) argument => supported argument
  | _ => false

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"

private def name (index : Nat) : String := "sc_v" ++ toString index

def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    name nextId, nextId + 1⟩

def snapshot (indent : Nat) (value : Rendered) : Rendered :=
  let captured := bindValue .word indent value.nextId value.value
  ⟨value.lines ++ captured.lines, captured.value, captured.nextId⟩

def unaryValue (operation : UnaryOp) (operand : String) : Except EmitError String :=
  match operation with
  | .boolNot => .ok ("(!" ++ operand ++ ")")
  | .wordNot => .ok ("(~" ++ operand ++ ")")
  | .wordClz => .ok ("sc_clz(" ++ operand ++ ")")
  | _ => .error (.unsupportedUnary operation)

def binaryValue (operation : BinaryOp) (left right : String) : Except EmitError String :=
  let infixValue (token : String) := "(" ++ left ++ " " ++ token ++ " " ++ right ++ ")"
  let call (callee first second : String) := callee ++ "(" ++ first ++ ", " ++ second ++ ")"
  match operation with
  | .wordAdd => .ok (infixValue "+")
  | .wordSub => .ok (infixValue "-")
  | .wordMul => .ok (infixValue "*")
  | .wordAnd => .ok (infixValue "&")
  | .wordOr => .ok (infixValue "|")
  | .wordXor => .ok (infixValue "^")
  | .wordEq => .ok (infixValue "==")
  | .wordGt => .ok (infixValue ">")
  | .wordDiv => .ok (call "sc_div" left right)
  | .wordMod => .ok (call "sc_mod" left right)
  | .wordShl => .ok (call "sc_shl" right left)
  | .wordShr => .ok (call "sc_shr" right left)
  | .wordSar => .ok (call "sc_sar" right left)
  | .wordSdiv => .ok (call "sc_sdiv" left right)
  | .wordSmod => .ok (call "sc_smod" left right)
  | .wordSgt => .ok ("tobool(" ++ call "sc_sgt" left right ++ ")")
  | .wordByte => .ok (call "sc_byte" left right)
  | .wordPow => .ok (call "sc_exp" left right)
  | .wordSignExtend => .ok (call "sc_signextend" left right)
  | _ => .error (.unsupportedBinary operation)

def ternaryValue (operation : TernaryOp) (first second third : String) : String :=
  let callee := match operation with
    | .wordAddMod => "sc_addmod"
    | .wordMulMod => "sc_mulmod"
  callee ++ "(" ++ first ++ ", " ++ second ++ ", " ++ third ++ ")"

/-- Bindings are nearest first, as in the original Core function. Raw opcode
arguments are captured left to right before reordered shift arguments are
printed. A call snapshots its argument before invoking its named helper.
Branch-local computations remain inside their selected branch. -/
def renderWithFunctions (functions : List String) (target : Target) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok (bindValue .word indent nextId (toString value.val))
  | .bool value => .ok (bindValue .bool indent nextId (if value then "true" else "false"))
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← renderWithFunctions functions .word locals indent nextId initializer
      let binding := bindValue .word indent value.nextId value.value
      let rest ← renderWithFunctions functions target (binding.value :: locals) indent binding.nextId body
      return ⟨value.lines ++ binding.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← renderWithFunctions functions .bool locals indent nextId condition
      let result := bindValue target indent tested.nextId (zero target)
      let selected ← renderWithFunctions functions target locals (indent + 4) result.nextId yes
      let fallback ← renderWithFunctions functions target locals (indent + 4) selected.nextId no
      return ⟨tested.lines ++ result.lines ++
        [line indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
        [line (indent + 4) (result.value ++ " = " ++ selected.value ++ ";"), line indent "} else {"] ++
        fallback.lines ++ [line (indent + 4) (result.value ++ " = " ++ fallback.value ++ ";"), line indent "}"],
        result.value, fallback.nextId⟩
  | .unary operation operand => do
      unless supportedUnary operation do throw (.unsupportedUnary operation)
      let value ← renderWithFunctions functions (if operation == .boolNot then .bool else .word) locals indent nextId operand
      let value := if operation == .wordClz then snapshot indent value else value
      let expression ← unaryValue operation value.value
      let result := bindValue target indent value.nextId expression
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      unless supportedBinary operation do throw (.unsupportedBinary operation)
      let first ← renderWithFunctions functions .word locals indent nextId left
      let first := if Source.supportedBinary operation then first else snapshot indent first
      let second ← renderWithFunctions functions .word locals indent first.nextId right
      let second := if Source.supportedBinary operation then second else snapshot indent second
      let expression ← binaryValue operation first.value second.value
      let result := bindValue target indent second.nextId expression
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .ternary operation first second third => do
      let first := snapshot indent (← renderWithFunctions functions .word locals indent nextId first)
      let second := snapshot indent (← renderWithFunctions functions .word locals indent first.nextId second)
      let third := snapshot indent (← renderWithFunctions functions .word locals indent second.nextId third)
      let result := bindValue target indent third.nextId (ternaryValue operation first.value second.value third.value)
      return ⟨first.lines ++ second.lines ++ third.lines ++ result.lines, result.value, result.nextId⟩
  | .unit => .error (.unsupportedExpression "unit")
  | .integer _ => .error (.unsupportedExpression "integer")
  | .pair _ _ => .error (.unsupportedExpression "pair")
  | .first _ => .error (.unsupportedExpression "first")
  | .second _ => .error (.unsupportedExpression "second")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply (.var index) argument => do
      unless target == .word do throw (.unsupportedExpression "apply")
      if index < locals.length then throw (.unsupportedExpression "apply")
      let some callee := functions[index - locals.length]? |
        throw (.unsupportedExpression "apply")
      let value := snapshot indent (← renderWithFunctions functions .word locals indent nextId argument)
      let result := bindValue .word indent value.nextId (callee ++ "(" ++ value.value ++ ")")
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .apply _ _ => .error (.unsupportedExpression "apply")
  | .inLeft _ _ => .error (.unsupportedExpression "inLeft")
  | .inRight _ _ => .error (.unsupportedExpression "inRight")
  | .caseE _ _ _ => .error (.unsupportedExpression "caseE")
  | .newCell _ _ => .error (.unsupportedExpression "newCell")
  | .loadCell _ => .error (.unsupportedExpression "loadCell")
  | .storeCell _ _ => .error (.unsupportedExpression "storeCell")
  | .construct _ _ => .error (.unsupportedExpression "construct")
  | .matchData _ _ _ _ => .error (.unsupportedExpression "matchData")

end Solcore.Synthesis.Source.CallGraphRenderer
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallGraphEmitter
/-! Full scalar primitive emission for checked acyclic Word-function graphs. Helpers
keep their Core declaration order and can call only earlier declarations.
`ScalarMeaning.CallGraph.emit_source_meaning` relates the emitted text to the original Core result under an independent
source semantics; see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallGraph

open Solcore.Synthesis.Core (CheckedWordFunctionDAG)

def emitterVersion : String := "solcore-source-call-graphs-v1"
def wrapperVersion : String := "solcore-word-call-graphs-contract-v1"
def contractName : String := "SynthesizedCallGraphs"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedCallGraphsDeploy"]
def runtimePath : List String := ["SynthesizedCallGraphsDeploy", "SynthesizedCallGraphs"]

def helperName (index : Nat) : String := "sc_fn" ++ toString index

/-- Emit all helper bodies and the entry from the same checked Core graph.
Local temporaries are fresh within each function and cannot shadow helper names. -/
def emit (graph : CheckedWordFunctionDAG) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""]
  for (body, index) in graph.helpers.zipIdx do
    let rendered ← CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 body
    let name := helperName index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""]
    names := name :: names
  let entry ← CallGraphRenderer.renderWithFunctions names .word ["sc_input"] 8 0 graph.entry
  lines := lines ++ ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
    ["        return uint256(" ++ entry.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.CallGraph
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallGraphCases
/-! Replayable cases for directly generated typed acyclic call graphs. The original
Core lambda chain is retained and executed independently of source lowering.
The older scalar profiles and their replay rules remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallGraph
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-call-graph-case.v1"
def profileVersion : String := "runtime-call-graphs-v1/direct-grammar-v1"
def generatorVersion : String := Solcore.Synthesis.Core.CallGraph.version
def boundaryVersion : String := Primitive.boundaryVersion
def callShapeVersion : String := Solcore.Synthesis.Core.CallGraph.callShapeVersion
def boundaryInputs : List Word := Primitive.boundaryInputs
def minimumProgramNodes : Nat := Solcore.Synthesis.Core.CallGraph.minimumAppliedNodes 1

def callShapes (function : CheckedWordFunctionDAG) : List String :=
  Solcore.Synthesis.Core.CallGraph.structuralShapes function

def inputWord := Primitive.inputWord

structure CheckedInput where
  function : CheckedWordFunctionDAG
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : CheckedWordFunctionDAG) (input : Word) (fuel : Nat) : Json :=
  let fields := match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (function : CheckedWordFunctionDAG) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson wordFunctionDAGVersion),
    ("boundaryVersion", toJson boundaryVersion),
    ("callShapeVersion", toJson callShapeVersion),
    ("generatorVersion", toJson generatorVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson function.features),
    ("helperCount", toJson function.helpers.length), ("callShapes", toJson (callShapes function))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : CheckedWordFunctionDAG) (input : Word)
    (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied function DAG exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel

private def decodeProgram (json : Json) : Except String Wire.Program := do
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.programNodes program ≤ 512 do throw "Core program exceeds the 512-node case limit"
  return program

def checkedFunction (json : Json) : Except String CheckedWordFunctionDAG := do
  let some function := CheckedWordFunctionDAG.ofProgram? (← decodeProgram json) |
    throw "program is not a checked scalar Word function DAG"
  return function

def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic function case schema"
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← decodeProgram (← json.getObjVal? "program")
  match program with
  | { resultType := .word, dataDefinitions := [], body := .apply functionBody (.word argument) } =>
      unless argument = input do throw "saved program argument differs from input"
      let some function := CheckedWordFunctionDAG.ofProgram? {
        resultType := .function .word .word, dataDefinitions := [], body := functionBody } |
        throw "applied function is outside the checked function DAG profile"
      let admitted : CheckedInput := ⟨function, input⟩
      unless Wire.encodeProgram admitted.program == (← json.getObjVal? "program") do
        throw "saved Core graph application is not canonical"
      return admitted
  | _ => throw "function case program is not a closed Word function DAG application"

def generatedFunction (seed : Seed) (nodes : Nat) :
    Except String (CheckedWordFunctionDAG × Json) := do
  let generated ← (Solcore.Synthesis.Core.CallGraph.generate
    {seed, maxProgramNodes := nodes}).mapError reprStr
  let origin := Json.mkObj [
    ("kind", toJson "call-graph-generated"),
    ("seed", toJson (toString generated.initialSeed.toNat)),
    ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson generated.maxProgramNodes),
    ("helperCount", toJson generated.function.helpers.length),
    ("bodyBudgets", toJson generated.bodyBudgets)]
  return (generated.function, origin)

/-- Helpers-only calls are dead without an entry call. This is a syntactic
reachability condition, not a claim that a branch or call executes. -/
def hasEntryCall (function : CheckedWordFunctionDAG) : Bool :=
  (functionFeatures function.entry).contains "functionCall"

def boundaryResults (function : CheckedWordFunctionDAG) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (function : CheckedWordFunctionDAG) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  unless hasEntryCall function do throw "entry has no helper call"
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all eight boundary inputs returned the same Word"
  acceptance.check boundaryInputs results

/-- Attempts count complete graph candidates. Accepted graphs yield up to eight
cases in fixed input order. Fuel exhaustion is an inconclusive exclusion. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) :
    Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "validation fuel exceeds profile limit"
        let (function, origin) ← generatedFunction seed nodes
        let emitted ← (emit function).mapError reprStr
        inputSensitive function fuel acceptance
        return (function, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-graph-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (function, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase function input emitted (acceptance.record (inputSelection.record origin)) fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  let admitted ← caseProgram json
  let savedFuel ← json.getObjValAs? Nat "executionFuel"
  unless savedFuel ≤ 10000000 do throw "saved execution fuel exceeds profile limit"
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("generatorVersion", generatorVersion), ("profileVersion", profileVersion),
      ("functionVersion", wordFunctionDAGVersion), ("boundaryVersion", boundaryVersion),
      ("callShapeVersion", callShapeVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core call graph"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the call graph wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.function.features do
    throw "saved features differ from the original Core call graph"
  unless (← provenance.getObjValAs? Nat "helperCount") = admitted.function.helpers.length do
    throw "saved helper count differs from the original Core call graph"
  unless (← provenance.getObjVal? "callShapes") == toJson (callShapes admitted.function) do
    throw "saved call shapes differ from the original Core call graph"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-graph-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (function, expectedOrigin) ← generatedFunction (Seed.ofNat seed) nodes
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved call graph differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive function validationFuel acceptance
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    unless origin == acceptance.record (inputSelection.record canonicalOrigin) do throw "generated call graph provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported call graph provenance is not canonical"
  else if kind = "reduced" then
    let parentProgram ← origin.getObjVal? "parentProgram"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent ← caseProgram (Json.mkObj [
      ("schema", toJson caseSchema), ("program", parentProgram), ("input", toJson parentText)])
    unless admitted.function.helpers.length = parent.function.helpers.length do
      throw "saved graph reduction changes helper count"
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved graph reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentProgram", parentProgram),
        ("parentInput", toJson parentText)] do
      throw "reduced call graph provenance is not canonical"
  else throw "unsupported call graph case origin"
  let fresh := makeCase admitted.function admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "call graph provenance contains unexpected fields"
  -- Ignore the saved observation, but require the complete canonical envelope.
  let _ ← json.getObjVal? "directCore"
  let savedEnvelope := json.setObjVal! "directCore" .null
  let freshEnvelope := (fresh.setObjVal! "directCore" .null).setObjVal!
    "executionFuel" (toJson savedFuel)
  unless savedEnvelope == freshEnvelope do throw "saved call graph case envelope is not canonical"
  return fresh

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.function.helpers.length = source.function.helpers.length
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

/-- Reuse the existing typed, scope-preserving local DAG reductions. Function
bindings are neither removed nor reordered; each result was fully resealed. -/
def reductions (source : CheckedInput) : List (Reduction source) :=
  (Function.reductions ⟨source.function, source.input⟩).map fun reduced =>
    ⟨⟨reduced.candidate.function, reduced.candidate.input⟩, reduced.sameHelperCount, reduced.strict⟩

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push (← emitCase reduced.candidate.function reduced.candidate.input origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.CallGraph
end
