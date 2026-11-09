import Solcore.Synthesis.Core.Fragment
import Solcore.Synthesis.Source.Emitter
import Solcore.Synthesis.Source.Cases
import Solcore.Synthesis.Source.Acceptance

/-!
# Profiles: words, functions, primitives, mutation

The profiles `runtime-word`, `runtime-functions`, `runtime-primitives` and `runtime-mutation`: Core
references, renderers, emitters and cases.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.WordFunction
/-! Checked scalar functions with one runtime Word input. This profile is
separate from the closed G0 program generator and does not change its version.
Literal abstraction creates candidates; the ordinary Core checker seals every
accepted function before it can be emitted or executed. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core

open Solcore.Core (Word)
open Solcore.Core.Wire

def wordFunctionVersion : String := "core-word-function-v1"
def abstractionVersion : String := "word-literal-preorder-v1"

/-- Word literals in scalar-expression preorder, including unselected branches. -/
def wordLiterals : Expr → List Word
  | .word value => [value]
  | .letE initializer body | .binary _ initializer body =>
      wordLiterals initializer ++ wordLiterals body
  | .ifE condition yes no | .ternary _ condition yes no =>
      wordLiterals condition ++ wordLiterals yes ++ wordLiterals no
  | .unary _ operand => wordLiterals operand
  | _ => []

def literalCount (body : Expr) : Nat := (wordLiterals body).length

private def abstractAt (depth selected : Nat) : Expr → Option Expr
  | .word _ => if selected = 0 then some (.var depth) else none
  | .letE initializer body =>
      let before := literalCount initializer
      if selected < before then
        (fun changed => .letE changed body) <$> abstractAt depth selected initializer
      else
        .letE initializer <$> abstractAt (depth + 1) (selected - before) body
  | .ifE condition yes no =>
      let before := literalCount condition
      let middle := literalCount yes
      if selected < before then
        (fun changed => .ifE changed yes no) <$> abstractAt depth selected condition
      else if selected < before + middle then
        (fun changed => .ifE condition changed no) <$> abstractAt depth (selected - before) yes
      else
        .ifE condition yes <$> abstractAt depth (selected - before - middle) no
  | .unary operation operand =>
      .unary operation <$> abstractAt depth selected operand
  | .binary operation left right =>
      let before := literalCount left
      if selected < before then
        (fun changed => .binary operation changed right) <$> abstractAt depth selected left
      else
        .binary operation left <$> abstractAt depth (selected - before) right
  | .ternary operation first second third =>
      let before := literalCount first
      let middle := literalCount second
      if selected < before then
        (fun changed => .ternary operation changed second third) <$> abstractAt depth selected first
      else if selected < before + middle then
        (fun changed => .ternary operation first changed third) <$>
          abstractAt depth (selected - before) second
      else
        .ternary operation first second <$> abstractAt depth (selected - before - middle) third
  | _ => none

/-- Replace exactly the selected scalar Word literal by an outer Word input.
Existing locals keep their indices. A `let` increases the replacement index
only in its body, so its initializer still sees the surrounding environment.
An out-of-range selection is explicitly rejected. -/
def abstractWordLiteral (body : Expr) (selected : Nat) : Option Expr :=
  if selected < literalCount body then abstractAt 0 selected body else none

theorem abstractWordLiteral_out_of_range (body : Expr) (selected : Nat)
    (outside : literalCount body ≤ selected) : abstractWordLiteral body selected = none := by
  simp [abstractWordLiteral, Nat.not_lt.mpr outside]

def wordFunctionProgram (body : Expr) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := .lambda .word .word body
}

/-- A single Word parameter is the only free scalar binding allowed in `body`.
The private constructor seals both that scope boundary and full Core typing. -/
structure CheckedWordFunction where private mk ::
  body : Expr
  checked : (wordFunctionProgram body).check = true
  fragment : acceptsAt 1 .word body = true

namespace CheckedWordFunction

def program (function : CheckedWordFunction) : Program := wordFunctionProgram function.body

def ofBody? (body : Expr) : Option CheckedWordFunction :=
  if checked : (wordFunctionProgram body).check = true then
    if fragment : acceptsAt 1 .word body = true then
      some ⟨body, checked, fragment⟩
    else none
  else none

/-- Admission accepts only the exact closed Word-to-Word lambda shape. -/
def ofProgram? : Program → Option CheckedWordFunction
  | { resultType := .function .word .word, dataDefinitions := [],
      body := .lambda .word .word body } => ofBody? body
  | _ => none

/-- Select one literal in an already checked G0 program, then check the new
function. Unsupported source-emitter operations remain explicit later errors. -/
def fromProgram? (source : CheckedWordProgram) (selected : Nat) : Option CheckedWordFunction := do
  ofBody? (← abstractWordLiteral source.program.body selected)

theorem wellTyped (function : CheckedWordFunction) : function.program.WellTyped :=
  Program.check_full_sound function.checked

/-- Apply the original Core lambda to the runtime input. No source or Hull
compilation participates in this independent observation path. -/
def instantiate (function : CheckedWordFunction) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply function.program.body (.word input)
}

theorem instantiate_wellTyped (function : CheckedWordFunction) (input : Word) :
    (function.instantiate input).WellTyped := by
  refine ⟨function.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply function.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (function : CheckedWordFunction) (input : Word) :
    (function.instantiate input).check = true :=
  Program.check_complete (function.instantiate_wellTyped input)

end CheckedWordFunction
end Solcore.Synthesis.Core
end

section
-- leanmerge: from Solcore.Synthesis.Core.WordFunctionDAG
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.LocalMutationDAG
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.FunctionEmitter
/-! Named helper emission for checked acyclic Word-function graphs. Helpers
keep their Core declaration order and can call only earlier declarations.
`ScalarMeaning.Function.emit_source_meaning` relates the emitted text to the original Core result under an independent
source semantics; see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Function

open Solcore.Synthesis.Core (CheckedWordFunctionDAG)

def emitterVersion : String := "solcore-source-functions-v2"
def wrapperVersion : String := "solcore-word-functions-contract-v1"

/-- The G0 features `emit` renders, those of `ScalarRenderer`. -/
def featureSupport := scalarSupport
def contractName : String := "SynthesizedFunctions"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedFunctionsDeploy"]
def runtimePath : List String := ["SynthesizedFunctionsDeploy", "SynthesizedFunctions"]

def helperName (index : Nat) : String := "sc_fn" ++ toString index

/-- Emit all helper bodies and the entry from the same checked Core graph.
Local temporaries are fresh within each function and cannot shadow helper names. -/
def emit (graph : CheckedWordFunctionDAG) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;", ""]
  for (body, index) in graph.helpers.zipIdx do
    let rendered ← ScalarRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 body
    let name := helperName index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""]
    names := name :: names
  let entry ← ScalarRenderer.renderWithFunctions names .word ["sc_input"] 8 0 graph.entry
  lines := lines ++ ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
    ["        return uint256(" ++ entry.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Function
end

section
-- leanmerge: from Solcore.Synthesis.Source.InputEmitter
/-! Source emission for a checked scalar function with one runtime Word input.
The ABI wrapper is separate from G0. `ScalarMeaning.Input.emit_source_meaning`
relates the emitted text to the original Core application for every input. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Input

open Solcore.Synthesis.Core (CheckedWordFunction)

def emitterVersion : String := "solcore-source-input-v2"
def wrapperVersion : String := "solcore-word-input-contract-v1"

/-- The G0 features `emit` renders, those of `ScalarRenderer`. -/
def featureSupport := scalarSupport
def contractName : String := "SynthesizedInput"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedInputDeploy"]
def runtimePath : List String := ["SynthesizedInputDeploy", "SynthesizedInput"]

/-- One source is shared by every runtime input. The input is converted from
its ABI wrapper once, and occupies the outermost scalar binding. -/
def emit (function : CheckedWordFunction) : Except EmitError EmittedProgram := do
  let body ← ScalarRenderer.render .word ["sc_input"] 8 0 function.body
  let lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ body.lines ++
    ["        return uint256(" ++ body.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Input
end

section
-- leanmerge: from Solcore.Synthesis.Source.InputCases
/-! Runtime-input cases retain an applied original Core lambda. Input selection
and literal abstraction have a separate version from the unchanged G0 generator.
Saved observations are never used as the execution oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Input
open Lean
open Solcore.Core
open Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-input-case.v1"
def profileVersion : String := "runtime-word-input-v1/literal-seed-mod-v1"

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.maximum, Word.ofNatModulo (2 ^ 255)]

def inputWord (text : String) : Except String Word := do
  let some value := text.toNat? | throw "input is not a decimal Word"
  unless toString value = text && value < 2 ^ 256 do
    throw "input must be a canonical decimal Word"
  return Word.ofNatModulo value

/-- The fixed-width ABI argument, following the independently checked selector. -/
def calldata (input : Word) : String :=
  selector ++ String.ofList ((List.range 64).map fun index =>
    Char.ofNat (let digit := input.val / 16 ^ (63 - index) % 16
      if digit < 10 then 48 + digit else 87 + digit))

structure CheckedInput where
  function : CheckedWordFunction
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : CheckedWordFunction) (input : Word) (fuel : Nat) : Json :=
  let fields := match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (function : CheckedWordFunction) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema),
  ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson wordFunctionVersion),
    ("abstractionVersion", toJson abstractionVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson ((features function.body).map featureName))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : CheckedWordFunction) (input : Word)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied input function exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program := do
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.programNodes program ≤ 512 do throw "Core program exceeds the 512-node case limit"
  return program

def checkedFunction (json : Json) : Except String CheckedWordFunction := do
  let some function := CheckedWordFunction.ofProgram? (← decodeProgram json) |
    throw "program is not a checked scalar Word-to-Word function"
  return function

def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic input case schema"
  let input ← inputWord (← json.getObjValAs? String "input")
  let program ← decodeProgram (← json.getObjVal? "program")
  match program with
  | { resultType := .word, dataDefinitions := [],
      body := .apply (.lambda .word .word body) (.word argument) } =>
      unless argument = input do throw "saved program argument differs from input"
      let some function := CheckedWordFunction.ofBody? body |
        throw "applied function is outside the checked scalar input profile"
      return ⟨function, input⟩
  | _ => throw "input case program is not a closed Word function application"

private def candidate (seed : Seed) (nodes : Nat) (revision : GeneratorRevision) :
    Except String (GeneratedProgram × Nat × CheckedWordFunction) := do
  let mask := revision.caseMask seed featureSupport
  let generated ← (generate {seed, maxProgramNodes := nodes, revision, mask}).mapError reprStr
  let count := literalCount generated.program.body
  unless count > 0 do throw "generated body has no Word literal to abstract"
  let literalIndex := seed.toNat % count
  let some function := CheckedWordFunction.fromProgram? generated.checkedProgram literalIndex |
    throw "literal abstraction did not produce a checked Word function"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ 512 do
    throw "applied input function exceeds the 512-node case limit"
  return (generated, literalIndex, function)

/-- A generation filter, not a claim that these four inputs cover a function. -/
def boundaryResults (function : CheckedWordFunction) (fuel : Nat) : Except String (List Word) := do
  boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (function : CheckedWordFunction) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all four boundary inputs returned the same Word"
  acceptance.check boundaryInputs results

/-- Attempt limits count functions; case limits count individual runtime inputs.
One accepted function emits the fixed four inputs in order, truncated by count. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (generated, literalIndex, function) ← candidate seed nodes revision
        let emitted ← (emit function).mapError reprStr
        inputSensitive function fuel acceptance
        return (generated, literalIndex, function, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)),
            ("stage", toJson "input-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (generated, literalIndex, function, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := Json.mkObj [
                ("kind", toJson "input-generated"),
                ("seed", toJson (toString generated.initialSeed.toNat)),
                ("finalSeed", toJson (toString generated.finalSeed.toNat)),
                ("maxProgramNodes", toJson generated.maxProgramNodes),
                ("literalIndex", toJson literalIndex), ("inputIndex", toJson inputIndex),
                ("validationFuel", toJson fuel)]
              cases := cases.push
                (makeCase function input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", wordFunctionVersion), ("abstractionVersion", abstractionVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core function"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the input wrapper"
  unless (← provenance.getObjVal? "features") ==
      toJson ((features admitted.function.body).map featureName) do
    throw "saved features differ from the original Core function"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "input-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported input case origin"
  if kind = "input-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless nodes ≤ 512 do throw "saved generation budget exceeds limit"
    let (generated, literalIndex, function) ← candidate (Seed.ofNat seed) nodes revision
    unless (← origin.getObjValAs? Nat "literalIndex") = literalIndex do
      throw "saved literal index differs from the input profile"
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved function differs from its generation seed"
    unless (← origin.getObjValAs? String "finalSeed") = toString generated.finalSeed.toNat do
      throw "saved final seed differs from generation"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive function validationFuel (← Acceptance.ofOrigin origin)
  return makeCase admitted.function admitted.input emitted origin fuel revision mask

/-- Sealing includes both full Core typing and a strictly smaller applied case. -/
structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (body : Wire.Expr) (input : Word) :
    Option (Reduction source) := do
  let function ← CheckedWordFunction.ofBody? body
  let candidate : CheckedInput := ⟨function, input⟩
  if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)
    then some ⟨candidate, strict⟩ else none

/-- Reuse capture-avoiding G0 shrinking under a dummy Word binder. Only candidates
retaining that binder are extracted; the input function is then independently
sealed. Input reduction is separate and cannot change the emitted source. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let wrapped : Wire.Program := {
    resultType := .word, dataDefinitions := [],
    body := .letE (.word Word.zero) source.function.body }
  let mut bodies : List Wire.Expr := [.word Word.zero, .var 0]
  if let some checked := CheckedWordProgram.ofProgram? wrapped then
    for reduced in shrink checked do
      if let .letE (.word value) body := reduced.body then
        if value = Word.zero then bodies := bodies ++ [body]
  let raw := bodies.map (fun body => (body, source.input)) ++
    [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (source.input.val / 2)].map
      (fun input => (source.function.body, input))
  let mut seen : List String := []
  let mut result := []
  for (body, input) in raw do
    if let some reduced := sealReduction source body input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.function reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Input
end

section
-- leanmerge: from Solcore.Synthesis.Source.FunctionCases
/-! Replayable, bounded cases for acyclic named Word functions. The original
Core lambda chain is retained and executed independently of source lowering.
The older scalar profiles and their replay rules remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Function
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-function-case.v1"
def profileVersion : String := "runtime-functions-v1/seed-chain-v1"

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
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson wordFunctionDAGVersion),
    ("abstractionVersion", toJson abstractionVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson function.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : CheckedWordFunctionDAG) (input : Word)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied function DAG exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel revision mask

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
      return ⟨function, input⟩
  | _ => throw "function case program is not a closed Word function DAG application"

/-- Scalar budgets account for every helper lambda, binding, call, input and
program node. The final measured applied program remains the admission rule. -/
def generatedFunction (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedWordFunctionDAG × Json) := do
  let count := 1 + seed.toNat % 3
  unless nodes ≤ 512 && 9 * count + 6 ≤ nodes do
    throw "node budget is too small for the selected helper count or exceeds 512"
  let scalarBudget := (nodes - (8 * count + 6)) / count + 2
  let mut helpers : List Wire.Expr := []
  let mut metadata : Array Json := #[]
  let mut finalSeed := seed
  -- One mask for every helper of the case.
  let mask := revision.caseMask seed featureSupport
  for index in List.range count do
    let helperSeed := Seed.ofNat (seed.toNat + index)
    let generated ←
      (generate {seed := helperSeed, maxProgramNodes := scalarBudget, revision, mask}).mapError reprStr
    let literals := literalCount generated.program.body
    unless literals > 0 do throw "generated helper has no Word literal to abstract"
    let selected := helperSeed.toNat % literals
    let some scalar := CheckedWordFunction.fromProgram? generated.checkedProgram selected |
      throw "helper literal abstraction did not produce a checked Word function"
    let body := if index = 0 then scalar.body else
      Wire.Expr.binary .wordAdd scalar.body (.apply (.var 1) (.var 0))
    helpers := helpers ++ [body]
    metadata := metadata.push (Json.mkObj [
      ("index", toJson index), ("seed", toJson (toString helperSeed.toNat)),
      ("finalSeed", toJson (toString generated.finalSeed.toNat)),
      ("maxProgramNodes", toJson scalarBudget), ("literalIndex", toJson selected)])
    finalSeed := generated.finalSeed
  let some function := CheckedWordFunctionDAG.ofParts? helpers (.apply (.var 1) (.var 0)) |
    throw "generated helper chain did not pass the full Core checker"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ nodes do
    throw "applied helper chain exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "function-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", toJson (toString finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
    ("helperCount", toJson count), ("helpers", .arr metadata)]
  return (function, origin)

def boundaryResults (function : CheckedWordFunctionDAG) (fuel : Nat) : Except String (List Word) :=
  Input.boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (function : CheckedWordFunctionDAG) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all four boundary inputs returned the same Word"
  acceptance.check Input.boundaryInputs results

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (function, origin) ← generatedFunction seed nodes revision
        let emitted ← (emit function).mapError reprStr
        inputSensitive function fuel acceptance
        return (function, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "function-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (function, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs Input.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase function input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", wordFunctionDAGVersion), ("abstractionVersion", abstractionVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core function DAG"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the function wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.function.features do
    throw "saved features differ from the original Core function DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "function-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported function case origin"
  if kind = "function-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (function, expectedOrigin) ← generatedFunction (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "helperCount", "helpers"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated helper provenance")
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved function DAG differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Input.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive function validationFuel (← Acceptance.ofOrigin origin)
  return makeCase admitted.function admitted.input emitted origin fuel revision mask

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.function.helpers.length = source.function.helpers.length
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (helpers : List Wire.Expr)
    (entry : Wire.Expr) (input : Word) : Option (Reduction source) := do
  let function ← CheckedWordFunctionDAG.ofParts? helpers entry
  let candidate : CheckedInput := ⟨function, input⟩
  if count : candidate.function.helpers.length = source.function.helpers.length then
    if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)
      then some ⟨candidate, count, strict⟩ else none
  else none

/-- Local rewrites never remove or reorder the surrounding function bindings.
Removing a scalar binder is deliberately omitted; final DAG checking validates
every variable and call after all other rewrites. -/
private def bodyReductions (target : Target) : Wire.Expr → List Wire.Expr
  | .word _ | .bool _ | .var _ => [if target = .word then .word Word.zero else .bool false]
  | .letE initializer body =>
      [if target = .word then .word Word.zero else .bool false] ++
      (if target = .word then [initializer] else []) ++
      (bodyReductions .word initializer).map (fun changed => .letE changed body) ++
      (bodyReductions target body).map (.letE initializer)
  | .ifE condition yes no =>
      [if target = .word then .word Word.zero else .bool false, yes, no] ++
      (bodyReductions .bool condition).map (fun changed => .ifE changed yes no) ++
      (bodyReductions target yes).map (fun changed => .ifE condition changed no) ++
      (bodyReductions target no).map (.ifE condition yes)
  | .unary operation operand =>
      [if target = .word then .word Word.zero else .bool false, operand] ++
      (bodyReductions (Target.unaryOperand operation) operand).map (.unary operation)
  | .binary operation left right =>
      [if target = .word then .word Word.zero else .bool false, left, right] ++
      (bodyReductions .word left).map (fun changed => .binary operation changed right) ++
      (bodyReductions .word right).map (.binary operation left)
  | .ternary operation first second third =>
      [.word Word.zero, first, second, third] ++
      (bodyReductions .word first).map (fun changed => .ternary operation changed second third) ++
      (bodyReductions .word second).map (fun changed => .ternary operation first changed third) ++
      (bodyReductions .word third).map (.ternary operation first second)
  | .apply function argument =>
      [.word Word.zero, argument] ++ (bodyReductions .word argument).map (.apply function)
  | _ => []

def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (List Wire.Expr × Wire.Expr × Word) := []
  for (body, index) in source.function.helpers.zipIdx do
    for changed in bodyReductions .word body do
      raw := raw ++ [(source.function.helpers.set index changed, source.function.entry, source.input)]
  for changed in bodyReductions .word source.function.entry do
    raw := raw ++ [(source.function.helpers, changed, source.input)]
  for input in [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (source.input.val / 2)] do
    raw := raw ++ [(source.function.helpers, source.function.entry, input)]
  let mut seen : List String := []
  let mut result := []
  for (helpers, entry, input) in raw do
    if let some reduced := sealReduction source helpers entry input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.function reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Function
end

section
-- leanmerge: from Solcore.Synthesis.Source.MutationRenderer
/-! Statement rendering for private mutable locals. Every cell read is copied
to a fresh immutable temporary before any later operand can mutate that cell.
Unit bindings occupy Core indices but need no source-level value. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MutationRenderer

open Solcore.Core.Wire
open Solcore.Synthesis.Core.LocalMutation (Target Local)

/-- The G0 features this renderer renders: its unary and binary operations go
through `ScalarRenderer`, and it renders no ternary. -/
def support := scalarSupport

inductive Binding where
  | word (name : String)
  | bool (name : String)
  | cellWord (name : String)
  | unit

def Binding.kind : Binding → Local
  | .word _ => .word
  | .bool _ => .bool
  | .cellWord _ => .cellWord
  | .unit => .unit

structure Rendered where
  lines : List String
  value : Option String
  nextId : Nat

private def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def name (index : Nat) : String := "sc_v" ++ toString index
private def cellName (index : Nat) : String := "sc_c" ++ toString index

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"
  | .unit => "unit"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"
  | .unit => ""

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    some (name nextId), nextId + 1⟩

def requireValue (rendered : Rendered) : Except EmitError String :=
  match rendered.value with
  | some value => .ok value
  | none => .error (.unsupportedExpression "Unit used as a scalar value")

private def scalarTarget : Target → Except EmitError Solcore.Synthesis.Core.Target
  | .word => .ok .word
  | .bool => .ok .bool
  | .unit => .error (.unsupportedExpression "Unit used as a scalar target")

private def fromScalar (rendered : ScalarRenderer.Rendered) : Rendered :=
  ⟨rendered.lines, some rendered.value, rendered.nextId⟩

private def scalar (target : Target) (operands : List String)
    (indent nextId : Nat) (expression : Expr) : Except EmitError Rendered := do
  return fromScalar (← ScalarRenderer.render (← scalarTarget target) operands indent nextId expression)

private def cell (bindings : List Binding) (index : Nat) : Except EmitError String :=
  match bindings[index]? with
  | some (.cellWord name) => .ok name
  | _ => .error (.unsupportedExpression "cell reference is not a direct private local")

/-- The context includes every Core binder, including elided Unit values.
Helper function indices begin immediately after this complete local context. -/
def render (functions : List String) (target : Target) (bindings : List Binding)
    (indent nextId : Nat) : Expr → Except EmitError Rendered
  | .word value => scalar .word [] indent nextId (.word value)
  | .bool value => scalar .bool [] indent nextId (.bool value)
  | .unit => .ok ⟨[], none, nextId⟩
  | .var index => match bindings[index]? with
      | some (.word value) | some (.bool value) => .ok ⟨[], some value, nextId⟩
      | some .unit => .ok ⟨[], none, nextId⟩
      | _ => .error (.unboundLocal index)
  | .letE (.newCell .word initializer) body => do
      let initial ← render functions .word bindings indent nextId initializer
      let value ← requireValue initial
      let binding := cellName initial.nextId
      let rest ← render functions target (.cellWord binding :: bindings) indent (initial.nextId + 1) body
      return ⟨initial.lines ++ [line indent ("let " ++ binding ++ ": word = " ++ value ++ ";")] ++ rest.lines,
        rest.value, rest.nextId⟩
  | .letE initializer body => do
      let some kind := Solcore.Synthesis.Core.LocalMutation.infer?
          (bindings.map Binding.kind) functions.length initializer |
        throw (.unsupportedExpression "unsupported local initializer")
      let initial ← render functions kind bindings indent nextId initializer
      match kind with
      | .unit =>
        let rest ← render functions target (.unit :: bindings) indent initial.nextId body
        return ⟨initial.lines ++ rest.lines, rest.value, rest.nextId⟩
      | .word | .bool =>
        let value ← requireValue initial
        let bound := bindValue kind indent initial.nextId value
        let binding := if kind == .word then Binding.word (name initial.nextId)
          else Binding.bool (name initial.nextId)
        let rest ← render functions target (binding :: bindings) indent bound.nextId body
        return ⟨initial.lines ++ bound.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← render functions .bool bindings indent nextId condition
      let conditionValue ← requireValue tested
      if target == .unit then
        let selected ← render functions .unit bindings (indent + 4) tested.nextId yes
        let fallback ← render functions .unit bindings (indent + 4) selected.nextId no
        return ⟨tested.lines ++ [line indent ("if (" ++ conditionValue ++ ") {")] ++
          selected.lines ++ [line indent "} else {"] ++ fallback.lines ++ [line indent "}"],
          none, fallback.nextId⟩
      else
        let result := bindValue target indent tested.nextId (zero target)
        let resultValue ← requireValue result
        let selected ← render functions target bindings (indent + 4) result.nextId yes
        let selectedValue ← requireValue selected
        let fallback ← render functions target bindings (indent + 4) selected.nextId no
        let fallbackValue ← requireValue fallback
        return ⟨tested.lines ++ result.lines ++ [line indent ("if (" ++ conditionValue ++ ") {")] ++
          selected.lines ++ [line (indent + 4) (resultValue ++ " = " ++ selectedValue ++ ";"),
            line indent "} else {"] ++ fallback.lines ++
          [line (indent + 4) (resultValue ++ " = " ++ fallbackValue ++ ";"), line indent "}"],
          some resultValue, fallback.nextId⟩
  | .loadCell (.var index) => do
      return bindValue .word indent nextId (← cell bindings index)
  | .storeCell (.var index) value => do
      let reference ← cell bindings index
      let written ← render functions .word bindings indent nextId value
      let result ← requireValue written
      return ⟨written.lines ++ [line indent (reference ++ " = " ++ result ++ ";")], none, written.nextId⟩
  | .unary operation operand => do
      let operandTarget := if operation == .boolNot then Target.bool else Target.word
      let rendered ← render functions operandTarget bindings indent nextId operand
      let value ← requireValue rendered
      let result ← scalar target [value] indent rendered.nextId (.unary operation (.var 0))
      return ⟨rendered.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      let first ← render functions .word bindings indent nextId left
      let firstValue ← requireValue first
      let second ← render functions .word bindings indent first.nextId right
      let secondValue ← requireValue second
      let result ← scalar target [firstValue, secondValue] indent second.nextId
        (.binary operation (.var 0) (.var 1))
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .apply (.var index) argument => do
      if index < bindings.length then throw (.unsupportedExpression "apply")
      let some callee := functions[index - bindings.length]? | throw (.unsupportedExpression "apply")
      let argument ← render functions .word bindings indent nextId argument
      let value ← requireValue argument
      let result := bindValue .word indent argument.nextId (callee ++ "(" ++ value ++ ")")
      return ⟨argument.lines ++ result.lines, result.value, result.nextId⟩
  | .ternary operation _ _ _ => .error (.unsupportedTernary operation)
  | .integer _ => .error (.unsupportedExpression "integer")
  | .pair _ _ => .error (.unsupportedExpression "pair")
  | .first _ => .error (.unsupportedExpression "first")
  | .second _ => .error (.unsupportedExpression "second")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply _ _ => .error (.unsupportedExpression "apply")
  | .inLeft _ _ => .error (.unsupportedExpression "inLeft")
  | .inRight _ _ => .error (.unsupportedExpression "inRight")
  | .caseE _ _ _ => .error (.unsupportedExpression "caseE")
  | .newCell _ _ => .error (.unsupportedExpression "newCell outside direct Word let initializer")
  | .loadCell _ => .error (.unsupportedExpression "loadCell")
  | .storeCell _ _ => .error (.unsupportedExpression "storeCell")
  | .construct _ _ => .error (.unsupportedExpression "construct")
  | .matchData _ _ _ _ => .error (.unsupportedExpression "matchData")

end Solcore.Synthesis.Source.MutationRenderer
end

section
-- leanmerge: from Solcore.Synthesis.Source.MutationEmitter
/-! Source mutation uses only private Word locals. The same original Core DAG
drives the independent runtime result. `ScalarMeaning.Mutation.emit_source_meaning`
relates the emitted text to the original Core result under an independent
source semantics; see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Mutation

open Solcore.Synthesis.Core.LocalMutation (CheckedDAG)

def emitterVersion : String := "solcore-source-mutation-v2"
def wrapperVersion : String := "solcore-word-mutation-contract-v1"

/-- The G0 features `emit` renders, those of `MutationRenderer`. -/
def featureSupport := MutationRenderer.support
def contractName : String := "SynthesizedMutation"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedMutationDeploy"]
def runtimePath : List String := ["SynthesizedMutationDeploy", "SynthesizedMutation"]

def emit (graph : CheckedDAG) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;", ""]
  for (body, index) in graph.helpers.zipIdx do
    let rendered ← MutationRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← MutationRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← MutationRenderer.render names .word [.word "sc_input"] 8 0 graph.entry
  let result ← MutationRenderer.requireValue entry
  lines := lines ++ ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
    ["        return uint256(" ++ result ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Mutation
end

section
-- leanmerge: from Solcore.Synthesis.Source.MutationCases
/-! Replayable cases with private mutable Word locals. The original Core
allocations, ordered loads/stores and helper calls remain the independent oracle.
The older profiles and their replay rules remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Mutation
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-mutation-case.v1"
def profileVersion : String := "runtime-mutation-v1/template-seed-v1"
def templateVersion : String := "local-word-mutation-templates-v1"

structure CheckedInput where
  function : CheckedLocalMutationDAG
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : CheckedLocalMutationDAG) (input : Word) (fuel : Nat) : Json :=
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

def makeCase (function : CheckedLocalMutationDAG) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson LocalMutation.version),
    ("templateVersion", toJson templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson function.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : CheckedLocalMutationDAG) (input : Word)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied function DAG exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program := do
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.programNodes program ≤ 512 do throw "Core program exceeds the 512-node case limit"
  return program

def checkedFunction (json : Json) : Except String CheckedLocalMutationDAG := do
  let some function := LocalMutation.CheckedDAG.ofProgram? (← decodeProgram json) |
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
      let some function := LocalMutation.CheckedDAG.ofProgram? {
        resultType := .function .word .word, dataDefinitions := [], body := functionBody } |
        throw "applied function is outside the checked function DAG profile"
      return ⟨function, input⟩
  | _ => throw "function case program is not a closed Word function DAG application"

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def load (index : Nat) : Wire.Expr := .loadCell (.var index)

/-- `depth` counts intervening Unit bindings. Cell and scalar indices always
include them, even though the emitted source does not name the Unit values. -/
private def updates (pattern depth ordinal : Nat) : Nat → Wire.Expr
  | 0 => if pattern = 2 then .binary .wordAdd (load (depth + 1)) (load depth) else load depth
  | remaining + 1 =>
      let stored :=
        if pattern = 2 then
          let target := depth + (if ordinal % 2 = 0 then 1 else 0)
          let other := depth + (if ordinal % 2 = 0 then 0 else 1)
          .storeCell (.var target)
            (.binary .wordAdd (.binary .wordAdd (load target) (load other)) (.var (depth + 2)))
        else if pattern = 1 then
          .ifE (.binary .wordGt (load depth) (.var (depth + 1)))
            (.storeCell (.var depth) (.binary .wordAdd (load depth) (.var (depth + 1))))
            (.storeCell (.var depth) (.binary .wordSub (load depth) (.var (depth + 1))))
        else if pattern = 3 then
          .storeCell (.var depth) (.binary .wordAdd (.var (depth + 1)) (word ordinal))
        else
          .storeCell (.var depth) (.binary .wordAdd (load depth) (.var (depth + 1)))
      .letE stored (updates pattern (depth + 1) (ordinal + 1) remaining)

/-- A closed G0 subtree remains closed beneath these binders. Pattern three
must snapshot its left load before the right-hand stores are evaluated. -/
def template (pattern count : Nat) (scalar : Wire.Expr) : Wire.Expr :=
  .letE scalar (.letE (.newCell .word (.var 1))
    (if pattern = 2 then
      .letE (.newCell .word (load 0)) (updates pattern 0 0 count)
    else if pattern = 3 then
      .binary .wordAdd (load 0) (updates pattern 0 0 count)
    else updates pattern 0 0 count))

private def helperBody (index pattern count : Nat) (scalar : Wire.Expr) : Wire.Expr :=
  let body := template pattern count scalar
  if index = 0 then body else .apply (.var 1) body

private def patternFor (seed : Seed) : Nat := seed.toNat / 3 % 4
private def updatesFor (seed : Seed) : Nat := 1 + seed.toNat / 12 % 4

private def appliedNodes (helpers : List Wire.Expr) : Nat := Wire.programNodes {
  resultType := .word, dataDefinitions := [],
  body := .apply (functionDAGExpression helpers (.apply (.var 1) (.var 0))) (word 0) }

/-- Budget from the actual full applied skeleton, with one scalar placeholder
per helper. The final measured program is checked again after generation. -/
def generatedFunction (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedLocalMutationDAG × Json) := do
  let count := 1 + seed.toNat % 3
  let skeleton := (List.range count).map fun index =>
    let helperSeed := Seed.ofNat (seed.toNat + index)
    helperBody index (patternFor helperSeed) (updatesFor helperSeed) (word 0)
  let skeletonNodes := appliedNodes skeleton
  unless nodes ≤ 512 && skeletonNodes ≤ nodes do
    throw "node budget is too small for the selected mutation template or exceeds 512"
  let scalarBudget := (nodes - (skeletonNodes - count)) / count + 2
  let mut helpers : List Wire.Expr := []
  let mut metadata : Array Json := #[]
  let mut finalSeed := seed
  -- One mask for every helper of the case.
  let mask := revision.caseMask seed featureSupport
  for index in List.range count do
    let helperSeed := Seed.ofNat (seed.toNat + index)
    let generated ←
      (generate {seed := helperSeed, maxProgramNodes := scalarBudget, revision, mask}).mapError reprStr
    let pattern := patternFor helperSeed
    let updateCount := updatesFor helperSeed
    let body := helperBody index pattern updateCount generated.program.body
    helpers := helpers ++ [body]
    metadata := metadata.push (Json.mkObj [
      ("index", toJson index), ("seed", toJson (toString helperSeed.toNat)),
      ("finalSeed", toJson (toString generated.finalSeed.toNat)),
      ("maxProgramNodes", toJson scalarBudget), ("template", toJson pattern),
      ("updates", toJson updateCount)])
    finalSeed := generated.finalSeed
  let some function := LocalMutation.CheckedDAG.ofParts? helpers (.apply (.var 1) (.var 0)) |
    throw "generated helper chain did not pass the full Core checker"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ nodes do
    throw "applied helper chain exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "mutation-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", toJson (toString finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
    ("helperCount", toJson count), ("helpers", .arr metadata)]
  return (function, origin)

def boundaryResults (function : CheckedLocalMutationDAG) (fuel : Nat) : Except String (List Word) :=
  Input.boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (function : CheckedLocalMutationDAG) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all four boundary inputs returned the same Word"
  acceptance.check Input.boundaryInputs results

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (function, origin) ← generatedFunction seed nodes revision
        let emitted ← (emit function).mapError reprStr
        inputSensitive function fuel acceptance
        return (function, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "mutation-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (function, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs Input.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase function input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", LocalMutation.version), ("templateVersion", templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core function DAG"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the function wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.function.features do
    throw "saved features differ from the original Core function DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "mutation-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported function case origin"
  if kind = "mutation-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (function, expectedOrigin) ← generatedFunction (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "helperCount", "helpers"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated helper provenance")
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved function DAG differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Input.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive function validationFuel (← Acceptance.ofOrigin origin)
  return makeCase admitted.function admitted.input emitted origin fuel revision mask

/-- Binder kinds in expression preorder, including Unit binders and both
branches. The enclosing helper declaration binders are handled separately. -/
def bindingKinds (locals : List LocalMutation.Local) (prior : Nat) : Wire.Expr → List LocalMutation.Local
  | .letE initializer body =>
      match LocalMutation.initializerKind? locals prior initializer with
      | none => []
      | some kind => bindingKinds locals prior initializer ++ [kind] ++
          bindingKinds (kind :: locals) prior body
  | .ifE condition yes no | .ternary _ condition yes no =>
      bindingKinds locals prior condition ++ bindingKinds locals prior yes ++ bindingKinds locals prior no
  | .binary _ left right => bindingKinds locals prior left ++ bindingKinds locals prior right
  | .unary _ operand | .newCell _ operand => bindingKinds locals prior operand
  | .apply _ argument | .storeCell _ argument => bindingKinds locals prior argument
  | _ => []

def bindingInventory (function : CheckedLocalMutationDAG) : List LocalMutation.Local :=
  (function.helpers.zipIdx.flatMap fun (body, index) => bindingKinds [.word] index body) ++
    bindingKinds [.word] function.helpers.length function.entry

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.function.helpers.length = source.function.helpers.length
  sameBindings : bindingInventory candidate.function = bindingInventory source.function
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (helpers : List Wire.Expr)
    (entry : Wire.Expr) (input : Word) : Option (Reduction source) := do
  let function ← LocalMutation.CheckedDAG.ofParts? helpers entry
  let candidate : CheckedInput := ⟨function, input⟩
  if count : candidate.function.helpers.length = source.function.helpers.length then
    if bindings : bindingInventory candidate.function = bindingInventory source.function then
      if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)
        then some ⟨candidate, count, bindings, strict⟩ else none
    else none
  else none

/-- Typed local rewrites keep every cell/Unit/Word/Bool binder in order.
Replacing a store by Unit is allowed only when its value contains no binders;
otherwise its value is recursively reduced. Whole-DAG checking remains final. -/
private def bodyReductions (locals : List LocalMutation.Local) (prior : Nat)
    (expression : Wire.Expr) : List Wire.Expr :=
  let canonical := if (bindingKinds locals prior expression).isEmpty then
      match LocalMutation.initializerKind? locals prior expression with
      | some .word => [word 0]
      | some .bool => [.bool false]
      | some .unit => [.unit]
      | _ => []
    else []
  canonical ++ match expression with
  | .letE initializer body =>
      match LocalMutation.initializerKind? locals prior initializer with
      | none => []
      | some kind =>
          ((bodyReductions locals prior initializer).filter fun changed =>
            LocalMutation.initializerKind? locals prior changed == some kind).map
              (fun changed => .letE changed body) ++
          (bodyReductions (kind :: locals) prior body).map (.letE initializer)
  | .ifE condition yes no =>
      (bodyReductions locals prior condition).map (fun changed => .ifE changed yes no) ++
      (bodyReductions locals prior yes).map (fun changed => .ifE condition changed no) ++
      (bodyReductions locals prior no).map (.ifE condition yes)
  | .unary operation operand =>
      (bodyReductions locals prior operand).map (.unary operation)
  | .binary operation left right =>
      (bodyReductions locals prior left).map (fun changed => .binary operation changed right) ++
      (bodyReductions locals prior right).map (.binary operation left)
  | .ternary operation first second third =>
      (bodyReductions locals prior first).map (fun changed => .ternary operation changed second third) ++
      (bodyReductions locals prior second).map (fun changed => .ternary operation first changed third) ++
      (bodyReductions locals prior third).map (.ternary operation first second)
  | .newCell .word initializer =>
      (bodyReductions locals prior initializer).map (.newCell .word)
  | .storeCell reference value =>
      (bodyReductions locals prior value).map (.storeCell reference)
  | .apply function argument =>
      (bodyReductions locals prior argument).map (.apply function)
  | _ => []

def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (List Wire.Expr × Wire.Expr × Word) := []
  for (body, index) in source.function.helpers.zipIdx do
    for changed in bodyReductions [.word] index body do
      raw := raw ++ [(source.function.helpers.set index changed, source.function.entry, source.input)]
  for changed in bodyReductions [.word] source.function.helpers.length source.function.entry do
    raw := raw ++ [(source.function.helpers, changed, source.input)]
  for input in [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (source.input.val / 2)] do
    raw := raw ++ [(source.function.helpers, source.function.entry, input)]
  let mut seen : List String := []
  let mut result := []
  for (helpers, entry, input) in raw do
    if let some reduced := sealReduction source helpers entry input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.function reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Mutation
end

section
-- leanmerge: from Solcore.Synthesis.Source.PrimitiveRenderer
/-! An isolated scalar renderer for the extended runtime primitive profile.
Raw opcode aliases preserve the Core operations' zero and overflow behavior.
This is a tested printer, not a source meaning-preservation theorem. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.PrimitiveRenderer

open Solcore.Core.Wire
open Solcore.Synthesis.Core (Target FeatureMask)
open ScalarRenderer (Rendered)

def supportedUnary : UnaryOp → Bool
  | .wordClz => true
  | operation => Source.supportedUnary operation

def supportedBinary : BinaryOp → Bool
  | .wordDiv | .wordMod | .wordShl | .wordShr | .wordSar
  | .wordSdiv | .wordSmod | .wordSgt | .wordByte | .wordPow | .wordSignExtend => true
  | operation => Source.supportedBinary operation

def supportedTernary : TernaryOp → Bool
  | .wordAddMod | .wordMulMod => true

/-- The G0 features this renderer renders: every operator and form. -/
def support : FeatureMask := FeatureMask.supporting supportedUnary supportedBinary supportedTernary

/-- Syntax support is separate from the existing checked function boundary. -/
def supported : Expr → Bool
  | .word _ | .bool _ | .var _ => true
  | .letE initializer body => supported initializer && supported body
  | .ifE condition yes no => supported condition && supported yes && supported no
  | .unary operation operand => supportedUnary operation && supported operand
  | .binary operation left right => supportedBinary operation && supported left && supported right
  | .ternary operation first second third =>
      supportedTernary operation && supported first && supported second && supported third
  | _ => false

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"

private def name (index : Nat) : String := "sc_v" ++ toString index

private def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    name nextId, nextId + 1⟩

private def snapshot (indent : Nat) (value : Rendered) : Rendered :=
  let captured := bindValue .word indent value.nextId value.value
  ⟨value.lines ++ captured.lines, captured.value, captured.nextId⟩

private def unaryValue (operation : UnaryOp) (operand : String) : Except EmitError String :=
  match operation with
  | .boolNot => .ok ("(!" ++ operand ++ ")")
  | .wordNot => .ok ("(~" ++ operand ++ ")")
  | .wordClz => .ok ("sc_clz(" ++ operand ++ ")")
  | _ => .error (.unsupportedUnary operation)

private def binaryValue (operation : BinaryOp) (left right : String) : Except EmitError String :=
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

private def ternaryValue (operation : TernaryOp) (first second third : String) : String :=
  let callee := match operation with
    | .wordAddMod => "sc_addmod"
    | .wordMulMod => "sc_mulmod"
  callee ++ "(" ++ first ++ ", " ++ second ++ ", " ++ third ++ ")"

/-- Bindings are nearest first, as in the original Core function. Raw opcode
arguments are captured left to right before reordered shift arguments are
printed. Branch-local computations remain inside their selected branch. -/
def render (target : Target) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok (bindValue .word indent nextId (toString value.val))
  | .bool value => .ok (bindValue .bool indent nextId (if value then "true" else "false"))
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← render .word locals indent nextId initializer
      let binding := bindValue .word indent value.nextId value.value
      let rest ← render target (binding.value :: locals) indent binding.nextId body
      return ⟨value.lines ++ binding.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← render .bool locals indent nextId condition
      let result := bindValue target indent tested.nextId (zero target)
      let selected ← render target locals (indent + 4) result.nextId yes
      let fallback ← render target locals (indent + 4) selected.nextId no
      return ⟨tested.lines ++ result.lines ++
        [line indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
        [line (indent + 4) (result.value ++ " = " ++ selected.value ++ ";"), line indent "} else {"] ++
        fallback.lines ++ [line (indent + 4) (result.value ++ " = " ++ fallback.value ++ ";"), line indent "}"],
        result.value, fallback.nextId⟩
  | .unary operation operand => do
      unless supportedUnary operation do throw (.unsupportedUnary operation)
      let value ← render (if operation == .boolNot then .bool else .word) locals indent nextId operand
      let value := if operation == .wordClz then snapshot indent value else value
      let expression ← unaryValue operation value.value
      let result := bindValue target indent value.nextId expression
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      unless supportedBinary operation do throw (.unsupportedBinary operation)
      let first ← render .word locals indent nextId left
      let first := if Source.supportedBinary operation then first else snapshot indent first
      let second ← render .word locals indent first.nextId right
      let second := if Source.supportedBinary operation then second else snapshot indent second
      let expression ← binaryValue operation first.value second.value
      let result := bindValue target indent second.nextId expression
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .ternary operation first second third => do
      let first := snapshot indent (← render .word locals indent nextId first)
      let second := snapshot indent (← render .word locals indent first.nextId second)
      let third := snapshot indent (← render .word locals indent second.nextId third)
      let result := bindValue target indent third.nextId (ternaryValue operation first.value second.value third.value)
      return ⟨first.lines ++ second.lines ++ third.lines ++ result.lines, result.value, result.nextId⟩
  | .unit => .error (.unsupportedExpression "unit")
  | .integer _ => .error (.unsupportedExpression "integer")
  | .pair _ _ => .error (.unsupportedExpression "pair")
  | .first _ => .error (.unsupportedExpression "first")
  | .second _ => .error (.unsupportedExpression "second")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply _ _ => .error (.unsupportedExpression "apply")
  | .inLeft _ _ => .error (.unsupportedExpression "inLeft")
  | .inRight _ _ => .error (.unsupportedExpression "inRight")
  | .caseE _ _ _ => .error (.unsupportedExpression "caseE")
  | .newCell _ _ => .error (.unsupportedExpression "newCell")
  | .loadCell _ => .error (.unsupportedExpression "loadCell")
  | .storeCell _ _ => .error (.unsupportedExpression "storeCell")
  | .construct _ _ => .error (.unsupportedExpression "construct")
  | .matchData _ _ _ _ => .error (.unsupportedExpression "matchData")

end Solcore.Synthesis.Source.PrimitiveRenderer
end

section
-- leanmerge: from Solcore.Synthesis.Source.PrimitiveEmitter
/-! Source emission for independently checked Word functions with the full
scalar Word primitive catalog. Existing scalar emitter behavior is unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Primitive

open Solcore.Synthesis.Core (CheckedWordFunction)

def emitterVersion : String := "solcore-source-primitives-v2"
def wrapperVersion : String := "solcore-word-primitives-contract-v1"

/-- The G0 features `emit` renders: every operator and form. -/
def featureSupport := PrimitiveRenderer.support
def contractName : String := "SynthesizedPrimitives"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedPrimitivesDeploy"]
def runtimePath : List String := ["SynthesizedPrimitivesDeploy", "SynthesizedPrimitives"]

/-- Use raw opcode imports: the public `std.addmod` and `std.mulmod` wrappers
revert for modulus zero, whereas these Core operations return zero. -/
def opcodeImport : String :=
  "import { div as sc_div, mod as sc_mod, shl as sc_shl, shr as sc_shr, sar as sc_sar, " ++
  "sdiv as sc_sdiv, smod as sc_smod, sgt as sc_sgt, addmod as sc_addmod, mulmod as sc_mulmod, " ++
  "clz as sc_clz, byte as sc_byte, exp as sc_exp, signextend as sc_signextend } from std.opcodes;"

def emit (function : CheckedWordFunction) : Except EmitError EmittedProgram := do
  let body ← PrimitiveRenderer.render .word ["sc_input"] 8 0 function.body
  let lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    opcodeImport, "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ body.lines ++
    ["        return uint256(" ++ body.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Primitive
end

section
-- leanmerge: from Solcore.Synthesis.Source.PrimitiveCases
/-! Extended primitive cases retain the independently checked original Core
function. Generation reuses the unchanged broad G0 grammar and literal
abstraction, then checks the new emitter boundary. Saved observations never
supply the oracle. The complete applied program, including its input, is bounded. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Primitive
open Lean
open Solcore.Core
open Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-primitive-case.v1"
def profileVersion : String := "runtime-primitives-v1/literal-seed-v1"
def generatorVersion : String := "core-primitives-v1/" ++ Solcore.Synthesis.Core.generatorVersion

/-- The profile layer over one G0 revision; `generatorVersion` is its `v1` value. -/
def generatorVersionFor (revision : GeneratorRevision) : String :=
  "core-primitives-v1/" ++ revision.version
def boundaryVersion : String := "word-primitive-boundary-bank-v1"

/-- Difference measured from the existing Wire node-count definitions, including
the lambda's parameter/result types and the actual input application. -/
def appliedOverhead : Nat :=
  let scalar : Wire.Program := {resultType := .word, dataDefinitions := [], body := .word Word.zero}
  let applied : Wire.Program := {
    resultType := .word, dataDefinitions := [],
    body := .apply (wordFunctionProgram scalar.body).body (.word Word.zero)}
  Wire.programNodes applied - Wire.programNodes scalar

def minimumProgramNodes : Nat := Solcore.Synthesis.Core.minimumProgramNodes + appliedOverhead

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 2, Word.ofNatModulo 255,
    Word.ofNatModulo 256, Word.maximum, Word.ofNatModulo (2 ^ 255),
    Word.ofNatModulo (2 ^ 255 - 1)]

def inputWord (text : String) : Except String Word := do
  let some value := text.toNat? | throw "input is not a decimal Word"
  unless toString value = text && value < 2 ^ 256 do
    throw "input must be a canonical decimal Word"
  return Word.ofNatModulo value

/-- The fixed-width ABI argument, following the independently checked selector. -/
def calldata (input : Word) : String :=
  selector ++ String.ofList ((List.range 64).map fun index =>
    Char.ofNat (let digit := input.val / 16 ^ (63 - index) % 16
      if digit < 10 then 48 + digit else 87 + digit))

structure CheckedInput where
  function : CheckedWordFunction
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : CheckedWordFunction) (input : Word) (fuel : Nat) : Json :=
  let fields := match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (function : CheckedWordFunction) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema),
  ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson wordFunctionVersion),
    ("abstractionVersion", toJson abstractionVersion),
    ("generatorVersion", toJson (generatorVersionFor revision)),
    ("baseGeneratorVersion", toJson revision.version),
    ("boundaryVersion", toJson boundaryVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson ((features function.body).map featureName))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : CheckedWordFunction) (input : Word)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied primitive function exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program := do
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.programNodes program ≤ 512 do throw "Core program exceeds the 512-node case limit"
  return program

def checkedFunction (json : Json) : Except String CheckedWordFunction := do
  let some function := CheckedWordFunction.ofProgram? (← decodeProgram json) |
    throw "program is not a checked scalar Word-to-Word function"
  unless PrimitiveRenderer.supported function.body do
    throw "unsupported source primitive in the checked function"
  return function

def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic primitive case schema"
  let input ← inputWord (← json.getObjValAs? String "input")
  let program ← decodeProgram (← json.getObjVal? "program")
  match program with
  | { resultType := .word, dataDefinitions := [],
      body := .apply (.lambda .word .word body) (.word argument) } =>
      unless argument = input do throw "saved program argument differs from input"
      let some function := CheckedWordFunction.ofBody? body |
        throw "applied function is outside the checked scalar input profile"
      unless PrimitiveRenderer.supported function.body do
        throw "unsupported source primitive in the applied function"
      let admitted : CheckedInput := ⟨function, input⟩
      unless Wire.encodeProgram admitted.program == (← json.getObjVal? "program") do
        throw "saved Core function application is not canonical"
      return admitted
  | _ => throw "input case program is not a closed Word function application"

private def candidate (seed : Seed) (nodes : Nat) (revision : GeneratorRevision) :
    Except String (GeneratedProgram × Nat × CheckedWordFunction) := do
  unless minimumProgramNodes ≤ nodes && nodes ≤ 512 do
    throw "complete primitive program budget must be between the profile minimum and 512"
  let mask := revision.caseMask seed featureSupport
  let generated ←
    (generate {seed, maxProgramNodes := nodes - appliedOverhead, revision, mask}).mapError reprStr
  let count := literalCount generated.program.body
  unless count > 0 do throw "generated body has no Word literal to abstract"
  let literalIndex := seed.toNat % count
  let some function := CheckedWordFunction.fromProgram? generated.checkedProgram literalIndex |
    throw "literal abstraction did not produce a checked Word function"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ nodes do
    throw "applied primitive function exceeds its complete program budget"
  return (generated, literalIndex, function)

/-- A generation filter, not a claim that this finite bank covers a function. -/
def boundaryResults (function : CheckedWordFunction) (fuel : Nat) : Except String (List Word) := do
  boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (function : CheckedWordFunction) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all eight boundary inputs returned the same Word"
  acceptance.check boundaryInputs results

/-- Attempt limits count functions; case limits count individual runtime inputs.
One accepted function emits the fixed eight inputs in order, truncated by count. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (generated, literalIndex, function) ← candidate seed nodes revision
        let emitted ← (emit function).mapError (fun error => "unsupported source primitive: " ++ reprStr error)
        inputSensitive function fuel acceptance
        return (generated, literalIndex, function, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)),
            ("stage", toJson "primitive-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error.startsWith "unsupported source primitive:" then "unsupported-operation"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (generated, literalIndex, function, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := Json.mkObj [
                ("kind", toJson "primitive-generated"),
                ("seed", toJson (toString generated.initialSeed.toNat)),
                ("finalSeed", toJson (toString generated.finalSeed.toNat)),
                ("maxProgramNodes", toJson nodes),
                ("baseProgramNodes", toJson generated.maxProgramNodes),
                ("literalIndex", toJson literalIndex), ("inputIndex", toJson inputIndex),
                ("validationFuel", toJson fuel)]
              cases := cases.push
                (makeCase function input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  for (name, expected) in [
      ("generatorVersion", generatorVersionFor revision), ("profileVersion", profileVersion),
      ("baseGeneratorVersion", revision.version), ("boundaryVersion", boundaryVersion),
      ("functionVersion", wordFunctionVersion), ("abstractionVersion", abstractionVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core function"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the input wrapper"
  unless (← provenance.getObjVal? "features") ==
      toJson ((features admitted.function.body).map featureName) do
    throw "saved features differ from the original Core function"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "primitive-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported input case origin"
  if kind = "primitive-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumProgramNodes ≤ nodes && nodes ≤ 512 do throw "saved generation budget exceeds profile limits"
    let (generated, literalIndex, function) ← candidate (Seed.ofNat seed) nodes revision
    unless (← origin.getObjValAs? Nat "literalIndex") = literalIndex do
      throw "saved literal index differs from the input profile"
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved function differs from its generation seed"
    unless (← origin.getObjValAs? String "finalSeed") = toString generated.finalSeed.toNat do
      throw "saved final seed differs from generation"
    unless (← origin.getObjValAs? Nat "baseProgramNodes") = generated.maxProgramNodes do
      throw "saved base program budget differs from generation"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive function validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record (Json.mkObj [
        ("kind", toJson "primitive-generated"), ("seed", toJson seedText),
        ("finalSeed", toJson (toString generated.finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
        ("baseProgramNodes", toJson generated.maxProgramNodes), ("literalIndex", toJson literalIndex),
        ("inputIndex", toJson inputIndex), ("validationFuel", toJson validationFuel)])) do
      throw "generated primitive provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported primitive provenance is not canonical"
  else
    let parentProgram ← origin.getObjVal? "parentProgram"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent ← caseProgram (Json.mkObj [
      ("schema", toJson caseSchema), ("program", parentProgram), ("input", toJson parentText)])
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved primitive reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentProgram", parentProgram),
        ("parentInput", toJson parentText)] do
      throw "reduced primitive provenance is not canonical"
  let fresh := makeCase admitted.function admitted.input emitted origin fuel revision mask
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "primitive provenance contains unexpected fields"
  return fresh

/-- Sealing includes both full Core typing and a strictly smaller applied case. -/
structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (body : Wire.Expr) (input : Word) :
    Option (Reduction source) := do
  let function ← CheckedWordFunction.ofBody? body
  if !PrimitiveRenderer.supported function.body then none else do
    let candidate : CheckedInput := ⟨function, input⟩
    if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)
      then some ⟨candidate, strict⟩ else none

/-- Reuse capture-avoiding G0 shrinking under a dummy Word binder. Only candidates
retaining that binder are extracted; the input function is then independently
sealed. Input reduction is separate and cannot change the emitted source. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let wrapped : Wire.Program := {
    resultType := .word, dataDefinitions := [],
    body := .letE (.word Word.zero) source.function.body }
  let mut bodies : List Wire.Expr := [.word Word.zero, .var 0]
  if let some checked := CheckedWordProgram.ofProgram? wrapped then
    for reduced in shrink checked do
      if let .letE (.word value) body := reduced.body then
        if value = Word.zero then bodies := bodies ++ [body]
  let raw := bodies.map (fun body => (body, source.input)) ++
    [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (source.input.val / 2)].map
      (fun input => (source.function.body, input))
  let mut seen : List String := []
  let mut result := []
  for (body, input) in raw do
    if let some reduced := sealReduction source body input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.function reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Primitive
end
