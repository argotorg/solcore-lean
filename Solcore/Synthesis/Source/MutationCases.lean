import Solcore.Synthesis.Source.InputCases
import Solcore.Synthesis.Source.MutationEmitter

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
    (origin : Json) (fuel : Nat) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson LocalMutation.version),
    ("templateVersion", toJson templateVersion),
    ("generatorVersion", toJson generatorVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson function.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : CheckedLocalMutationDAG) (input : Word)
    (origin : Json) (fuel : Nat) : Except String Json := do
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
def generatedFunction (seed : Seed) (nodes : Nat) :
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
  for index in List.range count do
    let helperSeed := Seed.ofNat (seed.toNat + index)
    let generated ← (generate {seed := helperSeed, maxProgramNodes := scalarBudget}).mapError reprStr
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

def inputSensitive (function : CheckedLocalMutationDAG) (fuel : Nat) : Except String Unit := do
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all four boundary inputs returned the same Word"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (function, origin) ← generatedFunction seed nodes
        let emitted ← (emit function).mapError reprStr
        inputSensitive function fuel
        return (function, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "mutation-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (function, origin, emitted) =>
          for (input, inputIndex) in Input.boundaryInputs.zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push (makeCase function input emitted origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("generatorVersion", generatorVersion), ("profileVersion", profileVersion),
      ("functionVersion", LocalMutation.version), ("templateVersion", templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
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
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (function, expectedOrigin) ← generatedFunction (Seed.ofNat seed) nodes
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "helperCount", "helpers"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated helper provenance")
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved function DAG differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    unless Input.boundaryInputs[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive function validationFuel
  return makeCase admitted.function admitted.input emitted origin fuel

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
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push (← emitCase reduced.candidate.function reduced.candidate.input origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Mutation
