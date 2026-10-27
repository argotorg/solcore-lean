import Solcore.Synthesis.Source.InputCases
import Solcore.Synthesis.Source.AggregateEmitter

/-! Replayable aggregate cases retain structural pairs, sums, payload scopes and
private Word cells in the independent Core oracle. The older profiles and their
replay rules remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Aggregate
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-aggregate-case.v1"
def profileVersion : String := "runtime-aggregates-v2/template-seed-v1"
def templateVersion : String := "word-aggregate-templates-v1"

structure CheckedInput where
  function : Aggregates.CheckedDAG
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : Aggregates.CheckedDAG) (input : Word) (fuel : Nat) : Json :=
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

def makeCase (function : Aggregates.CheckedDAG) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Aggregates.version),
    ("templateVersion", toJson templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson function.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : Aggregates.CheckedDAG) (input : Word)
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

def checkedFunction (json : Json) : Except String Aggregates.CheckedDAG := do
  let some function := Aggregates.CheckedDAG.ofProgram? (← decodeProgram json) |
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
      let some function := Aggregates.CheckedDAG.ofProgram? {
        resultType := .function .word .word, dataDefinitions := [], body := functionBody } |
        throw "applied function is outside the checked function DAG profile"
      return ⟨function, input⟩
  | _ => throw "function case program is not a closed Word function DAG application"

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def load (index : Nat) : Wire.Expr := .loadCell (.var index)

/-- Both tags are reached by the four boundary inputs. The payloads are
already-evaluated Word expressions; the surrounding renderer must preserve
that order when creating the aggregate. -/
private def chooseSum (input left right : Wire.Expr) : Wire.Expr :=
  .ifE (.binary .wordGt input (word (2 ^ 255 - 1)))
    (.inRight .word right) (.inLeft .word left)

/-- A closed G0 subtree remains closed under all local and payload binders.
The templates combine aggregates with the same private Word-cell discipline as
the mutation profile. Their result is always a Word. -/
def template (pattern : Nat) (scalar : Wire.Expr) : Wire.Expr :=
  .letE scalar (.letE (.newCell .word (.var 1)) (
    if pattern = 0 then
      -- Pair construction snapshots its left load before the right store.
      .letE (.pair (load 0) (.letE (.storeCell (.var 0) (.var 1)) (load 1)))
        (.binary .wordAdd (.first (.var 0)) (.second (.var 0)))
    else if pattern = 1 then
      .letE (chooseSum (.var 2) (load 0) (load 0))
        (.caseE (.var 0)
          (.letE (.storeCell (.var 2) (.binary .wordAdd (.var 0) (.var 3))) (load 3))
          (.letE (.storeCell (.var 2) (.binary .wordXor (.var 0) (.var 3))) (load 3)))
    else if pattern = 2 then
      -- Case results use product and sum joins before a final Word projection.
      .letE (.pair (load 0) (.var 1))
        (.letE (chooseSum (.first (.var 0)) (.first (.var 0)) (.second (.var 0)))
          (.letE (.caseE (.var 0)
            (.pair (.var 0) (.letE (.storeCell (.var 3) (.var 4)) (load 4)))
            (.pair (.first (.var 2)) (.binary .wordAdd (.var 0) (.var 4))))
            (.letE (.caseE (.var 1)
              (.inLeft .word (.binary .wordAdd (.first (.var 1)) (.second (.var 1))))
              (.inRight .word (.binary .wordAdd (.first (.var 1)) (.second (.var 1)))))
              (.caseE (.var 0) (.var 0) (.var 0)))))
    else
      -- Nested cases add two payload binders; the saved Word and Unit bindings
      -- remain in the cell index even when source Unit values need no name.
      let inner := .letE (.var 0)
        (.letE (.storeCell (.var 4) (.binary .wordAdd (.var 0) (.var 2))) (load 5))
      .letE (chooseSum (.var 2) (load 0) (load 0))
        (.caseE (.var 0)
          (.caseE (.inLeft .word (.binary .wordAdd (.var 0) (.var 3))) inner inner)
          (.caseE (.inRight .word (.binary .wordXor (.var 0) (.var 3))) inner inner))))

private def helperBody (index pattern : Nat) (scalar : Wire.Expr) : Wire.Expr :=
  let body := template pattern scalar
  if index = 0 then body else .apply (.var 1) body

private def patternFor (seed : Seed) : Nat := seed.toNat / 3 % 4

private def appliedNodes (helpers : List Wire.Expr) : Nat := Wire.programNodes {
  resultType := .word, dataDefinitions := [],
  body := .apply (functionDAGExpression helpers (.apply (.var 1) (.var 0))) (word 0) }

/-- Budget from the actual full applied skeleton, with one scalar placeholder
per helper. The final measured program is checked again after generation. -/
def generatedFunction (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (Aggregates.CheckedDAG × Json) := do
  let count := 1 + seed.toNat % 3
  let skeleton := (List.range count).map fun index =>
    let helperSeed := Seed.ofNat (seed.toNat + index)
    helperBody index (patternFor helperSeed) (word 0)
  let skeletonNodes := appliedNodes skeleton
  unless nodes ≤ 512 && skeletonNodes ≤ nodes do
    throw "node budget is too small for the selected aggregate template or exceeds 512"
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
    let body := helperBody index pattern generated.program.body
    helpers := helpers ++ [body]
    metadata := metadata.push (Json.mkObj [
      ("index", toJson index), ("seed", toJson (toString helperSeed.toNat)),
      ("finalSeed", toJson (toString generated.finalSeed.toNat)),
      ("maxProgramNodes", toJson scalarBudget), ("template", toJson pattern)])
    finalSeed := generated.finalSeed
  let some function := Aggregates.CheckedDAG.ofParts? helpers (.apply (.var 1) (.var 0)) |
    throw "generated helper chain did not pass the full Core checker"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ nodes do
    throw "applied helper chain exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "aggregate-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", toJson (toString finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
    ("helperCount", toJson count), ("helpers", .arr metadata)]
  return (function, origin)

def boundaryResults (function : Aggregates.CheckedDAG) (fuel : Nat) : Except String (List Word) :=
  Input.boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (function : Aggregates.CheckedDAG) (fuel : Nat)
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
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "aggregate-profile"),
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
      ("functionVersion", Aggregates.version), ("templateVersion", templateVersion),
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
  unless kind = "aggregate-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported function case origin"
  if kind = "aggregate-generated" then
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

/-- Case payload markers are distinct from ordinary Word let binders. This
prevents a reduction from silently trading a payload scope for a local binder. -/
inductive Binding where
  | local (kind : Aggregates.Local)
  | leftPayload
  | rightPayload
  deriving DecidableEq, BEq, Repr

/-- Binder kinds in expression preorder, including both case payload scopes. -/
def bindingKinds (locals : List Aggregates.Local) (prior : Nat) : Wire.Expr → List Binding
  | .letE initializer body =>
      match Aggregates.initializerKind? locals prior initializer with
      | none => []
      | some kind => bindingKinds locals prior initializer ++ [.local kind] ++
          bindingKinds (kind :: locals) prior body
  | .caseE scrutinee left right =>
      bindingKinds locals prior scrutinee ++ [.leftPayload] ++
        bindingKinds (.word :: locals) prior left ++ [.rightPayload] ++
        bindingKinds (.word :: locals) prior right
  | .ifE condition yes no | .ternary _ condition yes no =>
      bindingKinds locals prior condition ++ bindingKinds locals prior yes ++ bindingKinds locals prior no
  | .binary _ left right | .pair left right =>
      bindingKinds locals prior left ++ bindingKinds locals prior right
  | .unary _ operand | .newCell _ operand | .first operand | .second operand |
      .inLeft _ operand | .inRight _ operand => bindingKinds locals prior operand
  | .apply _ argument | .storeCell _ argument => bindingKinds locals prior argument
  | _ => []

def bindingInventory (function : Aggregates.CheckedDAG) : List Binding :=
  (function.helpers.zipIdx.flatMap fun (body, index) => bindingKinds [.word] index body) ++
    bindingKinds [.word] function.helpers.length function.entry

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.function.helpers.length = source.function.helpers.length
  sameBindings : bindingInventory candidate.function = bindingInventory source.function
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (helpers : List Wire.Expr)
    (entry : Wire.Expr) (input : Word) : Option (Reduction source) := do
  let function ← Aggregates.CheckedDAG.ofParts? helpers entry
  let candidate : CheckedInput := ⟨function, input⟩
  if count : candidate.function.helpers.length = source.function.helpers.length then
    if bindings : bindingInventory candidate.function = bindingInventory source.function then
      if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)
        then some ⟨candidate, count, bindings, strict⟩ else none
    else none
  else none

/-- Rewrites retain every typed let and both case payload scopes. A case
branch is never extracted. Whole-DAG checking and the distinct binder inventory
are checked again before exposing a strictly smaller candidate. -/
private def bodyReductions (locals : List Aggregates.Local) (prior : Nat)
    (expression : Wire.Expr) : List Wire.Expr :=
  let canonical := if (bindingKinds locals prior expression).isEmpty then
      match Aggregates.initializerKind? locals prior expression with
      | some .word => [word 0]
      | some .bool => [.bool false]
      | some .unit => [.unit]
      | some .wordPair => [.pair (word 0) (word 0)]
      | some .wordSum => [.inLeft .word (word 0)]
      | _ => []
    else []
  canonical ++ match expression with
  | .letE initializer body =>
      match Aggregates.initializerKind? locals prior initializer with
      | none => []
      | some kind =>
          ((bodyReductions locals prior initializer).filter fun changed =>
            Aggregates.initializerKind? locals prior changed == some kind).map
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
  | .pair left right =>
      (bodyReductions locals prior left).map (fun changed => .pair changed right) ++
      (bodyReductions locals prior right).map (.pair left)
  | .first operand => (bodyReductions locals prior operand).map .first
  | .second operand => (bodyReductions locals prior operand).map .second
  | .inLeft type payload => (bodyReductions locals prior payload).map (.inLeft type)
  | .inRight type payload => (bodyReductions locals prior payload).map (.inRight type)
  | .caseE scrutinee left right =>
      (bodyReductions locals prior scrutinee).map (fun changed => .caseE changed left right) ++
      (bodyReductions (.word :: locals) prior left).map (fun changed => .caseE scrutinee changed right) ++
      (bodyReductions (.word :: locals) prior right).map (.caseE scrutinee left)
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

end Solcore.Synthesis.Source.Aggregate
