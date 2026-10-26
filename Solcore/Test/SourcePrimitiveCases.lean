import Solcore.Synthesis.Source.PrimitiveCases

/-! Runtime-input generation, original-Core observation, strict replay and
closed-lambda shrinking. Compiler agreement is checked separately by the real
Rust/Core/EVM integration runner. -/
set_option autoImplicit false

namespace Tests.SourcePrimitiveCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def rejected {α : Type} (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def function (body : Wire.Expr) : IO CheckedWordFunction :=
  match CheckedWordFunction.ofBody? body with
  | some checked => pure checked
  | none => throw (IO.userError "input-case fixture did not typecheck")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

private def field (value : Json) (key : String) : IO Json := get (value.getObjVal? key)
private def string (value : Json) (key : String) : IO String := get (value.getObjValAs? String key)
private def natural (value : Json) (key : String) : IO Nat := get (value.getObjValAs? Nat key)
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")

private def imported (body : Wire.Expr) (input : Word) : IO Json := do
  get (Primitive.emitCase (← function body) input (Json.mkObj [("kind", toJson "imported")]) 1000)

private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def primitiveChecks : IO Unit := do
  ensure (Primitive.appliedOverhead == 5 && Primitive.minimumProgramNodes == 8)
    "complete applied node overhead changed"
  ensure (Primitive.boundaryInputs.map (·.val) ==
    [0, 1, 2, 255, 256, Word.maximum.val, 2 ^ 255, 2 ^ 255 - 1])
    "primitive boundary bank changed"
  let maximum := Word.maximum.val
  let high := 2 ^ 255
  -- Independent small goldens exercise the actual Core evaluator; source never
  -- supplies expected results. Every saved edge case must also replay canonically.
  let fixtures : List (Wire.Expr × Nat × Nat) := [
    (.binary .wordDiv (.var 0) (word 0), maximum, 0),
    (.binary .wordMod (.var 0) (word 0), high, 0),
    (.binary .wordSdiv (.var 0) (word maximum), high, high),
    (.binary .wordSdiv (.var 0) (word 2), maximum - 6, maximum - 2),
    (.binary .wordSmod (.var 0) (word 2), maximum - 6, maximum),
    (.ifE (.binary .wordSgt (.var 0) (word 0)) (word 1) (word 0), high, 0),
    (.ifE (.binary .wordSgt (.var 0) (word 0)) (word 1) (word 0), high - 1, 1),
    (.binary .wordShl (word 1) (.var 0), 0, 1),
    (.binary .wordShl (word 1) (.var 0), 255, high),
    (.binary .wordShl (word 1) (.var 0), 256, 0),
    (.binary .wordShl (word 1) (.var 0), maximum, 0),
    (.binary .wordShr (word maximum) (.var 0), 0, maximum),
    (.binary .wordShr (word maximum) (.var 0), 255, 1),
    (.binary .wordShr (word maximum) (.var 0), 256, 0),
    (.binary .wordSar (word high) (.var 0), maximum, maximum),
    (.ternary .wordAddMod (.var 0) (word 1) (word maximum), maximum, 1),
    (.ternary .wordMulMod (.var 0) (word 2) (word maximum), high, 1),
    (.ternary .wordAddMod (.var 0) (word maximum) (word 0), maximum, 0),
    (.ternary .wordMulMod (.var 0) (word maximum) (word 0), maximum, 0),
    (.unary .wordClz (.var 0), 0, 256),
    (.unary .wordClz (.var 0), maximum, 0),
    (.unary .wordClz (.var 0), high, 0),
    (.unary .wordClz (.var 0), 1, 255),
    (.binary .wordByte (.var 0) (word 0x1234), 31, 0x34),
    (.binary .wordByte (.var 0) (word maximum), 32, 0),
    (.binary .wordByte (.var 0) (word maximum), maximum, 0),
    (.binary .wordSignExtend (word 0) (.var 0), 0x7f, 0x7f),
    (.binary .wordSignExtend (word 0) (.var 0), 0x80, maximum - 0x7f),
    (.binary .wordSignExtend (.var 0) (word high), 31, high),
    (.binary .wordSignExtend (.var 0) (word high), 32, high),
    (.binary .wordPow (.var 0) (word 0), 0, 1),
    (.binary .wordPow (.var 0) (word 0), maximum, 1),
    (.binary .wordPow (word 2) (.var 0), maximum, 0),
    (.binary .wordPow (word maximum) (.var 0), maximum, maximum)]
  for (body, input, expected) in fixtures do
    let saved ← imported body (Word.ofNatModulo input)
    ensure ((← field saved "directCore") == returned (Word.ofNatModulo expected))
      s!"primitive Core boundary differs at input {input}: {reprStr body}"
    ensure ((← get (Primitive.replayCase saved 1000)) == saved) "primitive boundary replay differs"
    ensure (← get (Primitive.caseProgram saved)).program.check "primitive boundary escaped Core typing"
  -- A scoped ternary branch uses both the let binder and original parameter.
  let nestedBody : Wire.Expr := .letE (.binary .wordAdd (.var 0) (word 1))
    (.ifE (.binary .wordSgt (.var 1) (word 0))
      (.ternary .wordAddMod (.var 0) (.var 1) (word 7))
      (.binary .wordByte (word 31) (.var 0)))
  for (input, expected) in [(0, 1), (1, 3), (maximum, 0), (high, 1)] do
    let saved ← imported nestedBody (Word.ofNatModulo input)
    ensure ((← field saved "directCore") == returned (Word.ofNatModulo expected))
      "scoped primitive let/branch altered binder meanings"
    let reductions ← get (Primitive.shrinkCases saved 20 1000)
    for row in (← cases reductions) do
      let _ ← get (Primitive.replayCase row 1000)
      ensure (← get (Primitive.caseProgram row)).program.check "primitive shrink escaped Core typing"

private def inputChecks : IO Unit := do
  for input in Primitive.boundaryInputs do
    ensure ((← get (Primitive.inputWord (toString input.val))) == input) "boundary input round trip failed"
    let encoded := Primitive.calldata input
    ensure (encoded.length == 74 && encoded.startsWith Primitive.selector) "ABI input width/selector changed"
  ensure (Primitive.calldata Word.zero == "0xa444f5e9" ++ String.ofList (List.replicate 64 '0'))
    "zero input ABI encoding changed"
  ensure (Primitive.calldata Word.maximum == "0xa444f5e9" ++ String.ofList (List.replicate 64 'f'))
    "maximum input ABI encoding changed"
  ensure (Primitive.calldata (Word.ofNatModulo (2 ^ 255)) ==
    "0xa444f5e98" ++ String.ofList (List.replicate 63 '0')) "high-bit input ABI encoding changed"
  for invalid in ["", "00", "01", "-1", "+1", "0x1", " 1", toString (2 ^ 256 : Nat)] do
    rejected (Primitive.inputWord invalid) "noncanonical or overflowing input accepted"
  let identity ← function (.var 0)
  let mut source : Option String := none
  for input in Primitive.boundaryInputs do
    let saved ← get (Primitive.emitCase identity input (Json.mkObj [("kind", toJson "imported")]) 1000)
    let emittedSource ← string saved "source"
    if let some prior := source then
      ensure (prior == emittedSource) "source text depends on runtime input"
    source := some emittedSource
    let checked ← get (Primitive.caseProgram saved)
    ensure (checked.program.check && checked.input == input) "applied original Core did not typecheck"
    ensure ((← field saved "directCore") == returned input) "identity did not use its runtime input"
    ensure ((← get (Primitive.replayCase saved 1000)) == saved) "imported case did not replay exactly"
    let forged := saved.setObjVal! "directCore" (returned (Word.ofNatModulo 17))
    ensure ((← get (Primitive.replayCase forged 1000)) == saved) "saved expected result was trusted"
    let exhausted ← get (Primitive.replayCase saved 0)
    ensure ((← string (← field exhausted "directCore") "status") == "out-of-fuel")
      "zero fuel was treated as a completed observation"
  let branch ← function (.ifE (.binary .wordGt (.var 0) (word 1)) (word 7) (word 0))
  ensure (Primitive.observe branch Word.zero 1000 == Primitive.observe branch (Word.ofNatModulo 1) 1000)
    "branch fixture should agree on zero and one"
  let _ ← get (Primitive.inputSensitive branch 1000)
  rejected (Primitive.inputSensitive (← function (word 7)) 1000) "constant generation candidate accepted"
  rejected (Primitive.inputSensitive identity 0) "fuel exhaustion passed the dynamic-input filter"
  let constant ← imported (word 7) Word.maximum
  ensure ((← field constant "directCore") == returned (Word.ofNatModulo 7))
    "imported constant functions must remain valid for shrinking"
  let oversized := (List.range 254).foldl (fun body _ => .binary .wordAdd body (word 0))
    (.var 0 : Wire.Expr)
  rejected (Primitive.emitCase (← function oversized) Word.zero
    (Json.mkObj [("kind", toJson "imported")]) 1000) "oversized applied function escaped case limit"

private def generationChecks : IO Json := do
  let corpus := Primitive.generateCases (Seed.ofNat 0) 24 17 64 1000
  ensure (corpus == Primitive.generateCases (Seed.ofNat 0) 24 17 64 1000)
    "input generation is nondeterministic"
  ensure ((← string corpus "status") == "complete") "bounded input corpus did not complete"
  let rows ← cases corpus
  let attempted ← natural corpus "attempted"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  ensure (rows.size == 17 && attempted ≤ 64 && attempted == 3 + excluded.size)
    "function attempts and individual case counts were confused"
  for index in List.range rows.size do
    let saved := rows[index]!
    let checked ← get (Primitive.caseProgram saved)
    let provenance ← field saved "provenance"
    let origin ← field provenance "origin"
    ensure ((← natural origin "inputIndex") == index % 8 &&
      some checked.input == Primitive.boundaryInputs[index % 8]?) "boundary order changed"
    ensure ((← string provenance "profileVersion") == Primitive.profileVersion &&
      (← string provenance "generatorVersion") == Primitive.generatorVersion &&
      (← string provenance "baseGeneratorVersion") == generatorVersion &&
      (← string provenance "boundaryVersion") == Primitive.boundaryVersion) "profile version changed G0"
    ensure (checked.program.check && Wire.programNodes checked.program ≤ 24)
      "generated applied case escaped checker/node bound"
    ensure ((← get (Primitive.replayCase saved 1000)) == saved) "generated input replay differs"
    let suspended ← get (Primitive.replayCase saved 0)
    ensure ((← string (← field suspended "directCore") "status") == "out-of-fuel")
      "generated replay confused its new observation budget with its validation budget"
    if index % 8 != 0 then
      ensure ((← string saved "source") == (← string rows[index - index % 8]! "source"))
        "one function's boundary cases emitted different source"
  let truncated := Primitive.generateCases (Seed.ofNat 0) 8 3 1 1000
  ensure ((← cases truncated).size == 3 && (← natural truncated "attempted") == 1 &&
    (← string truncated "status") == "complete") "case count did not truncate the input group"
  let exhausted := Primitive.generateCases (Seed.ofNat 0) 8 9 1 1000
  ensure ((← cases exhausted).size == 8 && (← string exhausted "status") == "generation-exhausted")
    "attempt limit counted input cases instead of functions"
  for corpus in [Primitive.generateCases (Seed.ofNat 0) 7 1 3 1000,
      Primitive.generateCases (Seed.ofNat 0) 8 1 3 0] do
    ensure ((← cases corpus).isEmpty && (← natural corpus "attempted") == 3 &&
      (← string corpus "status") == "generation-exhausted") "failed generation lost its bound"
    ensure ((← get (corpus.getObjValAs? (Array Json) "excluded")).size == 3)
      "generation failures were not recorded"
  ensure ((← natural (Primitive.generateCases (Seed.ofNat 0) 8 0 100 1000) "attempted") == 0)
    "zero case request consumed attempts"
  ensure ((← cases (Primitive.generateCases (Seed.ofNat 0) 8 1 0 1000)).isEmpty)
    "zero attempt limit ignored"
  let resources ← get ((Primitive.generateCases (Seed.ofNat 0) 8 1 1 0).getObjValAs? (Array Json) "excluded")
  ensure ((← string resources[0]! "category") == "inconclusive-resource" &&
    (← string resources[0]! "code") == "boundary-out-of-fuel")
    "generation fuel exhaustion lost its resource classification"
  for budget in [8, 96, 512] do
    let bounded := Primitive.generateCases (Seed.ofNat 0) budget 8 64 1000
    ensure ((← string bounded "status") == "complete") "supported budget did not yield a function"
    for row in (← cases bounded) do
      let admitted ← get (Primitive.caseProgram row)
      ensure (Wire.programNodes admitted.program ≤ budget)
        "generator counted only its scalar body instead of the applied function"
      let _ ← get (Primitive.replayCase row 1000)
  let invalid := Primitive.generateCases (Seed.ofNat 0) 513 1 1 1000
  ensure ((← cases invalid).isEmpty && (← natural invalid "attempted") == 1)
    "oversized generation request accepted"
  return corpus

private def tamperingChecks (corpus : Json) : IO Unit := do
  let saved := (← cases corpus)[0]!
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["profileVersion", "functionVersion", "abstractionVersion",
      "generatorVersion", "baseGeneratorVersion", "boundaryVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Primitive.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 1000) "tampered version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "0"),
      ("literalIndex", toJson (999 : Nat)), ("inputIndex", toJson (9 : Nat)),
      ("maxProgramNodes", toJson (513 : Nat)), ("baseProgramNodes", toJson (512 : Nat)), ("validationFuel", toJson (10000001 : Nat)),
      ("kind", toJson "unknown")] do
    rejected (Primitive.replayCase (withOrigin (origin.setObjVal! name value)) 1000)
      s!"tampered {name} accepted"
  rejected (Primitive.replayCase (saved.setObjVal! "input" (toJson "1")) 1000)
    "input/program disagreement accepted"
  rejected (Primitive.replayCase (saved.setObjVal! "source" (toJson "forged")) 1000)
    "stale source accepted"
  let contract ← field saved "contract"
  for (name, value) in [("calldata", toJson "0xa444f5e9"),
      ("signature", toJson "run()"), ("runtimePath", toJson ["Other"])] do
    rejected (Primitive.replayCase (saved.setObjVal! "contract" (contract.setObjVal! name value)) 1000)
      "tampered ABI metadata accepted"
  rejected (Primitive.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "features" (toJson ([] : List String)))) 1000) "tampered features accepted"
  let identity ← function (.var 0)
  let badProgram := Wire.encodeProgram identity.program
  rejected (Primitive.caseProgram (saved.setObjVal! "program" badProgram))
    "bare lambda accepted as an applied input case"
  let invalidFunction : Wire.Program := {
    resultType := .function .word .word, dataDefinitions := [], body := .lambda .word .word (.var 1) }
  rejected (Primitive.checkedFunction (Wire.encodeProgram invalidFunction)) "unbound parameter escaped sealing"
  rejected (Primitive.replayCase (withOrigin (origin.setObjVal! "unexpected" (toJson true))) 1000)
    "extra generated provenance accepted"
  rejected (Primitive.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "unexpected" (toJson true))) 1000) "extra profile provenance accepted"
  let constant ← imported (word 7) Word.zero
  let constantProvenance ← field constant "provenance"
  rejected (Primitive.replayCase (constant.setObjVal! "provenance"
    (constantProvenance.setObjVal! "origin" (Json.mkObj [
      ("kind", toJson "imported"), ("seed", toJson "0")]))) 1000)
    "extra imported provenance accepted"
  let generated ← get ((generate {
    seed := Seed.ofNat 0,
    maxProgramNodes := 24 - Primitive.appliedOverhead}).mapError reprStr)
  let some constantFunction := CheckedWordFunction.fromProgram? generated.checkedProgram 0 |
    throw (IO.userError "constant generation fixture changed")
  let forgedOrigin := Json.mkObj [("kind", toJson "primitive-generated"),
    ("seed", toJson "0"), ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson (24 : Nat)), ("baseProgramNodes", toJson generated.maxProgramNodes),
    ("literalIndex", toJson (0 : Nat)), ("inputIndex", toJson (0 : Nat)),
    ("validationFuel", toJson (1000 : Nat))]
  let forged ← get (Primitive.emitCase constantFunction Word.zero forgedOrigin 1000)
  rejected (Primitive.replayCase forged 1000)
    "replay skipped the generated boundary variation requirement"

private def shrinkChecks : IO Unit := do
  let body := Wire.Expr.letE (.binary .wordAdd (.var 0) (word 17))
    (.ifE (.binary .wordGt (.var 0) (word 1))
      (.binary .wordXor (.var 0) (.var 1)) (word 99))
  let saved ← imported body Word.maximum
  let source ← get (Primitive.caseProgram saved)
  let shrunk ← get (Primitive.shrinkCases saved 100 1000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Primitive.shrinkCases saved 100 1000)))
    "input shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut changedInput := false
  let mut changedBody := false
  let mut constant := false
  for row in rows do
    let reduced ← get (Primitive.caseProgram row)
    ensure (reduced.program.check && Wire.programNodes reduced.program ≤ 512)
      "shrink escaped the applied lambda/checker/size boundary"
    ensure ((complexity reduced.program.body).isStrictlySmaller (complexity source.program.body))
      "input reduction was not strictly smaller"
    let key := (Wire.encodeProgram reduced.program).compress
    ensure (!seen.contains key) "input shrink produced duplicate programs"
    seen := key :: seen
    ensure ((← get (Primitive.replayCase row 1000)) == row) "shrunk input did not replay"
    let emitted ← get ((Primitive.emit reduced.function).mapError reprStr)
    ensure ((← string row "source") == emitted.source) "shrink retained stale emitted source"
    changedInput := changedInput || reduced.input != source.input
    changedBody := changedBody || Wire.encodeExpr reduced.function.body != Wire.encodeExpr source.function.body
    constant := constant || Wire.encodeExpr reduced.function.body == Wire.encodeExpr (word 0)
  ensure (changedInput && changedBody && constant) "shrinking missed input/body/constant candidates"
  ensure ((← cases (← get (Primitive.shrinkCases saved 2 1000))) == rows.extract 0 2)
    "input shrink limit changed ordering"
  ensure ((← cases (← get (Primitive.shrinkCases saved 0 1000))).isEmpty) "zero shrink limit ignored"
  rejected (Primitive.shrinkCases (saved.setObjVal! "source" (toJson "stale")) 100 1000)
    "shrinker accepted a stale source case"
  let row := rows[0]!
  let provenance ← field row "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun value => row.setObjVal! "provenance" (provenance.setObjVal! "origin" value)
  rejected (Primitive.replayCase (withOrigin (origin.setObjVal! "parentProgram"
    (← field row "program"))) 1000) "nonstrict or input-mismatched parent accepted"
  rejected (Primitive.replayCase (withOrigin (origin.setObjVal! "parentInput" (toJson "00"))) 1000)
    "noncanonical parent input accepted"
  rejected (Primitive.replayCase (withOrigin (origin.setObjVal! "unexpected" (toJson true))) 1000)
    "extra reduced provenance accepted"
  let selfOrigin := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", ← field row "program"), ("parentInput", ← field row "input")]
  rejected (Primitive.replayCase (withOrigin selfOrigin) 1000) "self-parent reduction accepted"


def testSourcePrimitiveCases : IO Unit := do
  primitiveChecks
  inputChecks
  let corpus ← generationChecks
  tamperingChecks corpus
  shrinkChecks

end Tests.SourcePrimitiveCases
