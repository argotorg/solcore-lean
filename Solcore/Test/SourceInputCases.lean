import Solcore.Synthesis.Source.InputCases

/-! Runtime-input generation, original-Core observation, strict replay and
closed-lambda shrinking. Compiler agreement is checked separately by the real
Rust/Core/EVM integration runner. -/
set_option autoImplicit false

namespace Tests.SourceInputCases
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
  get (Input.emitCase (← function body) input (Json.mkObj [("kind", toJson "imported")]) 1000)

private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def inputChecks : IO Unit := do
  for input in Input.boundaryInputs do
    ensure ((← get (Input.inputWord (toString input.val))) == input) "boundary input round trip failed"
    let encoded := Input.calldata input
    ensure (encoded.length == 74 && encoded.startsWith Input.selector) "ABI input width/selector changed"
  ensure (Input.calldata Word.zero == "0xa444f5e9" ++ String.ofList (List.replicate 64 '0'))
    "zero input ABI encoding changed"
  ensure (Input.calldata Word.maximum == "0xa444f5e9" ++ String.ofList (List.replicate 64 'f'))
    "maximum input ABI encoding changed"
  ensure (Input.calldata (Word.ofNatModulo (2 ^ 255)) ==
    "0xa444f5e98" ++ String.ofList (List.replicate 63 '0')) "high-bit input ABI encoding changed"
  for invalid in ["", "00", "01", "-1", "+1", "0x1", " 1", toString (2 ^ 256 : Nat)] do
    rejected (Input.inputWord invalid) "noncanonical or overflowing input accepted"
  let identity ← function (.var 0)
  let mut source : Option String := none
  for input in Input.boundaryInputs do
    let saved ← get (Input.emitCase identity input (Json.mkObj [("kind", toJson "imported")]) 1000)
    let emittedSource ← string saved "source"
    if let some prior := source then
      ensure (prior == emittedSource) "source text depends on runtime input"
    source := some emittedSource
    let checked ← get (Input.caseProgram saved)
    ensure (checked.program.check && checked.input == input) "applied original Core did not typecheck"
    ensure ((← field saved "directCore") == returned input) "identity did not use its runtime input"
    ensure ((← get (Input.replayCase saved 1000)) == saved) "imported case did not replay exactly"
    let forged := saved.setObjVal! "directCore" (returned (Word.ofNatModulo 17))
    ensure ((← get (Input.replayCase forged 1000)) == saved) "saved expected result was trusted"
    let exhausted ← get (Input.replayCase saved 0)
    ensure ((← string (← field exhausted "directCore") "status") == "out-of-fuel")
      "zero fuel was treated as a completed observation"
  let branch ← function (.ifE (.binary .wordGt (.var 0) (word 1)) (word 7) (word 0))
  ensure (Input.observe branch Word.zero 1000 == Input.observe branch (Word.ofNatModulo 1) 1000)
    "branch fixture should agree on zero and one"
  let _ ← get (Input.inputSensitive branch 1000)
  rejected (Input.inputSensitive (← function (word 7)) 1000) "constant generation candidate accepted"
  rejected (Input.inputSensitive identity 0) "fuel exhaustion passed the dynamic-input filter"
  let constant ← imported (word 7) Word.maximum
  ensure ((← field constant "directCore") == returned (Word.ofNatModulo 7))
    "imported constant functions must remain valid for shrinking"
  let oversized := (List.range 254).foldl (fun body _ => .binary .wordAdd body (word 0))
    (.var 0 : Wire.Expr)
  rejected (Input.emitCase (← function oversized) Word.zero
    (Json.mkObj [("kind", toJson "imported")]) 1000) "oversized applied function escaped case limit"

private def generationChecks : IO Json := do
  let corpus := Input.generateCases (Seed.ofNat 0) 24 12 64 1000
  ensure (corpus == Input.generateCases (Seed.ofNat 0) 24 12 64 1000)
    "input generation is nondeterministic"
  ensure ((← string corpus "status") == "complete") "bounded input corpus did not complete"
  let rows ← cases corpus
  let attempted ← natural corpus "attempted"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  ensure (rows.size == 12 && attempted ≤ 64 && attempted == 3 + excluded.size)
    "function attempts and individual case counts were confused"
  for index in List.range rows.size do
    let saved := rows[index]!
    let checked ← get (Input.caseProgram saved)
    let provenance ← field saved "provenance"
    let origin ← field provenance "origin"
    ensure ((← natural origin "inputIndex") == index % 4 &&
      some checked.input == Input.boundaryInputs[index % 4]?) "boundary order changed"
    ensure ((← string provenance "profileVersion") == Input.profileVersion &&
      (← string provenance "generatorVersion") == generatorVersion) "profile version changed G0"
    ensure (checked.program.check && Wire.programNodes checked.program ≤ 512)
      "generated applied case escaped checker/node bound"
    ensure ((← get (Input.replayCase saved 1000)) == saved) "generated input replay differs"
    let suspended ← get (Input.replayCase saved 0)
    ensure ((← string (← field suspended "directCore") "status") == "out-of-fuel")
      "generated replay confused its new observation budget with its validation budget"
    if index % 4 != 0 then
      ensure ((← string saved "source") == (← string rows[index - index % 4]! "source"))
        "one function's boundary cases emitted different source"
  let truncated := Input.generateCases (Seed.ofNat 0) 3 3 1 1000
  ensure ((← cases truncated).size == 3 && (← natural truncated "attempted") == 1 &&
    (← string truncated "status") == "complete") "case count did not truncate the input group"
  let exhausted := Input.generateCases (Seed.ofNat 0) 3 5 1 1000
  ensure ((← cases exhausted).size == 4 && (← string exhausted "status") == "generation-exhausted")
    "attempt limit counted input cases instead of functions"
  for corpus in [Input.generateCases (Seed.ofNat 0) 2 1 3 1000,
      Input.generateCases (Seed.ofNat 0) 3 1 3 0] do
    ensure ((← cases corpus).isEmpty && (← natural corpus "attempted") == 3 &&
      (← string corpus "status") == "generation-exhausted") "failed generation lost its bound"
    ensure ((← get (corpus.getObjValAs? (Array Json) "excluded")).size == 3)
      "generation failures were not recorded"
  ensure ((← natural (Input.generateCases (Seed.ofNat 0) 3 0 100 1000) "attempted") == 0)
    "zero case request consumed attempts"
  ensure ((← cases (Input.generateCases (Seed.ofNat 0) 3 1 0 1000)).isEmpty)
    "zero attempt limit ignored"
  let resources ← get ((Input.generateCases (Seed.ofNat 0) 3 1 1 0).getObjValAs? (Array Json) "excluded")
  ensure ((← string resources[0]! "category") == "inconclusive-resource" &&
    (← string resources[0]! "code") == "boundary-out-of-fuel")
    "generation fuel exhaustion lost its resource classification"
  return corpus

private def tamperingChecks (corpus : Json) : IO Unit := do
  let saved := (← cases corpus)[0]!
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["profileVersion", "functionVersion", "abstractionVersion",
      "generatorVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Input.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 1000) "tampered version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "0"),
      ("literalIndex", toJson (999 : Nat)), ("inputIndex", toJson (9 : Nat)),
      ("maxProgramNodes", toJson (513 : Nat)), ("validationFuel", toJson (10000001 : Nat)),
      ("kind", toJson "unknown")] do
    rejected (Input.replayCase (withOrigin (origin.setObjVal! name value)) 1000)
      s!"tampered {name} accepted"
  rejected (Input.replayCase (saved.setObjVal! "input" (toJson "1")) 1000)
    "input/program disagreement accepted"
  rejected (Input.replayCase (saved.setObjVal! "source" (toJson "forged")) 1000)
    "stale source accepted"
  let contract ← field saved "contract"
  for (name, value) in [("calldata", toJson "0xa444f5e9"),
      ("signature", toJson "run()"), ("runtimePath", toJson ["Other"])] do
    rejected (Input.replayCase (saved.setObjVal! "contract" (contract.setObjVal! name value)) 1000)
      "tampered ABI metadata accepted"
  rejected (Input.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "features" (toJson ([] : List String)))) 1000) "tampered features accepted"
  let identity ← function (.var 0)
  let badProgram := Wire.encodeProgram identity.program
  rejected (Input.caseProgram (saved.setObjVal! "program" badProgram))
    "bare lambda accepted as an applied input case"
  let invalidFunction : Wire.Program := {
    resultType := .function .word .word, dataDefinitions := [], body := .lambda .word .word (.var 1) }
  rejected (Input.checkedFunction (Wire.encodeProgram invalidFunction)) "unbound parameter escaped sealing"
  let generated ← get ((generate {seed := Seed.ofNat 1, maxProgramNodes := 24}).mapError reprStr)
  let literalIndex := 1 % literalCount generated.program.body
  let some constant := CheckedWordFunction.fromProgram? generated.checkedProgram literalIndex |
    throw (IO.userError "constant boundary seed fixture changed")
  let forgedOrigin := Json.mkObj [("kind", toJson "input-generated"),
    ("seed", toJson "1"), ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson (24 : Nat)), ("literalIndex", toJson literalIndex),
    ("inputIndex", toJson (0 : Nat)), ("validationFuel", toJson (1000 : Nat))]
  let forged ← get (Input.emitCase constant Word.zero forgedOrigin 1000)
  rejected (Input.replayCase forged 1000)
    "replay accepted generated provenance for a function rejected by the input-sensitivity filter"

private def shrinkChecks : IO Unit := do
  let body := Wire.Expr.letE (.binary .wordAdd (.var 0) (word 17))
    (.ifE (.binary .wordGt (.var 0) (word 1))
      (.binary .wordXor (.var 0) (.var 1)) (word 99))
  let saved ← imported body Word.maximum
  let source ← get (Input.caseProgram saved)
  let shrunk ← get (Input.shrinkCases saved 100 1000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Input.shrinkCases saved 100 1000)))
    "input shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut changedInput := false
  let mut changedBody := false
  let mut constant := false
  for row in rows do
    let reduced ← get (Input.caseProgram row)
    ensure (reduced.program.check && Wire.programNodes reduced.program ≤ 512)
      "shrink escaped the applied lambda/checker/size boundary"
    ensure ((complexity reduced.program.body).isStrictlySmaller (complexity source.program.body))
      "input reduction was not strictly smaller"
    let key := (Wire.encodeProgram reduced.program).compress
    ensure (!seen.contains key) "input shrink produced duplicate programs"
    seen := key :: seen
    ensure ((← get (Input.replayCase row 1000)) == row) "shrunk input did not replay"
    let emitted ← get ((Input.emit reduced.function).mapError reprStr)
    ensure ((← string row "source") == emitted.source) "shrink retained stale emitted source"
    changedInput := changedInput || reduced.input != source.input
    changedBody := changedBody || Wire.encodeExpr reduced.function.body != Wire.encodeExpr source.function.body
    constant := constant || Wire.encodeExpr reduced.function.body == Wire.encodeExpr (word 0)
  ensure (changedInput && changedBody && constant) "shrinking missed input/body/constant candidates"
  ensure ((← cases (← get (Input.shrinkCases saved 2 1000))) == rows.extract 0 2)
    "input shrink limit changed ordering"
  ensure ((← cases (← get (Input.shrinkCases saved 0 1000))).isEmpty) "zero shrink limit ignored"
  rejected (Input.shrinkCases (saved.setObjVal! "source" (toJson "stale")) 100 1000)
    "shrinker accepted a stale source case"

def testSourceInputCases : IO Unit := do
  inputChecks
  let corpus ← generationChecks
  tamperingChecks corpus
  shrinkChecks

end Tests.SourceInputCases
