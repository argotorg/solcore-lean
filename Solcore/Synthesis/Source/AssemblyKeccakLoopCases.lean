import Solcore.Synthesis.Source.KeccakLoopCases
import Solcore.Synthesis.Source.AssemblyKeccakLoopEmitter

/-! An inline Yul Keccak-loop case retains the Keccak-loop profile's checked
plan, transactions and original Core contract, and the form that renders them.
Generation repeats that profile's steps, so its Core reference, observation and
exclusions are unchanged, and draws the form from a hash of the seed.
Reductions are that profile's, each in the parent case's form. Saved outputs
are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyKeccakLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Source.AssemblyStorage (Form)
open Solcore.Synthesis.Stateful.KeccakLoopExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-assembly-keccak-loop-case.v1"
def planSchema : String := "solcore-lean.assembly-keccak-loop-plan.v1"
def profileVersion : String := "stateful-assembly-keccak-loops-v1/form-seed-v1"
def corpusSchema : String := "solcore-lean.semantic-assembly-keccak-loop-corpus.v1"

/-- A checked Keccak-loop scenario and the form that renders it. -/
structure CheckedScenario where
  loop : KeccakLoop.CheckedScenario
  form : Form

def CheckedScenario.plan (scenario : CheckedScenario) : Solcore.Synthesis.Core.KeccakLoop.CheckedPlan :=
  scenario.loop.plan

def CheckedScenario.transactions (scenario : CheckedScenario) : List Transaction := scenario.loop.transactions

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.loop.program

def planJson (plan : Solcore.Synthesis.Core.KeccakLoop.CheckedPlan) (form : Form) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("mask", toJson plan.mask), ("keyMask", toJson plan.keyMask), ("form", toJson form.name)]

/-- The Keccak-loop profile checks the step and both masks; then the form and
the whole saved plan must be canonical. -/
def checkedPlan (json : Json) : Except String (Solcore.Synthesis.Core.KeccakLoop.CheckedPlan × Form) := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported assembly Keccak-loop plan schema"
  let plan ← KeccakLoop.checkedPlan (Json.mkObj [("schema", toJson KeccakLoop.planSchema),
    ("stepProgram", ← json.getObjVal? "stepProgram"), ("mask", ← json.getObjVal? "mask"),
    ("keyMask", ← json.getObjVal? "keyMask")])
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "assembly Keccak-loop form must be split, carried or pipelined"
  unless json == planJson plan form do
    throw "saved assembly Keccak-loop plan differs from its canonical checked representation"
  return (plan, form)

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("keccakLoopPlan", planJson scenario.plan scenario.form),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", KeccakLoop.transactionsJson scenario.plan.mask scenario.transactions),
    ("initialState", KeccakLoop.initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.loop.observedSlots),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("loopProfileVersion", toJson KeccakLoop.profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.KeccakLoop.version),
      ("framingVersion", toJson Solcore.Synthesis.Core.EventLog.framingVersion),
      ("templateVersion", toJson KeccakLoop.templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", KeccakLoop.contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.form scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- The case in the Keccak-loop profile's shape must pass that profile's
checks: its transactions, the canonical Core program, the empty initial state,
the fuel and the derived observed slots. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic assembly Keccak-loop case schema"
  let (plan, form) ← checkedPlan (← json.getObjVal? "keccakLoopPlan")
  let loop ← KeccakLoop.caseProgram ((json.setObjVal! "schema" (toJson KeccakLoop.caseSchema)).setObjVal!
    "keccakLoopPlan" (KeccakLoop.planJson plan))
  return ⟨loop, form⟩

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  KeccakLoop.observe scenario.loop bindings fuel

/-- Separates the form stream from other uses of a case seed. -/
private def formDomain : UInt64 := 0x616b636c6f6f7001

def formFor (seed : Seed) : Form := AssemblyStorage.formFor formDomain seed

/-- The Keccak-loop profile's scenario and generated origin for the seed, with
the seed's form. A registered test requires both profiles to agree. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  let (loop, origin) ← KeccakLoop.generatedScenario seed nodes revision transactions
  let form := formFor seed
  return (⟨loop, form⟩,
    (origin.setObjVal! "kind" (toJson "assembly-keccak-loop-generated")).setObjVal! "form" (toJson form.name))

/-- Attempts count complete scenario candidates. The exclusions are those of
the Keccak-loop profile, in its order; fuel exhaustion is an inconclusive
exclusion. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.form scenario.plan).mapError reprStr
        KeccakLoop.validateGenerated scenario.loop fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "Keccak-loop history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "assembly-keccak-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- A sealed Keccak-loop reduction of the source scenario, kept in its form. -/
structure Reduction (source : CheckedScenario) where private mk ::
  loop : KeccakLoop.Reduction source.loop

def Reduction.candidate {source : CheckedScenario} (reduced : Reduction source) : CheckedScenario :=
  ⟨reduced.loop.candidate, source.form⟩

/-- The Keccak-loop profile's reductions, in their order, each in the form of
the source case. -/
def reductions (source : CheckedScenario) : List (Reduction source) :=
  (KeccakLoop.reductions source.loop).map fun reduced => ⟨reduced⟩

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan parent.form),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", KeccakLoop.transactionsJson parent.plan.mask parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("loopProfileVersion", KeccakLoop.profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.KeccakLoop.version),
      ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion),
      ("templateVersion", KeccakLoop.templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.form admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from assembly Keccak-loop plan emission"
  unless (← json.getObjVal? "contract") == KeccakLoop.contractJson emitted do
    throw "saved contract metadata differs from assembly Keccak-loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "assembly-keccak-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes")
      revision (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated assembly Keccak-loop provenance"
    unless planJson expected.plan expected.form == planJson admitted.plan admitted.form &&
        KeccakLoop.transactionsJson expected.plan.mask expected.transactions ==
          KeccakLoop.transactionsJson admitted.plan.mask admitted.transactions do
      throw "saved plan, form or transaction sequence differs from its generation seed"
    KeccakLoop.validateGenerated expected.loop validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let (parentPlan, parentForm) ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← KeccakLoop.decodeTransactions parentPlan.mask (← origin.getObjVal? "parentTransactions")
    let parent : CheckedScenario := ⟨← KeccakLoop.checkedScenario parentPlan parentTransactions, parentForm⟩
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its plan"
    unless parentForm == admitted.form do throw "reduction changes the parent case's form"
    unless (KeccakLoop.sealReduction parent.loop admitted.plan.step admitted.plan.mask admitted.plan.keyMask
        admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported assembly Keccak-loop case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.AssemblyKeccakLoop
