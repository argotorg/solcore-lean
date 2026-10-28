import Solcore.Synthesis.Source.AssemblyStorageLoopCases

/-! Generated inline Yul storage-loop cases. For the same seed, budget, G0
revision and transaction count, generation must agree with the storage-loop
profile: the same attempts and exclusions, and per case the same plan,
original Core program, transactions, initial state, observed slots, fuel and
observation, with an origin that differs only in its kind and recorded form.
The form must be the seed's, every form must be drawn, and each source must
have its form's blocks and call no std storage or revert wrapper. Each case
must replay to itself, and every reduction keeps the parent case's form and
replays. An unknown form, a storage-loop plan or case schema and a form that
its source was not emitted in are refused. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyStorageLoopCases

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Source.AssemblyStorage (Form)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def occurs (text part : String) : Bool := (text.splitOn part).length > 1

/-- The marks of a form: `split` writes through a fresh slot expression,
`carried` advances the counter in Yul without a conditional read, and
`pipelined` reads under two conditionals, before the loop and after the
writes. -/
private def hasForm (source : String) : Form → Bool
  | .split => occurs source "sstore(add(sc_counter, 2), sc_value)" && !occurs source "sc_counter := add(sc_counter, 1)"
  | .carried => occurs source "sc_counter := add(sc_counter, 1)" && !occurs source "if gt(sc_limit, sc_counter)"
  | .pipelined => (source.splitOn "if gt(sc_limit, sc_counter)").length == 3

/-- The storage-loop case fields that an inline Yul case keeps. -/
private def kept : List String := ["program", "transactions", "initialState", "observedSlots", "executionFuel"]

def testSourceAssemblyStorageLoopCases : IO Unit := do
  let fuel := 1000000
  let mut forms : List Form := []
  let mut cases : Array Json := #[]
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three, from seed 4, the first whose eight
  -- consecutive seeds draw every form.
  for (revision, transactions, count) in [(GeneratorRevision.v3, 8, 8), (GeneratorRevision.v1, 3, 8)] do
    let generated := Solcore.Synthesis.Source.AssemblyStorageLoop.generateCases (Seed.ofNat 4) 384 count 512 fuel
      revision transactions
    let parent := Solcore.Synthesis.Source.StorageLoop.generateCases (Seed.ofNat 4) 384 count 512 fuel revision transactions
    ensure ((generated.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    for key in ["requested", "attempted", "status"] do
      ensure ((generated.getObjVal? key).toOption == (parent.getObjVal? key).toOption)
        s!"{revision.version}: {key} differs from the storage-loop profile"
    let excluded ← get (generated.getObjValAs? (Array Json) "excluded")
    ensure (excluded.map (·.setObjVal! "stage" (toJson "storage-loop-profile")) ==
        (← get (parent.getObjValAs? (Array Json) "excluded"))) s!"{revision.version}: the exclusions differ"
    let ours ← get (generated.getObjValAs? (Array Json) "cases")
    let theirs ← get (parent.getObjValAs? (Array Json) "cases")
    ensure (ours.size == theirs.size) s!"{revision.version}: the case counts differ"
    for ((json, base), index) in (ours.zip theirs).zipIdx do
      let name := s!"{revision.version} case {index}"
      for key in kept do
        ensure ((json.getObjVal? key).toOption == (base.getObjVal? key).toOption) s!"{name}: {key} differs"
      let scenario ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram json)
      let loop ← get (Solcore.Synthesis.Source.StorageLoop.caseProgram base)
      ensure (Solcore.Synthesis.Source.StorageLoop.planJson scenario.plan ==
        Solcore.Synthesis.Source.StorageLoop.planJson loop.plan) s!"{name}: the plan differs"
      let origin ← get ((← get (json.getObjVal? "provenance")).getObjVal? "origin")
      let parentOrigin ← get ((← get (base.getObjVal? "provenance")).getObjVal? "origin")
      let some seed := (← get (origin.getObjValAs? String "seed")).toNat? | throw (IO.userError s!"{name}: no seed")
      ensure (scenario.form == Solcore.Synthesis.Source.AssemblyStorageLoop.formFor (Seed.ofNat seed))
        s!"{name}: the form is not the seed's"
      ensure (origin == (parentOrigin.setObjVal! "kind" (toJson "assembly-storage-loop-generated")).setObjVal!
        "form" (toJson scenario.form.name)) s!"{name}: the origin differs beyond its kind and form"
      if index == 0 then
        ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.observe scenario StorageExecution.fixtureBindings fuel ==
            Solcore.Synthesis.Source.StorageLoop.observe loop StorageExecution.fixtureBindings fuel)
          s!"{name}: the observation differs"
      ensure ((Solcore.Synthesis.Source.AssemblyStorageLoop.replayCase json fuel).toOption == some json)
        s!"{name}: replay differs"
      let source ← get (json.getObjValAs? String "source")
      ensure (Form.all.all fun form => hasForm source form == (form == scenario.form))
        s!"{name}: the source does not have exactly the {scenario.form.name} form's blocks"
      ensure (!occurs source "revert_(" && !occurs source "{sload")
        s!"{name}: the source calls a std wrapper"
      forms := scenario.form :: forms
      cases := cases.push json
  for form in Form.all do
    ensure (forms.contains form) s!"generation never drew the {form.name} form"
  -- Reductions are the storage-loop profile's in the parent case's form, and
  -- every emitted candidate replays.
  for json in cases.toList.take 1 ++ (cases.toList.drop 8).take 1 do
    let source ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram json)
    let reduced := Solcore.Synthesis.Source.AssemblyStorageLoop.reductions source
    ensure (!reduced.isEmpty && reduced.length == (Solcore.Synthesis.Source.StorageLoop.reductions source.loop).length)
      "the reductions differ from the storage-loop profile's"
    ensure (reduced.all fun candidate => candidate.candidate.form == source.form) "a reduction changes the form"
    let shrunk ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.shrinkCases json 16 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.AssemblyStorageLoop.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      ensure ((← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram candidate)).form == source.form)
        "an emitted reduction changes the form"
  -- An unknown form, the parent's schemas and another form's plan are refused.
  let some json := cases[0]? | throw (IO.userError "no case")
  let scenario ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram json)
  let plan ← get (json.getObjVal? "storageLoopPlan")
  ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.checkedPlan (plan.setObjVal! "form" (toJson "blocks"))).toOption.isNone
    "an unknown form was admitted"
  ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.checkedPlan
      (plan.setObjVal! "schema" (toJson Solcore.Synthesis.Source.StorageLoop.planSchema))).toOption.isNone
    "a storage-loop plan schema was admitted"
  ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram
      (json.setObjVal! "schema" (toJson Solcore.Synthesis.Source.StorageLoop.caseSchema))).toOption.isNone
    "a storage-loop case schema was admitted"
  ensure (Solcore.Synthesis.Source.StorageLoop.caseProgram json).toOption.isNone
    "the storage-loop profile admitted an inline Yul case"
  for other in Form.all do
    if other != scenario.form then
      let changed := json.setObjVal! "storageLoopPlan" (plan.setObjVal! "form" (toJson other.name))
      ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram changed).toOption.isSome
        "a plan in another form failed decoding"
      ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.replayCase changed fuel).toOption.isNone
        s!"the {other.name} form replayed with a {scenario.form.name} source"

end Tests.SourceAssemblyStorageLoopCases
