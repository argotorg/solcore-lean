import Solcore.Synthesis.Source.MethodsCases

/-! Several-methods cases: generation is deterministic and validates every
prescribed outcome against original Core; generated, imported and reduced
cases replay exactly; reductions remove transactions first, then methods no
transaction calls, and keep the G0 revision and swarm mask; and the case
boundary rejects method lists outside two to four, invalid or repeated names,
more than two arguments, colliding or missing selectors, calls of undeclared
methods or with other arguments, and any calldata, selector or std outcome that
differs from the transaction. -/
set_option autoImplicit false

namespace Tests.SourceMethodsCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Stateful.MethodsExecution (Method Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def fuel : Nat := 1000000

private def cases (corpus : Json) : IO (Array Json) := get (corpus.getObjValAs? (Array Json) "cases")

private def w (value : Nat) : Word := Word.ofNatModulo value

def testSourceMethodsCases : IO Unit := do
  let corpus := Methods.generateCases (Seed.ofNat 1) 448 4 64 fuel .v3 8
  ensure (corpus == Methods.generateCases (Seed.ofNat 1) 448 4 64 fuel .v3 8) "generation is nondeterministic"
  ensure ((← get (corpus.getObjValAs? String "status")) == "complete") "generation did not complete"
  let generated ← cases corpus
  let mut outcomes : List String := []
  let mut counts : List Nat := []
  for saved in generated do
    ensure ((← get (Methods.replayCase saved fuel)) == saved) "a generated case failed exact replay"
    let scenario ← get (Methods.caseProgram saved)
    ensure (scenario.transactions.length == 8) "a generated case lost its requested length"
    counts := (counts ++ [scenario.methods.length]).eraseDups
    outcomes := (outcomes ++ scenario.transactions.map fun tx =>
      (Methods.prescribed scenario tx).map Methods.selectorText |>.getD "accepted").eraseDups
    let contract ← get (saved.getObjVal? "contract")
    ensure ((contract.getObjValAs? String "selectorOrder").toOption == some (Methods.selectorOrder scenario.methods))
      "a case records another selector order"
  ensure (["0x4924aef0", "accepted"].all outcomes.contains) "generation misses an outcome"
  ensure (counts.length ≥ 2) "generation draws one method count only"
  let some first := generated[0]? | throw (IO.userError "no generated case")
  let provenance ← get (first.getObjVal? "provenance")
  let reduced ← cases (← get (Methods.shrinkCases first 12 fuel))
  let some removal := reduced[0]? | throw (IO.userError "a generated case has no reduction")
  let original ← get (first.getObjValAs? (List Json) "transactions")
  ensure ((← get (removal.getObjValAs? (List Json) "transactions")) == original.dropLast)
    "the first reduction does not remove the last transaction"
  for candidate in reduced do
    ensure ((← get (Methods.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
    let candidateProvenance ← get (candidate.getObjVal? "provenance")
    ensure ((candidateProvenance.getObjVal? "swarmMask").toOption == (provenance.getObjVal? "swarmMask").toOption &&
      (candidateProvenance.getObjVal? "generatorVersion").toOption == (provenance.getObjVal? "generatorVersion").toOption)
      "a reduction lost the parent's revision or swarm mask"
  -- An imported contract of four methods with the step `x ↦ x + 1`, two of
  -- them never called, through the case boundary; removing an uncalled method
  -- is a reduction.
  let some step := Aggregates.CheckedDAG.ofParts? [Aggregate.template 0 (.word (w 1))] (.apply (.var 1) (.var 0))
    | throw (IO.userError "the constant step failed admission")
  let methods : List Method := [⟨"m_00000001", 1⟩, ⟨"m_00000002", 0⟩, ⟨"m_00000003", 2⟩, ⟨"m_00000004", 1⟩]
  let missing := 0x43c9d5b5
  let some plan := ContractMethods.CheckedPlan.ofParts? (methods.map (·.shape)) (List.replicate 4 step)
    | throw (IO.userError "an imported plan failed admission")
  let transactions : List Transaction := [⟨"tx-0", some 2, [w 2, w 4]⟩, ⟨"tx-1", none, [w 1]⟩, ⟨"tx-2", some 0, [w 7]⟩]
  let imported ← get (Methods.checkedScenario plan methods missing transactions)
  let importedCase ← get (Methods.emitCase imported (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← get (Methods.replayCase importedCase fuel)) == importedCase) "an imported case failed exact replay"
  let rows ← get (importedCase.getObjValAs? (Array Json) "transactions")
  ensure ((rows.map fun row => (row.getObjVal? "stdRejection").toOption) ==
      #[some Json.null, some (toJson "0x4924aef0"), some Json.null]) "an imported case records other std outcomes"
  ensure ((rows.map fun row => (row.getObjVal? "selector").toOption) ==
      #[some (toJson "0x336e1e08"), some (toJson "0x43c9d5b5"), some (toJson "0x935853e4")])
    "an imported case records other selectors"
  let importedReductions ← cases (← get (Methods.shrinkCases importedCase 8 fuel))
  ensure (importedReductions.any fun candidate =>
      ((candidate.getObjVal? "contract").toOption.bind (·.getObjValAs? (List Json) "methods" |>.toOption)).map (·.length) ==
        some 3) "no reduction removes the uncalled methods"
  -- Method lists outside two to four, invalid or repeated names, three
  -- arguments, colliding or missing selectors, undeclared methods and wrong
  -- argument counts are rejected.
  let check := fun (methods : List Method) (missing : Nat) (transactions : List Transaction) =>
    match ContractMethods.CheckedPlan.ofParts? (methods.map (·.shape)) (methods.map fun _ => step) with
    | some plan => Methods.checkedScenario plan methods missing transactions
    | none => .error "plan failed admission"
  rejected (check [⟨"m_00000001", 1⟩] missing [⟨"tx-0", some 0, [w 2]⟩]) "one method was admitted"
  rejected (check (methods ++ [⟨"m_00000005", 1⟩]) missing [⟨"tx-0", some 0, [w 2]⟩]) "five methods were admitted"
  rejected (check [⟨"m_0000000G", 1⟩, ⟨"m_00000002", 0⟩] missing [⟨"tx-0", some 0, [w 2]⟩]) "an invalid name was admitted"
  rejected (check [⟨"m_00000001", 1⟩, ⟨"m_00000001", 0⟩] missing [⟨"tx-0", some 0, [w 2]⟩]) "a repeated name was admitted"
  rejected (check [⟨"m_00000001", 3⟩, ⟨"m_00000002", 0⟩] missing [⟨"tx-0", some 1, []⟩]) "three arguments were admitted"
  rejected (check methods 0x935853e4 [⟨"tx-0", some 0, [w 2]⟩]) "a missing selector of a method was admitted"
  rejected (check methods missing [⟨"tx-0", some 4, [w 2]⟩]) "an undeclared method was admitted"
  rejected (check methods missing [⟨"tx-0", some 1, [w 2]⟩]) "a call with another argument count was admitted"
  rejected (check methods missing [⟨"tx-0", none, []⟩]) "a missing selector without its Word was admitted"
  let row := rows[0]!
  for (key, value) in [("calldata", toJson "0x336e1e08"), ("selector", toJson "0x935853e4"),
      ("stdRejection", toJson "0x4924aef0"), ("method", toJson "m_0000000f"), ("value", toJson "1")] do
    rejected (Methods.decodeTransactions methods missing (toJson [row.setObjVal! key value]))
      s!"a transaction with a changed {key} was admitted"

end Tests.SourceMethodsCases
