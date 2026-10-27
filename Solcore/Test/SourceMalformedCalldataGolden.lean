import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Core.DynamicArray
import Solcore.Synthesis.Stateful.MalformedCalldataExecution

/-! Golden cases for the std model behind the malformed-calldata profile. The
expected outcome of every case is written out from the pinned std's
`dispatch.sol` and `std.sol`, not computed by either model: a rejection
reverts with its error selector as a Word and keeps the empty storage; an
accepted malformation behaves exactly like the canonical dynamic-array
contract on the words std decodes. Both the Core wrapper and the byte-level
`stdRejection?` must give that outcome. Cases with two defects check std's
decode order. -/
set_option autoImplicit false

namespace Tests.SourceMalformedCalldataGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.MalformedCalldataExecution (Malformation Transaction inputBytes stdRejection?)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The expected std outcome: the rejecting selector, or acceptance with the
decoded flags and elements. -/
private inductive Expected where
  | rejected (selector : Nat)
  | accepted (flags : Nat) (values : List Nat)

private def noSelector : Expected := .rejected MalformedCalldata.noSelectorError
private def truncated : Expected := .rejected MalformedCalldata.truncatedError

/-- Canonical arguments: flags 2 (even, so the body returns) and the elements
5 and 7. The canonical calldata is 164 bytes: selector, flags, offset 64,
length 2 and the two elements. -/
private def flags : Nat := 2
private def values : List Nat := [5, 7]
private def size : Nat := 164

private def malformed (malformation : Malformation) : Transaction :=
  ⟨"tx-0", w flags, values.map w, malformation⟩

private def cases : List (String × Malformation × Expected) := [
  ("canonical", .none, .accepted flags values),
  ("short-0", .short 0, noSelector), ("short-1", .short 1, noSelector), ("short-3", .short 3, noSelector),
  ("wrong-selector-low", .selector 1, noSelector), ("wrong-selector-high", .selector (2 ^ 31), noSelector),
  ("wrong-selector-all", .selector (2 ^ 32 - 1), noSelector),
  -- Only the selector: the head check comes after dispatch.
  ("truncated-selector-only", .truncate 4, truncated),
  ("truncated-head-36", .truncate 36, truncated), ("truncated-head-67", .truncate 67, truncated),
  -- The head is complete but the length word is not.
  ("truncated-length", .truncate 99, truncated),
  -- The length is complete but the last element is not.
  ("truncated-element", .truncate (size - 1), truncated), ("truncated-last-word", .truncate (size - 32), truncated),
  ("trailing-1-zero", .trailing 1 0, .accepted flags values), ("trailing-33-ones", .trailing 33 1, .accepted flags values),
  ("trailing-64-ramp", .trailing 64 2, .accepted flags values),
  -- 161 > size - 4: the advance to the length word fails.
  ("offset-past-end", .offset (w (size - 3)), truncated),
  -- 129 <= size - 4, but only 31 bytes remain at 4 + 129.
  ("offset-partial-length", .offset (w (size - 35)), truncated),
  ("offset-high-bit", .offset (w (2 ^ 255)), truncated),
  -- 4 + o wraps to 0, 2 and 3; std compares o with size - 4 first.
  ("offset-wraps-to-0", .offset (w (2 ^ 256 - 4)), truncated),
  ("offset-wraps-to-2", .offset (w (2 ^ 256 - 2)), truncated),
  ("offset-wraps-to-3", .offset (w (2 ^ 256 - 1)), truncated),
  -- Offset 0: the length is the flags word, 2, and the elements are the words
  -- at 36 and 68, the replaced offset 0 and the original length 2.
  ("offset-overlaps-flags", .offset (w 0), .accepted flags [0, 2]),
  -- Offset 32: the length is the offset word itself, 32, and 1,024 element
  -- bytes do not fit.
  ("offset-overlaps-itself", .offset (w 32), truncated),
  ("length-one-too-long", .length (w 3), truncated),
  ("length-above-max", .length (w (2 ^ 251)), truncated),
  -- 32 * (2^251 + 1) wraps to 32 in Word arithmetic; std's bound check rejects first.
  ("length-product-wraps", .length (w (2 ^ 251 + 1)), truncated),
  ("length-maximum", .length (w (2 ^ 256 - 1)), truncated),
  ("length-one-shorter", .length (w 1), .accepted flags [5]),
  ("length-zero", .length (w 0), .accepted flags [])]

/-- Raw calldata with two defects at once, for the decode order. -/
private def bytes (parts : List Nat) : ByteArray := ByteArray.mk (parts.map Nat.toUInt8).toArray

private def selectorBytes (selector : Nat) : List Nat :=
  [selector / 2 ^ 24 % 256, selector / 2 ^ 16 % 256, selector / 2 ^ 8 % 256, selector % 256]

private def wordBytes (value : Nat) : List Nat := (encodeWordBytesBE (w value)).data.toList.map UInt8.toNat

private def ordered : List (String × ByteArray × Expected) := [
  -- A wrong selector wins over a truncated head: dispatch fails first.
  ("wrong-selector-and-short-head", bytes (selectorBytes (MalformedCalldata.selector ^^^ 1) ++ wordBytes flags),
    noSelector),
  -- Three bytes of the right selector are still short calldata.
  ("three-selector-bytes", bytes ((selectorBytes MalformedCalldata.selector).take 3), noSelector),
  -- A truncated head wins over a bad offset in the bytes that are present.
  ("short-head-and-bad-offset", bytes (selectorBytes MalformedCalldata.selector ++ wordBytes flags ++
    (wordBytes (2 ^ 256 - 4)).take 31), truncated),
  -- A wrapping offset and a wrapping length together: the offset is checked first.
  ("bad-offset-and-length", bytes (selectorBytes MalformedCalldata.selector ++ wordBytes flags ++
    wordBytes (2 ^ 256 - 4) ++ wordBytes (2 ^ 251 + 1)), truncated),
  -- The selector of another method with a canonical body is no match.
  ("other-selector-canonical-body", bytes (selectorBytes 0x7357f5d2 ++ wordBytes flags ++ wordBytes 64 ++
    wordBytes 0), noSelector)]

private def selectorOutput (selector : Nat) : String := encodeBytesText (encodeWordBytesBE (w selector))

private def row (history : Json) : IO Json := do
  let some first := (← get (history.getObjValAs? (Array Json) "transactions"))[0]?
    | throw (IO.userError "no transaction row")
  return first

/-- The original Core contract run once from an empty world on raw calldata. -/
private def runRaw (contract : CheckedCoreContract) (input : ByteArray) (fuel : Nat) : IO Json := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let world := StorageExecution.initialWorldForContract contract bindings
  let some ⟨resolved, installed⟩ := registry.resolve? world bindings.address
    | throw (IO.userError "contract does not resolve")
  if bounded : input.size < Solcore.Core.wordModulus then
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := ⟨input, bounded⟩ }
    match TopLevelExecution.run resolved invocation installed fuel with
    | .completed terminal =>
        match terminal.outcome with
        | .returned output => return Json.mkObj [("status", toJson "returned"), ("output", toJson (encodeBytesText output))]
        | .reverted output => return Json.mkObj [("status", toJson "reverted"), ("output", toJson (encodeBytesText output))]
        | .trapped _ => return Json.mkObj [("status", toJson "trapped")]
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "golden case exhausted fuel")
  else throw (IO.userError "golden input exceeds a Word")

private def checkExpected (name : String) (canonical : DynamicArray.CheckedPlan)
    (input : ByteArray) (outcome : Json) (expected : Expected) (fuel : Nat) : IO Unit := do
  match expected with
  | .rejected selector =>
      ensure (stdRejection? input == some selector) s!"{name}: the byte model does not reject with {selector}"
      ensure ((← get (outcome.getObjValAs? String "status")) == "reverted" &&
        (← get (outcome.getObjValAs? String "output")) == selectorOutput selector)
        s!"{name}: original Core does not revert with the std selector"
  | .accepted expectedFlags expectedValues =>
      ensure (stdRejection? input == none) s!"{name}: the byte model rejects an accepted malformation"
      ensure (MalformedCalldataExecution.stdDecoded? input == some (expectedFlags, expectedValues))
        s!"{name}: the byte model decodes other words"
      -- The canonical dynamic-array contract on the decoded words is the reference
      -- for the body. Elements past the third are never read.
      let reference := DynamicArrayExecution.observe canonical
        [⟨"tx-0", w expectedFlags, (expectedValues.take MalformedCalldata.maxElements).map w⟩]
        StorageExecution.fixtureBindings fuel
      let referenceRow ← row reference
      if expectedValues.length ≤ MalformedCalldata.maxElements then
        for key in ["status", "output", "committedStorage", "accountStorage"] do
          ensure ((outcome.getObjVal? key).toOption == (referenceRow.getObjVal? key).toOption)
            s!"{name}: {key} differs from the canonical contract on the decoded words"

def testSourceMalformedCalldataGolden : IO Unit := do
  let fuel := 1000000
  ensure (MalformedCalldata.selector == 0x9a94c44b) "the profile selector is not run(uint256,uint256[])"
  ensure ((DynamicArrayExecution.inputBytes (w flags) (values.map w)).size == size) "canonical calldata size changed"
  let (step, _) ← get (Solcore.Synthesis.Source.Aggregate.generatedFunction (Seed.ofNat 1)
    (384 - MalformedCalldata.programOverhead))
  let some plan := MalformedCalldata.CheckedPlan.ofStep? step | throw (IO.userError "the std wrapper failed admission")
  let some canonical := DynamicArray.CheckedPlan.ofStep? step | throw (IO.userError "the dynamic-array wrapper failed admission")
  for (name, malformation, expected) in cases do
    let tx := malformed malformation
    let history := MalformedCalldataExecution.observe plan [tx] StorageExecution.fixtureBindings fuel
    let outcome ← row history
    checkExpected name canonical (inputBytes tx) outcome expected fuel
    match expected with
    | .rejected _ =>
        ensure ((outcome.getObjVal? "committedStorage").toOption == (history.getObjVal? "initialStorage").toOption &&
          (outcome.getObjVal? "accountStorage").toOption == (history.getObjVal? "initialAccountStorage").toOption)
          s!"{name}: a std rejection changed storage"
    | .accepted _ _ => pure ()
  for (name, input, expected) in ordered do
    checkExpected name canonical input (← runRaw plan.contract input fuel) expected fuel

end Tests.SourceMalformedCalldataGolden
