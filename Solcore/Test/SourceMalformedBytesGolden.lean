import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Core.LongBytes
import Solcore.Synthesis.Stateful.MalformedBytesExecution

/-! Golden cases for the std model behind the malformed-bytes profile. The
expected outcome of every case is written out from the pinned std's
`dispatch.sol` and `std.sol` (`decodeBytesLike`), not computed by either model:
a rejection reverts with its error selector as a Word and keeps the empty
storage; an accepted malformation behaves exactly like the canonical
long-bytes contract on the payload std decodes, except that its result counts
the actual calldata size. Both the Core wrapper and the byte-level
`stdDecode` must give that outcome. Cases with two defects check std's decode
order. -/
set_option autoImplicit false

namespace Tests.SourceMalformedBytesGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.MalformedBytesExecution (Malformation Transaction inputBytes stdRejection?)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The expected std outcome: the rejecting selector, or acceptance with the
decoded flags and payload. -/
private inductive Expected where
  | rejected (selector : Nat)
  | accepted (flags : Nat) (payload : List Nat)

private def noSelector : Expected := .rejected StdDispatch.noSelectorError
private def truncated : Expected := .rejected StdDispatch.truncatedError

/-- The ramp `1, 2, ..., count`. -/
private def ramp (count : Nat) : List Nat := (List.range count).map (· + 1)

/-- 65 bytes, flags 2 (even, so the body returns): the payload at bytes 100 to
164 and 31 bytes of zero padding to 196. -/
private def odd : List Nat := ramp 65
/-- 64 bytes without padding; 164 bytes of calldata. -/
private def even : List Nat := ramp 64

private def malformed (payload : List Nat) (malformation : Malformation) : Transaction :=
  ⟨"tx-0", w 2, payload.map Nat.toUInt8, malformation⟩

private def cases : List (String × List Nat × Malformation × Expected) := [
  ("canonical", odd, .none, .accepted 2 odd),
  ("short-0", odd, .short 0, noSelector), ("short-3", odd, .short 3, noSelector),
  ("wrong-selector-low", odd, .selector 1, noSelector),
  ("wrong-selector-high", odd, .selector (2 ^ 31), noSelector),
  ("wrong-selector-all", odd, .selector (2 ^ 32 - 1), noSelector),
  ("truncated-selector-only", odd, .truncate 4, truncated),
  ("truncated-head", odd, .truncate 67, truncated),
  -- 31 bytes remain at 4 + 64.
  ("truncated-length", odd, .truncate 99, truncated),
  -- The last payload byte at 164 is cut.
  ("truncated-payload", odd, .truncate 164, truncated),
  -- Only padding is cut: std neither requires nor reads it.
  ("cut-all-padding", odd, .truncate 165, .accepted 2 odd),
  ("cut-last-padding-byte", odd, .truncate 195, .accepted 2 odd),
  ("truncated-unpadded-payload", even, .truncate 163, truncated),
  ("trailing-1-zero", odd, .trailing 1 0, .accepted 2 odd),
  ("trailing-33-ones", odd, .trailing 33 1, .accepted 2 odd),
  ("trailing-64-ramp", odd, .trailing 64 2, .accepted 2 odd),
  ("offset-past-end", odd, .offset (w 193), truncated),
  ("offset-partial-length", odd, .offset (w 161), truncated),
  ("offset-high-bit", odd, .offset (w (2 ^ 255)), truncated),
  ("offset-wraps", odd, .offset (w (2 ^ 256 - 4)), truncated),
  -- Offset 0: the length is the flags Word, 2, and the payload the first two
  -- bytes of the offset Word, now zero.
  ("offset-overlaps-flags", odd, .offset (w 0), .accepted 2 [0, 0]),
  -- Offset 32: the length is the offset Word, 32, and the payload is the
  -- original length Word, which ends in 65.
  ("offset-overlaps-itself", odd, .offset (w 32), .accepted 2 (List.replicate 31 0 ++ [65])),
  -- One byte of the padding becomes payload.
  ("length-into-padding", odd, .length (w 66), .accepted 2 (odd ++ [0])),
  ("length-most-that-fits", odd, .length (w 96), .accepted 2 (odd ++ List.replicate 31 0)),
  ("length-past-data", odd, .length (w 97), truncated),
  ("length-past-unpadded-data", even, .length (w 65), truncated),
  -- Above ~0 - 63: the range check rejects before std's bound.
  ("length-above-bound", odd, .length (w (2 ^ 256 - 63)), truncated),
  ("length-maximum", odd, .length (w (2 ^ 256 - 1)), truncated),
  ("length-high-bit", odd, .length (w (2 ^ 255)), truncated),
  ("length-one-shorter", odd, .length (w 64), .accepted 2 even),
  ("length-zero", odd, .length (w 0), .accepted 2 []),
  -- Nonzero padding is ignored.
  ("padding-ones", odd, .padding 0, .accepted 2 odd),
  ("padding-ramp", odd, .padding 1, .accepted 2 odd),
  ("padding-last-byte", odd, .padding 2, .accepted 2 odd)]

/-- Raw calldata with two defects at once, for the decode order. -/
private def bytes (parts : List Nat) : ByteArray := ByteArray.mk (parts.map Nat.toUInt8).toArray

private def selectorBytes (selector : Nat) : List Nat :=
  [selector / 2 ^ 24 % 256, selector / 2 ^ 16 % 256, selector / 2 ^ 8 % 256, selector % 256]

private def wordBytes (value : Nat) : List Nat := (encodeWordBytesBE (w value)).data.toList.map UInt8.toNat

private def canonical (payload : List Nat) : ByteArray :=
  DynamicBytesExecution.inputBytes (w 2) (payload.map Nat.toUInt8)

private def ordered : List (String × ByteArray × Expected) := [
  -- A wrong selector wins over a bad length: dispatch fails first.
  ("wrong-selector-and-bad-length",
    StdCalldata.replaceWord ((StdCalldata.Change.selector 1).apply (canonical odd)) 68 (w (2 ^ 256 - 1)), noSelector),
  ("three-selector-bytes", bytes ((selectorBytes MalformedBytes.selector).take 3), noSelector),
  -- A truncated head wins over a bad offset in the bytes that are present.
  ("short-head-and-bad-offset", bytes (selectorBytes MalformedBytes.selector ++ wordBytes 2 ++
    (wordBytes (2 ^ 256 - 4)).take 31), truncated),
  -- A wrapping offset and a bad length: the offset is checked first.
  ("bad-offset-and-length",
    StdCalldata.replaceWord (StdCalldata.replaceWord (canonical odd) 36 (w (2 ^ 256 - 4))) 68 (w (2 ^ 256 - 1)), truncated),
  -- Nonzero padding with a cut inside it: the last payload Word at 164 keeps
  -- its payload byte 65 and gains `0xff` padding, cut after 180 bytes.
  ("ones-padding-then-cut", ((StdCalldata.Change.word 164 (w (2 ^ 248 * 65 + (2 ^ 248 - 1)))).apply (canonical odd)).extract 0 180,
    .accepted 2 odd),
  -- The dynamic-array selector with a canonical bytes body is no match.
  ("dynamic-array-selector-bytes-body",
    bytes (selectorBytes 0x9a94c44b) ++ (canonical odd).extract 4 (canonical odd).size, noSelector)]

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
        let storage := match terminal.finalWorld.account? bindings.address with
          | some account => LongBytesExecution.storageJson account
          | none => Json.null
        let fields := match terminal.outcome with
          | .returned output => [("status", toJson "returned"), ("output", toJson (encodeBytesText output))]
          | .reverted output => [("status", toJson "reverted"), ("output", toJson (encodeBytesText output))]
          | .trapped _ => [("status", toJson "trapped")]
        return Json.mkObj (fields ++ [("committedStorage", storage),
          ("accountStorage", AccountStorage.contractJson terminal.finalWorld bindings.address)])
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "golden case exhausted fuel")
  else throw (IO.userError "golden input exceeds a Word")

/-- The Word a row returns or reverts with. -/
private def outputWord (row : Json) : IO Nat := do
  let some bytes := decodeBytesText? (← get (row.getObjValAs? String "output"))
    | throw (IO.userError "output is not hexadecimal")
  return StdCalldata.wordAt bytes 0

private def checkExpected (name : String) (canonicalPlan : LongBytes.CheckedPlan)
    (input : ByteArray) (outcome : Json) (expected : Expected) (fuel : Nat) : IO Unit := do
  match expected with
  | .rejected selector =>
      ensure (stdRejection? input == some selector) s!"{name}: the byte model does not reject with {selector}"
      ensure ((← get (outcome.getObjValAs? String "status")) == "reverted" &&
        (← get (outcome.getObjValAs? String "output")) == selectorOutput selector)
        s!"{name}: original Core does not revert with the std selector"
      let empty := LongBytesExecution.observe canonicalPlan [] StorageExecution.fixtureBindings fuel
      ensure ((outcome.getObjVal? "committedStorage").toOption == (empty.getObjVal? "initialStorage").toOption &&
        (outcome.getObjVal? "accountStorage").toOption == (empty.getObjVal? "initialAccountStorage").toOption)
        s!"{name}: a std rejection changed storage"
  | .accepted flags payload =>
      ensure (stdRejection? input == none) s!"{name}: the byte model rejects an accepted malformation"
      ensure (MalformedBytesExecution.stdDecoded? input == some (flags, payload.map Nat.toUInt8))
        s!"{name}: the byte model decodes another payload"
      -- The canonical long-bytes contract on the decoded payload is the
      -- reference for the body; its result counts the canonical calldata size.
      let bytesPayload := payload.map Nat.toUInt8
      let reference := LongBytesExecution.observe canonicalPlan [⟨"tx-0", w flags, bytesPayload⟩]
        StorageExecution.fixtureBindings fuel
      let referenceRow ← row reference
      for key in ["status", "committedStorage", "accountStorage"] do
        ensure ((outcome.getObjVal? key).toOption == (referenceRow.getObjVal? key).toOption)
          s!"{name}: {key} differs from the canonical contract on the decoded payload"
      let canonicalSize := (DynamicBytesExecution.inputBytes (w flags) bytesPayload).size
      ensure ((← outputWord outcome) == ((← outputWord referenceRow) + input.size - canonicalSize) % 2 ^ 256)
        s!"{name}: the result differs from the canonical contract's beyond the calldata size"

def testSourceMalformedBytesGolden : IO Unit := do
  let fuel := 1000000
  ensure (MalformedBytes.selector == 0x220eb9b6) "the profile selector is not run(uint256,bytes)"
  ensure ((canonical odd).size == 196 && (canonical even).size == 164) "canonical calldata size changed"
  let (step, _) ← get (Solcore.Synthesis.Source.Aggregate.generatedFunction (Seed.ofNat 1)
    (448 - MalformedBytes.programOverhead))
  let some plan := MalformedBytes.CheckedPlan.ofStep? step | throw (IO.userError "the std wrapper failed admission")
  let some reference := LongBytes.CheckedPlan.ofStep? step | throw (IO.userError "the long-bytes wrapper failed admission")
  for (name, payload, malformation, expected) in cases do
    let tx := malformed payload malformation
    ensure (malformation.valid tx.payload (MalformedBytesExecution.canonicalBytes tx).size)
      s!"{name}: the malformation is outside its bounds"
    let history := MalformedBytesExecution.observe plan [tx] StorageExecution.fixtureBindings fuel
    checkExpected name reference (inputBytes tx) (← row history) expected fuel
  for (name, input, expected) in ordered do
    checkExpected name reference input (← runRaw plan.contract input fuel) expected fuel

end Tests.SourceMalformedBytesGolden
