import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Core.NestedArray
import Solcore.Synthesis.Stateful.MalformedNestedArrayExecution

/-! Golden cases for the std model behind the malformed-nested-array profile.
The expected outcome of every case is written out from the pinned std's
`dispatch.sol` and `std.sol`, not computed by either model: a rejection
reverts with its error selector as a Word and keeps the empty storage; an
accepted malformation behaves exactly like the canonical nested-array contract
on the Words std decodes. Both the Core wrapper and the byte-level `stdDecode`
must give that outcome. Cases on four rows check std's lazy row checks, and
cases with two defects check its decode order. -/
set_option autoImplicit false

namespace Tests.SourceMalformedNestedArrayGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.MalformedNestedArrayExecution (Malformation Transaction inputBytes stdRejection?)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The expected std outcome: the rejecting selector, or acceptance with the
decoded flags, outer length and the elements of every row the body reads. -/
private inductive Expected where
  | rejected (selector : Nat)
  | accepted (flags rows : Nat) (read : List (List Nat))

private def noSelector : Expected := .rejected StdDispatch.noSelectorError
private def truncated : Expected := .rejected StdDispatch.truncatedError

/-- Three rows, flags 2 (even, so the body returns). The calldata is 388
bytes: the head, the outer length 3 at byte 68, the table at 100 with the
Words 96, 192 and 256, then row zero at 196 (length 2, elements 1 and 4 at 228
and 260), row one at 292 (length 1, element 9 at 324) and the empty row two at
356. -/
private def three : List (List Nat) := [[1, 4], [9], []]
/-- Two rows: the table Words 64 and 160, row zero at 164, row one at 260; 324 bytes. -/
private def two : List (List Nat) := [[1, 4], [9]]
/-- Four rows: the table Words 128, 192, 224 and 352, row zero at 228 (length
1, element 3), the empty row one at 292, row two at 324 (length 3, elements 7,
1 and 0 at 356, 388 and 420) and row three at 452 (length 1, element 1 at
484); 516 bytes. The body never reads row three or row two's third element. -/
private def four : List (List Nat) := [[3], [], [7, 1, 0], [1]]

private def malformed (values : List (List Nat)) (malformation : Malformation) : Transaction :=
  ⟨"tx-0", w 2, values.map (·.map w), malformation⟩

private def cases : List (String × List (List Nat) × Malformation × Expected) := [
  ("canonical", three, .none, .accepted 2 3 three),
  ("short-0", three, .short 0, noSelector), ("short-1", three, .short 1, noSelector),
  ("short-3", three, .short 3, noSelector),
  ("wrong-selector-low", three, .selector 1, noSelector),
  ("wrong-selector-high", three, .selector (2 ^ 31), noSelector),
  ("wrong-selector-all", three, .selector (2 ^ 32 - 1), noSelector),
  ("truncated-selector-only", three, .truncate 4, truncated),
  ("truncated-head", three, .truncate 67, truncated),
  -- 31 bytes remain at 4 + 64.
  ("truncated-outer-length", three, .truncate 99, truncated),
  -- The table needs 96 bytes at 100; 16 remain.
  ("truncated-table", three, .truncate 116, truncated),
  -- Row zero's elements need 64 bytes at 228; 63 remain.
  ("truncated-first-row", three, .truncate 291, truncated),
  -- Row two's length Word at 356 has 31 bytes.
  ("truncated-last-row", three, .truncate 387, truncated),
  ("trailing-1-zero", three, .trailing 1 0, .accepted 2 3 three),
  ("trailing-33-ones", three, .trailing 33 1, .accepted 2 3 three),
  ("trailing-64-ramp", three, .trailing 64 2, .accepted 2 3 three),
  ("offset-past-end", three, .offset (w 385), truncated),
  ("offset-partial-length", three, .offset (w 353), truncated),
  ("offset-high-bit", three, .offset (w (2 ^ 255)), truncated),
  ("offset-wraps", three, .offset (w (2 ^ 256 - 4)), truncated),
  -- Offset 0: the outer length is the flags Word, 2, and the table starts at
  -- 36. Its first Word, the offset 0 itself, makes row zero start at 36 with
  -- length 0. Its second Word, the original outer length 3, makes row one
  -- start at 39, where the Word holds bytes 39 to 70, all zero.
  ("offset-overlaps-flags", three, .offset (w 0), .accepted 2 2 [[], []]),
  -- Offset 32: the outer length is the offset Word, 32, and a 1,024-byte table does not fit.
  ("offset-overlaps-itself", three, .offset (w 32), truncated),
  -- A fourth table Word, row zero's length 2, which the body never reads.
  ("length-unread-extra-row", three, .length (w 4), .accepted 2 4 three),
  ("length-above-max", three, .length (w (2 ^ 251)), truncated),
  -- 32 * (2^251 + 1) wraps to 32 in Word arithmetic; std's bound check rejects first.
  ("length-product-wraps", three, .length (w (2 ^ 251 + 1)), truncated),
  ("length-maximum", three, .length (w (2 ^ 256 - 1)), truncated),
  ("length-one-shorter", three, .length (w 2), .accepted 2 2 two),
  ("length-zero", three, .length (w 0), .accepted 2 0 []),
  -- A third table Word, row zero's length 2, which the body reads: row two
  -- starts at 102, where the Word holds the low bytes of the table Word 64
  -- and is 64 * 2^16, far too long.
  ("length-read-extra-row", two, .length (w 3), truncated),
  -- 289 > size - T = 288.
  ("row-offset-past-end", three, .rowOffset 1 (w 289), truncated),
  -- 288 is in range, but no length Word remains at 388.
  ("row-offset-at-end", three, .rowOffset 1 (w 288), truncated),
  ("row-offset-partial-length", three, .rowOffset 1 (w 257), truncated),
  ("row-offset-high-bit", three, .rowOffset 1 (w (2 ^ 255)), truncated),
  -- T + r would wrap onto the outer length Word at 68.
  ("row-offset-wraps-onto-outer-length", three, .rowOffset 1 (w (2 ^ 256 - 32)), truncated),
  ("row-offset-maximum", three, .rowOffset 1 (w (2 ^ 256 - 1)), truncated),
  -- Row zero starts at its own table Word, now 0, and is empty.
  ("row-offset-own-entry", three, .rowOffset 0 (w 0), .accepted 2 3 [[], [9], []]),
  -- Row one starts at the table: its length is the table Word 96, which does not fit.
  ("row-offset-into-table", three, .rowOffset 1 (w 0), truncated),
  ("row-offset-aliases-row", three, .rowOffset 1 (w 96), .accepted 2 3 [[1, 4], [1, 4], []]),
  -- Row one starts at row zero's first element, 1, so its element is row zero's second, 4.
  ("row-offset-inside-row", three, .rowOffset 1 (w 128), .accepted 2 3 [[1, 4], [4], []]),
  -- Row zero runs into row one's length Word.
  ("row-length-one-too-long", three, .rowLength 0 (w 3), .accepted 2 3 [[1, 4, 1], [9], []]),
  ("row-length-most-that-fits", three, .rowLength 0 (w 5), .accepted 2 3 [[1, 4, 1, 9, 0], [9], []]),
  ("row-length-one-past-fit", three, .rowLength 0 (w 6), truncated),
  ("row-length-last-row", three, .rowLength 2 (w 1), truncated),
  ("row-length-above-max", three, .rowLength 1 (w (2 ^ 251)), truncated),
  ("row-length-product-wraps", three, .rowLength 1 (w (2 ^ 251 + 1)), truncated),
  ("row-length-maximum", three, .rowLength 1 (w (2 ^ 256 - 1)), truncated),
  ("row-length-one-shorter", three, .rowLength 0 (w 1), .accepted 2 3 [[1], [9], []]),
  ("row-length-zero", three, .rowLength 0 (w 0), .accepted 2 3 [[], [9], []]),
  -- Lazy checks on four rows.
  ("four-rows", four, .none, .accepted 2 4 (four.take 3)),
  ("unread-row-offset", four, .rowOffset 3 (w (2 ^ 256 - 1)), .accepted 2 4 (four.take 3)),
  ("unread-row-length", four, .rowLength 3 (w (2 ^ 256 - 1)), .accepted 2 4 (four.take 3)),
  ("cut-inside-unread-row", four, .truncate 515, .accepted 2 4 (four.take 3)),
  ("cut-unread-row-length", four, .truncate 468, .accepted 2 4 (four.take 3)),
  -- The table is checked whole, including row three's Word.
  ("cut-inside-table", four, .truncate 212, truncated),
  -- Row two's region is checked whole, including the third element the body skips.
  ("cut-skipped-element", four, .truncate 451, truncated),
  ("row-length-into-unread-row", four, .rowLength 2 (w 4), .accepted 2 4 [[3], [], [7, 1, 0, 1]]),
  -- Row one is checked after row zero has been folded and written; nothing commits.
  ("second-row-after-first", four, .rowOffset 1 (w (2 ^ 256 - 32)), truncated)]

/-- Raw calldata with two defects at once, for the decode order. -/
private def bytes (parts : List Nat) : ByteArray := ByteArray.mk (parts.map Nat.toUInt8).toArray

private def selectorBytes (selector : Nat) : List Nat :=
  [selector / 2 ^ 24 % 256, selector / 2 ^ 16 % 256, selector / 2 ^ 8 % 256, selector % 256]

private def wordBytes (value : Nat) : List Nat := (encodeWordBytesBE (w value)).data.toList.map UInt8.toNat

private def canonical (values : List (List Nat)) : ByteArray :=
  NestedArrayExecution.inputBytes (w 2) (values.map (·.map w))

private def replaced (input : ByteArray) (changes : List (Nat × Nat)) : ByteArray :=
  changes.foldl (fun bytes (position, value) => StdCalldata.replaceWord bytes position (w value)) input

private def ordered : List (String × ByteArray × Expected) := [
  -- A wrong selector wins over a malformed row: dispatch fails first.
  ("wrong-selector-and-bad-row",
    replaced ((StdCalldata.Change.selector 1).apply (canonical three)) [(132, 2 ^ 256 - 1)], noSelector),
  -- Three bytes of the right selector are still short calldata.
  ("three-selector-bytes", bytes ((selectorBytes MalformedNestedArray.selector).take 3), noSelector),
  -- A truncated head wins over a bad offset in the bytes that are present.
  ("short-head-and-bad-offset", bytes (selectorBytes MalformedNestedArray.selector ++ wordBytes 2 ++
    (wordBytes (2 ^ 256 - 4)).take 31), truncated),
  -- A wrapping head offset and a wrapping row offset: the outer array is checked first.
  ("bad-offset-and-row", replaced (canonical three) [(36, 2 ^ 256 - 4), (132, 2 ^ 256 - 1)], truncated),
  -- An outer length of 2 leaves row two unread, so its maximal length is never checked.
  ("row-unread-by-length", replaced (canonical three) [(68, 2), (356, 2 ^ 256 - 1)], .accepted 2 2 two),
  -- Row zero overlaps its own table Word and is accepted; row one is then rejected.
  ("accepted-row-then-bad-row", replaced (canonical three) [(100, 0), (132, 2 ^ 256 - 32)], truncated),
  -- The dynamic-array selector with a canonical nested body is no match.
  ("other-selector-canonical-body",
    bytes (selectorBytes 0x9a94c44b) ++ (canonical three).extract 4 (canonical three).size, noSelector)]

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
          | some account => NestedArrayExecution.storageJson account
          | none => Json.null
        let fields := match terminal.outcome with
          | .returned output => [("status", toJson "returned"), ("output", toJson (encodeBytesText output))]
          | .reverted output => [("status", toJson "reverted"), ("output", toJson (encodeBytesText output))]
          | .trapped _ => [("status", toJson "trapped")]
        return Json.mkObj (fields ++ [("committedStorage", storage),
          ("accountStorage", AccountStorage.contractJson terminal.finalWorld bindings.address)])
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "golden case exhausted fuel")
  else throw (IO.userError "golden input exceeds a Word")

private def checkExpected (name : String) (canonical : NestedArray.CheckedPlan)
    (input : ByteArray) (outcome : Json) (expected : Expected) (fuel : Nat) : IO Unit := do
  match expected with
  | .rejected selector =>
      ensure (stdRejection? input == some selector) s!"{name}: the byte model does not reject with {selector}"
      ensure ((← get (outcome.getObjValAs? String "status")) == "reverted" &&
        (← get (outcome.getObjValAs? String "output")) == selectorOutput selector)
        s!"{name}: original Core does not revert with the std selector"
      -- Nothing commits: storage stays empty.
      let empty := NestedArrayExecution.observe canonical [] StorageExecution.fixtureBindings fuel
      ensure ((outcome.getObjVal? "committedStorage").toOption == (empty.getObjVal? "initialStorage").toOption &&
        (outcome.getObjVal? "accountStorage").toOption == (empty.getObjVal? "initialAccountStorage").toOption)
        s!"{name}: a std rejection changed storage"
  | .accepted flags rows read =>
      ensure (stdRejection? input == none) s!"{name}: the byte model rejects an accepted malformation"
      ensure (MalformedNestedArrayExecution.stdDecoded? input == some (flags, rows, read))
        s!"{name}: the byte model decodes other Words"
      -- The canonical nested-array contract on the decoded Words is the reference
      -- for the body. Rows past the third are never read, so they stay empty.
      let values : List (List Word) := (read ++ List.replicate (rows - read.length) ([] : List Nat)).map (·.map w)
      let reference := NestedArrayExecution.observe canonical [⟨"tx-0", w flags, values⟩]
        StorageExecution.fixtureBindings fuel
      let referenceRow ← row reference
      for key in ["status", "output", "committedStorage", "accountStorage"] do
        ensure ((outcome.getObjVal? key).toOption == (referenceRow.getObjVal? key).toOption)
          s!"{name}: {key} differs from the canonical contract on the decoded Words"

def testSourceMalformedNestedArrayGolden : IO Unit := do
  let fuel := 1000000
  ensure (MalformedNestedArray.selector == 0x7095aff8) "the profile selector is not run(uint256,uint256[][])"
  for (values, size) in [(three, 388), (two, 324), (four, 516)] do
    ensure ((canonical values).size == size) "canonical calldata size changed"
  ensure (MalformedNestedArrayExecution.rowStart (four.map (·.map w)) 3 == 452) "row positions changed"
  let (step, _) ← get (Solcore.Synthesis.Source.Aggregate.generatedFunction (Seed.ofNat 1)
    (448 - MalformedNestedArray.programOverhead))
  let some plan := MalformedNestedArray.CheckedPlan.ofStep? step | throw (IO.userError "the std wrapper failed admission")
  let some reference := NestedArray.CheckedPlan.ofStep? step | throw (IO.userError "the nested-array wrapper failed admission")
  for (name, values, malformation, expected) in cases do
    let tx := malformed values malformation
    ensure (malformation.valid tx.values (MalformedNestedArrayExecution.canonicalBytes tx).size)
      s!"{name}: the malformation is outside its bounds"
    let history := MalformedNestedArrayExecution.observe plan [tx] StorageExecution.fixtureBindings fuel
    checkExpected name reference (inputBytes tx) (← row history) expected fuel
  for (name, input, expected) in ordered do
    checkExpected name reference input (← runRaw plan.contract input fuel) expected fuel

end Tests.SourceMalformedNestedArrayGolden
