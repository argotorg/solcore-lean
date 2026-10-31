import Solcore.ContractRuntime.CallChoiceExecution
import Solcore.Test.ContractCallChain

/-! Golden laws for the choice chain. A small parent chooses its own number of
calls: its call phase writes the input to slot 0 and, for the requested count
`r = (input >> 8) & 3`, finishes with the input when `r` is zero, and otherwise
requests a call with the input as argument, keeping the target, the input and
the calls made. One resume program follows every call: it writes the status
Word plus twice the data's size to slot `calls + 1`, then requests the next
call with `input + calls` while fewer than `r` calls are made, and otherwise
finishes with the data's first Word plus the calls made, or reverts with the
status Word under the input's bit 10. The child is the call chain test's
raw-outcome child: it writes its argument `x` to slot 0, counts its calls in
slot 1, and returns `(x >> 1) & 63` bytes of `x xor R1 ‖ x xor R2`, or reverts
with them when `x` is odd.

Zero to three calls follow from the input. Each phase reads only the latest
call's data, a child revert leaves the world of the phase that requested it, a
phase revert commits nothing, a request with no phase left stops the
transaction, and the parent's code and every balance stay as they were. The
call chain's parent runs alike through `ofChain`. -/

set_option autoImplicit false

namespace Tests.ContractCallChoice

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.CallChoiceExecution

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def firstRamp : Word := w 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
private def secondRamp : Word := w 0x2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40

private def parentAddress : Address := ⟨0x10, by decide⟩
private def childAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩
private def getSelector : Nat := 0x9507d39a

private def readInput (locals offset : Nat) : Expr :=
  .caseE (.apply (.var (HostFunction.inputDataWordBE?.index + locals)) (.word (w offset)))
    (.word Word.zero) (.var 0)

private def inputSize (locals : Nat) : Expr :=
  .apply (.var (HostFunction.inputDataSize.index + locals)) .unit

private def storageWrite (locals : Nat) (slot value : Expr) : Expr :=
  .apply (.var (HostFunction.storageWrite.index + locals)) (.pair slot value)

private def bitSet (value : Expr) (bit : Nat) : Expr :=
  .binary .wordEq (.binary .wordAnd value (.word (w bit))) (.word (w bit))

/-- The requested count, the input's bits 8 and 9. -/
private def requestedOf (input : Expr) : Expr :=
  .binary .wordAnd (.binary .wordShr input (.word (w 8))) (.word (w 3))

/-- A returned tuple of seven Words. -/
private def returned (first second third fourth fifth sixth seventh : Expr) : Expr :=
  .inLeft (.sum .word .word)
    (.pair first (.pair second (.pair third (.pair fourth (.pair fifth (.pair sixth seventh))))))

private def zero : Expr := .word Word.zero

/-- The call phase: target and input from the calldata, the input written to
slot 0, then a finish with the input or the first request. -/
def callProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 5).resultType
  body :=
    .letE (readInput 0 0)
      (.letE (readInput 1 32)
        (.letE (storageWrite 2 (.word (w 0)) (.var 0))
          (.letE (requestedOf (.var 1))
            (.ifE (.binary .wordEq (.var 0) zero)
              (returned zero (.var 2) zero zero zero zero zero)
              (returned (.word (w 1)) (.var 3) (.word (w getSelector)) (.var 2) (.var 3) (.var 2) zero)))))
}

theorem callProgram_checked : callProgram.checkHost = true := by
  decide

def callContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨callProgram, callProgram_checked⟩ 5 rfl

/-- The resume phase after every call: the kept target, input and calls made,
the status Word and the data from byte 128. -/
def resumeProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 5).resultType
  body :=
    .letE (inputSize 0)
      (.letE (readInput 1 0)
        (.letE (readInput 2 32)
          (.letE (readInput 3 64)
            (.letE (readInput 4 96)
              (.letE (readInput 5 128)
                (.letE (.binary .wordAdd (.var 2) (.word (w 1)))
                  (.letE (storageWrite 7 (.var 0)
                      (.binary .wordAdd (.var 2) (.binary .wordMul (.word (w 2)) (.binary .wordSub (.var 6) (.word (w 128))))))
                    (.letE (requestedOf (.var 5))
                      (.ifE (bitSet (.var 6) 1024)
                        (.inRight (CoreContractEntryProfile.wordTupleType 6) (.inLeft .word (.var 4)))
                        (.ifE (.binary .wordGt (.var 0) (.var 2))
                          (returned (.word (w 1)) (.var 7) (.word (w getSelector)) (.binary .wordAdd (.var 6) (.var 2))
                            (.var 7) (.var 6) (.var 2))
                          (returned zero (.binary .wordAdd (.var 3) (.var 2)) zero zero zero zero zero)))))))))))
}

theorem resumeProgram_checked : resumeProgram.checkHost = true := by
  decide

def resumeContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨resumeProgram, resumeProgram_checked⟩ 5 rfl

/-- The choosing parent with `count` resume phases, all the same program. -/
def choiceParent (count : Nat) : CallChoiceParent := {
  call := ⟨callContract, .choose⟩
  resumes := List.replicate count ⟨resumeContract, .choose⟩
  keptWords := 3
  call_entryProfile := rfl
  resumes_entryProfile := by
    intro phase member
    rw [List.eq_of_mem_replicate member]
    rfl
}

private def child : CheckedCoreContract := Tests.ContractCallChain.childContract

private def balanceOf (value : Nat) : Account → Account := fun account => account.withBalance (w value)

private def worldWith (code : CheckedHostCoreProgram) : WorldState :=
  WorldState.empty
    |>.putAccount callerAddress (balanceOf 9 Account.empty)
    |>.putAccount parentAddress (balanceOf 5 (Account.empty.withCode code))
    |>.putAccount childAddress (balanceOf 3 (Account.empty.withCode child.code))

private def initialWorld : WorldState := worldWith callContract.code

private def registry : CheckedContractRegistry := {
  lookup := fun address => if address = childAddress then some child else none }

private def input (value : Nat) : HostStorageDriver.InputData := {
  bytes := encodeWordBytesBE (addressToWord childAddress) ++ encodeWordBytesBE (w value)
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

private def choice (resumes value : Nat) : Result :=
  run registry (choiceParent resumes) initialWorld parentAddress callerAddress (input value) 4096

private def slot (world : WorldState) (address : Address) (index : Nat) : Word :=
  ((world.account? address).map fun account => account.storageRead (w index)).getD (w 0)

private def text (outcome : FrameOutcome Word) : String :=
  match outcome with
  | .returned bytes => encodeBytesText bytes
  | .reverted bytes => "revert:" ++ encodeBytesText bytes
  | .trapped reason => "trap:" ++ toString reason.val

/-- The outcome, the parent's slots 0 to 3, the child's slots 0 and 1, and each
call's argument, status and delivered bytes. -/
private def summary : Result → Option (String × List Word × List Word ×
    List (Word × CallResumeExecution.ChildStatus × String))
  | .completed outcome finalWorld calls =>
      some (text outcome, [0, 1, 2, 3].map (slot finalWorld parentAddress),
        [0, 1].map (slot finalWorld childAddress),
        calls.map fun call => (call.request.argument, call.child.status, encodeBytesText call.child.data))
  | _ => none

private def balancesAndCode (world : WorldState) (code : CheckedHostCoreProgram) : Result → Bool
  | .completed _ finalWorld _ =>
      [callerAddress, parentAddress, childAddress].all (fun address =>
        finalWorld.balance? address == world.balance? address) &&
      (match finalWorld.code? parentAddress with
        | some installed => installed.program == code.program
        | none => false)
  | _ => false

private def xorWord (left right : Word) : Word := w (left.val ^^^ right.val)

/-- The first `count` bytes of `x xor R1 ‖ x xor R2` as hexadecimal text. -/
private def childData (x count : Nat) : String :=
  encodeBytesText ((encodeWordBytesBE (xorWord (w x) firstRamp) ++
    encodeWordBytesBE (xorWord (w x) secondRamp)).extract 0 count)

private def wordText (value : Word) : String := encodeBytesText (encodeWordBytesBE value)

def testContractCallChoice : IO Unit := do
  -- A zero count finishes in the call phase without a call.
  ensure (summary (choice 3 4) == some (wordText (w 4), [w 4, w 0, w 0, w 0], [w 0, w 0], []))
    "a zero count made a call or did not finish with the input"
  -- One call: the resume phase reads its status and size, then finishes.
  ensure (summary (choice 3 260) == some (wordText (w 1), [w 260, w 5, w 0, w 0], [w 260, w 1],
      [(w 260, .returned, childData 260 2)]))
    "one call differs"
  -- Two calls, a return then a revert: the revert leaves the first call's world.
  ensure (summary (choice 3 516) == some (wordText (w 2), [w 516, w 5, w 4, w 0], [w 516, w 1],
      [(w 516, .returned, childData 516 2), (w 517, .reverted, childData 517 2)]))
    "a return then a revert differs"
  -- Three calls through the same resume program.
  ensure (summary (choice 3 772) == some (wordText (w 3), [w 772, w 5, w 4, w 7], [w 774, w 2],
      [(w 772, .returned, childData 772 2), (w 773, .reverted, childData 773 2),
        (w 774, .returned, childData 774 3)]))
    "three calls differ"
  -- A long call: the finishing phase reads that call's first Word.
  ensure (summary (choice 3 322) == some (wordText (w ((xorWord (w 322) firstRamp).val + 1)),
      [w 322, w 67, w 0, w 0], [w 322, w 1], [(w 322, .returned, childData 322 33)]))
    "a long call differs"
  -- A resume phase revert commits nothing.
  ensure (summary (choice 3 1284) == some ("revert:0x" ++ hexWord "1", [w 0, w 0, w 0, w 0], [w 0, w 0],
      [(w 1284, .returned, childData 1284 2)]))
    "a resume phase revert committed a phase"
  -- A request with no phase left stops the transaction.
  ensure ((match choice 2 772 with
    | .callLimit 2 => true
    | _ => false))
    "a third request without a third resume phase did not stop at call 2"
  ensure ((match choice 0 260 with
    | .callLimit 0 => true
    | _ => false))
    "a request without resume phases did not stop at call 0"
  -- Every balance and the parent's code stay as they were.
  for value in [4, 260, 516, 772, 322, 1284] do
    ensure (balancesAndCode initialWorld callContract.code (choice 3 value))
      s!"input {value} changed a balance or the parent's code"
  -- Fuel runs out in the call phase first, and a parent without its call phase
  -- installed does not run.
  ensure ((match run registry (choiceParent 3) initialWorld parentAddress callerAddress (input 260) 0 with
    | .outOfFuel .call => true
    | _ => false))
    "an exhausted call phase did not report its step"
  ensure ((match run registry (choiceParent 3) initialWorld childAddress callerAddress (input 260) 4096 with
    | .unresolved .call => true
    | _ => false))
    "a parent without its call phase ran"
  -- The call chain's parent runs alike as request phases and a finish phase.
  let chainWorld := worldWith Tests.ContractCallChain.callContract.code
  for value in [4, 5, 66, 63, 260, 516] do
    let viaChoice := run registry (ofChain Tests.ContractCallChain.parentContract) chainWorld parentAddress
      callerAddress (input value) 4096
    let viaChain := (CallChainExecution.run registry Tests.ContractCallChain.parentContract chainWorld parentAddress
      callerAddress (input value) 4096).toChoice
    ensure (summary viaChoice == summary viaChain && (summary viaChoice).isSome)
      s!"input {value}: the call chain through ofChain differs"
    ensure (balancesAndCode chainWorld Tests.ContractCallChain.callContract.code viaChoice)
      s!"input {value}: the call chain through ofChain changed a balance or the parent's code"

end Tests.ContractCallChoice
