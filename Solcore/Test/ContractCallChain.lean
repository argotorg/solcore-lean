import Solcore.ContractRuntime.CallChainExecution
import Solcore.Test.OneLevelNestedExecutionFixture

/-! Golden laws for the raw-outcome child convention and the call chain. Raw
return and revert data are the first bytes of the data Words up to the length
the length Word names, written out as hexadecimal text; a trap carries its
reason, wrong annotations do not decode, and a raw-outcome contract has no
one-Word view, so a word call to it is unavailable.

A small parent makes two calls through the chain: its call phase writes the
input to slot 0 and requests a call with the input as argument, keeping the
target and the input; a raw-outcome child writes its argument `x` to slot 0 and
counts its calls in slot 1, then returns `(x >> 1) & 63` bytes of
`x xor R1 ‖ x xor R2`, or reverts with them when `x` is odd; the middle phase
writes the status Word plus twice the data's size to slot 1 and requests a
call with `input + 3`, or reverts under the input's bit 8; the last phase
writes the same for the second call to slot 2 and returns the data's first
Word, or reverts with it under the input's bit 9. Each phase sees the latest
call's data only, a child revert leaves the world of the phase that requested
it, a phase revert commits nothing, and the parent's code and every balance
stay as they were. Without its middle phase the chain is the one-call
convention. -/

set_option autoImplicit false

namespace Tests.ContractCallChain

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.CallChainExecution

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def firstRamp : Word := w 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
private def secondRamp : Word := w 0x2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40

/-! Kernel-checked recognition facts. -/

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 1) (.sum (CoreContractEntryProfile.rawBytesType 1) .word)) =
      some (.rawOutcomeV1 1) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 2) (.sum (CoreContractEntryProfile.rawBytesType 2) .word)) =
      some (.rawOutcomeV1 2) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 1) (.sum (CoreContractEntryProfile.rawBytesType 2) .word)) =
      none := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (CoreContractEntryProfile.rawBytesType 1) (.sum .word .word)) =
      some (.rawBytesOutcomeV1 1) := rfl

example : (CoreContractEntryProfile.rawOutcomeV1 2).returnsOneWord = false := rfl

example (extraWords other : Nat) :
    (CoreContractEntryProfile.rawOutcomeV1 extraWords).resultType ≠
      (CoreContractEntryProfile.rawBytesOutcomeV1 other).resultType := by
  intro equal
  cases CoreContractEntryProfile.resultType_injective equal

private def rawValue (length first second : Word) : Value :=
  .pair .unit (.pair (.word length) (.pair (.word first) (.word second)))

private def rawErrors : Ty := .sum (CoreContractEntryProfile.rawBytesType 1) .word

private def returnedRaw (payload : Value) : Option (FrameOutcome Word) :=
  CoreContractEntryProfile.decode? (.rawOutcomeV1 1) (.inLeft rawErrors payload)

private def revertedRaw (payload : Value) : Option (FrameOutcome Word) :=
  CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
    (.inRight (CoreContractEntryProfile.rawBytesType 1) (.inLeft .word payload))

private def text (outcome : Option (FrameOutcome Word)) : Option String :=
  match outcome with
  | some (.returned bytes) => some (encodeBytesText bytes)
  | some (.reverted bytes) => some ("revert:" ++ encodeBytesText bytes)
  | _ => none

/-! The chained parent and the raw-outcome child. -/

private def parentAddress : Address := ⟨0x10, by decide⟩
private def childAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩
private def getSelector : Nat := 0x9507d39a

private def readInput (locals offset : Nat) : Expr :=
  .caseE (.apply (.var (HostFunction.inputDataWordBE?.index + locals)) (.word (w offset)))
    (.word Word.zero) (.var 0)

private def inputSize (locals : Nat) : Expr :=
  .apply (.var (HostFunction.inputDataSize.index + locals)) .unit

private def storageRead (locals slot : Nat) : Expr :=
  .apply (.var (HostFunction.storageRead.index + locals)) (.word (w slot))

private def storageWrite (locals slot : Nat) (value : Expr) : Expr :=
  .apply (.var (HostFunction.storageWrite.index + locals)) (.pair (.word (w slot)) value)

private def bitSet (value : Expr) (bit : Nat) : Expr :=
  .binary .wordEq (.binary .wordAnd value (.word (w bit))) (.word (w bit))

/-- The status Word plus twice the data's size after the two kept Words and the
status Word. -/
private def statusAndSize (status size : Expr) : Expr :=
  .binary .wordAdd status (.binary .wordMul (.word (w 2)) (.binary .wordSub size (.word (w 96))))

/-- The call phase: target and input from the calldata, the input written to
slot 0, then the request keeping the target and the input. -/
def callProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 3).resultType
  body :=
    .letE (readInput 0 0)
      (.letE (readInput 1 32)
        (.letE (storageWrite 2 0 (.var 0))
          (.inLeft (.sum .word .word)
            (.pair (.var 2) (.pair (.word (w getSelector)) (.pair (.var 1) (.pair (.var 2) (.var 1))))))))
}

theorem callProgram_checked : callProgram.checkHost = true := by
  decide

def callContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨callProgram, callProgram_checked⟩ 3 rfl

/-- The raw-outcome child: its argument to slot 0, its call count to slot 1,
then `(x >> 1) & 63` bytes of `x xor R1 ‖ x xor R2`, reverted for an odd `x`. -/
def childProgram : Program := {
  resultType := (CoreContractEntryProfile.rawOutcomeV1 1).resultType
  body :=
    .letE (readInput 0 4)
      (.letE (storageWrite 1 0 (.var 0))
        (.letE (storageWrite 2 1 (.binary .wordAdd (storageRead 2 1) (.word (w 1))))
          (.letE (.binary .wordAnd (.binary .wordShr (.var 2) (.word (w 1))) (.word (w 63)))
            (.ifE (bitSet (.var 3) 1)
              (.inRight (CoreContractEntryProfile.rawBytesType 1) (.inLeft .word
                (.pair .unit (.pair (.var 0) (.pair (.binary .wordXor (.var 3) (.word firstRamp))
                  (.binary .wordXor (.var 3) (.word secondRamp)))))))
              (.inLeft rawErrors
                (.pair .unit (.pair (.var 0) (.pair (.binary .wordXor (.var 3) (.word firstRamp))
                  (.binary .wordXor (.var 3) (.word secondRamp))))))))))
}

theorem childProgram_checked : childProgram.checkHost = true := by
  decide

def childContract : CheckedCoreContract :=
  CheckedCoreContract.rawOutcomeV1 ⟨childProgram, childProgram_checked⟩ 1 rfl

/-- The middle phase: the status and size of the first call to slot 1, then the
request for `input + 3`, or a revert with the status Word under bit 8. -/
def middleProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 3).resultType
  body :=
    .letE (inputSize 0)
      (.letE (readInput 1 0)
        (.letE (readInput 2 32)
          (.letE (readInput 3 64)
            (.letE (storageWrite 4 1 (statusAndSize (.var 0) (.var 3)))
              (.ifE (bitSet (.var 2) 256)
                (.inRight (CoreContractEntryProfile.wordTupleType 4) (.inLeft .word (.var 1)))
                (.inLeft (.sum .word .word)
                  (.pair (.var 3) (.pair (.word (w getSelector))
                    (.pair (.binary .wordAdd (.var 2) (.word (w 3))) (.pair (.var 3) (.var 2)))))))))))
}

theorem middleProgram_checked : middleProgram.checkHost = true := by
  decide

def middleContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨middleProgram, middleProgram_checked⟩ 3 rfl

/-- The last phase: the status and size of the second call to slot 2, then its
data's first Word, reverted under bit 9. -/
def lastProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE (inputSize 0)
      (.letE (readInput 1 32)
        (.letE (readInput 2 64)
          (.letE (readInput 3 96)
            (.letE (storageWrite 4 2 (statusAndSize (.var 1) (.var 3)))
              (.ifE (bitSet (.var 3) 512)
                (.inRight .word (.inLeft .word (.var 1)))
                (.inLeft (.sum .word .word) (.var 1)))))))
}

theorem lastProgram_checked : lastProgram.checkHost = true := by
  decide

def lastContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 ⟨lastProgram, lastProgram_checked⟩ rfl

def parentContract : CallChainParent := {
  call := callContract
  middles := [middleContract]
  last := lastContract
  keptWords := 2
  call_entryProfile := rfl
  middles_entryProfile := by simp [middleContract, CheckedCoreContract.wordTupleOutcomeV1]
  last_entryProfile := rfl
}

/-- The same call and last phases as a one-call parent. -/
def oneCallParent : CallResumeParent := {
  call := callContract
  resume := lastContract
  keptWords := 2
  call_entryProfile := rfl
  resume_entryProfile := rfl
}

private def balanceOf (value : Nat) : Account → Account := fun account => account.withBalance (w value)

private def initialWorld : WorldState :=
  WorldState.empty
    |>.putAccount callerAddress (balanceOf 9 Account.empty)
    |>.putAccount parentAddress (balanceOf 5 (Account.empty.withCode callContract.code))
    |>.putAccount childAddress (balanceOf 3 (Account.empty.withCode childContract.code))

private def registry : CheckedContractRegistry := {
  lookup := fun address => if address = childAddress then some childContract else none }

private def input (value : Nat) : HostStorageDriver.InputData := {
  bytes := encodeWordBytesBE (addressToWord childAddress) ++ encodeWordBytesBE (w value)
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

private def chain (value : Nat) : Result :=
  CallChainExecution.run registry parentContract initialWorld parentAddress callerAddress (input value) 4096

private def slot (world : WorldState) (address : Address) (index : Nat) : Word :=
  ((world.account? address).map fun account => account.storageRead (w index)).getD (w 0)

/-- The outcome, the parent's slots 0 to 2, the child's slots 0 and 1, and each
call's argument, status and delivered bytes. -/
private def summary : Result → Option (Option String × List Word × List Word ×
    List (Word × CallResumeExecution.ChildStatus × String))
  | .completed outcome finalWorld calls =>
      some (text (some outcome), [0, 1, 2].map (slot finalWorld parentAddress),
        [0, 1].map (slot finalWorld childAddress),
        calls.map fun call => (call.request.argument, call.child.status, encodeBytesText call.child.data))
  | _ => none

private def balancesAndCode : Result → Bool
  | .completed _ finalWorld _ =>
      [callerAddress, parentAddress, childAddress].all (fun address =>
        finalWorld.balance? address == initialWorld.balance? address) &&
      (match finalWorld.code? parentAddress with
        | some code => code.program == callContract.code.program
        | none => false)
  | _ => false

private def xorWord (left right : Word) : Word := w (left.val ^^^ right.val)

/-- The first `count` bytes of `x xor R1 ‖ x xor R2` as hexadecimal text. -/
private def childData (x count : Nat) : String :=
  encodeBytesText ((encodeWordBytesBE (xorWord (w x) firstRamp) ++
    encodeWordBytesBE (xorWord (w x) secondRamp)).extract 0 count)

def testContractCallChain : IO Unit := do
  -- Raw return and revert data are exactly the named bytes, with no padding.
  ensure (text (returnedRaw (rawValue (w 0) firstRamp secondRamp)) == some "0x")
    "a zero length did not return empty data"
  ensure (text (revertedRaw (rawValue (w 0) firstRamp secondRamp)) == some "revert:0x")
    "a zero length did not revert with empty data"
  ensure (text (revertedRaw (rawValue (w 1) firstRamp secondRamp)) == some "revert:0x01")
    "a one-byte revert differs from its byte"
  ensure (text (revertedRaw (rawValue (w 33) firstRamp secondRamp)) ==
      some "revert:0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021")
    "a 33-byte revert differs from its bytes"
  ensure (text (returnedRaw (rawValue (w 64) firstRamp secondRamp)) ==
      some ("0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" ++
        "2122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40"))
    "a 64-byte return differs from its two Words"
  ensure (text (revertedRaw (rawValue (w (2 ^ 256 - 1)) firstRamp secondRamp)) ==
      text (revertedRaw (rawValue (w ((2 ^ 256 - 1) % 65)) firstRamp secondRamp)))
    "the largest length Word does not name its residue in a revert"
  ensure (CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
      (.inRight (CoreContractEntryProfile.rawBytesType 1)
        (.inRight (CoreContractEntryProfile.rawBytesType 1) (.word (w 7)))) == some (.trapped (w 7)))
    "a raw-outcome trap differs from its reason"
  -- Wrong annotations and payloads do not decode.
  ensure (CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
      (.inLeft (.sum .word .word) (rawValue (w 1) firstRamp secondRamp))).isNone
    "a return with the one-Word revert annotation decoded"
  ensure (CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
      (.inRight (CoreContractEntryProfile.rawBytesType 2) (.inLeft .word (rawValue (w 1) firstRamp secondRamp)))).isNone
    "a revert with another capacity's annotation decoded"
  ensure (CoreContractEntryProfile.decode? (.rawOutcomeV1 1)
      (.inRight (CoreContractEntryProfile.rawBytesType 1)
        (.inRight .word (.word (w 7))))).isNone
    "a trap with the one-Word revert annotation decoded"
  ensure (revertedRaw (.word (w 1))).isNone
    "a one-Word revert decoded as raw bytes"
  ensure (CoreContractEntryProfile.decodeWordOutcome? (.rawOutcomeV1 1)
      (.inLeft rawErrors (rawValue (w 1) firstRamp secondRamp))).isNone
    "a raw-outcome value has a one-Word view"
  ensure ((CheckedCoreContract.ofCode? childContract.code).map (·.entryProfile) == some (.rawOutcomeV1 1))
    "admission does not recognize the raw-outcome convention"
  -- A word call to a registered raw-outcome contract is unavailable.
  ensure ((match (OneLevelNestedExecutionFixture.runScenario
      (OneLevelNestedExecutionFixture.rootContract .commit OneLevelNestedExecutionFixture.childTargetWord)
      childContract 512).view with
    | .completed terminal => some terminal.outcome
    | .outOfFuel _ _ _ => none) == some (.trapped ContractCallFailure.unavailable.code))
    "a word call reached a raw-outcome contract"
  -- A returned call commits and a reverted one leaves the world its
  -- requesting phase left; each phase reads only the latest call's data.
  ensure (summary (chain 4) == some (some ("0x" ++ hexWord "0"), [w 4, w 5, w 6], [w 4, w 1],
      [(w 4, .returned, childData 4 2), (w 7, .reverted, childData 7 3)]))
    "a return then a revert differs"
  ensure (summary (chain 5) == some (some ("0x" ++ hexWord "0"), [w 5, w 4, w 9], [w 8, w 1],
      [(w 5, .reverted, childData 5 2), (w 8, .returned, childData 8 4)]))
    "a revert then a return differs"
  -- A long first call: the last phase reads the second call's first Word, not the first's.
  ensure (summary (chain 66) == some (some (encodeBytesText (encodeWordBytesBE (xorWord (w 69) firstRamp))),
      [w 66, w 67, w 68], [w 66, w 1], [(w 66, .returned, childData 66 33), (w 69, .reverted, childData 69 34)]))
    "a long return then a long revert differs"
  ensure (summary (chain 63) == some (some (encodeBytesText (encodeWordBytesBE (xorWord (w 66) firstRamp))),
      [w 63, w 62, w 67], [w 66, w 1], [(w 63, .reverted, childData 63 31), (w 66, .returned, childData 66 33)]))
    "a short revert then a long return differs"
  -- A middle or last phase revert commits nothing.
  ensure (summary (chain (4 + 256)) == some (some ("revert:0x" ++ hexWord "1"), [w 0, w 0, w 0], [w 0, w 0],
      [(w 260, .returned, childData 260 2)]))
    "a middle phase revert committed a phase or made a second call"
  ensure (summary (chain (4 + 512)) == some (some ("revert:0x" ++ hexWord "0"), [w 0, w 0, w 0], [w 0, w 0],
      [(w 516, .returned, childData 516 2), (w 519, .reverted, childData 519 3)]))
    "a last phase revert committed a phase"
  -- Every balance and the parent's code stay as they were.
  for value in [4, 5, 66, 63, 260, 516] do
    ensure (balancesAndCode (chain value)) s!"input {value} changed a balance or the parent's code"
  -- Without the middle phase the chain is the one-call convention.
  for value in [4, 5, 66, 516] do
    let chained := CallChainExecution.run registry (ofCallResume oneCallParent) initialWorld parentAddress
      callerAddress (input value) 4096
    let single := CallResumeExecution.run registry oneCallParent initialWorld parentAddress callerAddress
      (input value) 4096
    ensure ((match chained.toCallResume, single with
      | .completed outcome finalWorld request child, .completed outcome' finalWorld' request' child' =>
          outcome == outcome' && [0, 1, 2].all (fun index => slot finalWorld parentAddress index ==
            slot finalWorld' parentAddress index) && request.map (·.argument) == request'.map (·.argument) &&
            child.map (fun child => (child.status, encodeBytesText child.data)) ==
              child'.map (fun child => (child.status, encodeBytesText child.data))
      | _, _ => false))
      s!"input {value}: the chain without middle phases differs from the one-call convention"
  -- A parent whose call phase is not installed does not run, and fuel runs out
  -- in the call phase first.
  ensure ((match CallChainExecution.run registry parentContract initialWorld childAddress callerAddress
      (input 4) 4096 with
    | .unresolved .call => true
    | _ => false))
    "a parent without its call phase ran"
  ensure ((match CallChainExecution.run registry parentContract initialWorld parentAddress callerAddress
      (input 4) 0 with
    | .outOfFuel .call => true
    | _ => false))
    "an exhausted call phase did not report its step"

end Tests.ContractCallChain
