import Solcore.ContractRuntime.CheckedCoreWordOutcome
import Solcore.Test.Adr0148NestedCreationLifecycleFixture
import Solcore.Test.OneLevelNestedExecutionFixture

/-! Golden laws for the static Word-tuple entry convention. The expected return
data is written out by hand as hexadecimal text: a returned tuple of two, three
or four Words is the concatenation of their 32-byte big-endian encodings, a
revert carries one Word and a trap its reason. Wrong annotations, arities and
payloads do not decode, a tuple has no one-Word view, and the nested executor
treats a registered tuple contract as unavailable to a word call and a template
with a tuple initializer as unavailable to creation, while a tuple root
returns its whole tuple. -/

set_option autoImplicit false

namespace Tests.ContractTupleEntryProfile

open Solcore.Core
open Solcore.ContractRuntime
open Tests.OneLevelNestedExecutionFixture

/-! Kernel-checked recognition and typing facts. -/

example : (CoreContractEntryProfile.wordTupleOutcomeV1 0).resultType =
    .sum (.product .word .word) (.sum .word .word) := rfl

example : (CoreContractEntryProfile.wordTupleOutcomeV1 2).resultType =
    .sum (.product .word (.product .word (.product .word .word))) (.sum .word .word) := rfl

example : CoreContractEntryProfile.ofResultType?
    (.sum (.product .word (.product .word .word)) (.sum .word .word)) =
      some (.wordTupleOutcomeV1 1) := rfl

example : CoreContractEntryProfile.ofResultType? (.sum .word (.sum .word .word)) =
    some .wordOutcomeV1 := rfl

example : CoreContractEntryProfile.ofResultType? (.sum (.product .word .bool) (.sum .word .word)) =
    none := rfl

example : CoreContractEntryProfile.ofResultType? (.sum (.product (.product .word .word) .word)
    (.sum .word .word)) = none := rfl

example : CoreContractEntryProfile.ofResultType? (.product .word .word) = none := rfl

example : (CoreContractEntryProfile.wordTupleOutcomeV1 1).returnsOneWord = false := rfl

example (extraWords : Nat) :
    CoreContractEntryProfile.ofResultType?
        (CoreContractEntryProfile.wordTupleOutcomeV1 extraWords).resultType =
      some (.wordTupleOutcomeV1 extraWords) :=
  CoreContractEntryProfile.ofResultType?_resultType _

example (left right : Nat) (equal :
    (CoreContractEntryProfile.wordTupleOutcomeV1 left).resultType =
      (CoreContractEntryProfile.wordTupleOutcomeV1 right).resultType) : left = right := by
  have profiles := CoreContractEntryProfile.resultType_injective equal
  cases profiles
  rfl

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- One Word's 64 hexadecimal digits, written as the digits after a run of zeros. -/
private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def tupleValue : List Word → Value
  | [] => .unit
  | [last] => .word last
  | head :: rest => .pair (.word head) (tupleValue rest)

private def returned (extraWords : Nat) (words : List Word) :
    Option (FrameOutcome Word) :=
  CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 extraWords)
    (.inLeft (.sum .word .word) (tupleValue words))

private def returnedText (outcome : Option (FrameOutcome Word)) : Option String :=
  match outcome with
  | some (.returned bytes) => some (encodeBytesText bytes)
  | _ => none

/-- A registered child whose convention returns two Words, after writing the
child slot. -/
def tupleChildProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 0).resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word childSlot) (.word childNewValue)))
      (.inLeft (.sum .word .word) (.pair (.word childPayload) (.word childNewValue)))
}

theorem tupleChildProgram_checked : tupleChildProgram.checkHost = true := by
  decide

def tupleChildContract : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1
    ⟨tupleChildProgram, tupleChildProgram_checked⟩ 0 rfl

/-- A creation template whose initializer returns two Words. -/
def tupleInitializerProgram : Program := {
  resultType := (CoreContractEntryProfile.wordTupleOutcomeV1 0).resultType
  body := .inLeft (.sum .word .word)
    (.pair (.word Adr0148CheckedCreationPreflightFixture.initializerPayload)
      (.word Adr0148CheckedCreationPreflightFixture.initializerPayload))
}

theorem tupleInitializerProgram_checked : tupleInitializerProgram.checkHost = true := by
  decide

def tupleInitializer : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1
    ⟨tupleInitializerProgram, tupleInitializerProgram_checked⟩ 0 rfl

/-- The preflight fixture's environment with the tuple initializer in its template. -/
def tupleTemplateEnvironment : ExecutionEnvironment := {
  callRegistry := Adr0148CheckedCreationPreflightFixture.validCallRegistry
  creationTemplates := {
    lookup := fun identifier =>
      if identifier = Adr0148CheckedCreationPreflightFixture.templateId then
        some { initializer := tupleInitializer, runtime := Adr0148CheckedCreationPreflightFixture.runtime }
      else none }
  creationAddressPolicy := Adr0148CheckedCreationPreflightFixture.addressPolicy
}

private def completionFuel : Nat := 512

/-- The creating root's outcome, and the working creator nonce and created
account when it halts. -/
private def creationAt (environment : ExecutionEnvironment) :
    Option (FrameHaltKind × FrameOutcome Word × Option Word × Bool) :=
  match (OneLevelNestedExecution.runWithEnvironment Adr0148NestedCreationLifecycleFixture.rootContract
      Adr0148NestedCreationLifecycleFixture.rootInvocation Adr0148NestedCreationLifecycleFixture.rootInstalled
      environment completionFuel).view with
  | .completed terminal =>
      let working := terminal.terminalContext.context.values.working.1
      some (terminal.outcome.kind, terminal.outcome,
        working.nonce? Adr0148CheckedCreationPreflightFixture.creator,
        (working.account? Adr0148CheckedCreationPreflightFixture.created).isSome)
  | .outOfFuel _ _ _ => none

private def childAt {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : OneLevelNestedExecution.Result initialWorld root invocation) :
    Option (FrameOutcome Word × Option Word × Option Word) :=
  match result.view with
  | .completed terminal =>
      some (terminal.outcome, childStorageValue? terminal.terminalContext.context.values.working.1,
        childStorageValue? terminal.finalWorld)
  | .outOfFuel _ _ _ => none

def testContractTupleEntryProfile : IO Unit := do
  -- Returned tuples of two, three and four Words, including both extremes.
  ensure (returnedText (returned 0 [w 1, w 2]) ==
      some ("0x" ++ hexWord "1" ++ hexWord "2"))
    "a returned pair differs from its two concatenated Words"
  ensure (returnedText (returned 1 [w 0, w (2 ^ 255), w (2 ^ 256 - 1)]) ==
      some ("0x" ++ hexWord "" ++ hexWord ("8" ++ String.ofList (List.replicate 63 '0')) ++
        String.ofList (List.replicate 64 'f')))
    "a returned triple differs from its three concatenated Words"
  ensure (returnedText (returned 2 [w 0x11, w 0x2222, w 0x333333, w 0x44444444]) ==
      some ("0x" ++ hexWord "11" ++ hexWord "2222" ++ hexWord "333333" ++ hexWord "44444444"))
    "a returned quadruple differs from its four concatenated Words"
  -- The decoded size is exactly 32 bytes per Word.
  for (extraWords, words) in [(0, [w 5, w 6]), (1, [w 5, w 6, w 7]), (2, [w 5, w 6, w 7, w 8])] do
    match returned extraWords words with
    | some (.returned bytes) => ensure (bytes.size == 32 * (extraWords + 2)) "a tuple has the wrong size"
    | _ => throw (IO.userError "a well-typed tuple did not decode")
  -- Revert and trap carry one Word, under the exact tuple annotation.
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 1)
      (.inRight (.product .word (.product .word .word)) (.inLeft .word (.word (w 0x99)))) ==
        some (.reverted (encodeWordBytesBE (w 0x99))))
    "a tuple revert differs from its one Word"
  ensure ((match CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 1)
      (.inRight (.product .word (.product .word .word)) (.inLeft .word (.word (w 0x99)))) with
    | some (.reverted bytes) => some (encodeBytesText bytes)
    | _ => none) == some ("0x" ++ hexWord "99"))
    "a tuple revert's bytes differ"
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 2)
      (.inRight (.product .word (.product .word (.product .word .word)))
        (.inRight .word (.word (w 7)))) == some (.trapped (w 7)))
    "a tuple trap differs from its reason"
  -- A wrong annotation, arity or payload does not decode.
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 1)
      (.inRight .word (.inLeft .word (.word (w 1))))).isNone
    "a revert with another annotation decoded"
  ensure (returned 0 [w 1, w 2, w 3]).isNone "a triple decoded as a pair"
  ensure (returned 1 [w 1, w 2]).isNone "a pair decoded as a triple"
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 0)
      (.inLeft (.sum .word .word) (.pair (.word (w 1)) (.bool true)))).isNone
    "a pair with a Boolean decoded"
  ensure (CoreContractEntryProfile.decode? (.wordTupleOutcomeV1 0)
      (.inLeft (.sum .word .bool) (tupleValue [w 1, w 2]))).isNone
    "a return with another annotation decoded"
  -- One-Word conventions are unchanged, and a tuple has no one-Word view.
  ensure (CoreContractEntryProfile.decode? .wordOutcomeV1
      (.inLeft (.sum .word .word) (.word (w 3))) == some (.returned (encodeWordBytesBE (w 3))))
    "the one-Word outcome convention changed"
  ensure (CoreContractEntryProfile.decodeWordOutcome? (.wordTupleOutcomeV1 0)
      (.inLeft (.sum .word .word) (tupleValue [w 1, w 2]))).isNone
    "a tuple has a one-Word view"
  ensure (CoreContractEntryProfile.wordOutcomeV1.returnsOneWord &&
      CoreContractEntryProfile.returnWord.returnsOneWord &&
      !(CoreContractEntryProfile.wordTupleOutcomeV1 0).returnsOneWord)
    "the one-Word predicate changed"
  -- Admission recognizes the tuple contract's exact convention.
  ensure ((CheckedCoreContract.ofCode? tupleChildContract.code).map (·.entryProfile) ==
      some (.wordTupleOutcomeV1 0))
    "admission does not recognize the tuple convention"
  -- A word call to a registered tuple contract is unavailable: the child never
  -- runs, its slot keeps the old value, and the root traps with the failure.
  ensure (childAt (runScenario (rootContract .commit childTargetWord) tupleChildContract completionFuel) ==
      some (.trapped ContractCallFailure.unavailable.code, some childOldValue, some childOldValue))
    "a word call reached a tuple contract"
  -- Creation from a template with a tuple initializer is unavailable before
  -- the creator's nonce advances; the one-Word initializer still deploys.
  ensure (creationAt tupleTemplateEnvironment ==
      some (.trapped, .trapped ContractCallFailure.unavailable.code,
        some Adr0148CheckedCreationPreflightFixture.oldNonce, false))
    "creation started a tuple initializer"
  ensure ((creationAt Adr0148CheckedCreationPreflightFixture.validEnvironment).map
      (fun (kind, _, nonce, present) => (kind, nonce, present)) ==
      some (.returned, some Adr0148CheckedCreationPreflightFixture.nextNonce, true))
    "the one-Word initializer no longer deploys"
  -- A tuple root returns its whole tuple through the nested executor.
  ensure (childAt (runScenario tupleChildContract childReturnContract completionFuel) ==
      some (.returned (encodeWordBytesBE childPayload ++ encodeWordBytesBE childNewValue),
        some childOldValue, some childOldValue))
    "a tuple root did not return its whole tuple"

end Tests.ContractTupleEntryProfile
