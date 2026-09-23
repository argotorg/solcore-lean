import Solcore.ContractRuntime.AddressWordBridge

/-! Executable boundary tests for strict address and word conversion. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressZero : Address := ⟨0, by decide⟩
private def addressOne : Address := ⟨1, by decide⟩
private def addressMaximum : Address := ⟨addressModulus - 1, by decide⟩

private def wordZero : Word := ⟨0, by decide⟩
private def wordOne : Word := ⟨1, by decide⟩
private def wordAddressMaximum : Word :=
  ⟨addressModulus - 1, by decide⟩
private def firstAddressOverflow : Word := ⟨addressModulus, by decide⟩
private def wordMaximum : Word := ⟨wordModulus - 1, by decide⟩

private def representativeAddress : Address :=
  ⟨0x123456789abcdef, by decide⟩
private def representativeWord : Word :=
  ⟨0x123456789abcdef, by decide⟩

private def representativeAddresses : List Address :=
  [addressZero, addressOne, representativeAddress, addressMaximum]

private def representativeWords : List Word :=
  [wordZero, wordOne, representativeWord, wordAddressMaximum]

def testAddressWordBridge : IO Unit := do
  assertTrue (addressToWord addressZero == wordZero)
    "widening the zero address must produce the zero word"
  assertTrue (addressToWord addressOne == wordOne)
    "widening address one must preserve its natural-number value"
  assertTrue (addressToWord addressMaximum == wordAddressMaximum)
    "widening the maximum address must preserve all 160 bits"
  assertTrue (wordToAddress? wordZero == some addressZero)
    "the zero word must narrow to the zero address"
  assertTrue (wordToAddress? wordOne == some addressOne)
    "word one must narrow to address one"
  assertTrue (wordToAddress? wordAddressMaximum == some addressMaximum)
    "the largest in-range word must narrow to the maximum address"
  assertTrue (wordToAddress? firstAddressOverflow == none)
    "the first 160-bit overflow word must be rejected instead of truncated to zero"
  assertTrue (wordToAddress? wordMaximum == none)
    "the maximum word must be rejected instead of truncated to an address"
  assertTrue
    (representativeAddresses.all fun address =>
      wordToAddress? (addressToWord address) == some address)
    "zero, one, a middle address, and the maximum must survive widening and narrowing"
  assertTrue
    (representativeWords.all fun word =>
      match wordToAddress? word with
      | some address => addressToWord address == word
      | none => false)
    "successfully narrowed zero, one, middle, and maximum-address words must reconstruct"

end Tests
