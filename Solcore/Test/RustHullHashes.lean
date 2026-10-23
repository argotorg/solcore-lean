import Solcore.Frontend.RustHull.Sha256
import Solcore.Frontend.RustHull.Ripemd160
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullHashes
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def number (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private abbrev Hash := Expr → Expr → Expr → Expr → Expr

private def program (hash : Hash) (input : List UInt8) (offset count : Nat) : Program := {
  resultType := .product (LanguageResult.resultType .word) .word
  dataDefinitions := Memory.definitions
  body := .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input offset)))
    (.letE (.newCell .word (number 0))
      (.pair (hash (.var 1) (.var 0) (number offset) (number count)) (.loadCell (.var 0))))
}

private def check (label : String) (hash : Hash) (input : List UInt8) (expected : Nat)
    (offset : Nat := 0) : IO Unit := do
  let compiled := program hash input offset input.length
  require compiled.check s!"{label}: hash produced ill-typed Core"
  match compiled.runStateful 20000000 with
  | .done actual store =>
      let memorySize := if input.isEmpty then 0 else ((offset + input.length + 31) / 32) * 32
      require (actual == .pair (.inRight .word (scalar expected)) (scalar memorySize))
        s!"{label}: wrong hash or memory extent: {reprStr actual}"
      require (store[0]? == some (WordMapping.encode (Memory.packBytes input offset)))
        s!"{label}: hashing changed input memory"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

/-- Boundary vectors generated independently with Python hashlib/OpenSSL;
input byte i is (37*i+11) mod 256. Published empty/abc vectors are also checked. -/
private def vectors : List (Nat × Nat × Nat) := [
  (0, 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855, 0x9c1185a5c5e9fc54612808977ee8f548b2258d31),
  (1, 0xe7cf46a078fed4fafd0b5e3aff144802b853f8ae459a4f0c14add3314b7cc3a6, 0xe257e7861ba1b82bdcff75ff2bb1613d83b797bd),
  (31, 0x0cc420417cb6a768e632bf1be8d1f197c9c0e9dd1dd2021e3bd37c46cee0516f, 0x1078ea07048643129aeb91ed28e495723c52265c),
  (32, 0x83b7a8ed859053c81d818870fab1f8b1ae44d06a98a9665d369a8fd7d2838ded, 0x36781d5c249ba2f726af6d7f101dea2b4164b603),
  (55, 0x2900465fcb533e05a158fd2b3be0e5e3b03740d83060aa3580e0d98a96bf2384, 0xcb9a91b689c2e5a5aff392733f33c8fb75998dbb),
  (56, 0x31454ff48ef36af2f08fd511bdc37d9d5855ac23e992e5ff5445cb6b7674a674, 0x0fde8285ccc694b28a3205e30e3153c3f2a2dfa2),
  (63, 0x5f6401b96532c36de4e65beec0409b69b1d181864c8009b7a04f43e5d56350d1, 0x28d9c6a82ecf3196a0c5ab9cd79053118ca43301),
  (64, 0x94eb5de4943613fd048dc93393ab06877405faa39c11f53e9386083339833e7e, 0xc9b1871a7c604823d7cc8cc48e4ea37a4f841001),
  (65, 0xfc518669b6eb4b4dd91827ecacef86689c725bd5bab888fd3b26dbb196eec954, 0x26bc5a01292f459c7bd3310eaf53b72d25df1e71),
  (119, 0xb0dc41b1a384e2f1203f0351b38fbeaafceef577ce1191d5bfc25da39f721eae, 0x3e51052aaeaf2b4b120980b0c3c79f26301ff2f9),
  (120, 0x5df24dd802ac26132ce608dcb5f09841eef039ee0f152acf98d26d17fe4e88e6, 0x0268020acd3f91628e14766d7791dbf683bff67d),
  (127, 0x0fe729ff19257bd6fec853acc2ea355f6b34b58e6c0f684c3e188fcdfcd9baae, 0x24ba60dff396cf212ad4c3969eb1e281f044a7b0),
  (128, 0x0aedd4856f8eba0963627336ad5144a9a7dbe12498e6066f0165fc97d8ddee4c, 0x2349a24ad9bd73b09329b1c014c333610548ac55),
  (129, 0x4f1757ae4bffbae86d775b831765b75af154d52f7deaa46dd378051a2d3ad57f, 0x5a83b0b39268fa523094d515def4dafe725d5930),
  (1024, 0xffbad8f947474cfdd5b2bb22d7e0bf5ee8ba2b7af859d0c2bb28622db6a4be47, 0xba940bb0f331e6c62ae7eead37a76d5c52c799ed)]

def run : IO Unit := do
  check "SHA256 abc" Sha256.hash "abc".toUTF8.toList
    0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  check "RIPEMD160 abc" Ripemd160.hash "abc".toUTF8.toList
    0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc
  for (length, sha, ripemd) in vectors do
    let input := (List.range length).map fun index => UInt8.ofNat (index * 37 + 11)
    check s!"SHA256 length{length}" Sha256.hash input sha
    check s!"RIPEMD160 length{length}" Ripemd160.hash input ripemd
    if length = 65 then
      check "SHA256 unaligned offset" Sha256.hash input sha 7
      check "RIPEMD160 unaligned offset" Ripemd160.hash input ripemd 7
  check "SHA256 empty max offset" Sha256.hash []
    0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 (wordModulus - 1)
  check "RIPEMD160 empty max offset" Ripemd160.hash []
    0x9c1185a5c5e9fc54612808977ee8f548b2258d31 (wordModulus - 1)
  for (label, hash, expected) in [("SHA256", Sha256.hash,
      0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad),
      ("RIPEMD160", Ripemd160.hash, 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc)] do
    let resumable := program hash "abc".toUTF8.toList 0 3
    match resumable.runStateful 200 with
    | .outOfFuel state =>
        match runStateful 20000000 state with
        | .done actual _ =>
            require (actual == .pair (.inRight .word (scalar expected)) (scalar 32))
              s!"{label}: suspension changed the digest"
        | other => throw (IO.userError s!"{label}: failed resume: {reprStr other}")
    | _ => throw (IO.userError s!"{label}: hash did not suspend")
    let overflow := program hash [] (wordModulus - 16) 32
    require overflow.check s!"{label}: overflow expression is ill-typed"
    match overflow.runStateful 10000 with
    | .done actual store =>
        require (actual == .pair (.inLeft .word (.word Memory.overflowReason)) (scalar 0))
          s!"{label}: overflowing input range was accepted"
        require (store[0]? == some (WordMapping.encode [])) s!"{label}: overflow changed memory"
    | other => throw (IO.userError s!"{label}: unexpected overflow result {reprStr other}")

end Tests.RustHullHashes
