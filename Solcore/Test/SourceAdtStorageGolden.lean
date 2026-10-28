import Solcore.Synthesis.Source.AdtStorageCases

/-! Golden cases for the enum and struct storage profile. Each emitted contract
is written out in full. Every expected row is written out by hand from the
layout: which slot holds a tag, a payload Word `r + o·K` or a record Word, and
which slot keeps a stale Word, with only the additions, the products with
`K` and Horner's rule evaluated here; the mappings' entry slots come from the
independent `Solcore.Abi.V1.Keccak256`. The steps add a known constant `c`, so
a writing method's `r` is its input plus the accumulator plus `c`. The three
shapes cover two, three and four variants, a pair payload, the payload-free
variant first, between others and last, the enum at record positions 0, 1
and 2, both Word types and both keys of a wrapping key base; the sequences
cover every method, overwrites of longer variants by shorter ones and the
reverse, clears, field updates of the enum and of Words, stale payload and
tag Words a later read must ignore, and reverts of a write, an update and a
read. Both original Core and the slot-map model must give each row. -/
set_option autoImplicit false

namespace Tests.SourceAdtStorageGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.AdtStorage (CheckedPlan Method Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.AdtStorageExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The multiplier, written out. -/
def K : Nat := 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95

def plus (left right : Nat) : Nat := (left + right) % 2 ^ 256

/-- The Word written at offset `o` of a value written with `r`. -/
def kv (r o : Nat) : Nat := (r + o * K) % 2 ^ 256

/-- Horner's rule with `K` over decoded Words, from zero. -/
def horner (tokens : List Nat) : Nat := tokens.foldl (fun total token => (total * K + token) % 2 ^ 256) 0

/-- Slot `offset` of the entry of `key` in the mapping at slot `base`. -/
def entry (base key offset : Nat) : Nat := ((AdtStorageExecution.entrySlot base (w key)).val + offset) % 2 ^ 256

def maxKey : Nat := 2 ^ 256 - 1

/-- The expected row: status, output Word and every nonzero observed slot. -/
structure Expected where
  status : String
  output : Nat
  slots : List (Nat × Nat)

private def tx (index : Nat) (method : Method) (flags key field variant input : Nat := 0) : Transaction :=
  ⟨"tx-" ++ toString index, method, w flags, w key, field, variant, w input⟩

/-- `None | Some(word)` with the enum first in the record: the accumulator at
slot 0, the enum at 1 and 2, the record at 3 to 6 (its enum at 3 and 4, its
Words at 5 and 6), `c = 5`. -/
def g1Shape : Shape := {variants := [.words 0, .words 1], position := 0, wordType := .word}
def g1Methods : List Method := [.putChoice, .clearChoice, .getChoice, .putRecord, .setRecord, .getRecord]

/-- `Some(7 + K)`, read back; cleared, which leaves the payload at slot 2;
read as `None`; a whole record reverted, then written with `None`; its enum
field updated to `Some`, the Words kept; and the record read. -/
def g1Rows : List (Transaction × Expected) :=
  let read := horner [1, kv 7 1]
  let record := horner [1, kv 13 1, kv 8 2, kv 8 3]
  [ -- r = 2 + 0 + 5: tag one at slot 1, the payload at offset 1.
    (tx 0 .putChoice (variant := 1) (input := 2), ⟨"returned", 7, [(0, 7), (1, 1), (2, kv 7 1)]⟩),
    (tx 1 .getChoice, ⟨"returned", read, [(0, read), (1, 1), (2, kv 7 1)]⟩),
    -- r = 1 + read + 5: tag zero at slot 1; slot 2 keeps its stale payload.
    (tx 2 .clearChoice (input := 1), ⟨"returned", plus read 6, [(0, plus read 6), (2, kv 7 1)]⟩),
    (tx 3 .getChoice, ⟨"returned", 0, [(2, kv 7 1)]⟩),
    -- r = 3 + 0 + 5, reverted with the prior slots.
    (tx 4 .putRecord 1 (variant := 1) (input := 3), ⟨"reverted", 8, [(2, kv 7 1)]⟩),
    -- `ScRecord(None, 8 + 2K, 8 + 3K)`: the enum's tag zero, the Words at offsets 2 and 3.
    (tx 5 .putRecord (variant := 0) (input := 3), ⟨"returned", 8, [(0, 8), (2, kv 7 1), (5, kv 8 2), (6, kv 8 3)]⟩),
    -- r = 0 + 8 + 5: `record.f0 = Some(13 + K)` at slots 3 and 4; slots 5 and 6 kept.
    (tx 6 .setRecord (field := 0) (variant := 1), ⟨"returned", 13,
      [(0, 13), (2, kv 7 1), (3, 1), (4, kv 13 1), (5, kv 8 2), (6, kv 8 3)]⟩),
    (tx 7 .getRecord, ⟨"returned", record, [(0, record), (2, kv 7 1), (3, 1), (4, kv 13 1), (5, kv 8 2), (6, kv 8 3)]⟩)]

/-- `V0(ScPair) | V1 | V2(uint256, uint256)` with the enum last in the record:
the enum at 1 to 4, the record at 5 to 10 (its Words at 5 and 6, its enum at 7
to 10), `choices` at 11 and `records` at 12, keys `2^256 - 1` and 0, `c = 3`. -/
def g2Shape : Shape := {variants := [.pair, .words 0, .words 2], position := 2, wordType := .uint256}
def g2Methods : List Method := [.putChoiceAt, .clearChoiceAt, .getChoiceAt, .putRecordAt, .setRecordAt, .getRecordAt]

/-- A pair at the top key and the last variant at key 0, each at its payload
offset; the top key cleared to the middle variant, which leaves the pair's
second Word; read; a record at key 0 with a pair, whose enum field is updated
to the last variant through the entry's read-modify-write; an update of its
first Word reverted; and the record read. -/
def g2Rows : List (Transaction × Expected) :=
  let top := fun offset => entry 11 maxKey offset
  let zero := fun offset => entry 11 0 offset
  let record := fun offset => entry 12 0 offset
  let choices := [(zero 0, 1), (zero 1, 1), (zero 2, kv 9 2), (zero 3, kv 9 3)]
  let cleared := [(top 0, 1), (top 2, kv 4 2)] ++ choices
  let digest := horner [9, kv 9 1, 2, kv 12 4, kv 12 5]
  let updated := [(record 0, 9), (record 1, kv 9 1), (record 2, 1), (record 3, 1), (record 4, kv 12 4), (record 5, kv 12 5)]
  [ -- r = 1 + 0 + 3: tag zero, the pair at offsets 1 and 2.
    (tx 0 .putChoiceAt (key := maxKey) (variant := 0) (input := 1), ⟨"returned", 4, [(0, 4), (top 1, kv 4 1), (top 2, kv 4 2)]⟩),
    -- r = 2 + 4 + 3: tags one and one, the payload at offsets 2 and 3.
    (tx 1 .putChoiceAt (key := 0) (variant := 2) (input := 2), ⟨"returned", 9,
      [(0, 9), (top 1, kv 4 1), (top 2, kv 4 2)] ++ choices⟩),
    -- r = 0 + 9 + 3: tags one and zero over the pair's tag and first Word.
    (tx 2 .clearChoiceAt (key := maxKey), ⟨"returned", 12, [(0, 12)] ++ cleared⟩),
    (tx 3 .getChoiceAt (key := maxKey), ⟨"returned", 1, [(0, 1)] ++ cleared⟩),
    -- r = 5 + 1 + 3: `ScRecord(9, 9 + K, V0(ScPair(9 + 3K, 9 + 4K)))`.
    (tx 4 .putRecordAt (key := 0) (variant := 0) (input := 5), ⟨"returned", 9,
      [(0, 9)] ++ cleared ++ [(record 0, 9), (record 1, kv 9 1), (record 3, kv 9 3), (record 4, kv 9 4)]⟩),
    -- r = 0 + 9 + 3: the last variant's tags over the pair's tag and first
    -- Word, its payload at record offsets 4 and 5; the Words kept.
    (tx 5 .setRecordAt (key := 0) (field := 2) (variant := 2), ⟨"returned", 12, [(0, 12)] ++ cleared ++ updated⟩),
    -- r = 7 + 12 + 3, reverted with the prior slots.
    (tx 6 .setRecordAt 1 (key := 0) (field := 0) (input := 7), ⟨"reverted", 22, [(0, 12)] ++ cleared ++ updated⟩),
    (tx 7 .getRecordAt (key := 0), ⟨"returned", digest, [(0, digest)] ++ cleared ++ updated⟩)]

/-- `V0(word) | V1 | V2 | V3(word)` with the enum between the record's Words:
the enum at 1 to 4, the record at 5 to 10 (its first Word at 5, its enum at 6
to 9, its last Word at 10), `records` at 12, keys 1 and 2, `c = 1`. -/
def g3Shape : Shape := {variants := [.words 1, .words 0, .words 0, .words 1], position := 1, wordType := .word}
def g3Methods : List Method := [.putChoice, .getChoice, .putRecordAt, .setRecord, .getRecordAt]

/-- The last variant's three tags and payload; the first variant over it,
which leaves the third tag and the last payload; read; the third variant,
whose zero tag at level two the read must reach; that read reverted; a record
at key 2 with the last variant; read; and the record field's last Word
updated. -/
def g3Rows : List (Transaction × Expected) :=
  let first := kv 2 1
  let third := plus first 1
  let r5 := plus first 6
  let entryRow := fun offset => entry 12 2 offset
  let record := horner [r5, 3, kv r5 4, kv r5 5]
  let r7 := plus record 2
  let written := [(entryRow 0, r5), (entryRow 1, 1), (entryRow 2, 1), (entryRow 3, 1), (entryRow 4, kv r5 4),
    (entryRow 5, kv r5 5)]
  [ -- r = 0 + 0 + 1: tags one at slots 1 to 3, the payload at offset 3.
    (tx 0 .putChoice (variant := 3), ⟨"returned", 1, [(0, 1), (1, 1), (2, 1), (3, 1), (4, kv 1 3)]⟩),
    -- r = 0 + 1 + 1: tag zero at slot 1, the payload at offset 1 over a tag.
    (tx 1 .putChoice (variant := 0), ⟨"returned", 2, [(0, 2), (2, first), (3, 1), (4, kv 1 3)]⟩),
    (tx 2 .getChoice, ⟨"returned", first, [(0, first), (2, first), (3, 1), (4, kv 1 3)]⟩),
    -- r = 0 + first + 1: tags one, one and zero; slot 4 keeps its payload.
    (tx 3 .putChoice (variant := 2), ⟨"returned", third, [(0, third), (1, 1), (2, 1), (4, kv 1 3)]⟩),
    (tx 4 .getChoice 1, ⟨"reverted", 2, [(0, third), (1, 1), (2, 1), (4, kv 1 3)]⟩),
    -- r = 4 + third + 1: `ScRecord(r, V3(r + 4K), r + 5K)` at key 2.
    (tx 5 .putRecordAt (key := 2) (variant := 3) (input := 4), ⟨"returned", r5,
      [(0, r5), (1, 1), (2, 1), (4, kv 1 3)] ++ written⟩),
    (tx 6 .getRecordAt (key := 2), ⟨"returned", record, [(0, record), (1, 1), (2, 1), (4, kv 1 3)] ++ written⟩),
    -- r = 1 + record + 1: `record.f2` at offset 5, slot 10.
    (tx 7 .setRecord (field := 2) (input := 1), ⟨"returned", r7,
      [(0, r7), (1, 1), (2, 1), (4, kv 1 3)] ++ written ++ [(10, kv r7 5)]⟩)]

private def wordText (value : Nat) : String := encodeBytesText (encodeWordBytesBE (w value))

private def valueAt (expected : Expected) (slot : Word) : Nat :=
  ((expected.slots.find? fun (candidate, _) => w candidate == slot).map Prod.snd).getD 0

private def storageJson (slots : List Word) (expected : Expected) : Json :=
  toJson (slots.map fun slot => Json.mkObj [
    ("slot", toJson (toString slot.val)), ("value", toJson (toString (valueAt expected slot)))])

def check (name : String) (slots : List Word) (row : Json) (model : AdtStorageExecution.ModelRow)
    (expected : Expected) : IO Unit := do
  ensure (expected.slots.all fun (slot, value) => value != 0 && slots.contains (w slot))
    s!"{name}: an expected slot is zero or not observed"
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (wordText expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (storageJson slots expected))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") && model.result == w expected.output &&
      AdtStorageExecution.modelSlots model slots == slots.map (fun slot => w (valueAt expected slot)))
    s!"{name}: the slot-map model differs from the expected row"

/-- Each golden sequence's name, shape, methods, key base, step constant and rows. -/
def goldenPlans : List (String × Shape × List Method × Nat × Nat × List (Transaction × Expected)) := [
  ("two variants", g1Shape, g1Methods, maxKey, 5, g1Rows),
  ("three variants", g2Shape, g2Methods, maxKey, 3, g2Rows),
  ("four variants", g3Shape, g3Methods, 1, 1, g3Rows)]

/-- The emitted contract of the first shape with its six field methods and
`c = 5`, written out. -/
def g1Source : String := "import * from std;
import * from std.dispatch;
import * from std.Generic;
import * from std.StorageGeneric;
import {mstore, revert_} from std.opcodes;

enum ScChoice {
    V0,
    V1(word)
}

struct ScRecord {
    f0: ScChoice;
    f1: word;
    f2: word;
}

function sc_fn0(sc_arg: word) returns (word) {
    let sc_v0: word = 5;
    let sc_v1: word = sc_v0;
    let sc_c2: word = sc_arg;
    let sc_v3: word = sc_c2;
    sc_c2 = sc_v1;
    let sc_v4: word = sc_c2;
    let sc_v5: (word, word) = (sc_v3, sc_v4);
    let sc_v6: (word, word) = sc_v5;
    let sc_v7: word = 0;
    match (sc_v6) {
        case (sc_p8, sc_p9) {
            sc_v7 = sc_p8;
        }
    }
    let sc_v10: word = 0;
    match (sc_v6) {
        case (sc_p11, sc_p12) {
            sc_v10 = sc_p12;
        }
    }
    let sc_v13: word = (sc_v7 + sc_v10);
    return sc_v13;
}

function sc_step(sc_arg: word) returns (word) {
    let sc_v0: word = sc_fn0(sc_arg);
    return sc_v0;
}

contract SynthesizedAdtStorage {
    acc: word;
    choice: ScChoice;
    record: ScRecord;
    choices: mapping(word => ScChoice);
    records: mapping(word => ScRecord);

    function putChoice(flags: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_variant == 0) {
            choice = ScChoice.V0;
        } else {
            choice = ScChoice.V1((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95));
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function clearChoice(flags: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        choice = ScChoice.V0;
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function getChoice(flags: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_digest: word = 0;
        match (choice) {
            case ScChoice.V0 {
                sc_digest = 0;
            }
            case ScChoice.V1(sc_a0) {
                sc_digest = ((1 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_a0);
            }
        }
        acc = sc_digest;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_digest);
            revert_(0, 32);
        }
        return uint256(sc_digest);
    }

    function putRecord(flags: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_variant == 0) {
            record = ScRecord(ScChoice.V0, (sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a), (sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf));
        } else {
            record = ScRecord(ScChoice.V1((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), (sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a), (sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf));
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function setRecord(flags: uint256, field: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_field: word = Typedef.rep(field);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_field == 0) {
            if (sc_variant == 0) {
                record.f0 = ScChoice.V0;
            } else {
                record.f0 = ScChoice.V1((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95));
            }
        } else {
            if (sc_field == 1) {
                record.f1 = (sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a);
            } else {
                record.f2 = (sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf);
            }
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function getRecord(flags: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_digest: word = 0;
        match (record) {
            case ScRecord(ScChoice.V0, sc_x1, sc_x2) {
                sc_digest = ((((0 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_x1) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_x2);
            }
            case ScRecord(ScChoice.V1(sc_a0), sc_x1, sc_x2) {
                sc_digest = ((((((1 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_a0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_x1) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_x2);
            }
        }
        acc = sc_digest;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_digest);
            revert_(0, 32);
        }
        return uint256(sc_digest);
    }
}
"

/-- The emitted contract of the second shape with its six keyed methods and
`c = 5`, written out. -/
def g2Source : String := "import * from std;
import * from std.dispatch;
import * from std.Generic;
import * from std.StorageGeneric;
import {mstore, revert_} from std.opcodes;

struct ScPair {
    a: uint256;
    b: uint256;
}

enum ScChoice {
    V0(ScPair),
    V1,
    V2(uint256, uint256)
}

struct ScRecord {
    f0: uint256;
    f1: uint256;
    f2: ScChoice;
}

function sc_fn0(sc_arg: word) returns (word) {
    let sc_v0: word = 5;
    let sc_v1: word = sc_v0;
    let sc_c2: word = sc_arg;
    let sc_v3: word = sc_c2;
    sc_c2 = sc_v1;
    let sc_v4: word = sc_c2;
    let sc_v5: (word, word) = (sc_v3, sc_v4);
    let sc_v6: (word, word) = sc_v5;
    let sc_v7: word = 0;
    match (sc_v6) {
        case (sc_p8, sc_p9) {
            sc_v7 = sc_p8;
        }
    }
    let sc_v10: word = 0;
    match (sc_v6) {
        case (sc_p11, sc_p12) {
            sc_v10 = sc_p12;
        }
    }
    let sc_v13: word = (sc_v7 + sc_v10);
    return sc_v13;
}

function sc_step(sc_arg: word) returns (word) {
    let sc_v0: word = sc_fn0(sc_arg);
    return sc_v0;
}

contract SynthesizedAdtStorage {
    acc: word;
    choice: ScChoice;
    record: ScRecord;
    choices: mapping(word => ScChoice);
    records: mapping(word => ScRecord);

    function putChoiceAt(flags: uint256, key: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_variant == 0) {
            choices[sc_key] = ScChoice.V0(ScPair(uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), uint256((sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a))));
        } else {
            if (sc_variant == 1) {
                choices[sc_key] = ScChoice.V1;
            } else {
                choices[sc_key] = ScChoice.V2(uint256((sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a)), uint256((sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf)));
            }
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function clearChoiceAt(flags: uint256, key: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        choices[sc_key] = ScChoice.V1;
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function getChoiceAt(flags: uint256, key: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_digest: word = 0;
        match (choices[sc_key]) {
            case ScChoice.V0(ScPair(sc_a0, sc_a1)) {
                sc_digest = ((((0 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a0)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a1));
            }
            case ScChoice.V1 {
                sc_digest = 1;
            }
            case ScChoice.V2(sc_a0, sc_a1) {
                sc_digest = ((((2 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a0)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a1));
            }
        }
        acc = sc_digest;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_digest);
            revert_(0, 32);
        }
        return uint256(sc_digest);
    }

    function putRecordAt(flags: uint256, key: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_variant == 0) {
            records[sc_key] = ScRecord(uint256(sc_r), uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), ScChoice.V0(ScPair(uint256((sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf)), uint256((sc_r + 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54)))));
        } else {
            if (sc_variant == 1) {
                records[sc_key] = ScRecord(uint256(sc_r), uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), ScChoice.V1);
            } else {
                records[sc_key] = ScRecord(uint256(sc_r), uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), ScChoice.V2(uint256((sc_r + 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54)), uint256((sc_r + 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9))));
            }
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function setRecordAt(flags: uint256, key: uint256, field: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_field: word = Typedef.rep(field);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        match (records[sc_key]) {
            case ScRecord(sc_x0, sc_x1, sc_x2) {
                if (sc_field == 0) {
                    records[sc_key] = ScRecord(uint256(sc_r), sc_x1, sc_x2);
                } else {
                    if (sc_field == 1) {
                        records[sc_key] = ScRecord(sc_x0, uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), sc_x2);
                    } else {
                        if (sc_variant == 0) {
                            records[sc_key] = ScRecord(sc_x0, sc_x1, ScChoice.V0(ScPair(uint256((sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf)), uint256((sc_r + 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54)))));
                        } else {
                            if (sc_variant == 1) {
                                records[sc_key] = ScRecord(sc_x0, sc_x1, ScChoice.V1);
                            } else {
                                records[sc_key] = ScRecord(sc_x0, sc_x1, ScChoice.V2(uint256((sc_r + 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54)), uint256((sc_r + 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9))));
                            }
                        }
                    }
                }
            }
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function getRecordAt(flags: uint256, key: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_digest: word = 0;
        match (records[sc_key]) {
            case ScRecord(sc_x0, sc_x1, ScChoice.V0(ScPair(sc_a0, sc_a1))) {
                sc_digest = ((((((((Typedef.rep(sc_x0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_x1)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + 0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a0)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a1));
            }
            case ScRecord(sc_x0, sc_x1, ScChoice.V1) {
                sc_digest = ((((Typedef.rep(sc_x0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_x1)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + 1);
            }
            case ScRecord(sc_x0, sc_x1, ScChoice.V2(sc_a0, sc_a1)) {
                sc_digest = ((((((((Typedef.rep(sc_x0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_x1)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + 2) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a0)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a1));
            }
        }
        acc = sc_digest;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_digest);
            revert_(0, 32);
        }
        return uint256(sc_digest);
    }
}
"

def testSourceAdtStorageGolden : IO Unit := do
  let fuel := 1000000
  let five ← step 5
  for (name, shape, methods, expected) in [("two variants", g1Shape, g1Methods, g1Source),
      ("three variants", g2Shape, g2Methods, g2Source)] do
    let some plan := CheckedPlan.ofParts? shape methods (w maxKey) five
      | throw (IO.userError s!"{name}: the contract failed admission")
    let emitted ← get (Solcore.Synthesis.Source.AdtStorage.emitted plan)
    ensure (emitted.source == expected) s!"{name}: the emitted contract differs from the hand-written text"
  for (name, shape, methods, keyBase, constant, rows) in goldenPlans do
    let some plan := CheckedPlan.ofParts? shape methods (w keyBase) (← step constant)
      | throw (IO.userError s!"{name}: the contract failed admission")
    let transactions := rows.map Prod.fst
    ensure (transactions.all (·.valid plan)) s!"{name}: a transaction lies outside the plan"
    let slots := AdtStorageExecution.planSlots plan
    let history := AdtStorageExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := AdtStorageExecution.model plan fuel transactions
      | throw (IO.userError s!"{name}: the slot-map model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" slots row model expected
  -- A changed expectation fails: one payload Word off by one.
  let some plan := CheckedPlan.ofParts? g1Shape g1Methods (w maxKey) five | throw (IO.userError "admission")
  let transaction := (g1Rows.head?.map Prod.fst).getD (tx 0 .getChoice)
  let history := AdtStorageExecution.observe plan [transaction] StorageExecution.fixtureBindings fuel
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := AdtStorageExecution.model plan fuel [transaction] | throw (IO.userError "model")
  let changed : Expected := ⟨"returned", 7, [(0, 7), (1, 1), (2, plus (kv 7 1) 1)]⟩
  let (some row, some model) := (rows[0]?, modelled[0]?) | throw (IO.userError "no row")
  let failed ← tryCatch (do
      check "changed" (AdtStorageExecution.planSlots plan) row model changed
      pure false) (fun _ => pure true)
  ensure failed "a changed expectation passed"

end Tests.SourceAdtStorageGolden
