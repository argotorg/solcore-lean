import Solcore.Synthesis.Source.AssemblyMemoryCases
import Solcore.Synthesis.Core.StorageMapping
import Solcore.Abi.Keccak256

/-! The `runtime-assembly-memory` profile. Its step is the `runtime-primitives`
function of the same seed by the same steps, and its Core reference keeps the
96-byte window as three Words with byte placement as shifts and masks and the
hash as a closure over the Core Keccak builders. Each length's closure agrees
with `cast keccak` and the separate `Solcore.Abi.V1.Keccak256`, the 64-byte one
is the mapping profile's closure, and the reference agrees with a byte-list
model of the schedule on generated plans. A fixture's source and results are
golden. Generation draws every stage count, width, delta class and hash option
and replays exactly; tampering is refused, and reductions are strictly smaller
and replay. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyMemoryCases

open Lean
open Solcore.Core (Word)
open Solcore.Core.Wire (Expr)
open Solcore.ContractRuntime (encodeWordBytesBE decodeWordBytesBE?)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Core.AssemblyMemory (Schedule Stage Hash Width)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def errorOf {α : Type} : Except String α → Option String
  | .error error => some error
  | .ok _ => none

private def fuel : Nat := 1000000

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def excluded (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "excluded")

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def withPlan (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "assemblyMemoryPlan" (change (← get (case.getObjVal? "assemblyMemoryPlan")))

private def run (program : Solcore.Core.Wire.Program) : IO Nat :=
  match program.toCore.runStateful fuel with
  | .done (.word value) _ => pure value.val
  | _ => throw (IO.userError "a reference program did not return a Word")

/-- Keccak-256 of the first `length` bytes of two big-endian Words, by the separate ABI implementation. -/
private def abiHash (length first second : Nat) : Nat :=
  let bytes := (encodeWordBytesBE (Word.ofNatModulo first) ++ encodeWordBytesBE (Word.ofNatModulo second)).extract 0 length
  ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash bytes)).map (·.val)).getD 0

private def closed (body : Expr) : Solcore.Core.Wire.Program := {resultType := .word, dataDefinitions := [], body}

private def closureHash (length first second : Nat) : IO Nat :=
  run (closed (.apply (AssemblyMemory.hashClosure length) (.pair (word first) (word second))))

private def closureNodes (length : Nat) : Nat :=
  Solcore.Core.Wire.programNodes
    ({resultType := .function (.product .word .word) .word, dataDefinitions := [], body := AssemblyMemory.hashClosure length} :
      Solcore.Core.Wire.Program)

private def maximum : Nat := 2 ^ 256 - 1

/-- `cast keccak` of the first bytes of `0x00..1f ++ 0x20..3f`, for each length. -/
private def castHashes : List (Nat × Nat) := [
  (0, 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470),
  (1, 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a), (31, 0x3e50547cf72e8583ee91462f9d99fe624f53282f78e1a5ec2347b1d0123d0d9b), (32, 0x8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d), (33, 0xf08683775f4a25dfef721c487073fb77026d45ac57e423424290e47af9fd2835), (64, 0x002030bde3d4cf89919649775cd71875c4d0ab1708a380e03fefc3a28aa24831)]

private def counting : Nat × Nat :=
  ((List.range 32).foldl (fun acc index => acc * 256 + index) 0,
   (List.range 32).foldl (fun acc index => acc * 256 + 32 + index) 0)

private def hashChecks : IO Unit := do
  ensure (AssemblyMemory.hashLengths.map closureNodes == [2270, 2278, 2458, 2462, 2470, 2654])
    "a hash closure changed size"
  ensure (Solcore.Core.Wire.encodeExpr (AssemblyMemory.hashClosure 64) ==
      Solcore.Core.Wire.encodeExpr StorageMapping.hashClosure)
    "the 64-byte closure is not the mapping profile's closure"
  for (length, expected) in castHashes do
    ensure ((← closureHash length counting.1 counting.2) == expected && abiHash length counting.1 counting.2 == expected)
      s!"the {length}-byte closure differs from cast keccak"
  for length in AssemblyMemory.hashLengths do
    for (first, second) in [(0, 0), (maximum, 7), (2 ^ 255 + 1, maximum - 2 ^ 128)] do
      ensure ((← closureHash length first second) == abiHash length first second)
        s!"the {length}-byte closure differs from Solcore.Abi.V1.Keccak256"

/-- A byte-list model of a plan at one input: the window bytes, the step by
its own Core function, and the hash by the separate ABI Keccak-256. -/
private def byteModel (plan : AssemblyMemory.CheckedPlan) (input : Nat) : IO Nat := do
  let step := fun (value : Nat) => run (plan.function.instantiate (Word.ofNatModulo value))
  let bytesOf := fun (value : Nat) => (List.range 32).map fun index => value / 256 ^ (31 - index) % 256
  let readWord := fun (memory : Array Nat) (offset : Nat) =>
    (List.range 32).foldl (fun acc index => acc * 256 + memory.getD (offset + index) 0) 0
  let mut memory : Array Nat := (bytesOf input ++ bytesOf (← step input) ++ bytesOf (maximum - input)).toArray
  for stage in plan.schedule.stages do
    let value ← step (readWord memory stage.read)
    match stage.width with
    | .word =>
        for (byte, index) in (bytesOf value).zipIdx do
          memory := memory.set! (stage.write + index) byte
    | .byte => memory := memory.set! stage.write (value % 256)
  let result ← step (readWord memory plan.schedule.final)
  match plan.schedule.hash with
  | none => return result
  | some hash =>
      let bytes := ByteArray.mk ((List.range hash.length).map
        fun index => UInt8.ofNat (memory.getD (hash.offset + index) 0)).toArray
      let digest := ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash bytes)).map (·.val)).getD 0
      return (result + digest) % 2 ^ 256

private def modelChecks : IO Unit := do
  let corpus := AssemblyMemory.generateCases (Seed.ofNat 1) 96 (8 * 24) 512 fuel .v4
  let all ← cases corpus
  ensure (all.size == 8 * 24) "model generation did not complete"
  let mut hashed := 0
  for case in all do
    let checked ← get (AssemblyMemory.caseProgram case)
    if checked.plan.schedule.hash.isSome then hashed := hashed + 1
    let observed ← get ((← get (case.getObjVal? "directCore")).getObjValAs? String "word")
    ensure (observed == toString (← byteModel checked.plan checked.input.val))
      s!"the Core reference differs from the byte model at input {checked.input.val}"
  ensure (hashed > 0 && hashed < all.size) "the model plans did not mix hashed and unhashed schedules"

/-- `if a > 1000 then (3a) xor (a >> 7) else a + 77`. -/
private def fixtureStep : Expr :=
  .ifE (.binary .wordGt (.var 0) (word 1000))
    (.binary .wordXor (.binary .wordMul (.var 0) (word 3)) (.binary .wordShr (.var 0) (word 7)))
    (.binary .wordAdd (.var 0) (word 77))

private def fixtureSchedule : Schedule :=
  {stages := [⟨7, .word, 13⟩, ⟨40, .byte, 70⟩], final := 33, hash := some ⟨5, 33⟩}

private def alignedSchedule : Schedule := {stages := [⟨0, .word, 0⟩], final := 0, hash := none}

private def fixtureInputs : List Nat := [0, 1, 1001, maximum, 2 ^ 255]

/-- From a separate Python byte model with `cast`-checked Keccak-256. -/
private def fixtureResults : List Nat := [
  110185045784767375427769875027799576749316767568423648043270614598653477256537,
  61429659347378633297406769563880590345839053942026463851594556187924875762631,
  47432681453954187113048786422149475504612106509254933618506966340297808359691,
  86278112449216878584690821040707056911088705185690605313631675068037507226035,
  87400343485929131098010694833534200512004183788348265012709545369942392530013]

private def alignedResults : List Nat := [154, 155, 8995,
  113975770454724016332759355177924187618999331219652427750508572832984316510214,
  58804204009954187257191307419725814043770319055814350164203297591420971384832]

private def fixtureSource : String := String.intercalate "\n" [
  "import * from std;",
  "import * from std.dispatch;",
  "",
  "contract SynthesizedAssemblyMemory {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_out: word = 0;",
  "        assembly {",
  "            function sc_step(sc_arg) -> sc_ret {",
  "                let sc_y0 := 0",
  "                switch gt(sc_arg, 1000)",
  "                case 0 {",
  "                    sc_y0 := add(sc_arg, 77)",
  "                }",
  "                default {",
  "                    sc_y0 := xor(mul(sc_arg, 3), shr(7, sc_arg))",
  "                }",
  "                sc_ret := sc_y0",
  "            }",
  "            let sc_base := mload(64)",
  "            mstore(sc_base, sc_input)",
  "            mstore(add(sc_base, 32), sc_step(sc_input))",
  "            mstore(add(sc_base, 64), not(sc_input))",
  "            let sc_m0 := mload(add(sc_base, 7))",
  "            mstore(add(sc_base, 13), sc_step(sc_m0))",
  "            let sc_m1 := mload(add(sc_base, 40))",
  "            mstore8(add(sc_base, 70), sc_step(sc_m1))",
  "            let sc_m2 := mload(add(sc_base, 33))",
  "            let sc_h := keccak256(add(sc_base, 5), 33)",
  "            sc_out := add(sc_step(sc_m2), sc_h)",
  "        }",
  "        return uint256(sc_out);",
  "    }",
  "}"] ++ "\n"

private def fixturePlan (schedule : Schedule) : IO AssemblyMemory.CheckedPlan := do
  let some function := CheckedWordFunction.ofBody? fixtureStep |
    throw (IO.userError "the fixture step is not a checked Word function")
  let some plan := AssemblyMemory.CheckedPlan.ofParts? function schedule |
    throw (IO.userError "the fixture plan failed admission")
  return plan

private def fixtureChecks : IO Unit := do
  let plan ← fixturePlan fixtureSchedule
  let emitted ← get ((AssemblyMemory.emit plan.function plan.schedule).mapError reprStr)
  ensure (emitted.source == fixtureSource) "the fixture's source differs from its golden text"
  for (input, expected) in fixtureInputs.zip fixtureResults do
    ensure ((← run (plan.program (Word.ofNatModulo input))) == expected)
      s!"the fixture's Core reference differs from its golden result at {input}"
    ensure ((← byteModel plan input) == expected) s!"the byte model differs from the golden result at {input}"
  let aligned ← fixturePlan alignedSchedule
  for (input, expected) in fixtureInputs.zip alignedResults do
    ensure ((← run (aligned.program (Word.ofNatModulo input))) == expected)
      s!"the aligned fixture differs from its golden result at {input}"
  ensure (Solcore.Core.Wire.programNodes (aligned.program Word.zero) < 100)
    "an unhashed plan carries a closure"
  -- Outside the window, an unadmitted length and four stages are refused.
  for schedule in [{fixtureSchedule with final := 65}, {fixtureSchedule with hash := some ⟨64, 33⟩},
      {fixtureSchedule with hash := some ⟨0, 2⟩}, {fixtureSchedule with stages := [⟨0, .byte, 96⟩]},
      {fixtureSchedule with stages := [⟨0, .word, 65⟩]}, {fixtureSchedule with stages := []},
      {fixtureSchedule with stages := List.replicate 4 ⟨0, .word, 0⟩}] do
    ensure (AssemblyMemory.CheckedPlan.ofParts? plan.function schedule).isNone
      "an unadmitted schedule passed admission"

private def classOf (offset : Nat) : Nat :=
  (AssemblyMemory.deltaClasses.findIdx? fun (low, high) => low ≤ offset % 32 && offset % 32 ≤ high).getD 6

private def generationChecks : IO Unit := do
  let mut counts : List Nat := []
  let mut widths : List Width := []
  let mut reads : List Nat := []
  let mut words : List Nat := []
  let mut bytes : List Nat := []
  let mut hashes : List (Option Nat) := []
  for index in List.range 600 do
    let schedule := AssemblyMemory.scheduleFor (Seed.ofNat (index + 1))
    ensure schedule.admitted s!"the schedule of seed {index + 1} is not admitted"
    counts := counts ++ [schedule.stages.length]
    hashes := hashes ++ [schedule.hash.map (·.length)]
    reads := reads ++ [classOf schedule.final]
    for stage in schedule.stages do
      widths := widths ++ [stage.width]
      reads := reads ++ [classOf stage.read]
      match stage.width with
      | .word => words := words ++ [classOf stage.write]
      | .byte => bytes := bytes ++ [classOf stage.write]
  ensure ([1, 2, 3].all counts.contains && [Width.word, .byte].all widths.contains)
    "generation missed a stage count or a width"
  ensure ((List.range 6).all fun index => reads.contains index && words.contains index && bytes.contains index)
    "generation missed a delta class"
  ensure ((none :: AssemblyMemory.hashLengths.map some).all hashes.contains) "generation missed a hash option"
  let corpus := AssemblyMemory.generateCases (Seed.ofNat 1) 96 64 256 fuel .v4
  ensure (corpus == AssemblyMemory.generateCases (Seed.ofNat 1) 96 64 256 fuel .v4) "generation is not deterministic"
  for case in ← cases corpus do
    let checked ← get (AssemblyMemory.caseProgram case)
    let seed ← get (((← provenance case).getObjVal? "origin" >>= (·.getObjValAs? String "seed")))
    ensure (checked.plan.schedule == AssemblyMemory.scheduleFor (Seed.ofNat seed.toNat!))
      "a generated plan's schedule differs from its seed's"
    ensure ((← get (AssemblyMemory.replayCase case fuel)) == case) "a generated case failed exact replay"
  for entry in ← excluded corpus do
    ensure ((entry.getObjValAs? String "stage").toOption == some "assembly-memory-profile")
      "an exclusion lacks the profile's stage"

private def tamperChecks : IO Unit := do
  let all ← cases (AssemblyMemory.generateCases (Seed.ofNat 1) 96 64 256 fuel .v4)
  let some hashed := all.find? fun case =>
      ((case.getObjVal? "assemblyMemoryPlan" >>= (·.getObjVal? "hash")).toOption.getD .null) != .null |
    throw (IO.userError "no generated case hashes")
  ensure (errorOf (AssemblyMemory.replayCase (← withPlan hashed (·.setObjVal! "hash" (Json.mkObj
      [("offset", toJson 0), ("length", toJson 2)]))) fuel) ==
      some "assembly memory schedule is outside the admitted stages, offsets and hashed lengths")
    "an unadmitted hashed length replayed"
  ensure (errorOf (AssemblyMemory.replayCase (← withPlan hashed (·.setObjVal! "finalRead" (toJson 65))) fuel) ==
      some "assembly memory schedule is outside the admitted stages, offsets and hashed lengths")
    "a read past the window replayed"
  let moved ← withPlan hashed (·.setObjVal! "finalRead" (toJson 0))
  ensure (AssemblyMemory.replayCase moved fuel matches .error _) "a changed schedule replayed"
  ensure (errorOf (AssemblyMemory.replayCase (hashed.setObjVal! "source" (toJson "contract X {}")) fuel) ==
      some "saved source differs from emission of the assembly memory plan")
    "a changed source replayed"
  ensure (AssemblyMemory.replayCase (hashed.setObjVal! "program" (Solcore.Core.Wire.encodeProgram (closed (word 1)))) fuel
      matches .error _)
    "a changed reference replayed"
  ensure (errorOf (AssemblyMemory.replayCase (hashed.setObjVal! "provenance" ((← provenance hashed).setObjVal!
      "memoryVersion" (toJson "core-assembly-memory-v0"))) fuel) == some "memoryVersion changed")
    "a changed memory version replayed"
  -- A reduction is strictly smaller, replays, and a hashed plan's shrink batch holds at most eight.
  let reduced ← cases (← get (AssemblyMemory.shrinkCases hashed 64 fuel))
  ensure (!reduced.isEmpty && reduced.size ≤ 8) "a hashed plan's shrink batch is empty or exceeds eight"
  for candidate in reduced do
    ensure ((← get (AssemblyMemory.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← get (AssemblyMemory.caseProgram hashed)
  for reduction in AssemblyMemory.reductions parent do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  let reducedPlan ← get ((reduced[0]!.getObjVal? "provenance") >>= (·.getObjVal? "origin"))
  ensure (AssemblyMemory.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedPlan.setObjVal! "parentPlan" (← get (reduced[0]!.getObjVal? "assemblyMemoryPlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceAssemblyMemoryCases : IO Unit := do
  hashChecks
  fixtureChecks
  generationChecks
  tamperChecks
  modelChecks

end Tests.SourceAssemblyMemoryCases
