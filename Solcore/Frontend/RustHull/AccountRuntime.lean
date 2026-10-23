import Solcore.Frontend.RustHull.Lowering
import Solcore.Frontend.RustHull.Calls

/-! Single-contract message calls on ordinary Core cells. Child frames share
storage, transient storage, balances and logs. A failed child restores those
cells before returning its status and bytes to the parent. Other executable
accounts require a future account catalog; only explicitly listed empty
accounts and implemented precompiles are accepted here. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.AccountRuntime
open Core

def contextType : Core.Ty := bundleType
  [WordMapping.type, .word, WordMapping.type, .word, .word, .word,
   .sum .unit .word, WordMapping.type, WordMapping.type, .bool, .bool]

def snapshotType : Core.Ty := bundleType
  [.word, .word, .word, WordMapping.type, WordMapping.type,
   WordMapping.type, .word, WordMapping.type]

def resultType : Core.Ty := .product (LanguageResult.resultType .unit) snapshotType

private abbrev Code := Nat → Core.Expr
private def constant (value : Core.Expr) : Code := fun _ => value
private def number (value : Nat) : Code := constant (.word (Word.ofNatModulo value))
private def boolean (value : Bool) : Code := constant (.bool value)
private def unit : Code := constant .unit
private def empty : Code := constant WordMapping.empty
private def part (index count : Nat) (value : Code) : Code :=
  fun depth => projectArgument index count (value depth)
private def packet (values : List Code) : Code := fun depth => bundle (values.map (· depth))
private def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
private def bindResult (type : Core.Ty) (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind type (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
private def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
private def failure (type : Core.Ty) (reason : Code) : Code := fun depth => LanguageResult.failure type (reason depth)
private def lambda (parameter result : Core.Ty) (body : Code → Code) : Code := fun depth =>
  .lambda parameter result (body (fun here => .var (here - depth - 1)) (depth + 1))
private def apply (function argument : Code) : Code := fun depth => .apply (function depth) (argument depth)
private def choose (test yes no : Code) : Code := fun depth => .ifE (test depth) (yes depth) (no depth)
private def binary (op : BinaryOp) (a b : Code) : Code := fun depth => .binary op (a depth) (b depth)
private def load (reference : Code) : Code := fun depth => .loadCell (reference depth)
private def store (reference value : Code) : Code := fun depth => .storeCell (reference depth) (value depth)
private def allocate (type : Core.Ty) (value : Code) : Code := fun depth => .newCell type (value depth)
private def present (value : Code) : Code := fun depth => .inRight .unit (value depth)
private def lookup (mapping key : Code) : Code := fun depth => WordMapping.lookup (mapping depth) (key depth)
private def insert (mapping key value : Code) : Code := fun depth =>
  WordMapping.insert (mapping depth) (key depth) (value depth)
private def callResult (ok data size : Code) : Code := success (packet [ok, data, size])

private def sharedNames : List String := ["storage", "transient", "logs", "logSize", "balances"]
private abbrev References := List (String × Code)
private def reference (references : References) (name : String) : Code :=
  (references.find? (·.1 == name)).map Prod.snd |>.getD unit

/-- A closed Core function receives frame cells, keeping all generated function
closures attached to those exact cells. -/
private def compileFrame (program : Program) (code : CodeBlock)
    (slots : List (String × Core.Ty)) (fuel : Nat) : LowerM Core.Expr := do
  let entry := "$lean$object$entry"
  if (program.functions ++ code.functions).any (·.name == entry) then
    fail "reserved runtime entry name"
  let function : Function := {name := entry, args := [], ret := .unit, body := code.stmts}
  let runtime : Scope := slots.reverse.map fun (name, type) =>
    ⟨some (Effects.slotName name), type, false⟩
  let (_, body) ← assemble (program.functions ++ code.functions ++ [function]) entry runtime fuel
  let scope := runtime.temporary (LanguageResult.resultType .unit)
  let snapshot ← [("exit", Core.Ty.word), ("returnOffset", .word), ("returnSize", .word),
      ("memory", WordMapping.type), ("storage", WordMapping.type),
      ("logs", WordMapping.type), ("logSize", .word),
      ("balances", WordMapping.type)].mapM fun (name, type) => do
    return Core.Expr.loadCell (← Effects.reference scope name type)
  let completed := Core.Expr.letE body (.pair (.var 0) (bundle snapshot))
  let unpacked := slots.zipIdx.foldr (fun (_, index) body =>
    Core.Expr.letE (projectArgument index slots.length (.var (index + 1))) body) completed
  pure (.lambda (bundleType (slots.map fun (_, type) => .cell type)) resultType (.letE .unit unpacked))

private def allocateFrame (slots : List (String × Core.Ty)) (shared : References)
    (frame callback gas : Code) (codeBytes : Option (List UInt8))
    (continuation : List Code → Code) : Code :=
  let rec loop : List (String × Core.Ty) → List Code → Code
    | [], values => continuation values.reverse
    | (name, type) :: rest, values =>
      if let some (_, sharedReference) := shared.find? (·.1 == name) then
        loop rest (sharedReference :: values)
      else if name == "callHandler" then loop rest (callback :: values)
      else
        let initial := match name with
          | "memory" | "returnData" => empty
          | "address" => part 0 8 frame
          | "caller" => part 1 8 frame
          | "callvalue" => part 2 8 frame
          | "isStatic" => part 3 8 frame
          | "callDepth" => part 4 8 frame
          | "availableGas" => gas
          | "calldata" => part 6 8 frame
          | "calldataSize" => part 7 8 frame
          | "code" => constant (WordMapping.literal (Memory.packBytes (codeBytes.getD [])))
          | "codeSize" => number (codeBytes.getD []).length
          | _ => number 0
        bind (allocate type initial) fun cell => loop rest (cell :: values)
  loop slots []

private def checkpoint (shared : References) (continuation : Code → Code) : Code :=
  let rec capture : List String → List (Code × Code) → Code
    | [], saved =>
      let restore := saved.foldr (fun (cell, value) next => bind (store cell value) (fun _ => next)) unit
      continuation restore
    | name :: rest, saved =>
      let cell := reference shared name
      bind (load cell) fun value => capture rest ((cell, value) :: saved)
  capture sharedNames []

private def precompile (request : Code) : Code :=
  bind (allocate WordMapping.type (part 6 8 request)) fun memory =>
  bind (allocate .word (number 0)) fun size =>
  bind (allocate WordMapping.type empty) fun data =>
  bind (allocate .word (number 0)) fun dataSize =>
  bindResult Calls.responseType (fun depth => Precompiles.staticCall
    (memory depth) (size depth) (data depth) (dataSize depth)
    (part 5 8 request depth) (part 0 8 request depth)
    (number 0 depth) (part 7 8 request depth) (number 0 depth) (number 0 depth)) fun flag =>
  callResult (binary .wordEq flag (number 1)) (load data) (load dataSize)

private def childResult (result : Code) : Code :=
  let status := fun depth => Core.Expr.first (result depth)
  let snapshot := fun depth => Core.Expr.second (result depth)
  let exit := part 0 8 snapshot
  let offset := part 1 8 snapshot
  let count := part 2 8 snapshot
  let memory := part 3 8 snapshot
  let copyResult (ok : Bool) : Code :=
    bind (allocate WordMapping.type empty) fun data =>
    bind (allocate .word (number 0)) fun size =>
    bindResult Calls.responseType (fun depth => Memory.copyPackedFrom
      (data depth) (size depth) (number 0 depth) (memory depth) (offset depth) (count depth)) fun _ =>
    callResult (boolean ok) (load data) count
  choose (binary .wordEq exit (number 3)) (callResult (boolean false) empty (number 0)) <|
  choose (binary .wordEq exit (number 2)) (copyResult false) <|
  choose (binary .wordEq exit (number 1)) (copyResult true) <|
  fun depth => .caseE (status depth)
    (LanguageResult.failure Calls.responseType (.var 0))
    (callResult (boolean true) empty (number 0) (depth + 1))

private def isPrecompile (target : Code) : Code :=
  choose (binary .wordEq target (number 256)) (boolean true)
    (choose (binary .wordGt target (number 0))
      (binary .wordGt (number 5) target) (boolean false))

private def dispatch (slots : List (String × Core.Ty)) (codeBytes : Option (List UInt8))
    (shared : References) (selfAddress emptyAccounts codeAvailable callback compiled request : Code) : Code :=
  let target := part 0 8 request
  let caller := part 1 8 request
  let value := part 2 8 request
  let balances := reference shared "balances"
  let run := choose (isPrecompile target) (precompile request) <|
    choose (binary .wordEq target selfAddress)
      (choose codeAvailable
        (allocateFrame slots shared request callback (present (part 5 8 request)) codeBytes fun cells =>
          bind (apply compiled (packet cells)) childResult)
        (callResult (boolean true) empty (number 0)))
      (bindResult Calls.responseType (lookup emptyAccounts target) fun known =>
        choose (binary .wordEq known (number 1))
          (callResult (boolean true) empty (number 0))
          (failure Calls.responseType (number 7)))
  checkpoint shared fun restore =>
  bindResult Calls.responseType (lookup (load balances) caller) fun callerBalance =>
  choose (binary .wordGt value callerBalance) (callResult (boolean false) empty (number 0)) <|
  bindResult Calls.responseType (lookup (load balances) target) fun targetBalance =>
  -- A self-transfer is a balance check, without a debit or credit.
  bindResult Calls.responseType
    (choose (binary .wordEq value (number 0)) (success unit) <|
      choose (binary .wordEq caller target) (success unit)
      (choose (binary .wordGt targetBalance (binary .wordSub (number (wordModulus - 1)) value))
        (failure .unit (number 12))
        (bindResult .unit (insert (load balances) caller (binary .wordSub callerBalance value)) fun debited =>
          bindResult .unit (insert debited target (binary .wordAdd targetBalance value)) fun credited =>
          success (store balances credited)))) fun _ =>
  fun depth => .caseE (run depth)
    ((bind restore fun _ => failure Calls.responseType (fun here => .var (here - depth - 1))) (depth + 1))
    ((let response : Code := fun here => .var (here - depth - 1)
      choose (part 0 3 response) (success response)
        (bind restore fun _ => success response)) (depth + 1))

private def select : List Object → List String → LowerM CodeBlock
  | _, [] => fail "an explicit Hull object path is required"
  | objects, name :: rest =>
      let candidates := objects.filter fun (.object candidate _ _ _) => candidate == name
      match candidates with
      | [.object _ code children _] => if rest.isEmpty then pure code else select children rest
      | [] => fail s!"unknown Hull object: {name}"
      | _ => fail s!"ambiguous Hull object: {name}"

def compileObject (program : Program) (objectPath : List String)
    (fuel : Nat := 4096) (codeBytes : Option (List UInt8) := none) : LowerM Core.Expr := do
  let code ← select program.objects objectPath
  let slots := Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else [])
  let compiled ← compileFrame program code slots fuel
  let expression := lambda contextType resultType fun context =>
    bind (constant compiled) fun frameCode =>
    bind (allocate WordMapping.type (part 2 11 context)) fun storage =>
    bind (allocate WordMapping.type empty) fun transient =>
    bind (allocate WordMapping.type empty) fun logs =>
    bind (allocate .word (number 0)) fun logSize =>
    bind (allocate WordMapping.type (part 7 11 context)) fun balances =>
    bind (constant (OptionalCell.allocate Calls.callbackType)) fun callback =>
    let shared := [("storage", storage), ("transient", transient), ("logs", logs),
      ("logSize", logSize), ("balances", balances)]
    let handler := lambda Calls.requestType (LanguageResult.resultType Calls.responseType) fun request =>
      dispatch slots codeBytes shared (part 5 11 context) (part 8 11 context) (part 10 11 context) callback frameCode request
    bind (store callback (present handler)) fun _ =>
    let request := packet [part 5 11 context, part 4 11 context, part 3 11 context,
      part 9 11 context, number 0, number 0, part 0 11 context, part 1 11 context]
    allocateFrame slots shared request callback (part 6 11 context) codeBytes fun cells =>
      apply frameCode (packet cells)
  let expression := expression 0
  let type ← (Core.inferDetailed [] [] expression Memory.definitions).mapError fun error =>
    ⟨s!"Core account runtime validation: {reprStr error}", none⟩
  expectType (.function contextType resultType) type
  pure expression

end Solcore.Frontend.RustHull.AccountRuntime
