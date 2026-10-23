import Solcore.Frontend.RustHull.Lowering
import Solcore.Frontend.RustHull.Calls
import Solcore.Frontend.RustHull.AccountState
import Solcore.Frontend.RustHull.CreationRuntime
import Solcore.Frontend.RustHull.MemorySnapshot
import Solcore.Frontend.RustHull.ImageComparison

/-! Message frames, account creation, and transaction finalization expressed
using ordinary Core cells. Executable account images are explicitly linked to
checked Hull objects; code and storage addresses remain separate. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountRuntime
open Core CodeBuilder

structure CodeDefinition where
  program : Program
  path : List String
  bytes : List UInt8
  isInit : Bool := false
  deriving Repr

def contextType : Core.Ty := bundleType
  [WordMapping.type, .word, .word, .word, .word, .sum .unit .word,
   WordMapping.type, AccountState.type, .bool, .bool, Ambient.contextType, .bool]
def snapshotType : Core.Ty := bundleType
  [.word, .word, .word, WordMapping.type, WordMapping.type,
   WordMapping.type, .word, WordMapping.type, AccountState.type]
def resultType : Core.Ty := .product (LanguageResult.resultType .unit) snapshotType
private def dispatchType : Core.Ty := bundleType [Calls.requestType, .word, .word]
private def dispatchCallbackType : Core.Ty :=
  .function dispatchType (LanguageResult.resultType Calls.responseType)
private def callResult (ok data size : Code) : Code := success (packet [ok, data, size])
private def sharedNames : List String := ["world", "logs", "logSize", "balances"]
private abbrev References := List (String × Code)
private def reference (references : References) (name : String) : Code :=
  (references.find? (·.1 == name)).map Prod.snd |>.getD unit
private def raw (expression : Core.Expr) : Code := fun depth => expression.rename (· + depth)
private def first (value : Code) : Code := fun depth => .first (value depth)
private def second (value : Code) : Code := fun depth => .second (value depth)
private def worldGet (shared : References) (target : Code) : Code := fun depth =>
  AccountState.get (load (reference shared "world") depth) (target depth)
    (load (reference shared "worldComplete") depth)

private def compileFrame (program : Program) (code : CodeBlock)
    (slots : List (String × Core.Ty)) (fuel : Nat) : LowerM Core.Expr := do
  let entry := "$lean$object$entry"
  if (program.functions ++ code.functions).any (·.name == entry) then
    fail "reserved runtime entry name"
  let function : Function := {name := entry, args := [], ret := .unit, body := code.stmts}
  let runtime : Scope := slots.reverse.map fun (name, type) =>
    ⟨some (Effects.slotName name), type, false⟩
  let (_, body) ← assemble (program.functions ++ code.functions ++ [function]) entry runtime fuel
  let mut cells : References := []
  for (name, type) in slots do
    cells := cells ++ [(name, raw (← Effects.reference runtime name type))]
  let read (name : String) := load (reference cells name)
  let snapshot (storage : Code) := packet [read "exit", read "returnOffset", read "returnSize",
    read "memory", storage, read "logs", read "logSize", read "balances", read "world"]
  let completed := (bind (raw body) fun status =>
    bind (worldGet cells (read "address")) fun account => fun depth =>
      .caseE (account depth)
        ((packet [failure .unit (fun here => .var (here - depth - 1)), snapshot empty]) (depth + 1))
        ((packet [status, snapshot (part 0 9 (fun here => .var (here - depth - 1)))]) (depth + 1))) 0
  let unpacked := slots.zipIdx.foldr (fun (_, index) body =>
    Core.Expr.letE (projectArgument index slots.length (.var (index + 1))) body) completed
  pure (.lambda (bundleType (slots.map fun (_, type) => .cell type)) resultType (.letE .unit unpacked))

private def allocateFrame (slots : List (String × Core.Ty)) (shared : References)
    (frame dispatcher creator gas code codeSize codeKnown : Code)
    (continuation : List Code → Code) : Code :=
  let wrapper (mode : Nat) : Code :=
    lambda Calls.requestType (LanguageResult.resultType Calls.responseType) fun request =>
      bindResult Calls.responseType (fun depth => OptionalCell.read dispatchCallbackType (dispatcher depth) (Word.ofNatModulo 7)) fun handler =>
      apply handler (packet [request, number mode, part 0 8 frame])
  let rec loop : List (String × Core.Ty) → List Code → Code
    | [], values => continuation values.reverse
    | (name, type) :: rest, values =>
      if let some (_, cell) := shared.find? (·.1 == name) then loop rest (cell :: values)
      else if name == "createHandler" then loop rest (creator :: values)
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
          | "callHandler" => present (wrapper 0)
          | "callCodeHandler" => present (wrapper 1)
          | "delegateCallHandler" => present (wrapper 2)
          | "code" => code
          | "codeSize" => codeSize
          | "codeKnown" => codeKnown
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
  let snapshot := second result
  let exit := part 0 9 snapshot
  let offset := part 1 9 snapshot
  let count := part 2 9 snapshot
  let memory := part 3 9 snapshot
  let copyResult (ok : Bool) : Code :=
    bindResult Calls.responseType (fun depth => MemorySnapshot.extract
      (memory depth) (offset depth) (count depth)) fun data =>
    callResult (boolean ok) data count
  choose (binary .wordEq exit (number 3)) (callResult (boolean false) empty (number 0)) <|
  choose (binary .wordEq exit (number 2)) (copyResult false) <|
  choose (binary .wordEq exit (number 1)) (copyResult true) <|
  fun depth => .caseE (first result depth)
    (LanguageResult.failure Calls.responseType (.var 0))
    (callResult (boolean true) empty (number 0) (depth + 1))

private def isPrecompile (target : Code) : Code :=
  choose (binary .wordEq target (number 256)) (boolean true)
    (choose (binary .wordGt target (number 0))
      (binary .wordGt (number 5) target) (boolean false))

/-- Balance checks and transfers use the execution address even for delegated
frames. CALLCODE checks funds without moving them; DELEGATECALL inherits value. -/
private def transfer (shared : References) (source target value : Code) : Code :=
  let balances := reference shared "balances"
  choose (binary .wordEq value (number 0)) (success unit) <|
  choose (binary .wordEq source target) (success unit) <|
  bindResult .unit (lookup (load balances) source) fun sourceBalance =>
  bindResult .unit (lookup (load balances) target) fun targetBalance =>
  choose (binary .wordGt targetBalance (binary .wordSub (number (wordModulus - 1)) value))
    (failure .unit (number 12)) <|
  bindResult .unit (insert (load balances) source (binary .wordSub sourceBalance value)) fun debited =>
  bindResult .unit (insert debited target (binary .wordAdd targetBalance value)) fun credited =>
  success (store balances credited)

private def dispatch (shared : References) (runFrame : Code → Code → Code)
    (extended : Code) : Code :=
  let request := part 0 3 extended
  let mode := part 1 3 extended
  let source := part 2 3 extended
  let target := part 0 8 request
  let value := part 2 8 request
  let executionAddress := choose (binary .wordEq mode (number 0)) target source
  let run := choose (isPrecompile target) (precompile request) <|
    bindResult Calls.responseType (worldGet shared target) fun record =>
      choose (binary .wordEq (part 3 9 record) (number 0))
        (choose (part 6 9 record)
          (choose (binary .wordEq (part 5 9 record) (number 0))
            (callResult (boolean true) empty (number 0))
            (failure Calls.responseType (number 16)))
          (failure Calls.responseType (number 15)))
        (runFrame record (packet [executionAddress, part 1 8 request, value,
          part 3 8 request, part 4 8 request, part 5 8 request, part 6 8 request, part 7 8 request]))
  checkpoint shared fun restore =>
  bindResult Calls.responseType (lookup (load (reference shared "balances")) source) fun sourceBalance =>
  choose (choose (binary .wordEq mode (number 2)) (boolean false)
    (binary .wordGt value sourceBalance)) (callResult (boolean false) empty (number 0)) <|
  bindResult Calls.responseType
    (choose (binary .wordEq mode (number 0)) (transfer shared source target value) (success unit)) fun _ =>
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

private def imageMatches (bytes : List UInt8) (memory size : Code) (allowSuffix : Bool) : Code :=
  fun depth => ImageComparison.compareBytes bytes (memory depth) (size depth) allowSuffix

private def install (shared : References) (images : List (Nat × List UInt8))
    (target response : Code) : Code :=
  let rec identify : List (Nat × List UInt8) → Code
    | [] => failure .word (number 16)
    | (identity, bytes) :: rest =>
      bindResult .word (imageMatches bytes (part 1 3 response) (part 2 3 response) false) fun yes =>
      choose yes (success (number identity)) (identify rest)
  bindResult .unit
    (choose (binary .wordEq (part 2 3 response) (number 0)) (success (number 0)) (identify images)) fun identity =>
  bindResult .unit (worldGet shared target) fun record =>
  let updated := fun depth =>
    AccountState.replace (AccountState.replace (AccountState.replace
      (AccountState.replace (record depth) 3 (identity depth))
      4 (part 1 3 response depth)) 5 (part 2 3 response depth)) 6 (.bool true)
  bindResult .unit (fun depth => AccountState.put (load (reference shared "world") depth)
    (target depth) (updated depth)) fun world => success (store (reference shared "world") world)

private def replaceResult (result status : Code) (exit : Option Code := none) : Code :=
  packet [status, packet ((List.range 9).map fun index =>
    if index == 0 then exit.getD (part 0 9 (second result)) else part index 9 (second result))]

private def finalize (shared : References) (target result : Code) : Code :=
  bind (fun depth => AccountState.finalize (reference shared "world" depth)
    (reference shared "balances" depth)) fun finalized =>
  let rebuilt (storage : Code) := packet [first result,
    packet ((List.range 9).map fun index =>
      if index == 4 then storage else if index == 7 then load (reference shared "balances")
      else if index == 8 then load (reference shared "world") else part index 9 (second result))]
  let failed (reason : Code) := replaceResult result (failure .unit reason) (some (number 0))
  fun depth => .caseE (finalized depth)
    (failed (fun here => .var (here - depth - 1)) (depth + 1))
    ((bind (fun here => AccountState.get (load (reference shared "world") here) (target here) (.bool true)) fun account =>
      fun here => .caseE (account here)
        (failed (fun d => .var (d - here - 1)) (here + 1))
        (rebuilt (part 0 9 (fun d => .var (d - here - 1))) (here + 1))) (depth + 1))

private def finishDeployment (shared : References) (images : List (Nat × List UInt8))
    (target result : Code) : Code :=
  let failed (reason : Code) := replaceResult result (failure .unit reason) (some (number 0))
  let invalid := replaceResult result (success unit) (some (number 3))
  let completed := finalize shared target result
  let installation := bindResult .unit (childResult result) fun response =>
    bindResult .unit (fun depth => Memory.readMemoryByte (part 1 3 response depth) (number 0 depth)) fun leading =>
    choose (binary .wordGt (part 2 3 response) (number 24576)) (failure .unit (number 17)) <|
    choose (choose (binary .wordEq (part 2 3 response) (number 0)) (boolean false)
      (binary .wordEq leading (number 239))) (failure .unit (number 17)) <|
    install shared images target response
  fun depth => .caseE (installation depth)
    ((let reason : Code := fun here => .var (here - depth - 1)
      choose (binary .wordEq reason (number 17)) invalid (failed reason)) (depth + 1))
    (completed (depth + 1))

private def allocateShared (context : Code) (continuation : References → Code) : Code :=
  let values := [("world", AccountState.type, part 7 12 context),
    ("worldComplete", .bool, part 9 12 context),
    ("logs", WordMapping.type, empty), ("logSize", .word, number 0),
    ("balances", WordMapping.type, part 6 12 context)] ++
    (Ambient.slots.zipIdx.map fun ((name, type), index) =>
      (name, type, part index Ambient.slots.length (part 10 12 context)))
  let rec loop : List (String × Core.Ty × Code) → References → Code
    | [], references => continuation references
    | (name, type, value) :: rest, references =>
      bind (allocate type value) fun cell => loop rest ((name, cell) :: references)
  loop values []

def compileObject (program : Program) (objectPath : List String)
    (fuel : Nat := 4096) (codeBytes : Option (List UInt8) := none)
    (catalog : List CodeDefinition := []) : LowerM Core.Expr := do
  let code ← select program.objects objectPath
  let slots := Effects.slots ++ (if codeBytes.isSome || !catalog.isEmpty then Effects.codeSlots else [])
  let compiled ← compileFrame program code slots fuel
  let others ← catalog.mapM fun definition => do
    compileFrame definition.program (← select definition.program.objects definition.path) slots fuel
  let images := (codeBytes.toList.map (1, ·)) ++
    (catalog.zipIdx.filterMap fun (definition, index) =>
      if definition.isInit then none else some (index + 2, definition.bytes))
  let expression := lambda contextType resultType fun context =>
    bind (packet ((compiled :: others).map constant)) fun functions =>
    allocateShared context fun shared =>
    bind (constant (OptionalCell.allocate dispatchCallbackType)) fun dispatcher =>
    bind (constant (OptionalCell.allocate Creation.callbackType)) fun creator =>
    let invoke (index : Nat) (frame gas bytes size known : Code) :=
      allocateFrame slots shared frame dispatcher creator gas bytes size known fun cells =>
        bind (apply (part index (others.length + 1) functions) (packet cells)) childResult
    let runFrame (record frame : Code) :=
      (List.range (others.length + 1)).foldr (fun index fallback =>
        choose (binary .wordEq (part 3 9 record) (number (index + 1)))
          (invoke index frame (present (part 5 8 frame)) (part 4 9 record) (part 5 9 record) (part 6 9 record))
          fallback) (failure Calls.responseType (number 16))
    let runInit (target request : Code) :=
      let templates := catalog.zipIdx.filter fun (definition, _) => definition.isInit
      let rec identify : List (CodeDefinition × Nat) → Code → Code
        | [], found => success found
        | (definition, index) :: rest, found =>
          bindResult .word (imageMatches definition.bytes (part 6 8 request) (part 7 8 request) true) fun yes =>
          choose yes
            (choose (binary .wordEq found (number 0)) (identify rest (number (index + 2)))
              (failure .word (number 16)))
            (identify rest found)
      bindResult Calls.responseType (identify templates (number 0)) fun identity =>
      templates.foldr (fun (_, index) fallback =>
        choose (binary .wordEq identity (number (index + 2)))
          (invoke (index + 1)
            (packet [target, part 0 8 request, part 1 8 request, boolean false,
              part 4 8 request, part 5 8 request, empty, number 0])
            (present (part 5 8 request)) (part 6 8 request) (part 7 8 request) (boolean true)) fallback)
        (failure Calls.responseType (number 16))

    let handler := lambda dispatchType (LanguageResult.resultType Calls.responseType) (dispatch shared runFrame)
    let createHandler := lambda Creation.requestType (LanguageResult.resultType Creation.responseType) fun request =>
      CreationRuntime.dispatch (reference shared "world") (reference shared "balances")
        (reference shared "logs") (reference shared "logSize")
        (load (reference shared "worldComplete")) request runInit (install shared images)
    bind (store dispatcher (present handler)) fun _ =>
    bind (store creator (present createHandler)) fun _ =>
    let request := packet [part 4 12 context, part 3 12 context, part 2 12 context,
      part 8 12 context, number 0, number 0, part 0 12 context, part 1 12 context]
    allocateFrame slots shared request dispatcher creator (part 5 12 context)
      (constant (WordMapping.literal (Memory.packBytes (codeBytes.getD []))))
      (number (codeBytes.getD []).length) (boolean codeBytes.isSome) fun cells =>
    bind (apply (part 0 (others.length + 1) functions) (packet cells)) fun result =>
    -- A failed top-level message exports no state. Successful completion resets
    -- transaction-local state and applies delayed SELFDESTRUCT deletion.
    let finish := choose (part 11 12 context)
      (finishDeployment shared images (part 4 12 context) result)
      (finalize shared (part 4 12 context) result)
    let successful := choose (binary .wordEq (part 0 9 (second result)) (number 1)) (boolean true)
      (choose (binary .wordEq (part 0 9 (second result)) (number 0))
        (fun depth => .caseE (first result depth) (.bool false) (.bool true)) (boolean false))
    choose successful finish result
  let expression := expression 0
  let type ← (Core.inferDetailed [] [] expression AccountState.definitions).mapError fun error =>
    ⟨s!"Core account runtime validation: {reprStr error}", none⟩
  expectType (.function contextType resultType) type
  pure expression

end Solcore.Frontend.RustHull.AccountRuntime
