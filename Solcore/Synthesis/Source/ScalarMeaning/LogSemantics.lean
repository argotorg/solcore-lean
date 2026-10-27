import Solcore.Synthesis.Source.ScalarMeaning.RollbackSemantics

/-! Log programs: rollback programs that may also write memory and emit logs,
as a separate grammar and meaning, so the rollback fragment and every result
about it are unchanged. A file imports `sload`, `sstore`, `mload`, `mstore` and
`revert_` from `std.opcodes`, optionally followed by `opcode as alias` pairs;
an alias of `log0` to `log4` names that wrapper. Besides the rollback
statements, its method body may contain the store `mstore(offset, value);` and
the log block

    if (a op b) {
        let x: T = f(c op' d);
        mstore(offset, value);
        ...
        logger(offset, size, topic1, ..., topicN);
    }

whose `if` has no `else` (`crates/parser/src/parse/stmt.rs`). The block binds
one call `let` in its own scope, writes memory and emits one log. As `sload`
reads the current storage, the method body's calls to `mload` read the current
memory; free functions see no memory.

The pinned `std.opcodes` wrappers pass their `word` arguments to `MLOAD`,
`MSTORE` and `LOG0` to `LOG4`. Memory is known word by word: a byte offset maps
to the word whose 32-byte big-endian encoding starts there, when the fragment
knows it. `mstore` makes its word known and forgets every known word whose
bytes overlap it. `mload` and a log read only known words; a log's data are the
`size / 32` words from its offset. A size that is not a multiple of 32, bytes
at or past `2^256`, or an unknown word has no meaning. Gas and memory expansion
are not modeled.

A call returns its word with the final storage and its logs in emission order,
or reverts with the word of its revert data. A revert discards the call's
storage writes and its logs, so the outcome records only the data. Nothing here
refers to Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-- The body of a log block: the call `let x: T = f(a op b);`, the stores
`mstore(offset, value);` in order, and the call
`logger(dataOffset, dataSize, topic1, ..., topicN);`. -/
structure LogBlock where
  identifier : String
  type : LocalType
  callee : String
  op : BinaryOp
  left : Expr
  right : Expr
  stores : List (Operand × Operand)
  logger : String
  dataOffset : Operand
  dataSize : Operand
  topics : List Operand
  deriving Repr

/-- A statement of a log method body. -/
inductive LogStmt where
  /-- A rollback statement. -/
  | rollback (statement : RollbackStmt)
  /-- `mstore(offset, value);` -/
  | store (offset value : Operand)
  /-- `if (a op b) { block }` -/
  | logIf (op : BinaryOp) (left right : Expr) (block : LogBlock)
  deriving Repr

/-- A public method with `uint256` parameters whose final statement is
`return uint256(result);`. -/
structure LogMethod where
  name : String
  parameters : List String
  body : List LogStmt
  result : Operand
  deriving Repr

/-- A log file: the imports, free functions and one contract with one method. -/
structure LogFile where
  opcodeAliases : List (String × String)
  functions : List FunctionDecl
  contract : String
  method : LogMethod
  deriving Repr

/-- The block's binding, as the storage statement it prints as. -/
def LogBlock.binding (block : LogBlock) : StorageStmt :=
  .letCall block.identifier block.type block.callee block.op block.left block.right

/-! ### Identifiers -/

def storesIdentifiers : List (Operand × Operand) → List String
  | [] => []
  | (offset, value) :: rest => offset.identifiers ++ value.identifiers ++ storesIdentifiers rest

def topicsIdentifiers : List Operand → List String
  | [] => []
  | topic :: rest => topic.identifiers ++ topicsIdentifiers rest

def LogBlock.identifiers (block : LogBlock) : List String :=
  block.binding.identifiers ++ storesIdentifiers block.stores ++
    block.logger :: (block.dataOffset.identifiers ++ block.dataSize.identifiers ++
      topicsIdentifiers block.topics)

def LogStmt.identifiers : LogStmt → List String
  | .rollback statement => statement.identifiers
  | .store offset value => offset.identifiers ++ value.identifiers
  | .logIf _ left right block => left.identifiers ++ right.identifiers ++ block.identifiers

def LogStmt.listIdentifiers : List LogStmt → List String
  | [] => []
  | statement :: rest => statement.identifiers ++ LogStmt.listIdentifiers rest

/-! ### Printing -/

def storeLine (indent : Nat) (offset value : Operand) : String :=
  indentLine indent ("mstore(" ++ offset.print ++ ", " ++ value.print ++ ");")

def storesLines (indent : Nat) : List (Operand × Operand) → List String
  | [] => []
  | (offset, value) :: rest => storeLine indent offset value :: storesLines indent rest

/-- Each topic after a comma. -/
def topicsText : List Operand → String
  | [] => ""
  | topic :: rest => ", " ++ topic.print ++ topicsText rest

def LogBlock.lines (indent : Nat) (block : LogBlock) : List String :=
  block.binding.lines indent ++ storesLines indent block.stores ++
    [indentLine indent (block.logger ++ "(" ++ block.dataOffset.print ++ ", " ++
      block.dataSize.print ++ topicsText block.topics ++ ");")]

def LogStmt.lines (indent : Nat) : LogStmt → List String
  | .rollback statement => statement.lines indent
  | .store offset value => [storeLine indent offset value]
  | .logIf op left right block =>
      [indentLine indent ("if (" ++ (Operand.operation op left right).print ++ ") {")] ++
        block.lines (indent + 4) ++ [indentLine indent "}"]

def LogStmt.listLines (indent : Nat) : List LogStmt → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ LogStmt.listLines indent rest

/-- `import {sload, sstore, mload, mstore, revert_, opcode as alias, ...} from std.opcodes;` -/
def logImportLine (aliases : List (String × String)) : String :=
  "import {" ++ String.intercalate ", " (["sload", "sstore", "mload", "mstore", "revert_"] ++
    aliases.map fun alias => alias.1 ++ " as " ++ alias.2) ++ "} from std.opcodes;"

def LogFile.lines (file : LogFile) : List String :=
  ["import * from std;", "import * from std.dispatch;", logImportLine file.opcodeAliases, ""] ++
  file.functions.flatMap FunctionDecl.lines ++
  ["contract " ++ file.contract ++ " {",
    "    function " ++ file.method.name ++ "(" ++ Method.parameterText file.method.parameters ++
      ") public returns (uint256) {"] ++
  LogStmt.listLines 8 file.method.body ++
  ["        return uint256(" ++ file.method.result.print ++ ");", "    }", "}"]

def LogFile.print (file : LogFile) : String :=
  String.intercalate "\n" file.lines ++ "\n"

/-! ### Meaning -/

/-- Memory known word by word: `memory offset = some value` when the 32 bytes
from byte `offset` are known to be the big-endian encoding of `value`. -/
abbrev Memory := Nat → Option Nat

/-- `MSTORE`: the 32 bytes from `offset` hold `value`; a word known at another
offset whose bytes overlap them is no longer known. -/
def Memory.store (memory : Memory) (offset value : Nat) : Memory :=
  fun other =>
    if other = offset then some value
    else if other + 32 ≤ offset ∨ offset + 32 ≤ other then memory other
    else none

/-- The `count` words from `offset`, 32 bytes apart, when all are known. -/
def Memory.words (memory : Memory) : Nat → Nat → Option (List Nat)
  | _, 0 => some []
  | offset, count + 1 => do
      let first ← memory offset
      let rest ← memory.words (offset + 32) count
      some (first :: rest)

/-- `mload` over a memory: the known word at the offset its one word argument
names, when its 32 bytes lie below `2^256`. -/
def memoryLoadMeaning (memory : Memory) : List Value → Option Value
  | [.word offset] => if offset + 32 ≤ Evm.modulus then (memory offset).map .word else none
  | _ => none

/-- The call context in which `mload` reads the given memory. -/
def Context.withMemory (context : Context) (memory : Memory) : Context :=
  { context with functions := ("mload", memoryLoadMeaning memory) :: context.functions }

/-- The `std.opcodes` function a callee names through an import alias. A
function of the same name shadows the alias, as in `Context.call`. -/
def Context.opcode? (context : Context) (callee : String) : Option String :=
  match context.functions.find? (·.1 == callee) with
  | some _ => none
  | none => (context.aliases.find? (·.2 == callee)).map Prod.fst

/-- One log: its topics and its data words, in order. -/
structure SourceLog where
  topics : List Nat
  data : List Nat
  deriving Repr, DecidableEq

/-- The word an operand means. -/
def Operand.word? (context : Context) (frames : Frames) (operand : Operand) : Option Nat :=
  match operand.expr.eval context frames with
  | some (.word value) => some value
  | _ => none

/-- The words of operands, evaluated left to right. -/
def Operand.words? (context : Context) (frames : Frames) : List Operand → Option (List Nat)
  | [] => some []
  | operand :: rest => do
      let value ← operand.word? context frames
      let values ← Operand.words? context frames rest
      some (value :: values)

/-- `mstore(offset, value);` against a storage and a memory: the offset and
then the value must be words, and the 32 bytes must lie below `2^256`. -/
def storeWord (context : Context) (storage : Storage) (frames : Frames) (memory : Memory)
    (offset value : Operand) : Option Memory := do
  let current := (context.withMemory memory).withStorage storage
  let address ← offset.word? current frames
  let word ← value.word? current frames
  if address + 32 ≤ Evm.modulus then some (memory.store address word) else none

def storeWords (context : Context) (storage : Storage) (frames : Frames) :
    Memory → List (Operand × Operand) → Option Memory
  | memory, [] => some memory
  | memory, (offset, value) :: rest => do
      let memory' ← storeWord context storage frames memory offset value
      storeWords context storage frames memory' rest

/-- The log of `logger(offset, size, topics)`: the logger names the
`std.opcodes` wrapper `logN` for its `N ≤ 4` topics, the size is a multiple of
32, the bytes lie below `2^256`, and the data are the known words from the
offset. -/
def emitLog (context : Context) (memory : Memory) (logger : String) (offset size : Nat)
    (topics : List Nat) : Option SourceLog :=
  if context.opcode? logger = some ("log" ++ toString topics.length) ∧ topics.length ≤ 4 ∧
      size % 32 = 0 ∧ offset + size ≤ Evm.modulus then
    (memory.words offset (size / 32)).map fun data => ⟨topics, data⟩
  else none

/-- A log block from a storage, a memory and frames. The binding runs in a
fresh scope, which the stores and the log call see; the block's emitted log is
returned with the memory after its stores. -/
def LogBlock.exec (context : Context) (storage : Storage) (memory : Memory) (frames : Frames)
    (block : LogBlock) : Option (Memory × SourceLog) := do
  let (_, inner) ← block.binding.exec (context.withMemory memory) (storage, [] :: frames)
  let memory' ← storeWords context storage inner memory block.stores
  let current := (context.withMemory memory').withStorage storage
  let offset ← block.dataOffset.word? current inner
  let size ← block.dataSize.word? current inner
  let topics ← Operand.words? current inner block.topics
  let log ← emitLog current memory' block.logger offset size topics
  some (memory', log)

/-- After log statements: the storage, memory, logs and frames to go on with,
or the word of a revert. -/
inductive LogFlow where
  | next (storage : Storage) (memory : Memory) (logs : List SourceLog) (frames : Frames)
  | reverted (data : Nat)

/-- One statement. A rollback statement runs as in the rollback fragment, its
calls to `mload` reading the current memory. A store replaces memory. The log
block's condition must be a Boolean: when it is `false` the block does nothing,
and when it is `true` the block runs and its log follows the earlier ones; the
block's scope ends with it. -/
def LogStmt.exec (context : Context) (storage : Storage) (memory : Memory)
    (logs : List SourceLog) (frames : Frames) : LogStmt → Option LogFlow
  | .rollback statement =>
      (statement.exec (context.withMemory memory) storage frames).map fun
        | .next storage' frames' => .next storage' memory logs frames'
        | .reverted data => .reverted data
  | .store offset value =>
      (storeWord context storage frames memory offset value).map fun memory' =>
        .next storage memory' logs frames
  | .logIf op left right block =>
      match (Expr.binary op left right).eval ((context.withMemory memory).withStorage storage)
          frames with
      | some (.bool false) => some (.next storage memory logs frames)
      | some (.bool true) =>
          (block.exec context storage memory frames).map fun emitted =>
            .next storage emitted.1 (logs ++ [emitted.2]) frames
      | _ => none

def LogStmt.execList (context : Context) :
    Storage → Memory → List SourceLog → Frames → List LogStmt → Option LogFlow
  | storage, memory, logs, frames, [] => some (.next storage memory logs frames)
  | storage, memory, logs, frames, statement :: rest =>
      match statement.exec context storage memory logs frames with
      | some (.next storage' memory' logs' frames') =>
          LogStmt.execList context storage' memory' logs' frames' rest
      | some (.reverted data) => some (.reverted data)
      | none => none

/-- The outcome of a call: the returned word with the final storage and the
emitted logs, or the word whose 32-byte big-endian encoding is the revert data.
A reverted call leaves the storage it started from and emits no log. -/
inductive LogOutcome where
  | returned (value : Nat) (storage : Storage) (logs : List SourceLog)
  | reverted (data : Nat)

/-- `RollbackMethod.run` with memory and logs: the body starts from the given
memory and no log. -/
def LogMethod.run (context : Context) (method : LogMethod) (storage : Storage) (memory : Memory)
    (arguments : List Nat) : Option LogOutcome := do
  let parameters ← Method.bindParameters method.parameters arguments
  match ← LogStmt.execList context storage memory [] [[], parameters] method.body with
  | .reverted data => some (.reverted data)
  | .next storage' memory' logs frames =>
      match ← (Expr.uint256 method.result.expr).eval
          ((context.withMemory memory').withStorage storage') frames with
      | .uint256 value => some (.returned value storage' logs)
      | _ => none

/-- The file's call context, without storage or memory. -/
def LogFile.context (file : LogFile) : Context :=
  { functions := declareFunctions file.opcodeAliases [] file.functions
    aliases := file.opcodeAliases }

/-- The outcome of calling `method` from the given storage and the memory the
dispatcher leaves. -/
def LogFile.call (file : LogFile) (storage : Storage) (memory : Memory) (method : String)
    (arguments : List Nat) : Option LogOutcome :=
  if file.method.name = method then file.method.run file.context storage memory arguments
  else none

end Solcore.Synthesis.Source.ScalarMeaning
