import Solcore.Synthesis.Source.ScalarMeaning.StorageSemantics

/-! Rollback programs: storage programs that may end with a revert, as a
separate grammar and meaning, so the storage fragment and every result about it
are unchanged. A file imports `sload`, `sstore`, `mstore` and `revert_` from
`std.opcodes`, optionally followed by `opcode as alias` pairs. Besides the
storage statements, its method body may contain `let x: T = a op b;` with one
infix operation without parentheses, and the terminal revert block

    if (a op b) {
        mstore(offset, value);
        revert_(offset, 32);
    }

whose `if` has no `else` (`crates/parser/src/parse/stmt.rs`). The pinned
`std.opcodes` wrappers pass their `word` arguments to the EVM instructions
`MSTORE` and `REVERT`: the block writes the 32-byte big-endian encoding of
`value` at `offset` and reverts with the 32 bytes at `offset`, which are exactly
those bytes. The block therefore reverts with `value`; another data offset or
size reads memory that this fragment does not model and has no meaning.

A call returns its word with the final storage, or reverts with the word of
its revert data. A revert discards the call's storage writes, so the storage
after a reverted call is the storage it started from; the outcome records only
the data. Nothing here refers to Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-- A statement of a rollback method body. -/
inductive RollbackStmt where
  /-- A storage statement. -/
  | storage (statement : StorageStmt)
  /-- `let x: T = a op b;` -/
  | letOperation (identifier : String) (type : LocalType) (op : BinaryOp) (left right : Expr)
  /-- `if (a op b) { mstore(offset, value); revert_(dataOffset, size); }` -/
  | revertIf (op : BinaryOp) (left right : Expr) (offset value dataOffset size : Operand)
  deriving Repr

/-- A public method with `uint256` parameters whose final statement is
`return uint256(result);`. -/
structure RollbackMethod where
  name : String
  parameters : List String
  body : List RollbackStmt
  result : Operand
  deriving Repr

/-- A rollback file: the imports, free functions and one contract with one
method. -/
structure RollbackFile where
  opcodeAliases : List (String × String)
  functions : List FunctionDecl
  contract : String
  method : RollbackMethod
  deriving Repr

/-! ### Identifiers -/

def RollbackStmt.identifiers : RollbackStmt → List String
  | .storage statement => statement.identifiers
  | .letOperation identifier _ _ left right =>
      identifier :: (left.identifiers ++ right.identifiers)
  | .revertIf _ left right offset value dataOffset size =>
      left.identifiers ++ right.identifiers ++ offset.identifiers ++ value.identifiers ++
        dataOffset.identifiers ++ size.identifiers

def RollbackStmt.listIdentifiers : List RollbackStmt → List String
  | [] => []
  | statement :: rest => statement.identifiers ++ RollbackStmt.listIdentifiers rest

/-! ### Printing -/

def RollbackStmt.lines (indent : Nat) : RollbackStmt → List String
  | .storage statement => statement.lines indent
  | .letOperation identifier type op left right =>
      [indentLine indent ("let " ++ identifier ++ ": " ++ type.spelling ++ " = " ++
        (Operand.operation op left right).print ++ ";")]
  | .revertIf op left right offset value dataOffset size =>
      [indentLine indent ("if (" ++ (Operand.operation op left right).print ++ ") {"),
        indentLine (indent + 4) ("mstore(" ++ offset.print ++ ", " ++ value.print ++ ");"),
        indentLine (indent + 4) ("revert_(" ++ dataOffset.print ++ ", " ++ size.print ++ ");"),
        indentLine indent "}"]

def RollbackStmt.listLines (indent : Nat) : List RollbackStmt → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ RollbackStmt.listLines indent rest

/-- `import {sload, sstore, mstore, revert_, opcode as alias, ...} from std.opcodes;` -/
def rollbackImportLine (aliases : List (String × String)) : String :=
  "import {" ++ String.intercalate ", " (["sload", "sstore", "mstore", "revert_"] ++
    aliases.map fun alias => alias.1 ++ " as " ++ alias.2) ++ "} from std.opcodes;"

def RollbackFile.lines (file : RollbackFile) : List String :=
  ["import * from std;", "import * from std.dispatch;", rollbackImportLine file.opcodeAliases,
    ""] ++
  file.functions.flatMap FunctionDecl.lines ++
  ["contract " ++ file.contract ++ " {",
    "    function " ++ file.method.name ++ "(" ++ Method.parameterText file.method.parameters ++
      ") public returns (uint256) {"] ++
  RollbackStmt.listLines 8 file.method.body ++
  ["        return uint256(" ++ file.method.result.print ++ ");", "    }", "}"]

def RollbackFile.print (file : RollbackFile) : String :=
  String.intercalate "\n" file.lines ++ "\n"

/-! ### Meaning -/

/-- The outcome of a call: the returned word with the final storage, or the
word whose 32-byte big-endian encoding is the revert data. A reverted call
leaves the storage it started from. -/
inductive RollbackOutcome where
  | returned (value : Nat) (storage : Storage)
  | reverted (data : Nat)

/-- After rollback statements: the storage and frames to go on with, or the
word of a revert. -/
inductive RollbackFlow where
  | next (storage : Storage) (frames : Frames)
  | reverted (data : Nat)

/-- One statement from a storage and frames. A storage statement runs as in
the storage fragment and an operation `let` as its parenthesized form. The
revert block's condition must be a Boolean. When it is `false` the block does
nothing; when it is `true`, the store's offset and value and the revert's
offset and size must be words, the revert must read the 32 bytes just
written, and the call reverts with the stored word. -/
def RollbackStmt.exec (context : Context) (storage : Storage) (frames : Frames) :
    RollbackStmt → Option RollbackFlow
  | .storage statement =>
      (statement.exec context (storage, frames)).map fun state => .next state.1 state.2
  | .letOperation identifier type op left right =>
      ((Stmt.letDecl identifier type (.binary op left right)).exec
        (context.withStorage storage) frames).map (.next storage)
  | .revertIf op left right offset value dataOffset size =>
      match (Expr.binary op left right).eval (context.withStorage storage) frames with
      | some (.bool false) => some (.next storage frames)
      | some (.bool true) =>
          match offset.expr.eval (context.withStorage storage) frames,
              value.expr.eval (context.withStorage storage) frames,
              dataOffset.expr.eval (context.withStorage storage) frames,
              size.expr.eval (context.withStorage storage) frames with
          | some (.word stored), some (.word word), some (.word read), some (.word length) =>
              if read = stored ∧ length = 32 then some (.reverted word) else none
          | _, _, _, _ => none
      | _ => none

def RollbackStmt.execList (context : Context) :
    Storage → Frames → List RollbackStmt → Option RollbackFlow
  | current, frames, [] => some (.next current frames)
  | current, frames, statement :: rest =>
      match statement.exec context current frames with
      | some (.next next frames') => RollbackStmt.execList context next frames' rest
      | some (.reverted data) => some (.reverted data)
      | none => none

/-- `StorageMethod.run` with reverts: a revert ends the call; otherwise the
method returns the word of `uint256(result)` with the final storage. -/
def RollbackMethod.run (context : Context) (method : RollbackMethod) (storage : Storage)
    (arguments : List Nat) : Option RollbackOutcome := do
  let parameters ← Method.bindParameters method.parameters arguments
  match ← RollbackStmt.execList context storage [[], parameters] method.body with
  | .reverted data => some (.reverted data)
  | .next storage' frames =>
      match ← (Expr.uint256 method.result.expr).eval (context.withStorage storage') frames with
      | .uint256 value => some (.returned value storage')
      | _ => none

/-- The file's call context, without storage. -/
def RollbackFile.context (file : RollbackFile) : Context :=
  { functions := declareFunctions file.opcodeAliases [] file.functions
    aliases := file.opcodeAliases }

/-- The outcome of calling `method` from the given storage. -/
def RollbackFile.call (file : RollbackFile) (storage : Storage) (method : String)
    (arguments : List Nat) : Option RollbackOutcome :=
  if file.method.name = method then file.method.run file.context storage arguments else none

end Solcore.Synthesis.Source.ScalarMeaning
