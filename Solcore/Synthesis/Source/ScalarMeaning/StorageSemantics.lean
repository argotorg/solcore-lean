import Solcore.Synthesis.Source.ScalarMeaning.Print
import Solcore.Synthesis.Source.ScalarMeaning.Semantics

/-! Storage programs: the loop-free fragment with persistent contract storage,
as a separate grammar and meaning, so `parseSource`, `sourceCall` and every
result about them are unchanged. A file imports `sload` and `sstore` from
`std.opcodes`, optionally followed by `opcode as alias` pairs. Its method body
may also contain `sstore(slot, value);` and `let x: T = f(a op b);`, and returns
`uint256(e)` or `uint256(a op b)`, where `a op b` is one infix operation without
parentheses. As in the pinned frontend (`crates/parser/src/parse/stmt.rs` and
`expr_pat.rs`), a call is a statement and an infix operation needs no
parentheses. The pinned `std.opcodes` wrappers pass their `word` arguments to
the EVM instructions `SLOAD` and `SSTORE`.

Storage maps each slot to a word. A method runs from a storage and returns its
result with the final storage. Its calls to `sload` read the current storage;
`sstore` replaces one slot's word. Free functions see no storage, so a free
function that calls `sload` has no meaning in this fragment. An infix operation
means its parenthesized form. Nothing here refers to Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-- A call argument or a returned value: an expression, or one infix operation
without parentheses. -/
inductive Operand where
  | plain (expression : Expr)
  | operation (op : BinaryOp) (left right : Expr)
  deriving Repr

/-- A statement of a storage method body. -/
inductive StorageStmt where
  /-- A loop-free statement; its calls to `sload` read the current storage. -/
  | plain (statement : Stmt)
  /-- `let x: T = f(a op b);` -/
  | letCall (identifier : String) (type : LocalType) (callee : String) (op : BinaryOp)
      (left right : Expr)
  /-- `sstore(slot, value);` -/
  | store (slot value : Operand)
  deriving Repr

/-- A public method with `uint256` parameters whose final statement is
`return uint256(result);`. -/
structure StorageMethod where
  name : String
  parameters : List String
  body : List StorageStmt
  result : Operand
  deriving Repr

/-- A storage file: the imports, free functions and one contract with one
method. -/
structure StorageFile where
  opcodeAliases : List (String × String)
  functions : List FunctionDecl
  contract : String
  method : StorageMethod
  deriving Repr

/-! ### Identifiers -/

def Operand.identifiers : Operand → List String
  | .plain expression => expression.identifiers
  | .operation _ left right => left.identifiers ++ right.identifiers

def StorageStmt.identifiers : StorageStmt → List String
  | .plain statement => statement.identifiers
  | .letCall identifier _ callee _ left right =>
      identifier :: callee :: (left.identifiers ++ right.identifiers)
  | .store slot value => slot.identifiers ++ value.identifiers

def StorageStmt.listIdentifiers : List StorageStmt → List String
  | [] => []
  | statement :: rest => statement.identifiers ++ StorageStmt.listIdentifiers rest

/-! ### Printing -/

def Operand.print : Operand → String
  | .plain expression => expression.print
  | .operation op left right => left.print ++ " " ++ op.spelling ++ " " ++ right.print

def StorageStmt.lines (indent : Nat) : StorageStmt → List String
  | .plain statement => statement.lines indent
  | .letCall identifier type callee op left right =>
      [indentLine indent ("let " ++ identifier ++ ": " ++ type.spelling ++ " = " ++ callee ++
        "(" ++ (Operand.operation op left right).print ++ ");")]
  | .store slot value =>
      [indentLine indent ("sstore(" ++ slot.print ++ ", " ++ value.print ++ ");")]

def StorageStmt.listLines (indent : Nat) : List StorageStmt → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ StorageStmt.listLines indent rest

/-- `import {sload, sstore, opcode as alias, ...} from std.opcodes;` -/
def storageImportLine (aliases : List (String × String)) : String :=
  "import {" ++ String.intercalate ", " (["sload", "sstore"] ++
    aliases.map fun alias => alias.1 ++ " as " ++ alias.2) ++ "} from std.opcodes;"

def StorageFile.lines (file : StorageFile) : List String :=
  ["import * from std;", "import * from std.dispatch;", storageImportLine file.opcodeAliases,
    ""] ++
  file.functions.flatMap FunctionDecl.lines ++
  ["contract " ++ file.contract ++ " {",
    "    function " ++ file.method.name ++ "(" ++ Method.parameterText file.method.parameters ++
      ") public returns (uint256) {"] ++
  StorageStmt.listLines 8 file.method.body ++
  ["        return uint256(" ++ file.method.result.print ++ ");", "    }", "}"]

def StorageFile.print (file : StorageFile) : String :=
  String.intercalate "\n" file.lines ++ "\n"

/-! ### Meaning -/

/-- The words of contract storage, by slot. -/
abbrev Storage := Nat → Nat

/-- Replace one slot's word. -/
def Storage.write (storage : Storage) (slot value : Nat) : Storage :=
  fun other => if other = slot then value else storage other

/-- `sload` over a storage: the word of the slot its one word argument names. -/
def loadMeaning (storage : Storage) : List Value → Option Value
  | [.word slot] => some (.word (storage slot))
  | _ => none

/-- The method's call context: `sload` reads the given storage, and every other
call resolves as in the file's context. -/
def Context.withStorage (context : Context) (storage : Storage) : Context :=
  { context with functions := ("sload", loadMeaning storage) :: context.functions }

/-- The expression an operand means: an operation means its parenthesized
form. -/
def Operand.expr : Operand → Expr
  | .plain expression => expression
  | .operation op left right => .binary op left right

/-- One statement from a storage and frames. A loop-free statement or a call
`let` runs as its parenthesized form against the current storage; `sstore`
evaluates its slot and then its value, both of which must be words, and
replaces that slot's word. -/
def StorageStmt.exec (context : Context) : Storage × Frames → StorageStmt →
    Option (Storage × Frames)
  | (storage, frames), .plain statement =>
      (statement.exec (context.withStorage storage) frames).map fun frames' => (storage, frames')
  | (storage, frames), .letCall identifier type callee op left right =>
      ((Stmt.letDecl identifier type (.call1 callee (.binary op left right))).exec
        (context.withStorage storage) frames).map fun frames' => (storage, frames')
  | (storage, frames), .store slot value =>
      match slot.expr.eval (context.withStorage storage) frames,
          value.expr.eval (context.withStorage storage) frames with
      | some (.word slotWord), some (.word valueWord) =>
          some (storage.write slotWord valueWord, frames)
      | _, _ => none

def StorageStmt.execList (context : Context) : Storage × Frames → List StorageStmt →
    Option (Storage × Frames)
  | state, [] => some state
  | state, statement :: rest =>
      match statement.exec context state with
      | some state' => StorageStmt.execList context state' rest
      | none => none

/-- `Method.run` from a storage: the body runs in a block scope inside the
parameter scope, the method returns the word of `uint256(result)` against the
final storage, and that storage is the method's final storage. -/
def StorageMethod.run (context : Context) (method : StorageMethod) (storage : Storage)
    (arguments : List Nat) : Option (Nat × Storage) := do
  let parameters ← Method.bindParameters method.parameters arguments
  let (storage', frames) ← StorageStmt.execList context (storage, [[], parameters]) method.body
  match ← (Expr.uint256 method.result.expr).eval (context.withStorage storage') frames with
  | .uint256 value => some (value, storage')
  | _ => none

/-- The file's call context, without storage: each free function sees only the
functions declared before it. -/
def StorageFile.context (file : StorageFile) : Context :=
  { functions := declareFunctions file.opcodeAliases [] file.functions
    aliases := file.opcodeAliases }

/-- The returned ABI word and the final storage of calling `method` from the
given storage. -/
def StorageFile.call (file : StorageFile) (storage : Storage) (method : String)
    (arguments : List Nat) : Option (Nat × Storage) :=
  if file.method.name = method then file.method.run file.context storage arguments else none

end Solcore.Synthesis.Source.ScalarMeaning
