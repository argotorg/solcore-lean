import Solcore.Synthesis.Source.ScalarMeaning.RollbackSemantics

/-! Keyed programs: rollback programs whose method may also bind the sum of
three expressions, as a separate grammar and meaning, so the rollback fragment
and every result about it are unchanged. Keyed slots need no new form: `sload`
and `sstore` already take any word as their slot, so `sload(sc_key)`,
`sload(sc_key + 1)` and `sstore(sc_key + 1, value)` are storage statements. The
new statement is `let x: T = a + b + c;`. As in the pinned frontend, the
additive operators fold to the left (`crates/parser/src/parse/expr_pat.rs`),
so it means `let x: T = ((a + b) + c);`. Nothing here refers to Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-- A statement of a keyed method body. -/
inductive KeyedStmt where
  /-- A rollback statement. -/
  | rollback (statement : RollbackStmt)
  /-- `let x: T = a + b + c;` -/
  | letSum (identifier : String) (type : LocalType) (first second third : Expr)
  deriving Repr

/-- A public method with `uint256` parameters whose final statement is
`return uint256(result);`. -/
structure KeyedMethod where
  name : String
  parameters : List String
  body : List KeyedStmt
  result : Operand
  deriving Repr

/-- A keyed file: the rollback imports, free functions and one contract with
one method. -/
structure KeyedFile where
  opcodeAliases : List (String × String)
  functions : List FunctionDecl
  contract : String
  method : KeyedMethod
  deriving Repr

def KeyedStmt.identifiers : KeyedStmt → List String
  | .rollback statement => statement.identifiers
  | .letSum identifier _ first second third =>
      identifier :: (first.identifiers ++ second.identifiers ++ third.identifiers)

def KeyedStmt.listIdentifiers : List KeyedStmt → List String
  | [] => []
  | statement :: rest => statement.identifiers ++ KeyedStmt.listIdentifiers rest

/-! ### Printing -/

def KeyedStmt.lines (indent : Nat) : KeyedStmt → List String
  | .rollback statement => statement.lines indent
  | .letSum identifier type first second third =>
      [indentLine indent ("let " ++ identifier ++ ": " ++ type.spelling ++ " = " ++
        first.print ++ " + " ++ second.print ++ " + " ++ third.print ++ ";")]

def KeyedStmt.listLines (indent : Nat) : List KeyedStmt → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ KeyedStmt.listLines indent rest

def KeyedFile.lines (file : KeyedFile) : List String :=
  ["import * from std;", "import * from std.dispatch;", rollbackImportLine file.opcodeAliases,
    ""] ++
  file.functions.flatMap FunctionDecl.lines ++
  ["contract " ++ file.contract ++ " {",
    "    function " ++ file.method.name ++ "(" ++ Method.parameterText file.method.parameters ++
      ") public returns (uint256) {"] ++
  KeyedStmt.listLines 8 file.method.body ++
  ["        return uint256(" ++ file.method.result.print ++ ");", "    }", "}"]

def KeyedFile.print (file : KeyedFile) : String :=
  String.intercalate "\n" file.lines ++ "\n"

/-! ### Meaning -/

/-- One statement from a storage and frames. A rollback statement runs as in
the rollback fragment; a sum `let` runs as its left-nested parenthesized form
against the current storage. -/
def KeyedStmt.exec (context : Context) (storage : Storage) (frames : Frames) :
    KeyedStmt → Option RollbackFlow
  | .rollback statement => statement.exec context storage frames
  | .letSum identifier type first second third =>
      ((Stmt.letDecl identifier type (.binary .add (.binary .add first second) third)).exec
        (context.withStorage storage) frames).map (.next storage)

def KeyedStmt.execList (context : Context) :
    Storage → Frames → List KeyedStmt → Option RollbackFlow
  | current, frames, [] => some (.next current frames)
  | current, frames, statement :: rest =>
      match statement.exec context current frames with
      | some (.next next frames') => KeyedStmt.execList context next frames' rest
      | some (.reverted data) => some (.reverted data)
      | none => none

/-- `RollbackMethod.run` for a keyed method body. -/
def KeyedMethod.run (context : Context) (method : KeyedMethod) (storage : Storage)
    (arguments : List Nat) : Option RollbackOutcome := do
  let parameters ← Method.bindParameters method.parameters arguments
  match ← KeyedStmt.execList context storage [[], parameters] method.body with
  | .reverted data => some (.reverted data)
  | .next storage' frames =>
      match ← (Expr.uint256 method.result.expr).eval (context.withStorage storage') frames with
      | .uint256 value => some (.returned value storage')
      | _ => none

/-- The file's call context, without storage. -/
def KeyedFile.context (file : KeyedFile) : Context :=
  { functions := declareFunctions file.opcodeAliases [] file.functions
    aliases := file.opcodeAliases }

/-- The outcome of calling `method` from the given storage. -/
def KeyedFile.call (file : KeyedFile) (storage : Storage) (method : String)
    (arguments : List Nat) : Option RollbackOutcome :=
  if file.method.name = method then file.method.run file.context storage arguments else none

end Solcore.Synthesis.Source.ScalarMeaning
