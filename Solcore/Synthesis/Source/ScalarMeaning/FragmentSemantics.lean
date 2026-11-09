import Solcore.Synthesis.Source.ScalarMeaning.Grammar
import Solcore.Synthesis.Source.ScalarMeaning.Semantics

/-!
# Meaning of the larger fragments

Loop, generic, storage, rollback and keyed programs, each a separate grammar and meaning. Main
declarations: `LoopStmt`, `InfixStmt`, `StorageStmt`, `RollbackStmt`, `KeyedStmt`, `Operand`.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.GenericSemantics
/-! Generic programs: the source fragment with the forms that the generic
selection wrapper adds, as a separate grammar and meaning, so `parseSource`,
`sourceCall` and every result about them are unchanged. A file may declare
generic free functions before the ordinary ones. A generic function has type
parameters, which may stand for the type of a parameter or of the result, and
its body may return early from `if (c) { return e; }`, an `if` without `else`
whose condition is a Boolean local.
A method-body statement may also be `let x: T = a op b;` or `x = a op b;` with
one infix operation without parentheses, also in the cases of a `match`. As in
the pinned frontend (`crates/parser/src/parse/items.rs`, `stmt.rs` and
`expr_pat.rs`), type parameters follow the function name in angle brackets, an
`if` needs no `else`, `return` is a statement and an infix operation needs no
parentheses. The meaning is dynamic: a type parameter admits every value, and
the frontend's typing instantiates it consistently. An infix statement means
the same statement with the parenthesized operation. Nothing here refers to
Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-- A type in a generic signature: a type of the fragment or a type
parameter. -/
inductive TypeRef where
  | concrete (type : LocalType)
  | param (name : String)
  deriving Repr

/-- A statement of a generic function body: a loop-free statement, or
`if (condition) { return value; }` on a Boolean local, which returns from the
function when the local holds `true`. -/
inductive GuardStmt where
  | plain (statement : Stmt)
  | guard (condition : String) (value : Expr)
  deriving Repr

/-- A generic free function, declared before the ordinary ones. Its body ends
with `return result;`. -/
structure GenericDecl where
  name : String
  typeParameters : List String
  parameters : List (String × TypeRef)
  resultType : TypeRef
  body : List GuardStmt
  result : Expr
  deriving Repr

/-- A method-body statement without nested statements: a loop-free statement,
or `let` or assignment of one infix operation without parentheses. -/
inductive InfixLeaf where
  | plain (statement : Stmt)
  | letInfix (identifier : String) (type : LocalType) (op : BinaryOp) (left right : Expr)
  | assignInfix (identifier : String) (op : BinaryOp) (left right : Expr)
  deriving Repr

/-- A method-body statement: a leaf, or a `match` whose cases run leaves. -/
inductive InfixStmt where
  | leaf (statement : InfixLeaf)
  | matchPair (scrutinee : Expr) (first second : String) (body : List InfixLeaf)
  | matchSum (scrutinee : Expr) (left : String) (leftBody : List InfixLeaf) (right : String)
      (rightBody : List InfixLeaf)
  deriving Repr

/-- A public method like `Method` whose body may contain infix statements. -/
structure InfixMethod where
  name : String
  parameters : List String
  body : List InfixStmt
  result : Expr
  deriving Repr

/-- A source file like `SourceFile` with generic functions before the ordinary
ones and an infix method body. -/
structure GenericFile where
  opcodeAliases : List (String × String)
  generics : List GenericDecl
  functions : List FunctionDecl
  contract : String
  method : InfixMethod
  deriving Repr

/-! ### Identifiers -/

def TypeRef.identifiers : TypeRef → List String
  | .concrete _ => []
  | .param name => [name]

def GuardStmt.identifiers : GuardStmt → List String
  | .plain statement => statement.identifiers
  | .guard condition value => condition :: value.identifiers

def GuardStmt.listIdentifiers : List GuardStmt → List String
  | [] => []
  | statement :: rest => statement.identifiers ++ GuardStmt.listIdentifiers rest

/-- The parameter names and the type parameters they use, in order. -/
def genericParameterIdentifiers : List (String × TypeRef) → List String
  | [] => []
  | parameter :: rest =>
      parameter.1 :: parameter.2.identifiers ++ genericParameterIdentifiers rest

/-- The identifiers of a generic function: its name, type parameters,
signature, body and result. -/
def GenericDecl.identifiers (declaration : GenericDecl) : List String :=
  declaration.name :: declaration.typeParameters ++
    genericParameterIdentifiers declaration.parameters ++
    declaration.resultType.identifiers ++ GuardStmt.listIdentifiers declaration.body ++
    declaration.result.identifiers

def InfixLeaf.identifiers : InfixLeaf → List String
  | .plain statement => statement.identifiers
  | .letInfix identifier _ _ left right => identifier :: (left.identifiers ++ right.identifiers)
  | .assignInfix identifier _ left right => identifier :: (left.identifiers ++ right.identifiers)

def InfixLeaf.listIdentifiers : List InfixLeaf → List String
  | [] => []
  | statement :: rest => statement.identifiers ++ InfixLeaf.listIdentifiers rest

def InfixStmt.identifiers : InfixStmt → List String
  | .leaf statement => statement.identifiers
  | .matchPair scrutinee first second body =>
      scrutinee.identifiers ++ first :: second :: InfixLeaf.listIdentifiers body
  | .matchSum scrutinee left leftBody right rightBody =>
      scrutinee.identifiers ++ left :: InfixLeaf.listIdentifiers leftBody ++
        right :: InfixLeaf.listIdentifiers rightBody

def InfixStmt.listIdentifiers : List InfixStmt → List String
  | [] => []
  | statement :: rest => statement.identifiers ++ InfixStmt.listIdentifiers rest

/-! ### Printing -/

def TypeRef.spelling : TypeRef → String
  | .concrete type => type.spelling
  | .param name => name

/-- The type parameters between the angle brackets. -/
def typeParameterText (names : List String) : String := String.intercalate ", " names

/-- The parameter list between a generic function's parentheses. -/
def genericParameterText (parameters : List (String × TypeRef)) : String :=
  String.intercalate ", " (parameters.map fun parameter =>
    parameter.1 ++ ": " ++ parameter.2.spelling)

/-- A guard is its `if` line, its `return` line and its closing brace. -/
def GuardStmt.lines (indent : Nat) : GuardStmt → List String
  | .plain statement => statement.lines indent
  | .guard condition value =>
      [indentLine indent ("if (" ++ condition ++ ") {"),
        indentLine (indent + 4) ("return " ++ value.print ++ ";"), indentLine indent "}"]

def GuardStmt.listLines (indent : Nat) : List GuardStmt → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ GuardStmt.listLines indent rest

/-- A generic free function, followed by one blank line. -/
def GenericDecl.lines (declaration : GenericDecl) : List String :=
  ["function " ++ declaration.name ++ "<" ++ typeParameterText declaration.typeParameters ++
      ">(" ++ genericParameterText declaration.parameters ++ ") returns (" ++
      declaration.resultType.spelling ++ ") {"] ++
    GuardStmt.listLines 4 declaration.body ++
    ["    return " ++ declaration.result.print ++ ";", "}", ""]

/-- One infix operation without parentheses. -/
def infixText (op : BinaryOp) (left right : Expr) : String :=
  left.print ++ " " ++ op.spelling ++ " " ++ right.print

def InfixLeaf.lines (indent : Nat) : InfixLeaf → List String
  | .plain statement => statement.lines indent
  | .letInfix identifier type op left right =>
      [indentLine indent ("let " ++ identifier ++ ": " ++ type.spelling ++ " = " ++
        infixText op left right ++ ";")]
  | .assignInfix identifier op left right =>
      [indentLine indent (identifier ++ " = " ++ infixText op left right ++ ";")]

def InfixLeaf.listLines (indent : Nat) : List InfixLeaf → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ InfixLeaf.listLines indent rest

/-- The layout of `Stmt.lines` for a `match` whose cases run leaves. -/
def InfixStmt.lines (indent : Nat) : InfixStmt → List String
  | .leaf statement => statement.lines indent
  | .matchPair scrutinee first second body =>
      [indentLine indent ("match (" ++ scrutinee.print ++ ") {"),
        indentLine (indent + 4) ("case (" ++ first ++ ", " ++ second ++ ") {")] ++
        InfixLeaf.listLines (indent + 8) body ++
        [indentLine (indent + 4) "}", indentLine indent "}"]
  | .matchSum scrutinee left leftBody right rightBody =>
      [indentLine indent ("match (" ++ scrutinee.print ++ ") {"),
        indentLine (indent + 4) ("case inl(" ++ left ++ ") {")] ++
        InfixLeaf.listLines (indent + 8) leftBody ++
        [indentLine (indent + 4) "}", indentLine (indent + 4) ("case inr(" ++ right ++ ") {")] ++
        InfixLeaf.listLines (indent + 8) rightBody ++
        [indentLine (indent + 4) "}", indentLine indent "}"]

def InfixStmt.listLines (indent : Nat) : List InfixStmt → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ InfixStmt.listLines indent rest

/-- The layout of `SourceFile.lines`, with the generic functions before the
ordinary ones. -/
def GenericFile.lines (file : GenericFile) : List String :=
  ["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
  aliasImportLines file.opcodeAliases ++ [""] ++
  file.generics.flatMap GenericDecl.lines ++
  file.functions.flatMap FunctionDecl.lines ++
  ["contract " ++ file.contract ++ " {",
    "    function " ++ file.method.name ++ "(" ++ Method.parameterText file.method.parameters ++
      ") public returns (uint256) {"] ++
  InfixStmt.listLines 8 file.method.body ++
  ["        return " ++ file.method.result.print ++ ";", "    }", "}"]

def GenericFile.print (file : GenericFile) : String :=
  String.intercalate "\n" file.lines ++ "\n"

/-! ### Meaning -/

/-- A type parameter admits every value; typing instantiates it. -/
def TypeRef.admits : TypeRef → Value → Bool
  | .concrete type, value => type.admits value
  | .param _, _ => true

/-- The outcome of generic function body statements: the frames to go on
with, or the value of an early `return`. -/
inductive Flow where
  | next (frames : Frames)
  | returned (value : Value)

/-- A guard's local must hold a `bool`. When it is `true`, the value is
evaluated in the guard's block scope and returned. -/
def GuardStmt.exec (context : Context) (frames : Frames) : GuardStmt → Option Flow
  | .plain statement => (statement.exec context frames).map .next
  | .guard condition value =>
      match frames.lookup condition with
      | some (.bool true) => (value.eval context ([] :: frames)).map .returned
      | some (.bool false) => some (.next frames)
      | _ => none

def GuardStmt.execList (context : Context) : Frames → List GuardStmt → Option Flow
  | frames, [] => some (.next frames)
  | frames, statement :: rest =>
      match statement.exec context frames with
      | some (.next frames') => GuardStmt.execList context frames' rest
      | some (.returned value) => some (.returned value)
      | none => none

/-- Bind parameters as `FunctionDecl.bindParameters` does, with type
parameters admitting every value. -/
def GenericDecl.bindParameters : List (String × TypeRef) → List Value → Option Scope
  | [], [] => some []
  | (parameter, type) :: parameters, argument :: arguments =>
      if type.admits argument then
        (fun scope => scope ++ [(parameter, argument)]) <$>
          GenericDecl.bindParameters parameters arguments
      else none
  | _, _ => none

/-- A generic function's meaning: its body runs as a free function's body;
an early `return` ends it, otherwise the final `return` does. The returned
value must have the declared type. -/
def GenericDecl.denote (context : Context) (declaration : GenericDecl)
    (arguments : List Value) : Option Value := do
  let parameters ← GenericDecl.bindParameters declaration.parameters arguments
  let value ← match ← GuardStmt.execList context [[], parameters] declaration.body with
    | .returned value => some value
    | .next frames => declaration.result.eval context frames
  if declaration.resultType.admits value then some value else none

/-- The call context after the given generic functions, each seeing only the
earlier ones, as `declareFunctions`. -/
def declareGenerics (aliases : List (String × String)) :
    List (String × (List Value → Option Value)) → List GenericDecl →
      List (String × (List Value → Option Value))
  | functions, [] => functions
  | functions, declaration :: rest =>
      declareGenerics aliases
        ((declaration.name, declaration.denote { functions, aliases }) :: functions) rest

/-- An infix statement means the statement with the parenthesized operation. -/
def InfixLeaf.exec (context : Context) (frames : Frames) : InfixLeaf → Option Frames
  | .plain statement => statement.exec context frames
  | .letInfix identifier type op left right =>
      (Stmt.letDecl identifier type (.binary op left right)).exec context frames
  | .assignInfix identifier op left right =>
      (Stmt.assign identifier (.binary op left right)).exec context frames

def InfixLeaf.execList (context : Context) : Frames → List InfixLeaf → Option Frames
  | frames, [] => some frames
  | frames, statement :: rest =>
      match statement.exec context frames with
      | some frames' => InfixLeaf.execList context frames' rest
      | none => none

/-- A `match` of leaves runs as `Stmt.exec` runs a `match`. -/
def InfixStmt.exec (context : Context) (frames : Frames) : InfixStmt → Option Frames
  | .leaf statement => statement.exec context frames
  | .matchPair scrutinee first second body =>
      match scrutinee.eval context frames with
      | some (.pair left right) =>
          match InfixLeaf.execList context ([(second, .word right), (first, .word left)] :: frames)
              body with
          | some (_ :: frames') => some frames'
          | _ => none
      | _ => none
  | .matchSum scrutinee left leftBody right rightBody =>
      match scrutinee.eval context frames with
      | some (.inl payload) =>
          match InfixLeaf.execList context ([(left, .word payload)] :: frames) leftBody with
          | some (_ :: frames') => some frames'
          | _ => none
      | some (.inr payload) =>
          match InfixLeaf.execList context ([(right, .word payload)] :: frames) rightBody with
          | some (_ :: frames') => some frames'
          | _ => none
      | _ => none

def InfixStmt.execList (context : Context) : Frames → List InfixStmt → Option Frames
  | frames, [] => some frames
  | frames, statement :: rest =>
      match statement.exec context frames with
      | some frames' => InfixStmt.execList context frames' rest
      | none => none

/-- `Method.run` for an infix method body. -/
def InfixMethod.run (context : Context) (method : InfixMethod) (arguments : List Nat) :
    Option Nat := do
  let parameters ← Method.bindParameters method.parameters arguments
  let frames ← InfixStmt.execList context [[], parameters] method.body
  match ← method.result.eval context frames with
  | .uint256 value => some value
  | _ => none

/-- The generic functions come first, then the ordinary ones. -/
def GenericFile.context (file : GenericFile) : Context :=
  { functions := declareFunctions file.opcodeAliases
      (declareGenerics file.opcodeAliases [] file.generics) file.functions
    aliases := file.opcodeAliases }

/-- `SourceFile.call` for a generic file. -/
def GenericFile.call (file : GenericFile) (method : String) (arguments : List Nat) :
    Option Nat :=
  if file.method.name = method then file.method.run file.context arguments else none


/-! ### Loop-free files -/

/-- A loop-free statement read as a method-body statement: a `match` as a
`match` of leaves, every other statement as a leaf. -/
def Stmt.toInfix : Stmt → InfixStmt
  | .matchPair scrutinee first second body => .matchPair scrutinee first second (body.map .plain)
  | .matchSum scrutinee left leftBody right rightBody =>
      .matchSum scrutinee left (leftBody.map .plain) right (rightBody.map .plain)
  | statement => .leaf (.plain statement)

/-- The same file read as a generic file without generic functions. -/
def SourceFile.toGeneric (file : SourceFile) : GenericFile where
  opcodeAliases := file.opcodeAliases
  generics := []
  functions := file.functions
  contract := file.contract
  method := {
    name := file.method.name
    parameters := file.method.parameters
    body := file.method.body.map Stmt.toInfix
    result := file.method.result }

theorem InfixLeaf.listLines_plain (indent : Nat) (statements : List Stmt) :
    InfixLeaf.listLines indent (statements.map .plain) = Stmt.listLines indent statements := by
  induction statements with
  | nil => rfl
  | cons statement rest ih => simp [InfixLeaf.listLines, Stmt.listLines, InfixLeaf.lines, ih]

theorem InfixStmt.listLines_toInfix (indent : Nat) (statements : List Stmt) :
    InfixStmt.listLines indent (statements.map Stmt.toInfix) =
      Stmt.listLines indent statements := by
  induction statements with
  | nil => rfl
  | cons statement rest ih =>
      simp only [List.map_cons, InfixStmt.listLines, Stmt.listLines, ih]
      cases statement <;>
        simp [Stmt.toInfix, InfixStmt.lines, InfixLeaf.lines, Stmt.lines, InfixLeaf.listLines_plain]

/-- A loop-free file prints as before. -/
theorem SourceFile.toGeneric_print (file : SourceFile) : file.toGeneric.print = file.print := by
  simp [GenericFile.print, SourceFile.print, GenericFile.lines, SourceFile.lines,
    SourceFile.toGeneric, InfixStmt.listLines_toInfix]

theorem InfixLeaf.listIdentifiers_plain (statements : List Stmt) :
    InfixLeaf.listIdentifiers (statements.map .plain) = Stmt.listIdentifiers statements := by
  induction statements with
  | nil => rfl
  | cons statement rest ih =>
      simp [InfixLeaf.listIdentifiers, Stmt.listIdentifiers, InfixLeaf.identifiers, ih]

theorem InfixStmt.listIdentifiers_toInfix (statements : List Stmt) :
    InfixStmt.listIdentifiers (statements.map Stmt.toInfix) =
      Stmt.listIdentifiers statements := by
  induction statements with
  | nil => rfl
  | cons statement rest ih =>
      simp only [List.map_cons, InfixStmt.listIdentifiers, Stmt.listIdentifiers, ih]
      cases statement <;>
        simp [Stmt.toInfix, InfixStmt.identifiers, InfixLeaf.identifiers, Stmt.identifiers,
          InfixLeaf.listIdentifiers_plain]

theorem InfixLeaf.execList_plain (context : Context) :
    ∀ (frames : Frames) (statements : List Stmt),
      InfixLeaf.execList context frames (statements.map .plain) =
        Stmt.execList context frames statements
  | _, [] => rfl
  | frames, statement :: rest => by
      simp only [List.map_cons, InfixLeaf.execList, InfixLeaf.exec, Stmt.execList]
      cases statement.exec context frames with
      | none => rfl
      | some frames' => exact InfixLeaf.execList_plain context frames' rest

theorem Stmt.toInfix_exec (context : Context) (frames : Frames) (statement : Stmt) :
    statement.toInfix.exec context frames = statement.exec context frames := by
  cases statement <;> simp [Stmt.toInfix, InfixStmt.exec, InfixLeaf.exec, Stmt.exec,
    InfixLeaf.execList_plain] <;> rfl

theorem InfixStmt.execList_toInfix (context : Context) :
    ∀ (frames : Frames) (statements : List Stmt),
      InfixStmt.execList context frames (statements.map Stmt.toInfix) =
        Stmt.execList context frames statements
  | _, [] => rfl
  | frames, statement :: rest => by
      simp only [List.map_cons, InfixStmt.execList, Stmt.toInfix_exec, Stmt.execList]
      cases statement.exec context frames with
      | none => rfl
      | some frames' => exact InfixStmt.execList_toInfix context frames' rest

/-- A loop-free file has the meaning of `SourceFile.call`. -/
theorem SourceFile.toGeneric_call (file : SourceFile) (method : String)
    (arguments : List Nat) : file.toGeneric.call method arguments = file.call method arguments := by
  simp only [GenericFile.call, SourceFile.call, SourceFile.toGeneric, InfixMethod.run, Method.run,
    GenericFile.context, SourceFile.context, declareGenerics, InfixStmt.execList_toInfix]
  rfl

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.StorageSemantics
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
  ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    storageImportLine file.opcodeAliases,
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.RollbackSemantics
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
  ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    rollbackImportLine file.opcodeAliases,
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.KeyedSemantics
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
  ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    rollbackImportLine file.opcodeAliases,
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.LoopSemantics
/-! Loop programs: the source fragment with `while (left op right) { .. }`
statements at the top level of the method body, as printed by the bounded-loop
wrappers. As in the pinned frontend (`crates/parser/src/parse/stmt.rs`), the
parentheses belong to the loop and enclose its condition, here one infix
operation. A loop body is a block of loop-free statements. Every evaluation of
the condition must give a `bool`; while it is `true`, the body runs in a fresh
scope that is discarded afterwards, as for an `if` branch. A loop need not
terminate, so this meaning is indexed by fuel: each loop may evaluate its
condition at most `fuel` times, and a loop that runs out of fuel has no meaning.
More fuel never changes a meaning, so all completed calls agree. A loop-free
file is a loop file (`SourceFile.toLoop`) with the same printing and, for every
fuel, the meaning of `SourceFile.call`. Nothing here refers to Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-- A statement of a loop method body: a loop-free statement, or
`while (left op right) { body }` whose body is a loop-free block. -/
inductive LoopStmt where
  | plain (statement : Stmt)
  | whileLoop (op : BinaryOp) (left right : Expr) (body : List Stmt)
  deriving Repr

/-- A public method like `Method` whose body may contain `while` loops. -/
structure LoopMethod where
  name : String
  parameters : List String
  body : List LoopStmt
  result : Expr
  deriving Repr

/-- A source file like `SourceFile` whose method body may contain `while`
loops. -/
structure LoopFile where
  opcodeAliases : List (String × String)
  functions : List FunctionDecl
  contract : String
  method : LoopMethod
  deriving Repr

/-- The same file read as a loop file without loops. -/
def SourceFile.toLoop (file : SourceFile) : LoopFile where
  opcodeAliases := file.opcodeAliases
  functions := file.functions
  contract := file.contract
  method := {
    name := file.method.name
    parameters := file.method.parameters
    body := file.method.body.map .plain
    result := file.method.result }

/-- Every identifier of a loop statement, in preorder. -/
def LoopStmt.identifiers : LoopStmt → List String
  | .plain statement => statement.identifiers
  | .whileLoop _ left right body =>
      left.identifiers ++ right.identifiers ++ Stmt.listIdentifiers body

def LoopStmt.listIdentifiers : List LoopStmt → List String
  | [] => []
  | statement :: rest => statement.identifiers ++ LoopStmt.listIdentifiers rest

/-! ### Printing -/

/-- A loop is its header line, its body indented by four further spaces and its
closing brace. The header's parentheses are those of the printed infix
operation. -/
def LoopStmt.lines (indent : Nat) : LoopStmt → List String
  | .plain statement => statement.lines indent
  | .whileLoop op left right body =>
      [indentLine indent ("while " ++ (Expr.binary op left right).print ++ " {")] ++
        Stmt.listLines (indent + 4) body ++ [indentLine indent "}"]

def LoopStmt.listLines (indent : Nat) : List LoopStmt → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ LoopStmt.listLines indent rest

/-- The layout of `SourceFile.lines` around a loop method body. -/
def LoopFile.lines (file : LoopFile) : List String :=
  ["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
  aliasImportLines file.opcodeAliases ++ [""] ++
  file.functions.flatMap FunctionDecl.lines ++
  ["contract " ++ file.contract ++ " {",
    "    function " ++ file.method.name ++ "(" ++ Method.parameterText file.method.parameters ++
      ") public returns (uint256) {"] ++
  LoopStmt.listLines 8 file.method.body ++
  ["        return " ++ file.method.result.print ++ ";", "    }", "}"]

def LoopFile.print (file : LoopFile) : String :=
  String.intercalate "\n" file.lines ++ "\n"

theorem LoopStmt.listLines_plain (indent : Nat) (statements : List Stmt) :
    LoopStmt.listLines indent (statements.map .plain) = Stmt.listLines indent statements := by
  induction statements with
  | nil => rfl
  | cons statement rest ih => simp [LoopStmt.listLines, Stmt.listLines, LoopStmt.lines, ih]

/-- A loop-free file prints as before. -/
theorem SourceFile.toLoop_print (file : SourceFile) : file.toLoop.print = file.print := by
  simp [LoopFile.print, SourceFile.print, LoopFile.lines, SourceFile.lines, SourceFile.toLoop,
    LoopStmt.listLines_plain]

/-! ### Meaning -/

/-- Run a loop with the given condition and body, evaluating the condition at
most `fuel` times. -/
def runWhile (context : Context) (condition : Expr) (body : List Stmt) :
    Nat → Frames → Option Frames
  | 0, _ => none
  | fuel + 1, frames =>
      match condition.eval context frames with
      | some (.bool true) =>
          match Stmt.execList context ([] :: frames) body with
          | some (_ :: frames') => runWhile context condition body fuel frames'
          | _ => none
      | some (.bool false) => some frames
      | _ => none

/-- Execute one loop statement; a loop-free statement runs as `Stmt.exec`. -/
def LoopStmt.exec (context : Context) (fuel : Nat) (frames : Frames) :
    LoopStmt → Option Frames
  | .plain statement => statement.exec context frames
  | .whileLoop op left right body => runWhile context (.binary op left right) body fuel frames

def LoopStmt.execList (context : Context) (fuel : Nat) : Frames → List LoopStmt → Option Frames
  | frames, [] => some frames
  | frames, statement :: rest =>
      match statement.exec context fuel frames with
      | some frames' => LoopStmt.execList context fuel frames' rest
      | none => none

/-- `Method.run` for a loop method body. -/
def LoopMethod.run (context : Context) (fuel : Nat) (method : LoopMethod)
    (arguments : List Nat) : Option Nat := do
  let parameters ← Method.bindParameters method.parameters arguments
  let frames ← LoopStmt.execList context fuel [[], parameters] method.body
  match ← method.result.eval context frames with
  | .uint256 value => some value
  | _ => none

def LoopFile.context (file : LoopFile) : Context :=
  { functions := declareFunctions file.opcodeAliases [] file.functions
    aliases := file.opcodeAliases }

/-- `SourceFile.call` for a loop file, with `fuel` for each loop. -/
def LoopFile.call (file : LoopFile) (fuel : Nat) (method : String) (arguments : List Nat) :
    Option Nat :=
  if file.method.name = method then file.method.run file.context fuel arguments else none

/-! ### Fuel -/

theorem runWhile_mono {context : Context} {condition : Expr} {body : List Stmt} :
    ∀ {fuel more : Nat} {frames frames' : Frames}, fuel ≤ more →
      runWhile context condition body fuel frames = some frames' →
      runWhile context condition body more frames = some frames'
  | 0, _, _, _, _, ran => by simp [runWhile] at ran
  | fuel + 1, more, frames, frames', enough, ran => by
      obtain ⟨more, rfl⟩ : ∃ rest, more = rest + 1 := ⟨more - 1, by omega⟩
      simp only [runWhile] at ran ⊢
      cases evaluated : condition.eval context frames with
      | none => simp [evaluated] at ran
      | some value =>
          cases value with
          | bool flag =>
              cases flag with
              | true =>
                  simp only [evaluated] at ran ⊢
                  cases executed : Stmt.execList context ([] :: frames) body with
                  | none => simp [executed] at ran
                  | some result =>
                      cases result with
                      | nil => simp [executed] at ran
                      | cons scope rest =>
                          simp only [executed] at ran ⊢
                          exact runWhile_mono (by omega) ran
              | false => simpa [evaluated] using ran
          | _ => simp [evaluated] at ran

theorem LoopStmt.execList_mono {context : Context} {fuel more : Nat} (enough : fuel ≤ more) :
    ∀ (statements : List LoopStmt) {frames frames' : Frames},
      LoopStmt.execList context fuel frames statements = some frames' →
      LoopStmt.execList context more frames statements = some frames'
  | [], _, _, ran => ran
  | statement :: rest, frames, frames', ran => by
      simp only [LoopStmt.execList] at ran ⊢
      cases executed : statement.exec context fuel frames with
      | none => simp [executed] at ran
      | some middle =>
          rw [executed] at ran
          have same : statement.exec context more frames = some middle := by
            cases statement with
            | plain statement => exact executed
            | whileLoop op left right body => exact runWhile_mono enough executed
          rw [same]
          exact LoopStmt.execList_mono enough rest ran

/-- More fuel keeps the result of a completed call. -/
theorem LoopFile.call_mono {file : LoopFile} {method : String} {arguments : List Nat}
    {fuel more result : Nat} (enough : fuel ≤ more)
    (called : file.call fuel method arguments = some result) :
    file.call more method arguments = some result := by
  unfold LoopFile.call at called ⊢
  by_cases named : file.method.name = method
  · rw [if_pos named] at called ⊢
    simp only [LoopMethod.run, Option.bind_eq_bind] at called ⊢
    cases parameters : Method.bindParameters file.method.parameters arguments with
    | none => simp [parameters] at called
    | some parameters' =>
        simp only [parameters, Option.bind_some] at called ⊢
        cases executed : LoopStmt.execList file.context fuel [[], parameters']
            file.method.body with
        | none => simp [executed] at called
        | some frames =>
            rw [LoopStmt.execList_mono enough file.method.body executed]
            simpa [executed] using called
  · rw [if_neg named] at called
    cases called

/-- All completed calls of a loop file return the same word. -/
theorem LoopFile.call_unique {file : LoopFile} {method : String} {arguments : List Nat}
    {first second firstResult secondResult : Nat}
    (firstCall : file.call first method arguments = some firstResult)
    (secondCall : file.call second method arguments = some secondResult) :
    firstResult = secondResult := by
  have left := LoopFile.call_mono (Nat.le_max_left first second) firstCall
  have right := LoopFile.call_mono (Nat.le_max_right first second) secondCall
  rw [left] at right
  exact Option.some.inj right

/-! ### Loop-free files -/

theorem LoopStmt.execList_plain (context : Context) (fuel : Nat) :
    ∀ (frames : Frames) (statements : List Stmt),
      LoopStmt.execList context fuel frames (statements.map .plain) =
        Stmt.execList context frames statements
  | _, [] => rfl
  | frames, statement :: rest => by
      simp only [List.map_cons, LoopStmt.execList, LoopStmt.exec, Stmt.execList]
      cases statement.exec context frames with
      | none => rfl
      | some frames' => exact LoopStmt.execList_plain context fuel frames' rest

/-- A loop-free file has the meaning of `SourceFile.call`, for every fuel. -/
theorem SourceFile.toLoop_call (file : SourceFile) (fuel : Nat) (method : String)
    (arguments : List Nat) :
    file.toLoop.call fuel method arguments = file.call method arguments := by
  simp only [LoopFile.call, SourceFile.call, SourceFile.toLoop, LoopMethod.run, Method.run,
    LoopFile.context, SourceFile.context, LoopStmt.execList_plain]
  rfl

end Solcore.Synthesis.Source.ScalarMeaning
end
