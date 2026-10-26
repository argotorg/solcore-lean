import Solcore.Synthesis.Source.ScalarMeaning.Print
import Solcore.Synthesis.Source.ScalarMeaning.Semantics

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
  ["import * from std;", "import * from std.dispatch;"] ++
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
