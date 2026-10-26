import Solcore.Synthesis.Source.ScalarMeaning.Syntax

/-! Concrete text of the scalar source fragment, in the exact layout used by
the scalar renderer and its wrappers: four-space indentation steps, one
statement or brace per line, and a trailing newline. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

def indentLine (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

def Expr.print : Expr → String
  | .name identifier => identifier
  | .number value => toString value
  | .bool value => if value then "true" else "false"
  | .unary op operand => "(" ++ op.spelling ++ operand.print ++ ")"
  | .binary op left right =>
      "(" ++ left.print ++ " " ++ op.spelling ++ " " ++ right.print ++ ")"
  | .typedefRep operand => "Typedef.rep(" ++ operand.print ++ ")"
  | .uint256 operand => "uint256(" ++ operand.print ++ ")"

mutual

/-- The lines of one statement at the given indentation. Branch blocks are
indented by four further spaces. -/
def Stmt.lines (indent : Nat) : Stmt → List String
  | .letDecl identifier type initializer =>
      [indentLine indent
        ("let " ++ identifier ++ ": " ++ type.spelling ++ " = " ++ initializer.print ++ ";")]
  | .assign identifier value =>
      [indentLine indent (identifier ++ " = " ++ value.print ++ ";")]
  | .ifElse condition thenBlock elseBlock =>
      [indentLine indent ("if (" ++ condition.print ++ ") {")] ++
        Stmt.listLines (indent + 4) thenBlock ++ [indentLine indent "} else {"] ++
        Stmt.listLines (indent + 4) elseBlock ++ [indentLine indent "}"]

def Stmt.listLines (indent : Nat) : List Stmt → List String
  | [] => []
  | statement :: rest => statement.lines indent ++ Stmt.listLines indent rest

end

theorem Stmt.listLines_append (indent : Nat) (first second : List Stmt) :
    Stmt.listLines indent (first ++ second) =
      Stmt.listLines indent first ++ Stmt.listLines indent second := by
  induction first with
  | nil => simp [Stmt.listLines]
  | cons statement rest ih =>
      simp [Stmt.listLines, ih, List.append_assoc]

/-- The parameter list between the method's parentheses. -/
def Method.parameterText (parameters : List String) : String :=
  String.intercalate ", " (parameters.map (· ++ ": uint256"))

def SourceFile.lines (file : SourceFile) : List String :=
  ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ file.contract ++ " {",
    "    function " ++ file.method.name ++ "(" ++ Method.parameterText file.method.parameters ++
      ") public returns (uint256) {"] ++
  Stmt.listLines 8 file.method.body ++
  ["        return " ++ file.method.result.print ++ ";", "    }", "}"]

def SourceFile.print (file : SourceFile) : String :=
  String.intercalate "\n" file.lines ++ "\n"

end Solcore.Synthesis.Source.ScalarMeaning
