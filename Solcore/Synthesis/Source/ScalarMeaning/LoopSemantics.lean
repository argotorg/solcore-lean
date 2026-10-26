import Solcore.Synthesis.Source.ScalarMeaning.Print
import Solcore.Synthesis.Source.ScalarMeaning.Semantics

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
  ["import * from std;", "import * from std.dispatch;"] ++
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
