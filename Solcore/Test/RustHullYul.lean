import Solcore.Frontend.RustHull.YulLowering
import Solcore.Core.Machine

set_option autoImplicit false

namespace Tests.RustHullYul

open Solcore
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} : LowerM α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error.message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def name (value : String) : YulName := ⟨value, none⟩
private def num (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def ref (value : String) : YulExpr := ⟨.ident (name value), none⟩
private def call (value : String) (args : List YulExpr) : YulExpr := ⟨.call (name value) args, none⟩
private def stmt (value : YulStmtKind) : YulStmt := ⟨value, none⟩
private def set (target : String) (value : YulExpr) : YulStmt := stmt (.assign [name target] value)
private def decl (target : String) (value : Option YulExpr := none) : YulStmt :=
  stmt (.letDecl [name target] value)
private def add (left right : YulExpr) : YulExpr := call "add" [left, right]
private def function (value : String) (parameters returns : List String)
    (body : List YulStmt) : YulStmt :=
  stmt (.functionDef (name value) (parameters.map name) (returns.map name) body)
private def outer : Scope := [⟨some "x", .word, true⟩]

private def check (label : String) (body : List YulStmt) (expected : Nat)
    (initial : Nat := 0) : IO Unit := do
  let lowered ← get (YulLowering.lowerStatements 1000 outer .word body)
  let returned ← get (outer.read "x")
  let program : Core.Program := {
    resultType := Core.LanguageResult.resultType .word
    body := .letE (Core.OptionalCell.allocateInitialized .word (.word (word initial)))
      (Core.LocalControl.finish .word (Core.LocalLoop.toControl .word lowered (word 2)) returned.expression)
  }
  require program.check s!"Yul {label}: generated Core code is ill-typed"
  let actual := program.run 10000
  require (actual == .done (.inRight .word (.word (word expected))))
    s!"Yul {label}: expected {expected}, got {reprStr actual}"

private def rejected (body : List YulStmt) (scope : Scope := outer) : Bool :=
  match YulLowering.lowerStatements 1000 scope .word body with
  | .error _ => true
  | .ok _ => false

private def checkStorageFunctions : IO Unit := do
  let slots : List (String × Core.Ty × Core.Expr) := [
    ("storage", Core.WordMapping.type, Core.WordMapping.empty),
    ("isStatic", .bool, .bool false), ("exit", .word, .word (word 0)),
    ("returnOffset", .word, .word (word 0)), ("returnSize", .word, .word (word 0)),
    ("memorySize", .word, .word (word 0))]
  let scope : Scope := (slots.reverse.map fun (name, type, _) =>
    ⟨some (Effects.slotName name), type, false⟩) ++ outer
  let body := [set "x" (call "sub" [call "tick" [], call "tick" []]),
    set "x" (add (call "mul" [ref "x", num 10]) (call "sload" [num 0])),
    function "tick" [] ["r"] [set "r" (call "sload" [num 0]),
      stmt (.expression (call "sstore" [num 0, add (ref "r") (num 1)]))]]
  let lowered ← get (YulLowering.lowerStatements 1000 scope .word body)
  let returned ← get (scope.read "x")
  let program : Core.Program := {
    dataDefinitions := Core.WordMapping.actualDefinitions
    resultType := Core.LanguageResult.resultType .word
    body := .letE (Core.OptionalCell.allocateInitialized .word (.word (word 0)))
      (slots.foldr (fun (_, type, initial) body => .letE (.newCell type initial) body)
        (Core.LocalControl.finish .word (Core.LocalLoop.toControl .word lowered (word 2)) returned.expression))
  }
  require program.check "Yul function storage effects generated ill-typed Core"
  require (program.run 100000 == .done (.inRight .word (.word (word 12))))
    "Yul functions lost runtime slots or evaluated effectful arguments in the wrong order"

def run : IO Unit := do
  check "zero initialization and Word Boolean" [decl "y", set "x" (add (ref "y")
    ⟨.literal (.bool true), none⟩)] 1
  check "lexical block shadowing" [decl "y", stmt (.block [decl "y" (some (num 9)),
    set "x" (ref "y")]), set "x" (add (ref "x") (ref "y"))] 9
  check "initializer resolves outer binding" [stmt (.block [
    decl "x" (some (add (ref "x") (num 1))),
    set "x" (add (ref "x") (num 1))])] 7 7
  check "nonzero condition" [stmt (.ifThen (num 256) [set "x" (num 3)]),
    stmt (.ifThen (num 0) [set "x" (num 99)])] 3
  check "loop init scope, continue and break" [
    stmt (.forLoop [decl "i" (some (num 0))]
      (call "lt" [ref "i", num 5]) [set "i" (add (ref "i") (num 1))] [
        stmt (.ifThen (call "eq" [ref "i", num 2]) [stmt .continueStmt]),
        stmt (.ifThen (call "eq" [ref "i", num 4]) [stmt .breakStmt]),
        set "x" (add (ref "x") (ref "i"))]),
    set "x" (add (ref "x") (num 10))] 14
  check "nested loops consume their own break" [
    stmt (.forLoop [decl "i" (some (num 0))]
      (call "lt" [ref "i", num 3]) [set "i" (add (ref "i") (num 1))] [
        stmt (.forLoop [] (num 1) [] [set "x" (add (ref "x") (num 1)), stmt .breakStmt])])] 3
  check "switch selected branch" [stmt (.switch (num 3) [
    ⟨.number "1", [set "x" (num 99)], none⟩,
    ⟨.number "3", [decl "y" (some (num 5)), set "x" (add (ref "x") (ref "y"))], none⟩]
    (some [set "x" (num 8)]))] 5
  check "switch default" [stmt (.switch (num 4) [
    ⟨.number "1", [set "x" (num 99)], none⟩] (some [set "x" (num 8)]))] 8
  check "switch omitted default" [stmt (.switch (num 4) [
    ⟨.number "1", [set "x" (num 99)], none⟩] none)] 2 2
  check "pop expression statement" [stmt (.expression (call "pop" [num 13])), set "x" (num 5)] 5
  check "hexadecimal literal" [set "x" ⟨.literal (.hex "0x2a"), none⟩] 42
  check "string packs bytes left aligned" [set "x" (call "byte" [num 0,
    ⟨.literal (.string "\"A\\n\""), none⟩])] 65
  check "string escapes" [set "x" (call "byte" [num 1,
    ⟨.literal (.string "\"A\\n\""), none⟩])] 10

  let missing ← get (YulLowering.lowerExpression 50 outer (call "add" [num 4, ref "x"]))
  let uninitialized : Core.Program := {
    resultType := Core.LanguageResult.resultType .word
    body := .letE (Core.OptionalCell.allocate .word) missing.expression
  }
  require (uninitialized.check && uninitialized.run 1000 ==
    .done (.inLeft .word (.word (word 1)))) "Yul nested call swallowed a language failure"

  require (rejected [stmt (.expression (num 1))]) "unused Yul result was accepted"
  require (rejected [stmt (.expression (call "sstore" [num 0, num 1]))])
    "unsupported storage effect was accepted"
  check "multiple zero locals" [stmt (.letDecl [name "a", name "b"] none),
    set "x" (add (ref "a") (ref "b"))] 0
  check "hoisted zero return slot" [set "x" (call "f" []), function "f" [] ["r"] []] 0 9
  check "hoisted builtin shadow after break" [stmt (.forLoop [] (num 1) [] [
    set "x" (call "add" [num 1, num 2]), stmt .breakStmt,
    function "add" ["a", "b"] ["r"] []])] 0
  check "zero-result function" [stmt (.expression (call "f" [])), set "x" (num 7),
    function "f" [] [] []] 7
  check "leave preserves return values" [set "x" (call "f" [num 8]),
    function "f" ["a"] ["r"] [set "r" (ref "a"), stmt .leave, set "r" (num 99)]] 8
  check "leave exits loops and function" [set "x" (call "f" []),
    function "f" [] ["r"] [stmt (.forLoop [] (num 1) [] [set "r" (num 3), stmt .leave]),
      set "r" (num 99)]] 3
  check "multiple default return slots" [stmt (.letDecl [name "a", name "b", name "c"]
    (some (call "f" []))), set "x" (add (ref "a") (add (ref "b") (ref "c"))),
    function "f" [] ["r", "s", "t"] []] 0
  check "parallel multiple assignment" [decl "a" (some (num 3)), decl "b" (some (num 7)),
    stmt (.assign [name "a", name "b"] (call "swap" [ref "a", ref "b"])),
    set "x" (add (call "mul" [ref "a", num 10]) (ref "b")),
    function "swap" ["a", "b"] ["c", "d"] [set "c" (ref "b"), set "d" (ref "a")]] 73
  check "multiple initialized locals" [stmt (.letDecl [name "a", name "b"] (some (call "pair" []))),
    set "x" (add (call "mul" [ref "a", num 10]) (ref "b")),
    function "pair" [] ["a", "b"] [set "a" (num 2), set "b" (num 9)]] 29
  check "function and value namespaces" [decl "add" (some (num 7)),
    set "x" (call "mul" [ref "add", call "add" [num 9, num 3]]),
    function "add" ["a", "b"] ["r"] [set "r" (call "sub" [ref "a", ref "b"])]] 42
  check "local function shadows host builtin" [set "x" (call "sload" [num 0]),
    function "sload" ["a"] ["r"] [set "r" (num 7)]] 7
  check "function lexical shadowing" [function "f" [] ["r"] [set "r" (num 1)],
    stmt (.block [set "x" (call "f" []), function "f" [] ["r"] [set "r" (num 2)]]),
    set "x" (add (ref "x") (call "f" []))] 3
  check "mutual recursion" [set "x" (add (call "even" [num 6]) (call "odd" [num 7])),
    function "even" ["n"] ["r"] [
      stmt (.ifThen (call "iszero" [ref "n"]) [set "r" (num 1), stmt .leave]),
      set "r" (call "odd" [call "sub" [ref "n", num 1]])],
    function "odd" ["n"] ["r"] [
      stmt (.ifThen (call "iszero" [ref "n"]) [stmt .leave]),
      set "r" (call "even" [call "sub" [ref "n", num 1]])]] 2
  check "function in for initializer" [stmt (.forLoop [decl "i",
    function "next" ["a"] ["r"] [set "r" (add (ref "a") (num 1))]]
    (call "lt" [ref "i", num 3]) [set "i" (call "next" [ref "i"])]
    [set "x" (add (ref "x") (num 1))])] 3
  require (rejected [function "f" [] ["r"] [set "r" (ref "x")]])
    "Yul function captured an enclosing Hull local"
  require (rejected [decl "y", function "f" [] ["r"] [set "r" (ref "y")]])
    "Yul function captured an enclosing Yul local"
  require (rejected [function "outer" ["a"] ["r"] [
    function "inner" [] ["r"] [set "r" (ref "a")]]])
    "nested Yul function captured an enclosing parameter"
  require (rejected [function "f" [] [] [], function "f" [] [] []])
    "duplicate Yul function declarations were accepted"
  require (rejected [function "f" ["a"] ["a"] []])
    "duplicate Yul parameter/return slots were accepted"
  require (rejected [decl (Effects.slotName "callvalue")] &&
    rejected [set (Effects.slotName "callvalue") (num 1)] &&
    rejected [set "x" (ref (Effects.slotName "callvalue"))])
    "inline Yul accessed a reserved runtime binding"
  require (rejected [set "x" (call "f" []), function "f" ["a"] ["r"] []])
    "Yul function call with wrong argument count was accepted"
  require (rejected [stmt (.letDecl [name "a", name "b"] (some (num 1)))])
    "Yul declaration with wrong result count was accepted"
  require (rejected [stmt (.forLoop [stmt .breakStmt] (num 0) [] [])] &&
    rejected [stmt (.forLoop [] (num 0) [stmt .continueStmt] [])])
    "Yul loop initializer or post accepted a loop transfer"
  require (rejected [function "f" [] [] [stmt (.forLoop [stmt .leave, stmt .breakStmt]
    (num 0) [] [])]]) "unreachable malformed Yul loop transfer was accepted"
  require (rejected [stmt (.forLoop [] (num 1) [] [function "f" [] [] [stmt .breakStmt]])])
    "a Yul function inherited an enclosing loop target"
  require (rejected [stmt .leave] && rejected [stmt .breakStmt] && rejected [stmt .continueStmt])
    "escaped Yul transfer was accepted"
  require (rejected [set "x" (num 1)] [⟨some "x", .bool, true⟩])
    "Yul assigned to a nonword Hull local"
  require (rejected [set "x" (ref "flag")] [⟨some "x", .word, true⟩, ⟨some "flag", .bool, true⟩])
    "Yul read a nonword Hull local"
  require (rejected [stmt (.block [decl "hidden"]), set "x" (ref "hidden")])
    "Yul block declaration leaked"
  require (rejected [stmt (.forLoop [decl "i"] (num 0) [] []), set "x" (ref "i")])
    "Yul initializer declaration leaked"
  require (rejected [stmt (.forLoop [decl "i"] (num 0) [set "x" (ref "bodyLocal")]
    [decl "bodyLocal"])]) "Yul body declarations leaked into post"
  require (rejected [stmt (.switch (num 0) [⟨.number "1", [], none⟩, ⟨.hex "0x1", [], none⟩] none)])
    "duplicate Yul switch labels were accepted"
  require (rejected [set "x" ⟨.literal (.string "\"invalid\\r\""), none⟩])
    "invalid Yul string escape was accepted"
  require (rejected [set "x" ⟨.literal (.string "\"12345678901234567890123456789012345\""), none⟩])
    "oversized Yul UTF8 string was accepted"
  checkStorageFunctions

end Tests.RustHullYul
