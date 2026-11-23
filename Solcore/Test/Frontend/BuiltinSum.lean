import Solcore.Frontend.SourceCompiler

/-!
# Upstream's builtin `sum`

`sum<a, b>` with its constructors `inl` and `inr`, unqualified in types, calls and patterns, as
upstream builds them in (`testAccepted`): constructed and matched, nested, at a tuple payload,
through a generic function, a type alias, an enum's payload, a lambda, a tuple and a generic enum,
with wildcard payloads, recursion and a leading dot, with whitespace before the brackets, and used
only in an imported module. A program's own or an imported `sum`, `inl` or `inr` comes first, as
upstream looks its builtins up last (`testPrecedence`). A missing arm, one type argument, `sum.inl`
in a call or a pattern, `inl` as a value, `==` on sums, a payload of the wrong type, the builtin
`inl` at another type and an unannotated `let` whose other side nothing fixes are refused
(`testRefused`). Each case is a source upstream's pinned checker was probed with: an accepted one
runs at 9 and 2^256 − 1 and gives the results upstream's checked Hull gives, and a refused one is
refused there too, `inl` as a value by upstream's Hull backend. The load adds the builtin's module
only where a file names it, so a program that names none of the three loads as before (`testLoad`).
-/

set_option autoImplicit false

namespace Tests.BuiltinSum

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def maximum : Nat := 2 ^ 256 - 1

private def same : List Nat := [9, maximum]

/-- A body that starts with `{` is `main`'s statements, any other the expression it returns. -/
private def workspace (imports declarations : List String) (body : String)
    (modules : List Workspace.RawSourceFile) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    { path := "main.solc", content := String.intercalate "\n" (["pragma solcore;"] ++ imports ++
        declarations ++ [s!"function main(a0: word) returns (word) " ++
          (if body.startsWith "{" then body else s!"\{ return {body}; }")]) }] ++ modules
  externalLibraries := []
}

/-- The function `main` loaded, checked, compiled and run at each input, or the stage that
refused it. -/
private def runMain (raw : Workspace.RawWorkspace) (inputs : List Nat) :
    IO (Except String (List Nat)) := do
  let loaded ← match loadProgram raw with
    | .ok loaded => pure loaded
    | .error _ => return .error "load"
  let checked ← match checkLoadedProgram loaded 4096 with
    | .ok checked => pure checked
    | .error _ => return .error "check"
  let seed := SourceCompiler.Seed.named loaded.workspace.entry.toModuleId "main"
  let options : SourceCompiler.Options :=
    {checkingFuel := 4096, compilationFuel := 4096, specializationBudget := 1024}
  let compiled ← match SourceCompiler.compileChecked checked [seed] options with
    | .ok compiled => pure compiled
    | .error _ => return .error "compile"
  let key ← match compiled.keys with
    | [key] => pure key
    | _ => return .error "keys"
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let session ← match bootstrap.resume 1000000 with
    | .ready session => pure session
    | _ => return .error "boot"
  let mut results := []
  for input in inputs do
    match ← session.run key [.word (Core.Word.ofNatModulo input)]
        {inputValidationFuel := 4096, outputValidationFuel := 4096, executionFuel := 1000000} with
    | .ok (.succeeded completion) => match completion.value with
      | .word word => results := results ++ [word.val]
      | _ => return .error "value"
    | _ => return .error "run"
  return .ok results

private def expectResults (label : String) (declarations : List String) (body : String)
    (expected : List Nat) (imports : List String := [])
    (modules : List Workspace.RawSourceFile := []) : IO Unit := do
  let found ← runMain (workspace imports declarations body modules) [9, maximum]
  assertTrue (match found with | .ok results => results == expected | .error _ => false)
    s!"{label}: expected {expected}, got {reprStr found}"

private def expectRefused (label : String) (declarations : List String) (body : String)
    (stage : String) (imports : List String := [])
    (modules : List Workspace.RawSourceFile := []) : IO Unit := do
  let found ← runMain (workspace imports declarations body modules) [9]
  assertTrue (match found with | .error refused => refused == stage | .ok _ => false)
    s!"{label}: expected a refusal at {stage}, got {reprStr found}"

private def matchBoth (left right : String) : String :=
  s!"match (s) \{ case inl(x) \{ return {left}; } case inr(y) \{ return {right}; } }"

private def pick : String :=
  "function pick(x: word) returns (sum<word, bool>) { " ++
    "match (x) { case 0 { return inr(true); } default { return inl(x); } } }"

private def swap : String :=
  "function swap<a, b>(s: sum<a, b>) returns (sum<b, a>) { " ++
    "match (s) { case inl(x) { return inr(x); } case inr(y) { return inl(y); } } }"

private def unwrap : String :=
  "function unwrap(s: sum<word, bool>) returns (word) { " ++
    "match (s) { case inl(x) { return x; } case inr(b) { return 1; } } }"

private def sumLibrary : Workspace.RawSourceFile :=
  { path := "sumlib.solc",
    content := "pragma solcore;\nexport { sum(*) };\nenum sum<a, b> { L(a), R(b) }" }

/-- The forms upstream accepts, with its results at 9 and 2^256 − 1. -/
private def testAccepted : IO Unit := do
  expectResults "inl, matched" [] ("{ let s: sum<word, word> = inl(a0); " ++ matchBoth "x" "0" ++ " }")
    same
  expectResults "inr, matched" [] ("{ let s: sum<word, word> = inr(a0); " ++ matchBoth "0" "y" ++ " }")
    same
  expectResults "returned by a function" [pick]
    "{ match (pick(a0)) { case inl(v) { return v; } case inr(b) { return 1; } } }" same
  expectResults "nested, matched twice" []
    ("{ let s: sum<sum<word, word>, word> = inl(inr(a0)); match (s) { case inl(inner) { " ++
      "match (inner) { case inl(x) { return 1; } case inr(y) { return y; } } } " ++
      "case inr(z) { return 2; } } }") same
  expectResults "nested, a nested pattern" []
    ("{ let s: sum<sum<word, word>, word> = inl(inr(a0)); match (s) { " ++
      "case inl(inl(x)) { return 1; } case inl(inr(y)) { return y; } case inr(z) { return 2; } } }")
    same
  expectResults "a tuple payload" []
    ("{ let s: sum<(word, word), word> = inl((a0, 3)); match (s) { " ++
      "case inl((x, y)) { return y; } case inr(z) { return z; } } }") [3, 3]
  expectResults "a generic function" [swap]
    ("{ let s: sum<word, bool> = inl(a0); match (swap(s)) { case inl(b) { return 0; } " ++
      "case inr(x) { return x; } } }") same
  expectResults "a wildcard arm" []
    ("{ let s: sum<word, word> = inr(a0); match (s) { case inl(x) { return x; } " ++
      "case _ { return 5; } } }") [5, 5]
  expectResults "inl at a typed parameter" [unwrap] "unwrap(inl(a0))" same
  expectResults "a type alias" ["type E = sum<word, bool>;", unwrap]
    "{ let s: E = inl(a0); return unwrap(s); }" same
  expectResults "an enum's payload" ["enum Box { B(sum<word, word>) }"]
    ("{ let b: Box = Box.B(inr(a0)); match (b) { case Box.B(s) { " ++ matchBoth "1" "y" ++ " } } }")
    same
  expectResults "bool literal patterns" []
    ("{ let s: sum<bool, word> = inl(true); match (s) { case inl(true) { return 1; } " ++
      "case inl(false) { return 2; } case inr(x) { return x; } } }") [1, 1]
  expectResults "in a lambda" []
    ("{ let g = lam (x: word) { let s: sum<word, word> = inr(x); match (s) { " ++
      "case inl(p) { return p; } case inr(q) { return q; } } }; return g(a0); }") same
  expectResults "a sum of sums, a nested pattern"
    ["function mk(x: word) returns (sum<word, sum<word, word>>) { return inr(inl(x)); }"]
    ("{ match (mk(a0)) { case inl(x) { return 1; } case inr(inl(y)) { return y; } " ++
      "case inr(inr(z)) { return 3; } } }") same
  expectResults "a leading dot in a call and in patterns" []
    ("{ let s: sum<word, word> = .inl(a0); match (s) { case .inl(x) { return x; } " ++
      "case .inr(y) { return 0; } } }") same
  expectResults "a leading dot in patterns only" []
    ("{ let s: sum<word, word> = inr(a0); match (s) { case .inl(x) { return x; } " ++
      "case .inr(y) { return y; } } }") same
  expectResults "a generic function's type arguments, inferred"
    ["function first<a, b>(s: sum<a, b>, d: a) returns (a) { " ++
      "match (s) { case inl(x) { return x; } case inr(y) { return d; } } }"]
    "{ let s: sum<word, bool> = inr(false); return first(s, a0); }" same
  expectResults "wildcard payloads" []
    ("{ let s: sum<word, word> = inr(a0); match (s) { case inl(_) { return 1; } " ++
      "case inr(_) { return 2; } } }") [2, 2]
  expectResults "a lambda that returns a sum" []
    ("{ let f = lam (x: word) -> sum<word, word> { return inl(x); }; " ++
      "let s: sum<word, word> = f(a0); " ++ matchBoth "x" "0" ++ " }") same
  expectResults "a sum in a tuple, a nested pattern" []
    ("{ let p: (sum<word, word>, word) = (inr(a0), 3); match (p) { case (inl(x), y) { return y; } " ++
      "case (inr(x), y) { return x; } } }") same
  expectResults "a sum inside a generic enum" ["enum Opt<a> { None, Some(a) }"]
    ("{ let o: Opt<sum<word, bool>> = Opt.Some(inl(a0)); match (o) { " ++
      "case Opt.Some(inl(x)) { return x; } case Opt.Some(inr(b)) { return 1; } " ++
      "case Opt.None { return 2; } } }") same
  expectResults "recursion over a sum"
    ["function f(n: word, s: sum<word, word>) returns (word) { match (s) { " ++
      "case inl(x) { return x; } case inr(y) { return f(n, inl(y)); } } }"]
    "f(0, inr(a0))" same
  expectResults "spaces before the brackets" []
    ("{ let s: sum <word, word> = inl (a0); match (s) { case inl (x) { return x; } " ++
      "case inr (y) { return 0; } } }") same
  expectResults "a newline between sum and its arguments" []
    ("{ let s: sum\n<word, word> = inl\n(a0); " ++ matchBoth "x" "0" ++ " }") same
  expectResults "used only in an imported module" [] "pickw(a0)" same ["import { pickw } from sumuse;"]
    [{ path := "sumuse.solc", content := "pragma solcore;\nexport { pickw };\n" ++
        "function pickw(x: word) returns (word) { let s: sum<word, word> = inl(x); " ++
        "match (s) { case inl(p) { return p; } case inr(q) { return 0; } } }" }]

/-- A program's own and an imported `sum`, `inl` and `inr` come first. -/
private def testPrecedence : IO Unit := do
  expectResults "a program's own type named sum" ["enum sum { A, B }"]
    "{ let x: sum = sum.A; return a0; }" same
  expectResults "a program's own generic type named sum" ["enum sum<a, b> { L(a), R(b) }"]
    ("{ let s: sum<word, word> = sum.L(a0); match (s) { case sum.L(x) { return x; } " ++
      "case sum.R(y) { return y; } } }") same
  expectResults "an imported type named sum" []
    ("{ let s: sum<word, word> = sum.L(a0); match (s) { case sum.L(x) { return x; } " ++
      "case sum.R(y) { return y; } } }") same ["import { sum } from sumlib;"] [sumLibrary]
  expectResults "a program's own function named inl" ["function inl(x: word) returns (word) { return 7; }"]
    "inl(a0)" [7, 7]
  expectResults "an imported function named inl" [] "inl(a0)" [8, 8] ["import { inl } from inllib;"]
    [{ path := "inllib.solc",
       content := "pragma solcore;\nexport { inl };\nfunction inl(x: word) returns (word) { return 8; }" }]
  expectResults "a program's own function named inr, beside the builtin inr's pattern"
    ["function inr(x: word) returns (word) { return 7; }"]
    ("{ let s: sum<word, word> = inl(a0); match (s) { case inl(x) { return inr(x); } " ++
      "case inr(y) { return y; } } }") [7, 7]
  expectResults "a local lambda named inl" []
    ("{ let s: sum<word, word> = inr(a0); let inl = lam (x: word) { return x; }; " ++
      "return inl(a0); }") same
  expectResults "a program's own enum with constructors inl and inr, qualified"
    ["enum E { inl(word), inr(word) }"]
    ("{ let s: E = E.inl(a0); match (s) { case E.inl(x) { return x; } " ++
      "case E.inr(y) { return y; } } }") same

/-- The forms upstream refuses. -/
private def testRefused : IO Unit := do
  expectRefused "a missing arm" []
    "{ let s: sum<word, word> = inl(a0); match (s) { case inl(x) { return x; } } }" "check"
  expectRefused "one type argument" [] "{ let s: sum<word> = inl(a0); return a0; }" "check"
  expectRefused "a qualified sum.inl" [] "{ let s: sum<word, word> = sum.inl(a0); return a0; }" "check"
  expectRefused "sum.inl in a pattern" []
    ("{ let s: sum<word, word> = inl(a0); match (s) { case sum.inl(x) { return x; } " ++
      "case sum.inr(y) { return 0; } } }") "check"
  expectRefused "inl as a value" [unwrap]
    "{ let f: function (word) returns (sum<word, bool>) = inl; return unwrap(f(a0)); }" "check"
  expectRefused "a payload of the wrong type" [] "{ let s: sum<word, word> = inr(true); return a0; }"
    "check"
  expectRefused "== on sums" []
    ("{ let s: sum<word, word> = inl(a0); let t: sum<word, word> = inl(a0); " ++
      "if (s == t) { return 1; } return 0; }") "check"
  expectRefused "a program's own enum's constructor, unqualified" ["enum E { inl(word), inr(word) }"]
    "{ let s: E = inl(a0); match (s) { case inl(x) { return x; } case inr(y) { return y; } } }"
    "check"
  expectRefused "the builtin inl at an imported sum" [] "{ let s: sum<word, word> = inl(a0); return a0; }"
    "check" ["import { sum } from sumlib;"] [sumLibrary]
  expectRefused "an open other side" []
    "{ let s = inl(a0); match (s) { case inl(x) { return x; } case inr(y) { return 0; } } }" "compile"

/-- The load adds the builtin's module only where a workspace file names `sum` before `<`, or `inl`
or `inr` before `(`, each a whole word with any whitespace between: a program that names none of
them loads exactly as before. -/
private def testLoad : IO Unit := do
  for (content, named) in [("let s: sum<word, word> = inl(a0);", true), ("sum <word, word>", true),
      ("inr\n(a0)", true), ("// inl(", true), ("checksum<word>", false), ("my_inl(a0)", false),
      ("inline(a0)", false), ("let sum = a0; return sum;", false)] do
    assertTrue (namesBuiltinSum content == named) s!"namesBuiltinSum {reprStr content}"
  let modules (body : String) : Nat :=
    match loadProgram (workspace [] [] body []) with
    | .ok loaded => loaded.environment.modules.length
    | .error _ => 0
  assertTrue (modules "a0" == 1) "a program that names no builtin sum loads one module"
  assertTrue (modules "{ let s: sum<word, word> = inl(a0); return a0; }" == 2)
    "a program that names the builtin sum loads its module too"

def run : IO Unit := do
  testLoad
  testAccepted
  testPrecedence
  testRefused
  IO.println "upstream's builtin sum: the load, upstream's forms, precedence and refusals with its results GREEN"

end Tests.BuiltinSum
