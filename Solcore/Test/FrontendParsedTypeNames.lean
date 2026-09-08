import Solcore.Syntax.Parser.Type
import Solcore.Frontend.TypeName

/-! Actual, completely consumed canonical type text feeds the explicit type
table. Parser acceptance is distinct from this monomorphic adapter's scope. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsedType? (content : String) : IO (Option Syntax.TypeExpr) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-type-name.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.typeExpr (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def table : TypeNameTable :=
  [(["Word"], .word), (["Word"], .bool), (["Bool"], .bool),
    (["Pkg", "Flag"], .bool), (["Pkg", "Cell"], .cell .word),
    (["Pkg", "Fn"], .function .word .bool), (["Pkg", "Pair"], .product .word .bool),
    (["W"], .word)]

private def checkNamed (content : String) (components : List String) (expected : Core.Ty) : IO Unit := do
  let some source ← parsedType? content
    | throw (IO.userError s!"{content}: expected one complete type")
  let .named name none := source.value
    | throw (IO.userError s!"{content}: expected an unapplied named type")
  assertTrue (decide (qualifiedTypeNameKey name = components))
    s!"{content}: changed qualified spelling components or their order"
  assertTrue (decide (interpretTypeName? table source = some expected))
    s!"{content}: wrong explicit type meaning or duplicate priority"
  assertTrue (interpretTypeName? [] source).isNone
    s!"{content}: acquired a meaning without a caller table"
  let invalidSpan : Syntax.SourceSpan := ⟨⟨.main, "unrelated.sol"⟩, 900, 2⟩
  let movedName : Syntax.QualifiedName := {
    span := invalidSpan
    value := { components := name.value.components.map fun component =>
      { component with span := invalidSpan } }
  }
  let moved : Syntax.TypeExpr := ⟨invalidSpan, .named movedName none⟩
  assertTrue (decide (interpretTypeName? table moved = some expected))
    s!"{content}: meaning depended on an outer, path, or component range"

def frontendParsedTypeNameTests : IO Unit := do
  checkNamed "Word" ["Word"] .word
  checkNamed "Bool" ["Bool"] .bool
  checkNamed "W" ["W"] .word
  checkNamed "Pkg.Flag" ["Pkg", "Flag"] .bool
  checkNamed " /* lead */ Pkg /* gap */ . Flag /* end */ " ["Pkg", "Flag"] .bool
  checkNamed "Pkg.Cell" ["Pkg", "Cell"] (.cell .word)
  checkNamed "Pkg.Fn" ["Pkg", "Fn"] (.function .word .bool)
  checkNamed "Pkg.Pair" ["Pkg", "Pair"] (.product .word .bool)
  let some wordSource ← parsedType? "Word"
    | throw (IO.userError "Word: complete parsing failed")
  assertTrue (decide (interpretTypeName? [(["Word"], .bool)] wordSource = some .bool))
    "Word spelling must not override the caller's explicitly supplied meaning"
  for content in ["Unknown", "word", "Flag", "Flag.Pkg", "Pkg.Other"] do
    let some source ← parsedType? content
      | throw (IO.userError s!"{content}: unknown names must still parse")
    assertTrue (interpretTypeName? table source).isNone
      s!"{content}: unknown or differently qualified name used a fallback meaning"
  for content in ["Word<Bool>", "Pkg.Flag<Word>", "mapping(Word => Bool)",
      "@Word", "function(Word) returns (Bool)", "comptime<Word>", "()", "(Word, Bool)"] do
    let some source ← parsedType? content
      | throw (IO.userError s!"{content}: unsupported adapter form should still parse")
    assertTrue (interpretTypeName? table source).isNone
      s!"{content}: unsupported type form received a monomorphic name meaning"
  for content in ["", "Word Bool", "Pkg.", ".Flag", "Word<", "Word<>",
      "Word;", "Word trailing", "\"Word\""] do
    assertTrue (← parsedType? content).isNone
      s!"{content}: accepted invalid or only partially consumed type text"

end Tests
