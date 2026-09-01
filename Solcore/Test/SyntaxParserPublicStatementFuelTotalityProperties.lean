import Solcore.Syntax.Lexer
import Solcore.Syntax.Parser.PublicStatementFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicStatementFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TermInternals.coreStatementTotalityFuel_add_two
example := @statement_invariantFreeOnValid
example := @statement_totalityContract
example := @statement_ne_invariant

private def sourceId : SourceId := {
  origin := .main
  path := "public-statement-fuel.sol"
}

private def assertMalformedOrdinary (content : String) : IO Unit := do
  let file : SourceFile := { id := sourceId, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"lexer invariant: {repr error}")
  match statement (State.initial file lexed) with
  | .ok .. | .reject .. => pure ()
  | .invariant error => throw (IO.userError
      s!"statement invariant for {repr content}: {repr error}")

def run : IO Unit := do
  for content in ["(", "[", "lam(", "match ("] do
    assertMalformedOrdinary content

end Solcore.Test.SyntaxParserPublicStatementFuelTotalityProperties

def main : IO Unit :=
  Solcore.Test.SyntaxParserPublicStatementFuelTotalityProperties.run
