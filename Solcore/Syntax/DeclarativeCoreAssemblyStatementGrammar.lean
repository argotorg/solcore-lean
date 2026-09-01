import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent bridge grammar for a Core `assembly` statement whose
braced Yul body is supplied by an abstract relation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact Core wrapper around an abstract Yul body grammar. -/
inductive AssemblyStatementParses
    (yulBodyParses :
      Remainder → SourceSpan → List Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {bodySpan : SourceSpan} {body : List Syntax.YulStmt}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .assemblyKw) input
        markerSpan afterMarker)
      (bodyParsed : yulBodyParses afterMarker bodySpan body output) :
      AssemblyStatementParses yulBodyParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .assembly body
      } output

end Solcore.Syntax.DeclarativeGrammar
