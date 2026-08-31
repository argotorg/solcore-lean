import Solcore.Syntax.Parser.Primitive

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def finishQualifiedName (first last : Identifier)
    (tailRev : List Identifier) (state : State) : Reply QualifiedName :=
  .ok {
    span := SourceSpan.cover first.span last.span
    value := {
      components := {
        head := first
        tail := tailRev.reverse
      }
    }
  } state

private def qualifiedNameTail (context : ParseContext)
    (phase : ParserPhase) (first : Identifier) :
    Nat → Identifier → List Identifier → State → Reply QualifiedName
  | 0, _, _, state => .invariant (.fuelExhausted phase state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .dot then
        match symbol .dot context state with
        | .ok _ afterDot =>
            match identifier context afterDot with
            | .ok component next =>
                qualifiedNameTail context phase first fuel component
                  (component :: tailRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        finishQualifiedName first last tailRev state

/-- Parse one nonempty dotted ordinary-identifier path. -/
def qualifiedName (context : ParseContext)
    (phase : ParserPhase) : Parser QualifiedName := fun state =>
  match identifier context state with
  | .ok first next =>
      qualifiedNameTail context phase first (next.remainingCount + 1)
        first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
