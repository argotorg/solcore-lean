import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.Type

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse one trait predicate `subject: Trait<arguments...>`. -/
def predicate : Parser Predicate := do
  let subject ← typeExpr
  let _ ← symbol .colon .typeExpr
  let traitName ← identifier .typeExpr
  let arguments ← parseNamedTypeArguments typeExpr
  let endSpan := match arguments with
    | some values => values.span
    | none => traitName.span
  pure {
    span := SourceSpan.cover subject.span endSpan
    subject
    traitName
    arguments
  }

namespace PredicateInternals

abbrev PredicateSequence := NonemptyDelimitedList Predicate

def barePredicatesTail (first : Predicate) :
    Nat → Predicate → List Predicate → State → Reply PredicateSequence
  | 0, _, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .comma then
        match symbol .comma .typeExpr state with
        | .ok comma afterComma =>
            if startsTypeExpr afterComma then
              match predicate afterComma with
              | .ok value next =>
                  barePredicatesTail first fuel value
                    (value :: tailRev) next
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
            else
              .ok {
                span := SourceSpan.cover first.span comma.span
                elements := { head := first, tail := tailRev.reverse }
              } afterComma
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok {
          span := SourceSpan.cover first.span last.span
          elements := { head := first, tail := tailRev.reverse }
        } state

def barePredicates : Parser PredicateSequence := fun state =>
  match predicate state with
  | .ok first next =>
      barePredicatesTail first (next.remainingCount + 1) first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

def groupedPredicates : Parser PredicateSequence := do
  let values ← delimited .leftParen .rightParen false predicate
    .typeExpr .topLevel
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

def predicateSequence : Parser PredicateSequence := fun state =>
  if isSymbol state .leftParen then
    orElse groupedPredicates barePredicates state
  else
    barePredicates state

end PredicateInternals

/-- Optional nonempty `where` predicate sequence. -/
def whereClause : Parser (Option WhereClause) := do
  let state ← getState
  if isContextual state .where then
    let whereToken ← contextual .where .typeExpr
    let predicates ← PredicateInternals.predicateSequence
    pure (some {
      span := SourceSpan.cover whereToken.span predicates.span
      predicates := predicates.elements
    })
  else
    pure none

end Solcore.Syntax.Parser
