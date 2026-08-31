import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.Type

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def requireTypeArguments (values : DelimitedList TypeExpr) :
    Parser (NonemptyDelimitedList TypeExpr) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .typeExpr values.span)

/-- Parse one trait predicate `subject: Trait<arguments...>`. -/
def predicate : Parser Predicate := do
  let subject ← typeExpr
  let _ ← symbol .colon .typeExpr
  let traitName ← identifier .typeExpr
  let state ← getState
  let arguments ←
    if isSymbol state .less then
      do
        let values ← delimited .less .greater false typeExpr
          .typeExpr .typeExpr
        let nonempty ← requireTypeArguments values
        pure (some nonempty)
    else
      pure none
  let endSpan := match arguments with
    | some values => values.span
    | none => traitName.span
  pure {
    span := SourceSpan.cover subject.span endSpan
    subject
    traitName
    arguments
  }

private structure PredicateSequence where
  span : SourceSpan
  values : NonemptyList Predicate

private def barePredicatesTail (first : Predicate) :
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
                values := { head := first, tail := tailRev.reverse }
              } afterComma
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok {
          span := SourceSpan.cover first.span last.span
          values := { head := first, tail := tailRev.reverse }
        } state

private def barePredicates : Parser PredicateSequence := fun state =>
  match predicate state with
  | .ok first next =>
      barePredicatesTail first (next.remainingCount + 1) first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

private def groupedPredicates : Parser PredicateSequence := do
  let values ← delimited .leftParen .rightParen false predicate
    .typeExpr .topLevel
  match values.elements with
  | head :: tail => pure {
      span := values.span
      values := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

private def predicateSequence : Parser PredicateSequence := fun state =>
  if isSymbol state .leftParen then
    orElse groupedPredicates barePredicates state
  else
    barePredicates state

/-- Optional nonempty `where` predicate sequence. -/
def whereClause : Parser (Option WhereClause) := do
  let state ← getState
  if isContextual state .where then
    let whereToken ← contextual .where .typeExpr
    let predicates ← predicateSequence
    pure (some {
      span := SourceSpan.cover whereToken.span predicates.span
      predicates := predicates.values
    })
  else
    pure none

end Solcore.Syntax.Parser
