import Solcore.Syntax.Parser.Delimited

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def reservedDeriveKeyword? : TokenKind → Option HardKeyword
  | .keyword value => match value with
    | .importKw | .exportKw | .pragmaKw | .typeKw | .dataKw |
        .classKw | .instanceKw | .contractKw | .publicKw | .payableKw |
        .functionKw | .constructorKw | .fallbackKw | .forallKw |
        .defaultKw => some value
    | _ => none
  | _ => none

private def deriveComponent : Parser Identifier := fun state =>
  match state.peek? with
  | some token => match reservedDeriveKeyword? token.value with
    | some keywordValue =>
        let name : Identifier := {
          span := token.span
          value := keywordValue.spelling
        }
        .ok name (({ state with cursor := state.cursor + 1 }).emit {
          span := token.span
          kind := .constraintViolation (.reservedDeriveTarget keywordValue)
        })
    | none => identifier .topItem state
  | none => rejectAt state { head := .identifier, tail := [] } .topItem

private def finishDeriveTarget (first last : Identifier)
    (tailRev : List Identifier) (state : State) : Reply DeriveTarget :=
  .ok {
    span := SourceSpan.cover first.span last.span
    value := { components := { head := first, tail := tailRev.reverse } }
  } state

private def deriveTargetTail (first : Identifier) :
    Nat → Identifier → List Identifier → State → Reply DeriveTarget
  | 0, _, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .dot then
        match symbol .dot .topItem state with
        | .ok _ afterDot =>
            match deriveComponent afterDot with
            | .ok component next =>
                deriveTargetTail first fuel component
                  (component :: tailRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        finishDeriveTarget first last tailRev state

/-- Parse one dotted trait path inside `derive`. -/
def deriveTarget : Parser DeriveTarget := fun state =>
  match deriveComponent state with
  | .ok first next =>
      deriveTargetTail first (next.remainingCount + 1) first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Parse one well-delimited canonical `#[derive(...)]` attribute. -/
def deriveAttribute : Parser DeriveAttribute := do
  let hash ← symbol .hash .topItem
  let _ ← symbol .leftBracket .topItem
  let _ ← contextual .derive .topItem
  let targets ← delimitedNoTrailing .leftParen .rightParen true
    deriveTarget .topItem .topLevel
  let closing ← symbol .rightBracket .topItem
  let span := SourceSpan.cover hash.span closing.span
  if targets.elements.isEmpty then
    let _ ← emitDiagnostic {
      span
      kind := .constraintViolation .deriveRequiresTarget
    }
  else
    pure ()
  pure { span, value := { targets } }

end Solcore.Syntax.Parser
