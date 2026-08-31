import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.TopLevel

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

private def validDeriveAttribute : Parser DeriveAttribute := do
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

private def startsDeriveContractField (state : State) : Bool :=
  isIdentifier state && state.peekOffsetKind? 1 == some (.symbol .colon)

private def atDeriveDeclarationBoundary (state : State) : Bool :=
  atTopItemStart state || startsDeriveContractField state ||
    isSymbol state .rightBrace

private def finishRecoveredDerive (hash last : SourceSpan)
    (constraint : ParseConstraint) (state : State) : Reply DeriveAttribute :=
  let span := SourceSpan.cover hash last
  .ok {
    span
    value := { targets := { span, elements := [] } }
  } (state.emit { span, kind := .constraintViolation constraint })

private def recoverDeriveTail (hash last : SourceSpan) :
    Nat → State → Reply DeriveAttribute
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if isSymbol state .rightBracket then
        match symbol .rightBracket .topItem state with
        | .ok closing next =>
            finishRecoveredDerive hash closing.span
              .malformedDeriveAttribute next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else if state.atEnd || atDeriveDeclarationBoundary state then
        finishRecoveredDerive hash last .unclosedDeriveAttribute state
      else
        match state.advance? with
        | some (token, next) =>
            recoverDeriveTail hash token.span fuel next
        | none => finishRecoveredDerive hash last .unclosedDeriveAttribute state

private def recoveredDeriveAttribute : Parser DeriveAttribute := fun state =>
  match symbol .hash .topItem state with
  | .ok hash afterHash =>
      match symbol .leftBracket .topItem afterHash with
      | .ok opening next =>
          recoverDeriveTail hash.span opening.span
            (next.remainingCount + 1) next
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/--
Parse one canonical derive attribute. Once `#[` has been consumed, malformed
and unclosed forms become empty recovered attributes without consuming the next
declaration boundary.
-/
def deriveAttribute : Parser DeriveAttribute :=
  orElse validDeriveAttribute recoveredDeriveAttribute

end Solcore.Syntax.Parser
