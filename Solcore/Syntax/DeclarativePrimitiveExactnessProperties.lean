import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeProperties
import Solcore.Syntax.DeclarativeExactOutcomeSpec

/-! Exact functionality of primitive declarative token outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One carrier slot contains at most one exact token. -/
theorem TokenAt.token_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- An exact-token success fixes the consumed source span. -/
theorem ExactTokenParses.span_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftSpan = rightSpan := by
  exact congrArg (fun token : Token => token.span)
    (leftParsed.1.token_unique rightParsed.1)

/-- An exact-token success fixes the one-token advanced remainder. -/
theorem ExactTokenParses.output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- An exact-token success fixes both its span and final remainder. -/
theorem ExactTokenParses.result_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftSpan = rightSpan ∧ leftOutput = rightOutput :=
  ⟨leftParsed.span_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The token at one checked-identifier position fixes its exact value. -/
theorem IdentifierParses.value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) : left = right := by
  have tokenEq : ({ span := left.span, value := .identifier left.value } :
      Token) = { span := right.span, value := .identifier right.value } :=
    leftParsed.1.token_unique rightParsed.1
  cases left
  cases right
  simp_all

/-- A checked identifier fixes both its exact value and final remainder. -/
theorem IdentifierParses.result_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Checked-identifier rejection has one exact nonconsuming endpoint. -/
theorem IdentifierRejects.output_unique {input left right : Remainder}
    (leftRejects : IdentifierRejects input left)
    (rightRejects : IdentifierRejects input right) : left = right := by
  cases leftRejects
  cases rightRejects
  rfl

/-- Checked identifiers have fully functional success and rejection outcomes. -/
theorem identifierExactOutcomeSpec :
    ExactDeterministicOutcomeSpec IdentifierParses IdentifierRejects where
  toDeterministicOutcomeSpec := identifierDeterministicOutcomeSpec
  successValueUnique := IdentifierParses.value_unique
  rejectOutputUnique := IdentifierRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
