import Solcore.Syntax.DeclarativeContractMemberCoreOutcomeGrammar

/-!
Parser-independent exact ordinary outcomes for contract-member recovery.
Recovery consumes one mandatory token, scans up to the next member boundary,
and returns an error member without consuming that boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact nonconsuming boundaries recognized by contract-member recovery. -/
inductive ContractMemberRecoveryBoundaryStartsAt : Remainder → Prop where
  | hash {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input (.symbol .hash)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | function {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.keyword .functionKw)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | constructor {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.keyword .constructorKw)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | fallback {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.keyword .fallbackKw)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | typeAlias {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input (.keyword .typeKw)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | rightBrace {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.symbol .rightBrace)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | enum {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.identifier ContextualKeyword.enum.spelling)) :
      ContractMemberRecoveryBoundaryStartsAt input

/-- Exact stops of the scan after recovery consumed its mandatory first
token.  A missing carrier slot inside the active window finishes recovery. -/
inductive ContractMemberRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      ContractMemberRecoveryStops input
  | boundary {input : Remainder}
      (starts : ContractMemberRecoveryBoundaryStartsAt input) :
      ContractMemberRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      ContractMemberRecoveryStops input

/-- Canonical error member produced from the first and last consumed spans. -/
def recoveredContractMemberValue
    (first last : SourceSpan) : Syntax.ContractMember := {
  span := SourceSpan.cover first last
  leadingComments := []
  value := .error
}

/-- Exact priority-ordered scan after the mandatory first recovery token. -/
inductive ContractMemberRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.ContractMember → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : ContractMemberRecoveryStops input) :
      ContractMemberRecoveryScanParses first last input
        (recoveredContractMemberValue first last) input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {member : Syntax.ContractMember}
      (continues : ¬ ContractMemberRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : ContractMemberRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } member output) :
      ContractMemberRecoveryScanParses first last input member output

/-- Successful recovery consumes one arbitrary current token before scanning. -/
inductive ContractMemberRecoveryParses :
    Remainder → Syntax.ContractMember → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {member : Syntax.ContractMember}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : ContractMemberRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } member output) :
      ContractMemberRecoveryParses input member output

/-- Recovery rejects only when its mandatory first token is unavailable. -/
inductive ContractMemberRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      ContractMemberRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      ContractMemberRecoveryRejects input input

end Solcore.Syntax.DeclarativeGrammar
