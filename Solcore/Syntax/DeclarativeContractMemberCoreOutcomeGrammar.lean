import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeContractFieldOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreTermPublicOutcomeProperties
import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeTypeAliasOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for attribute-free contract-member
dispatch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact current-token evidence for one contract-member dispatch selector. -/
def ContractMemberCoreTokenPresentAt (input : Remainder)
    (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := kind
  }

/-- Exact broad success of attribute-free contract-member dispatch in
executable priority order. -/
inductive ContractMemberCoreOrdinaryParses :
    Remainder → Syntax.ContractMember → Remainder → Prop where
  | field {input output : Remainder}
      {declaration : Syntax.ContractField}
      (fieldPresent : ContractFieldStartsAt input)
      (fieldParsed : ContractFieldOrdinaryParses
        CoreExpressionOrdinaryParses input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .field declaration
      } output
  | function {input output : Remainder}
      {declaration : Syntax.FunctionDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .functionKw))
      (functionParsed : FunctionDeclOrdinaryParses input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .function declaration
      } output
  | constructor {input output : Remainder}
      {declaration : Syntax.ConstructorDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .constructorKw))
      (constructorParsed : ConstructorDeclOrdinaryParses input declaration
        output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .constructor declaration
      } output
  | fallback {input output : Remainder}
      {declaration : Syntax.FallbackDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .fallbackKw))
      (fallbackParsed : FallbackDeclOrdinaryParses input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .fallback declaration
      } output
  | typeAlias {input output : Remainder}
      {declaration : Syntax.TypeAliasDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typePresent : ContractMemberCoreTokenPresentAt input
        (.keyword .typeKw))
      (typeParsed : TypeAliasDeclOrdinaryParses input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .typeAlias declaration
      } output
  | enum {input output : Remainder} {declaration : Syntax.EnumDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (enumPresent : ContractMemberCoreTokenPresentAt input
        (.identifier ContextualKeyword.enum.spelling))
      (enumParsed : EnumDeclOrdinaryParses none input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .enum declaration
      } output

/-- Exact selected branch and final remainder of an attribute-free member
rejection. -/
inductive ContractMemberCoreRejects : Remainder → Remainder → Prop where
  | fieldRejected {input rejected : Remainder}
      (fieldPresent : ContractFieldStartsAt input)
      (fieldRejected : ContractFieldRejects
        CoreExpressionOrdinaryParses CoreExpressionPublicRejects input
          rejected) :
      ContractMemberCoreRejects input rejected
  | functionRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .functionKw))
      (functionRejected : FunctionDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | constructorRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .constructorKw))
      (constructorRejected : ConstructorDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | fallbackRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .fallbackKw))
      (fallbackRejected : FallbackDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | typeAliasRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typePresent : ContractMemberCoreTokenPresentAt input
        (.keyword .typeKw))
      (typeRejected : TypeAliasDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | enumRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (enumPresent : ContractMemberCoreTokenPresentAt input
        (.identifier ContextualKeyword.enum.spelling))
      (enumRejected : EnumDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | unrecognized {input : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (enumAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.enum.spelling)) :
      ContractMemberCoreRejects input input

end Solcore.Syntax.DeclarativeGrammar
