import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar

/-! Exact ordered selection for one Core-type dispatch layer. Every later
branch retains all earlier negative guards, independently of any raw outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive TypeDispatchBranch where
  | function | comptime | mapping | proxy | tuple | named | final
  deriving DecidableEq

def TypeDispatchPairPresent (input : Remainder) (keyword : ContextualKeyword) (symbol : Symbol) : Prop :=
  ∃ markerSpan openingSpan,
    TokenAt input.tokens input.endIndex input.cursor { span := markerSpan, value := .identifier keyword.spelling } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) { span := openingSpan, value := .symbol symbol }

inductive TypeDispatchSelects (input : Remainder) : TypeDispatchBranch → Prop where
  | function
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .keyword .functionKw }) :
      TypeDispatchSelects input .function
  | comptime
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
      (present : TypeDispatchPairPresent input .comptime .less) :
      TypeDispatchSelects input .comptime
  | mapping
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (present : TypeDispatchPairPresent input .mapping .leftParen) :
      TypeDispatchSelects input .mapping
  | proxy
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (mappingAbsent : ContextualSymbolPairAbsentAt input .mapping .leftParen)
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at }) :
      TypeDispatchSelects input .proxy
  | tuple
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (mappingAbsent : ContextualSymbolPairAbsentAt input .mapping .leftParen)
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen }) :
      TypeDispatchSelects input .tuple
  | named
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (mappingAbsent : ContextualSymbolPairAbsentAt input .mapping .leftParen)
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (present : ∃ span text, TokenAt input.tokens input.endIndex input.cursor { span, value := .identifier text }) :
      TypeDispatchSelects input .named
  | final
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (mappingAbsent : ContextualSymbolPairAbsentAt input .mapping .leftParen)
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (identifierAbsent : IdentifierAbsentAt input) :
      TypeDispatchSelects input .final

end Solcore.Syntax.DeclarativeGrammar
