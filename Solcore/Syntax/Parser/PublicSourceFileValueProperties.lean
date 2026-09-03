import Solcore.Syntax.DeclarativePublicSourceFileValueProperties
import Solcore.Syntax.Parser.PublicSourceFileOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SourceFileExactnessProperties

/-! Public parsed-file value uniqueness; no public remainder or rejection is invented. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- At the same supplied file and lexed carrier, including its source, span,
tokens, and comments, successful public parses agree on their syntax AST. -/
theorem parseLexed_ok_parsed_value_unique_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    {file : SourceFile} {lexed : LexedFile} {left right : ParseOutput}
    (leftResult : parseLexed file lexed = .ok left)
    (rightResult : parseLexed file lexed = .ok right) :
    left.parsed = right.parsed :=
  DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique_of_topItem
    itemValues (parseLexed_ok_publicSourceFileOrdinary_sound leftResult)
    (parseLexed_ok_publicSourceFileOrdinary_sound rightResult)

/-- Exact top-item outcomes fix public syntax at one supplied lexed carrier. -/
theorem parseLexed_ok_parsed_value_unique_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    {file : SourceFile} {lexed : LexedFile} {left right : ParseOutput}
    (leftResult : parseLexed file lexed = .ok left)
    (rightResult : parseLexed file lexed = .ok right) :
    left.parsed = right.parsed :=
  parseLexed_ok_parsed_value_unique_of_topItemValues itemOutcomes.successValueUnique
    leftResult rightResult

/-- Two successful parses of the same source file share one lexical result;
top-item value uniqueness therefore fixes their complete public syntax AST. -/
theorem parse_ok_parsed_value_unique_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    {file : SourceFile} {left right : ParseOutput}
    (leftResult : parse file = .ok left)
    (rightResult : parse file = .ok right) : left.parsed = right.parsed := by
  rcases parse_ok_lexed_provenance file left leftResult with
    ⟨leftLexed, leftLexing, leftParsing, leftTokens, leftDiagnostics, leftComments⟩
  rcases parse_ok_lexed_provenance file right rightResult with
    ⟨rightLexed, rightLexing, rightParsing, rightTokens, rightDiagnostics,
      rightComments⟩
  have lexedEq : leftLexed = rightLexed :=
    Except.ok.inj (leftLexing.symm.trans rightLexing)
  subst lexedEq
  exact parseLexed_ok_parsed_value_unique_of_topItemValues itemValues
    leftParsing rightParsing

/-- Exact top-item outcomes fix public syntax at one supplied source file. -/
theorem parse_ok_parsed_value_unique_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    {file : SourceFile} {left right : ParseOutput}
    (leftResult : parse file = .ok left)
    (rightResult : parse file = .ok right) : left.parsed = right.parsed :=
  parse_ok_parsed_value_unique_of_topItemValues itemOutcomes.successValueUnique
    leftResult rightResult

end Solcore.Syntax.Parser
