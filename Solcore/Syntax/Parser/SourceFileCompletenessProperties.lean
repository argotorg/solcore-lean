import Solcore.Syntax.Parser.CanonicalParserTotalityProperties
import Solcore.Syntax.Parser.SourceFileExactnessProperties
import Solcore.Syntax.DeclarativeSyntaxExactnessProperties

/-! Complete source-file AST and remainder correspondence on valid parser states. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every independent source-file derivation is the executable result, and every
executable result has that derivation. Supplied comments need no validity premise
for this syntax-only correspondence. -/
theorem sourceFile_ordinary_iff_exists_ok_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (comments : List Comment) {input : State} (inputValid : input.ValidFor)
    {parsed : ParsedFile} {afterParsed : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
        input.declarativeRemainder parsed afterParsed ↔
      ∃ output, sourceFile comments input = .ok parsed output ∧
        output.declarativeRemainder = afterParsed := by
  constructor
  · intro expected
    rcases productionSourceFile_exists_ok comments input inputValid with
      ⟨actual, output, result⟩
    rcases (sourceFile_exactOutcomeSpec_of_topItem itemOutcomes input.file comments)
        |>.successResultUnique (sourceFile_success_ordinaryOutcome_sound result) expected with
      ⟨valueEq, remainderEq⟩
    exact ⟨output, by simpa only [valueEq] using result, remainderEq⟩
  · rintro ⟨output, result, remainderEq⟩
    simpa only [remainderEq] using sourceFile_success_ordinaryOutcome_sound result

/-- Canonical complete-file syntax and execution agree without a recursive
exactness premise; only the input state's existing validity contract is required. -/
theorem sourceFile_ordinary_iff_exists_ok
    (comments : List Comment) {input : State} (inputValid : input.ValidFor)
    {parsed : ParsedFile} {afterParsed : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
        input.declarativeRemainder parsed afterParsed ↔
      ∃ output, sourceFile comments input = .ok parsed output ∧
        output.declarativeRemainder = afterParsed :=
  sourceFile_ordinary_iff_exists_ok_of_topItem
    DeclarativeGrammar.topItemExactOutcomeSpec comments inputValid

end Solcore.Syntax.Parser.FileInternals
