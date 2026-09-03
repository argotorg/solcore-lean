import Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples

/-! Real lexical errors suppress a same-line pragma expectation report but
retain one after LF. Complete outputs share the same lexical byte ranges. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaNameCascadeExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples

private def invalidToken : LexicalDiagnostic := {
  span := byteSpan 0 2
  kind := .invalidToken
}

set_option maxRecDepth 4096 in
private theorem sameLineLexes :
    Lexer.lex (exampleFile "§ pragma ;") =
      .ok (lexicalCarrier (pragmaTokens 3 []) [invalidToken]) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 4096 in
private theorem nextLineLexes :
    Lexer.lex (exampleFile "§\npragma ;") =
      .ok (lexicalCarrier (pragmaTokens 3 []) [invalidToken]) := by
  apply lex_ok_of_toOption
  decide +kernel

private theorem sameLineSuppressed :
    LexicalCascadeSuppresses "§ pragma ;" [invalidToken.span] (byteSpan 10 11) := by
  refine ⟨invalidToken.span, by simp, rfl, Or.inl ?_⟩
  decide

/-- The invalid character remains in lexicalDiagnostics at bytes 0..2;
the same-line unexpected-semicolon report at 10..11 is removed completely. -/
theorem sameLine_parse_eq_output :
    parse (exampleFile "§ pragma ;") =
      .ok (expectedOutput "§ pragma ;" (pragmaTokens 3 []) [invalidToken] []) :=
  (completeOutputs sameLineLexes (pragmaTokensClear 3 [] .done)
    (pragmaSemicolonMissing "§ pragma ;" 3 []) (.drop sameLineSuppressed .nil)).2

private theorem nextLineRetained :
    ¬ LexicalCascadeSuppresses "§\npragma ;" [invalidToken.span] (byteSpan 10 11) := by
  rintro ⟨span, member, _sourceEq, suppressed⟩
  have spanEq : span = invalidToken.span := by simpa using member
  subst span
  rcases suppressed with sameLine | overlap | covered | adjacent
  · exact (by decide : cascadeLineIndex "§\npragma ;" invalidToken.span.startByte ≠
      cascadeLineIndex "§\npragma ;" (byteSpan 10 11).startByte) sameLine
  · exact (by decide : ¬ (byteSpan 10 11).startByte < invalidToken.span.endByte) overlap.2
  · exact (by decide : ¬ (byteSpan 10 11).startByte ≤ invalidToken.span.endByte) covered.2
  · rcases adjacent with ⟨_ordered, gap, sliced, whitespace⟩
    have exactGap : Trivia.utf8Slice? "§\npragma ;" invalidToken.span.endByte
        (byteSpan 10 11).startByte = some "\npragma " := by decide
    have gapEq : gap = "\npragma " := Option.some.inj (sliced.symm.trans exactGap)
    subst gap
    contradiction

/-- On the next LF line both diagnostics remain, with the actual found token,
identifier expectation, pragma context, and exact two independent byte spans. -/
theorem nextLine_parse_eq_output :
    parse (exampleFile "§\npragma ;") =
      .ok (expectedOutput "§\npragma ;" (pragmaTokens 3 []) [invalidToken]
        [{
          span := byteSpan 10 11
          kind := .unexpected (some (.symbol .semicolon))
            { head := .identifier, tail := [] } .pragmaDecl
        }]) :=
  (completeOutputs nextLineLexes (pragmaTokensClear 3 [] .done)
    (pragmaSemicolonMissing "§\npragma ;" 3 []) (.keep nextLineRetained .nil)).2

/-- Already-tokenized parsing uses validation from the same canonical lexical
fixture and returns the identical full suppressed output. -/
theorem sameLine_parseLexed_eq_output :
    parseLexed (exampleFile "§ pragma ;")
        (lexicalCarrier (pragmaTokens 3 []) [invalidToken]) =
      .ok (expectedOutput "§ pragma ;" (pragmaTokens 3 []) [invalidToken] []) :=
  (completeOutputs sameLineLexes (pragmaTokensClear 3 [] .done)
    (pragmaSemicolonMissing "§ pragma ;" 3 []) (.drop sameLineSuppressed .nil)).1

end Solcore.Test.SyntaxParserPublicPragmaNameCascadeExamples
