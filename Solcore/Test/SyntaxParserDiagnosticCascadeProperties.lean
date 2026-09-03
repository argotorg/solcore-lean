import Solcore.Syntax.Parser.DiagnosticCascadeProperties

/-! Consumers of independent keep/drop decisions and exact diagnostic lists. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDiagnosticCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List SourceSpan)
    (filtered : LexicalCascadeFilters file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical (topItemRecoveryDiagnostics raw) =
      topItemRecoveryDiagnostics kept :=
  (filterParseDiagnostics_recoveredTopItems_iff file lexical raw kept).mp filtered

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List SourceSpan)
    (result : filterParseDiagnostics file lexical (topItemRecoveryDiagnostics raw) =
      topItemRecoveryDiagnostics kept) :
    LexicalCascadeFilters file.content (lexical.map (·.span)) raw kept :=
  (filterParseDiagnostics_recoveredTopItems_iff file lexical raw kept).mpr result

example (file : SourceFile) (lexical : List LexicalDiagnostic) (span : SourceSpan)
    (suppressed : LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical (topItemRecoveryDiagnostics [span]) = [] :=
  filterParseDiagnostics_recoveredTopItems_of_filters file lexical (.drop suppressed .nil)

example (file : SourceFile) (lexical : List LexicalDiagnostic) (span : SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical (topItemRecoveryDiagnostics [span, span]) =
      topItemRecoveryDiagnostics [span, span] :=
  filterParseDiagnostics_recoveredTopItems_of_filters file lexical
    (.keep retained (.keep retained .nil))

example (source : String) (lexical raw : List SourceSpan) :
    ∃ kept, LexicalCascadeFilters source lexical raw kept ∧
      ∀ other, LexicalCascadeFilters source lexical raw other → other = kept := by
  rcases lexicalCascadeFilters_total source lexical raw with ⟨kept, filtered⟩
  exact ⟨kept, filtered, fun _ other => other.output_unique filtered⟩

end Solcore.Test.SyntaxParserDiagnosticCascadeProperties
