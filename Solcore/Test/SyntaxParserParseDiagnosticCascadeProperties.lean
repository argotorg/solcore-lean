import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties

/-! Mixed complete-report normalization, including protected metadata and duplicates. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserParseDiagnosticCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @ParseDiagnosticCascadeFilters.output_unique
example := @parseDiagnosticCascadeFilters_total
example := @parseDiagnosticCascadeFilters_protected_cons
example := @ParseDiagnosticCascadeFilters.sublist
example := @parseDiagnosticCascadeFilters_nil_lexical
example := @filterParseDiagnostics_cons_of_suppressed
example := @filterParseDiagnostics_cons_of_retained

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List ParseDiagnostic)
    (filtered : ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical raw = kept :=
  filterParseDiagnostics_eq_of_cascadeFilters file lexical filtered

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List ParseDiagnostic)
    (result : filterParseDiagnostics file lexical raw = kept) :
    ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) raw kept :=
  (filterParseDiagnostics_eq_iff_cascadeFilters file lexical raw kept).mp result

/-- Equal spans do not make protected metadata removable. The original order
and the repeated identifier report survive between heterogeneous failures. -/
theorem mixed_protected_reports_retained
    (file : SourceFile) (lexical : List LexicalDiagnostic) (span : SourceSpan)
    (text : String) (constraint : ParseConstraint) (nesting : NestingKind) (limit : Nat)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (site : RecoverySite)
    (suppressed : LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical [
      { span, kind := .invalidIdentifierHyphen text },
      { span, kind := .unexpected found expected context },
      { span, kind := .constraintViolation constraint },
      { span, kind := .recovered site },
      { span, kind := .nestingExceeded nesting limit },
      { span, kind := .invalidIdentifierHyphen text }
    ] = [
      { span, kind := .invalidIdentifierHyphen text },
      { span, kind := .constraintViolation constraint },
      { span, kind := .nestingExceeded nesting limit },
      { span, kind := .invalidIdentifierHyphen text }
    ] := by
  apply filterParseDiagnostics_eq_of_cascadeFilters
  exact .keep (fun h => h.1) (.drop ⟨trivial, suppressed⟩
    (.keep (fun h => h.1) (.drop ⟨trivial, suppressed⟩
      (.keep (fun h => h.1) (.keep (fun h => h.1) .nil)))))

/-- Distinct expectations at one retained span cannot be collapsed into a
single span-only event. Every payload and repeated report survives exactly. -/
theorem mixed_expectations_retained
    (file : SourceFile) (lexical : List LexicalDiagnostic) (span : SourceSpan)
    (leftFound rightFound : Option TokenKind)
    (leftExpected rightExpected : NonemptyList ParseExpectation)
    (leftContext rightContext : ParseContext)
    (retained : ¬ LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical [
      { span, kind := .unexpected leftFound leftExpected leftContext },
      { span, kind := .unexpected rightFound rightExpected rightContext },
      { span, kind := .unexpected leftFound leftExpected leftContext }
    ] = [
      { span, kind := .unexpected leftFound leftExpected leftContext },
      { span, kind := .unexpected rightFound rightExpected rightContext },
      { span, kind := .unexpected leftFound leftExpected leftContext }
    ] := by
  apply filterParseDiagnostics_eq_of_cascadeFilters
  exact .keep (fun h => retained h.2)
    (.keep (fun h => retained h.2) (.keep (fun h => retained h.2) .nil))

end Solcore.Test.SyntaxParserParseDiagnosticCascadeProperties
