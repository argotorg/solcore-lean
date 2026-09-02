import Solcore.Syntax.DeclarativeNestingOutcomeProperties
import Solcore.Syntax.DeclarativePublicSourceFileOutcomeGrammar

/-! Branch exclusion and exact shapes of broad public syntax outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The nesting-overflow and recovery-aware source-file branches are
exclusive before either syntax shape is inspected. -/
theorem publicSourceFileBranches_disjoint
    {tokens : List Syntax.Token} {overflow : NestingOverflow}
    (exceeds : NestingExceeds tokens overflow)
    (clears : NestingClears tokens) : False :=
  exceeds.disjointClears clears

/-- Exact inversion of the two public syntax branches. -/
theorem publicSourceFileOrdinaryParses_iff
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {parsedFile : Syntax.ParsedFile} :
    PublicSourceFileOrdinaryParses file tokens comments parsedFile ↔
      (∃ overflow,
        NestingExceeds tokens overflow ∧
          parsedFile = nestingExceededParsedFile file comments) ∨
      (NestingClears tokens ∧
        ∃ final, SourceFileOrdinaryParses file comments
          (sourceFileRootRemainder tokens) parsedFile final) := by
  constructor
  · intro parsed
    cases parsed with
    | nestingExceeded nesting =>
        exact Or.inl ⟨_, nesting, rfl⟩
    | sourceFile nesting sourceParsed =>
        exact Or.inr ⟨nesting, _, sourceParsed⟩
  · rintro (⟨overflow, nesting, rfl⟩ | ⟨nesting, final, parsed⟩)
    · exact .nestingExceeded nesting
    · exact .sourceFile nesting parsed

/-- Every public syntax outcome retains exact file provenance and comments. -/
theorem PublicSourceFileOrdinaryParses.shape
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {parsedFile : Syntax.ParsedFile}
    (parsed : PublicSourceFileOrdinaryParses file tokens comments parsedFile) :
    parsedFile.source = file.id ∧
      parsedFile.span = SourceSpan.fullFile file ∧
      parsedFile.comments = comments := by
  cases parsed with
  | nestingExceeded =>
      exact ⟨rfl, rfl, rfl⟩
  | sourceFile _ sourceParsed =>
      cases sourceParsed
      exact ⟨rfl, rfl, rfl⟩

/-- If nesting exceeded, any public syntax derivation is the canonical empty
file; a clear source-file derivation is excluded. -/
theorem PublicSourceFileOrdinaryParses.eq_nestingExceededParsedFile
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {parsedFile : Syntax.ParsedFile}
    {overflow : NestingOverflow}
    (parsed : PublicSourceFileOrdinaryParses file tokens comments parsedFile)
    (exceeds : NestingExceeds tokens overflow) :
    parsedFile = nestingExceededParsedFile file comments := by
  cases parsed with
  | nestingExceeded => rfl
  | sourceFile clears _ =>
      exact False.elim (publicSourceFileBranches_disjoint exceeds clears)

/-- If nesting clears, any public syntax derivation exposes an exact broad
source-file derivation while keeping its final remainder existential. -/
theorem PublicSourceFileOrdinaryParses.sourceFile_of_clears
    {file : Syntax.SourceFile} {tokens : List Syntax.Token}
    {comments : List Syntax.Comment} {parsedFile : Syntax.ParsedFile}
    (parsed : PublicSourceFileOrdinaryParses file tokens comments parsedFile)
    (clears : NestingClears tokens) :
    ∃ final, SourceFileOrdinaryParses file comments
      (sourceFileRootRemainder tokens) parsedFile final := by
  cases parsed with
  | nestingExceeded exceeds =>
      exact False.elim (publicSourceFileBranches_disjoint exceeds clears)
  | sourceFile _ sourceParsed =>
      exact ⟨_, sourceParsed⟩

end Solcore.Syntax.DeclarativeGrammar
