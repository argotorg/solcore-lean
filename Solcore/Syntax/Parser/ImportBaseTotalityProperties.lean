import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.ModulePathTotalityProperties

/-! Totality laws for import terminators and the two basic import forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem pure_ordinary {α : Type} (value : α) :
    Parser.Ordinary (pure value : Parser α) := by
  intro input
  exact Or.inl ⟨value, input, rfl⟩

private theorem bind_ordinary {α β : Type} {first : Parser α}
    {next : α → Parser β} (firstOrdinary : Parser.Ordinary first)
    (nextOrdinary : ∀ value, Parser.Ordinary (next value)) :
    Parser.Ordinary (first >>= next) := by
  intro input
  rcases firstOrdinary input with
    ⟨value, middle, firstResult⟩ | ⟨failure, rejected, firstResult⟩
  · rcases nextOrdinary value middle with
      ⟨result, final, nextResult⟩ | ⟨failure, rejected, nextResult⟩
    · exact Or.inl ⟨result, final, by
        simp only [bind, firstResult, nextResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [bind, firstResult, nextResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [bind, firstResult]⟩

namespace ImportInternals

/-- An import terminator always succeeds or reports a source rejection. -/
theorem terminator_ordinary (lastSpan : SourceSpan) :
    Parser.Ordinary (terminator lastSpan) := by
  intro input
  unfold terminator
  split
  · rcases symbol_ordinary .semicolon .importDecl input with
      ⟨token, next, result⟩ | ⟨failure, rejected, result⟩
    · exact Or.inl ⟨token.span, next, by simp only [result]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [result]⟩
  · split
    · exact Or.inl ⟨lastSpan, input.emit {
          span := input.currentSpan
          kind := .constraintViolation
            (.trailingSemicolonRequired .importDecl)
        }, rfl⟩
    · exact Or.inr ⟨_, input, rfl⟩

/-- Import terminators cannot expose an internal parser invariant. -/
theorem terminator_ne_invariant (lastSpan : SourceSpan) (input : State)
    (error : ParserInvariantError) :
    terminator lastSpan input ≠ .invariant error :=
  (terminator_ordinary lastSpan).ne_invariant input error

/-- Finishing an already parsed import payload is ordinary on every input. -/
theorem finish_ordinary (start last : SourceSpan) (value : ImportDeclValue) :
    Parser.Ordinary (finish start last value) := by
  unfold finish
  exact bind_ordinary (terminator_ordinary last) (fun endSpan =>
    pure_ordinary ({
      span := SourceSpan.cover start endSpan
      value
    } : ImportDecl))

/-- Import finishing cannot introduce an internal invariant. -/
theorem finish_ne_invariant (start last : SourceSpan)
    (value : ImportDeclValue) (input : State)
    (error : ParserInvariantError) :
    finish start last value input ≠ .invariant error :=
  (finish_ordinary start last value).ne_invariant input error

/-- Plain module imports are ordinary on every input. -/
theorem plainImport_ordinary (start : SourceSpan) :
    Parser.Ordinary (plainImport start) := by
  unfold plainImport
  exact bind_ordinary (modulePath_ordinary .importDecl) (fun path =>
    finish_ordinary start path.span (.plain path))

/-- Plain module imports cannot expose an internal invariant. -/
theorem plainImport_ne_invariant (start : SourceSpan) (input : State)
    (error : ParserInvariantError) :
    plainImport start input ≠ .invariant error :=
  (plainImport_ordinary start).ne_invariant input error

/-- Wildcard namespace-alias imports are ordinary on every input. -/
theorem namespaceImport_ordinary (start : SourceSpan) :
    Parser.Ordinary (namespaceImport start) := by
  unfold namespaceImport
  exact bind_ordinary (symbol_ordinary .star .importDecl) (fun _ =>
    bind_ordinary (keyword_ordinary .asKw .importDecl) (fun _ =>
      bind_ordinary (identifier_ordinary .importDecl) (fun alias =>
        bind_ordinary (contextual_ordinary .from .importDecl) (fun _ =>
          bind_ordinary (modulePath_ordinary .importDecl) (fun path =>
            finish_ordinary start path.span (.namespace path alias))))))

/-- Namespace imports cannot expose an internal invariant. -/
theorem namespaceImport_ne_invariant (start : SourceSpan) (input : State)
    (error : ParserInvariantError) :
    namespaceImport start input ≠ .invariant error :=
  (namespaceImport_ordinary start).ne_invariant input error

end ImportInternals
end Solcore.Syntax.Parser
