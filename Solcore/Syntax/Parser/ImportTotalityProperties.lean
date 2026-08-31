import Solcore.Syntax.Parser.ImportBaseTotalityProperties
import Solcore.Syntax.Parser.ImportSelectionTotalityProperties

/-! Totality laws for complete canonical import declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImportInternals

/-- Wildcard imports are invariant-free on every canonical valid input. -/
theorem wildcardImport_invariantFreeOnValid (start : SourceSpan) :
    Parser.InvariantFreeOnValid (wildcardImport start) := by
  unfold wildcardImport
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .star .importDecl)
    (symbol_ordinary .star .importDecl).invariantFreeOnValid
  intro _star
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .from .importDecl)
    (contextual_ordinary .from .importDecl).invariantFreeOnValid
  intro _fromMarker
  apply Parser.bind_invariantFreeOnValid
    (modulePath_validFor .importDecl)
    (modulePath_ordinary .importDecl).invariantFreeOnValid
  intro path
  apply Parser.bind_invariantFreeOnValid optionalHiding_validFor
    optionalHiding_invariantFreeOnValid
  intro hidden
  exact (finish_ordinary start
    (match hidden with
      | some clause => clause.span
      | none => path.span)
    (.wildcard path hidden)).invariantFreeOnValid

/-- A wildcard import has an ordinary success or rejection on valid input. -/
theorem wildcardImport_ordinary (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor) :
    (∃ value next, wildcardImport start input = .ok value next) ∨
      (∃ failure next, wildcardImport start input = .reject failure next) :=
  wildcardImport_invariantFreeOnValid start input inputValid

theorem wildcardImport_ne_invariant (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    wildcardImport start input ≠ .invariant error :=
  (wildcardImport_invariantFreeOnValid start).ne_invariant
    input inputValid error

/-- Selective imports are invariant-free on every canonical valid input. -/
theorem selectiveImport_invariantFreeOnValid (start : SourceSpan) :
    Parser.InvariantFreeOnValid (selectiveImport start) := by
  unfold selectiveImport
  apply Parser.bind_invariantFreeOnValid selectedImports_validFor
    selectedImports_invariantFreeOnValid
  intro _selection
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .from .importDecl)
    (contextual_ordinary .from .importDecl).invariantFreeOnValid
  intro _fromMarker
  apply Parser.bind_invariantFreeOnValid
    (modulePath_validFor .importDecl)
    (modulePath_ordinary .importDecl).invariantFreeOnValid
  intro path
  apply Parser.bind_invariantFreeOnValid optionalHiding_validFor
    optionalHiding_invariantFreeOnValid
  intro hidden
  exact (finish_ordinary start
    (match hidden with
      | some clause => clause.span
      | none => path.span)
    (.selected _selection path hidden)).invariantFreeOnValid

/-- A selective import has an ordinary success or rejection on valid input. -/
theorem selectiveImport_ordinary (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor) :
    (∃ value next, selectiveImport start input = .ok value next) ∨
      (∃ failure next, selectiveImport start input = .reject failure next) :=
  selectiveImport_invariantFreeOnValid start input inputValid

theorem selectiveImport_ne_invariant (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    selectiveImport start input ≠ .invariant error :=
  (selectiveImport_invariantFreeOnValid start).ne_invariant
    input inputValid error

end ImportInternals

/-- Complete import dispatch is invariant-free on canonical valid input. -/
theorem importDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid importDecl := by
  unfold importDecl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .importKw .importDecl)
    (keyword_ordinary .importKw .importDecl).invariantFreeOnValid
  intro importKeyword
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases star : isSymbol observed .star
  · simp only [star, if_true]
    by_cases namespaceAlias :
        observed.peekOffsetKind? 1 == some (.keyword .asKw)
    · simp only [namespaceAlias, if_true]
      exact (ImportInternals.namespaceImport_ordinary
        importKeyword.span).invariantFreeOnValid
    · simp only [namespaceAlias, Bool.false_eq_true, if_false]
      exact ImportInternals.wildcardImport_invariantFreeOnValid
        importKeyword.span
  · simp only [star, Bool.false_eq_true, if_false]
    by_cases selected : isSymbol observed .leftBrace
    · simp only [selected, if_true]
      exact ImportInternals.selectiveImport_invariantFreeOnValid
        importKeyword.span
    · simp only [selected, Bool.false_eq_true, if_false]
      exact (ImportInternals.plainImport_ordinary
        importKeyword.span).invariantFreeOnValid

/-- Complete import parsing has an ordinary reply on valid input. -/
theorem importDecl_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ value next, importDecl input = .ok value next) ∨
      (∃ failure next, importDecl input = .reject failure next) :=
  importDecl_invariantFreeOnValid input inputValid

theorem importDecl_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    importDecl input ≠ .invariant error :=
  importDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
