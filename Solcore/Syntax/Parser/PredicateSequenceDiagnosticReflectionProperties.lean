import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Predicate
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties

/-! Diagnostic-free reflection for predicates, their sequences, and `where`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem requireNonemptyForPredicate_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList TypeExpr) (phase : ParserPhase) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requireNonempty values phase) := by
  intro input nonempty next parsed diagnosticFree
  unfold requireNonempty at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail =>
      simp only [elements, pure] at parsed
      cases parsed
      exact diagnosticFree

private theorem parseNamedTypeArguments_reflectsDiagnosticFreeForPredicate
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimited_reflectsDiagnosticFreeOnSuccess .less .greater false nested
        .typeExpr .typeExpr nestedReflects)
    intro values
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (requireNonemptyForPredicate_reflectsDiagnosticFreeOnSuccess values
        .typeExpr)
    intro nonempty
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- One predicate cannot erase diagnostics from its recursive type stages. -/
theorem predicate_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess predicate := by
  unfold predicate
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    typeExpr_reflectsDiagnosticFreeOnSuccess
  intro subject
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .colon .typeExpr)
  intro colon
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .typeExpr)
  intro traitName
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (parseNamedTypeArguments_reflectsDiagnosticFreeForPredicate typeExpr
      typeExpr_reflectsDiagnosticFreeOnSuccess)
  intro arguments
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

namespace PredicateInternals

/-- Parenthesized predicate parsing reflects through its generic list. -/
theorem groupedPredicates_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess groupedPredicates := by
  unfold groupedPredicates
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen false
      predicate .typeExpr .topLevel
      predicate_reflectsDiagnosticFreeOnSuccess)
  intro values
  cases values.elements with
  | nil =>
      intro input result next parsed diagnosticFree
      simp at parsed
  | cons head tail =>
      exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem barePredicatesTail_reflectsDiagnosticFreeOnSuccess
    (first : Predicate) : ∀ fuel last tailRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (barePredicatesTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input values next parsed diagnosticFree
      simp [barePredicatesTail] at parsed
  | succ fuel inductionHypothesis =>
      intro last tailRev input values next parsed diagnosticFree
      unfold barePredicatesTail at parsed
      split at parsed
      · cases commaResult : symbol .comma .typeExpr input with
        | invariant error => simp [commaResult] at parsed
        | reject failure rejected => simp [commaResult] at parsed
        | ok comma afterComma =>
            simp only [commaResult] at parsed
            split at parsed
            · cases predicateResult : predicate afterComma with
              | invariant error => simp [predicateResult] at parsed
              | reject failure rejected => simp [predicateResult] at parsed
              | ok value afterPredicate =>
                  simp only [predicateResult] at parsed
                  have afterPredicateFree := inductionHypothesis value
                    (value :: tailRev) afterPredicate values next parsed
                    diagnosticFree
                  have afterCommaFree :=
                    predicate_reflectsDiagnosticFreeOnSuccess afterComma value
                      afterPredicate predicateResult afterPredicateFree
                  exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                    .typeExpr input comma afterComma commaResult afterCommaFree
            · have afterCommaFree : afterComma.diagnosticsRev = [] := by
                cases parsed
                exact diagnosticFree
              exact symbol_reflectsDiagnosticFreeOnSuccess .comma .typeExpr
                input comma afterComma commaResult afterCommaFree
      · cases parsed
        exact diagnosticFree

/-- A bare predicate sequence reflects through its first item and fuel loop. -/
theorem barePredicates_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess barePredicates := by
  intro input values next parsed diagnosticFree
  unfold barePredicates at parsed
  cases firstResult : predicate input with
  | invariant error => simp [firstResult] at parsed
  | reject failure rejected => simp [firstResult] at parsed
  | ok first afterFirst =>
      simp only [firstResult] at parsed
      have afterFirstFree := barePredicatesTail_reflectsDiagnosticFreeOnSuccess
        first (afterFirst.remainingCount + 1) first [] afterFirst values next
        parsed diagnosticFree
      exact predicate_reflectsDiagnosticFreeOnSuccess input first afterFirst
        firstResult afterFirstFree

/-- Transactional grouped-or-bare dispatch cannot erase diagnostics. -/
theorem predicateSequence_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess predicateSequence := by
  intro input values next parsed diagnosticFree
  unfold predicateSequence at parsed
  split at parsed
  · exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
      groupedPredicates_reflectsDiagnosticFreeOnSuccess
      barePredicates_reflectsDiagnosticFreeOnSuccess input values next parsed
      diagnosticFree
  · exact barePredicates_reflectsDiagnosticFreeOnSuccess input values next
      parsed diagnosticFree

end PredicateInternals

/-- Optional `where` parsing reflects through its marker and chosen sequence. -/
theorem whereClause_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess whereClause := by
  unfold whereClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (contextual_reflectsDiagnosticFreeOnSuccess .where .typeExpr)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      PredicateInternals.predicateSequence_reflectsDiagnosticFreeOnSuccess
    intro predicates
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

end Solcore.Syntax.Parser
