import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Term

/-!
Foundations of the grammar's exact diagnostic traces.

The contracts that a traced relation can satisfy (`TraceExactOutcomeSpec`,
`TraceOutcomeAgreement`), and the cascade laws that say which diagnostics an
earlier event suppresses. The per-construct trace files build on these.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeDiagnosticCascadeProperties
/-! Totality and exact retained-list uniqueness for independent cascade filtering. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem LexicalCascadeFilters.output_unique
    {source : String} {lexical raw left right : List SourceSpan}
    (leftFiltered : LexicalCascadeFilters source lexical raw left)
    (rightFiltered : LexicalCascadeFilters source lexical raw right) :
    left = right := by
  induction leftFiltered generalizing right with
  | nil => cases rightFiltered; rfl
  | keep retained tail ih =>
      cases rightFiltered with
      | keep _ rightTail => rw [ih rightTail]
      | drop suppressed _ => exact False.elim (retained suppressed)
  | drop suppressed tail ih =>
      cases rightFiltered with
      | keep retained _ => exact False.elim (retained suppressed)
      | drop _ rightTail => exact ih rightTail

theorem lexicalCascadeFilters_total (source : String)
    (lexical raw : List SourceSpan) :
    ∃ kept, LexicalCascadeFilters source lexical raw kept := by
  classical
  induction raw with
  | nil => exact ⟨[], .nil⟩
  | cons span raw ih =>
      rcases ih with ⟨kept, filtered⟩
      by_cases suppressed : LexicalCascadeSuppresses source lexical span
      · exact ⟨kept, .drop suppressed filtered⟩
      · exact ⟨span :: kept, .keep suppressed filtered⟩

theorem lexicalCascadeFilters_nil_lexical (source : String)
    (raw : List SourceSpan) : LexicalCascadeFilters source [] raw raw := by
  induction raw with
  | nil => exact .nil
  | cons span raw ih => exact .keep (by simp [LexicalCascadeSuppresses]) ih

theorem lexicalCascadeFilters_singleton_iff
    {source : String} {lexical kept : List SourceSpan} {span : SourceSpan} :
    LexicalCascadeFilters source lexical [span] kept ↔
      (LexicalCascadeSuppresses source lexical span ∧ kept = []) ∨
      (¬ LexicalCascadeSuppresses source lexical span ∧ kept = [span]) := by
  constructor
  · intro filtered
    cases filtered with
    | keep retained tail => cases tail; exact Or.inr ⟨retained, rfl⟩
    | drop suppressed tail => cases tail; exact Or.inl ⟨suppressed, rfl⟩
  · rintro (⟨suppressed, rfl⟩ | ⟨retained, rfl⟩)
    · exact .drop suppressed .nil
    · exact .keep retained .nil

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionTraceOutcomeSpec
/-! Parser-independent expression trace assumptions for compositional laws.
Existence is separate from exactness; neither asserts a concrete implementation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

structure ExpressionTraceExactOutcomeSpec
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (expressionRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop where
  successResultUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    expressionTrace source endByte input left afterLeft leftTrace →
    expressionTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace
  rejectResultUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    expressionRejects source endByte input afterLeft leftReport leftTrace →
    expressionRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace
  successRejectDisjoint : ∀ {input rejected diagnostic trace},
    expressionRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, expressionTrace source endByte input value output events

def ExpressionTraceOutcomeExists
    (expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (expressionRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop :=
  ∀ input, (∃ value output trace, expressionTrace source endByte input value output trace) ∨
    (∃ rejected diagnostic trace, expressionRejects source endByte input rejected diagnostic trace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties
/-! Total, unique, order-preserving normalization of complete diagnostic traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem ParseDiagnosticCascadeFilters.output_unique
    {source : String} {lexical : List SourceSpan} {raw left right : List ParseDiagnostic}
    (leftFiltered : ParseDiagnosticCascadeFilters source lexical raw left)
    (rightFiltered : ParseDiagnosticCascadeFilters source lexical raw right) :
    left = right := by
  induction leftFiltered generalizing right with
  | nil => cases rightFiltered; rfl
  | keep retained tail ih =>
      cases rightFiltered with
      | keep _ rightTail => rw [ih rightTail]
      | drop suppressed _ => exact False.elim (retained suppressed)
  | drop suppressed tail ih =>
      cases rightFiltered with
      | keep retained _ => exact False.elim (retained suppressed)
      | drop _ rightTail => exact ih rightTail

theorem parseDiagnosticCascadeFilters_total (source : String)
    (lexical : List SourceSpan) (raw : List ParseDiagnostic) :
    ∃ kept, ParseDiagnosticCascadeFilters source lexical raw kept := by
  classical
  induction raw with
  | nil => exact ⟨[], .nil⟩
  | cons diagnostic raw ih =>
      rcases ih with ⟨kept, filtered⟩
      by_cases suppressed : ParseDiagnosticCascadeSuppresses source lexical diagnostic
      · exact ⟨kept, .drop suppressed filtered⟩
      · exact ⟨diagnostic :: kept, .keep suppressed filtered⟩

/-- A protected kind survives even if its source span matches a lexical error. -/
theorem parseDiagnosticCascadeFilters_protected_cons
    {source : String} {lexical : List SourceSpan} {diagnostic : ParseDiagnostic}
    {raw kept : List ParseDiagnostic}
    (protectedKind : ¬ LexicalCascadeCandidate diagnostic.kind)
    (tail : ParseDiagnosticCascadeFilters source lexical raw kept) :
    ParseDiagnosticCascadeFilters source lexical (diagnostic :: raw) (diagnostic :: kept) :=
  .keep (fun suppressed => protectedKind suppressed.1) tail

/-- Retained occurrences remain ordered, without inventing reports. -/
theorem ParseDiagnosticCascadeFilters.sublist
    {source : String} {lexical : List SourceSpan} {raw kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters source lexical raw kept) :
    kept.Sublist raw := by
  induction filtered with
  | nil => exact .slnil
  | keep _ _ ih => exact .cons_cons _ ih
  | drop _ _ ih => exact .cons _ ih

theorem parseDiagnosticCascadeFilters_nil_lexical (source : String)
    (raw : List ParseDiagnostic) : ParseDiagnosticCascadeFilters source [] raw raw := by
  induction raw with
  | nil => exact .nil
  | cons diagnostic raw ih =>
      exact .keep (by simp [ParseDiagnosticCascadeSuppresses, LexicalCascadeSuppresses]) ih

/-- Independent filtering composes without reordering the concatenated traces. -/
theorem ParseDiagnosticCascadeFilters.append
    {source : String} {lexical : List SourceSpan}
    {left right keptLeft keptRight : List ParseDiagnostic}
    (leading : ParseDiagnosticCascadeFilters source lexical left keptLeft)
    (trailing : ParseDiagnosticCascadeFilters source lexical right keptRight) :
    ParseDiagnosticCascadeFilters source lexical (left ++ right) (keptLeft ++ keptRight) := by
  induction leading with
  | nil => exact trailing
  | keep retained tail ih => exact .keep retained ih
  | drop suppressed tail ih => exact .drop suppressed ih

/-- An entirely protected trace survives regardless of lexical error locations. -/
theorem parseDiagnosticCascadeFilters_of_protected (source : String)
    (lexical : List SourceSpan) {trace : List ParseDiagnostic}
    (protectedKinds : ∀ diagnostic ∈ trace, ¬ LexicalCascadeCandidate diagnostic.kind) :
    ParseDiagnosticCascadeFilters source lexical trace trace := by
  induction trace with
  | nil => exact .nil
  | cons diagnostic trace ih =>
      exact parseDiagnosticCascadeFilters_protected_cons
        (protectedKinds diagnostic (by simp))
        (ih (fun member found => protectedKinds member (List.mem_cons_of_mem _ found)))

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeParseDiagnosticCascadeStabilityProperties
/-! Normalized diagnostic traces are stable under the same lexical context. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every retained report lacks an independent suppression witness. -/
theorem ParseDiagnosticCascadeFilters.retained_not_suppressed
    {source : String} {lexical : List SourceSpan} {raw kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters source lexical raw kept) :
    ∀ diagnostic ∈ kept, ¬ ParseDiagnosticCascadeSuppresses source lexical diagnostic := by
  induction filtered with
  | nil => simp
  | keep retained tail ih =>
      intro diagnostic member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact retained
      · exact ih diagnostic inTail
  | drop suppressed tail ih => exact ih

/-- A trace consisting entirely of retained reports normalizes to itself. -/
theorem parseDiagnosticCascadeFilters_of_retained (source : String)
    (lexical : List SourceSpan) {trace : List ParseDiagnostic}
    (retained : ∀ diagnostic ∈ trace,
      ¬ ParseDiagnosticCascadeSuppresses source lexical diagnostic) :
    ParseDiagnosticCascadeFilters source lexical trace trace := by
  induction trace with
  | nil => exact .nil
  | cons diagnostic trace ih =>
      exact .keep (retained diagnostic (by simp))
        (ih (fun member found => retained member (List.mem_cons_of_mem _ found)))

/-- Reapplying normalization cannot delete a previously retained occurrence. -/
theorem ParseDiagnosticCascadeFilters.stable
    {source : String} {lexical : List SourceSpan} {raw kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters source lexical raw kept) :
    ParseDiagnosticCascadeFilters source lexical kept kept :=
  parseDiagnosticCascadeFilters_of_retained source lexical filtered.retained_not_suppressed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraceOutcomeSpec
/-! Parser-independent exact diagnostic outcomes for arbitrary result types.
This bundle expresses uniqueness and disjointness, not existence or execution.
Expression laws are reusable without assuming token-carrier preservation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

structure TraceExactOutcomeSpec {α : Type}
    (traceParses : SourceId → Nat → Remainder → α →
      Remainder → List ParseDiagnostic → Prop)
    (traceRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop where
  successResultUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    traceParses source endByte input left afterLeft leftTrace →
    traceParses source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace
  rejectResultUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    traceRejects source endByte input afterLeft leftReport leftTrace →
    traceRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace
  successRejectDisjoint : ∀ {input rejected diagnostic trace},
    traceRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, traceParses source endByte input value output events

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ExpressionTraceExactOutcomeSpec.toTraceExactOutcomeSpec
    (expressions : ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte) :
    TraceExactOutcomeSpec expressionTrace expressionRejects source endByte where
  successResultUnique := expressions.successResultUnique
  rejectResultUnique := expressions.rejectResultUnique
  successRejectDisjoint := expressions.successRejectDisjoint

theorem TraceExactOutcomeSpec.toExpressionTraceExactOutcomeSpec
    (expressions : TraceExactOutcomeSpec expressionTrace expressionRejects source endByte) :
    ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte where
  successResultUnique := expressions.successResultUnique
  rejectResultUnique := expressions.rejectResultUnique
  successRejectDisjoint := expressions.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraceOutcomeAgreement
/-! Pairwise diagnostic outcome agreement between distinct child relations.
Neither side is assumed to be functional internally, inhabited, or executable. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

structure TraceOutcomeAgreement {α : Type}
    (leftParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (leftRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (rightParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop where
  successResultAgree : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    leftParses source endByte input left afterLeft leftTrace →
    rightParses source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace
  rejectResultAgree : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    leftRejects source endByte input afterLeft leftReport leftTrace →
    rightRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace
  successRejectDisjoint : ∀ {input value output events rejected report trace},
    leftParses source endByte input value output events →
    rightRejects source endByte input rejected report trace → False
  rejectSuccessDisjoint : ∀ {input rejected report trace value output events},
    leftRejects source endByte input rejected report trace →
    rightParses source endByte input value output events → False

variable {α : Type}
  {leftParses rightParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TraceOutcomeAgreement.symm
    (agreement : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement rightParses rightRejects leftParses leftRejects source endByte where
  successResultAgree left right := by
    rcases agreement.successResultAgree right left with ⟨value, remainder, events⟩
    exact ⟨value.symm, remainder.symm, events.symm⟩
  rejectResultAgree left right := by
    rcases agreement.rejectResultAgree right left with ⟨remainder, report, events⟩
    exact ⟨remainder.symm, report.symm, events.symm⟩
  successRejectDisjoint left right := agreement.rejectSuccessDisjoint right left
  rejectSuccessDisjoint left right := agreement.successRejectDisjoint right left

theorem TraceExactOutcomeSpec.toTraceOutcomeAgreement
    (exactness : TraceExactOutcomeSpec leftParses leftRejects source endByte) :
    TraceOutcomeAgreement leftParses leftRejects leftParses leftRejects source endByte where
  successResultAgree := exactness.successResultUnique
  rejectResultAgree := exactness.rejectResultUnique
  successRejectDisjoint parsed rejected := exactness.successRejectDisjoint rejected ⟨_, _, _, parsed⟩
  rejectSuccessDisjoint rejected parsed := exactness.successRejectDisjoint rejected ⟨_, _, _, parsed⟩

theorem TraceOutcomeAgreement.toTraceExactOutcomeSpec
    (agreement : TraceOutcomeAgreement leftParses leftRejects leftParses leftRejects source endByte) :
    TraceExactOutcomeSpec leftParses leftRejects source endByte where
  successResultUnique := agreement.successResultAgree
  rejectResultUnique := agreement.rejectResultAgree
  successRejectDisjoint rejected := by
    rintro ⟨_, _, _, parsed⟩
    exact agreement.rejectSuccessDisjoint rejected parsed

end Solcore.Syntax.DeclarativeGrammar
end
