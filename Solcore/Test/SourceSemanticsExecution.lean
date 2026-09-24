import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.Staging.Materialization

/-!
Focused proof consumers for the declarative source execution boundary.

These examples deliberately construct small semantic witnesses rather than
calling an executable frontend.  They pin the public preservation and
correspondence APIs used by ADR-0378.
-/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsExecution

open Frontend
open Frontend.SourceInference
open SourceSemantics
open TypeSystem

/-- A concrete product materialization has exactly one frontend staged-value
representation. -/
theorem productMaterializationHasUniqueFrontend :
    ∃ frontend,
      SourceSemantics.Staging.FrontendValueRepresents
        (.product (.bool true) (.word Core.Word.zero)) frontend ∧
      ∀ other,
        SourceSemantics.Staging.FrontendValueRepresents
          (.product (.bool true) (.word Core.Word.zero)) other →
        other = frontend := by
  have materializes : SourceSemantics.Staging.Materializes
      (.product (.bool true) (.word Core.Word.zero))
      (.product (.bool true) (.word Core.Word.zero)) :=
    .product (.bool true) (.word Core.Word.zero)
  exact materializes.frontend_exists_unique

private def mutationBefore : SourceSemantics.Dynamic.Heap := {
  cells := [{ type := .bool, value := some (.bool false) }]
}

private def mutationAfter : SourceSemantics.Dynamic.Heap := {
  cells := [{ type := .bool, value := some (.bool true) }]
}

private def mutationPlace : SourceSemantics.Dynamic.ResolvedPlace := {
  location := ⟨0⟩
  rootType := .bool
  valueType := .bool
  projections := []
  selected := some (.bool false)
}

private theorem mutationBeforeWellTyped (context : SourceSemantics.Context) :
    SourceSemantics.Dynamic.HeapWellTyped context mutationBefore := by
  intro cell member
  simp only [mutationBefore, List.mem_singleton] at member
  subst cell
  exact ⟨.some (.bool false), .none .bool⟩

private theorem concretePlaceWrite :
    SourceSemantics.Dynamic.ResolvedPlaceWrites
      (SourceSemantics.Dynamic.ReplacesWith (.bool true))
      mutationBefore mutationPlace (.bool true) mutationAfter := by
  apply SourceSemantics.Dynamic.ResolvedPlaceWrites.intro
  · exact .intro .head
  · rfl
  · exact .initialized
  · exact .leaf (.intro _)
  · exact .intro (.intro .head) .head

/-- Writing a concrete Boolean place preserves deep heap typing. -/
theorem concretePlaceWritePreservesHeapTyping
    (context : SourceSemantics.Context) :
    SourceSemantics.Dynamic.HeapWellTyped context mutationAfter := by
  apply SourceSemantics.Dynamic.ResolvedPlaceWrites.preservesHeapTyping
      (mutationBeforeWellTyped context)
      (place := mutationPlace) (updatedRoot := .bool true)
  · exact .bool true
  · exact concretePlaceWrite

private def patternSourceId : Syntax.SourceId := {
  origin := .main
  path := "source_semantics_execution.sol"
}

private def patternSpan : Syntax.SourceSpan := {
  source := patternSourceId
  startByte := 0
  endByte := 0
}

private def wildcardPattern : TypedMatchPattern := {
  source := .wildcard patternSpan patternSpan
  type := .bool
  resolution := .wildcard
  requirements := []
}

private theorem wildcardPatternHasType (context : SourceSemantics.Context) :
    TypedMatchPatternHasType context wildcardPattern .bool [] 0 := by
  refine {
    type_eq := rfl
    source_represents := ?_
    resolution_type := ?_
    binders_distinct := ?_
  }
  · exact .wildcard
  · exact .wildcard
  · constructor <;> simp

private theorem wildcardPatternMatches (context : SourceSemantics.Context) :
    SourceSemantics.Dynamic.PatternMatches context wildcardPattern
      (.bool true) [] := by
  exact .intro .wildcard .wildcard

/-- A successful root-pattern match produces values at precisely the static
binder types and in precisely the static binder order. -/
theorem wildcardMatchPreservesBindings
    (context : SourceSemantics.Context) (heap : SourceSemantics.Dynamic.Heap) :
    SourceSemantics.Dynamic.BindingValuesHaveTypes context heap [] ∧
      (([] : List (TypedBinder × SourceSemantics.Dynamic.Value)).map Prod.fst) =
        ([] : List TypedBinder) := by
  exact SourceSemantics.Dynamic.PatternMatches.preserves
    (wildcardPatternHasType context) (.bool true)
    (wildcardPatternMatches context)

/-- Rigid generic substitution closes a valid semantic evidence tree without
rerunning trait search. -/
theorem assumedEvidenceClosedUnderSubstitution
    (substitution : ParameterSubstitution) (goal : ProgramPredicate) :
    EvidenceValid
      ([goal].map (ProgramPredicate.applyParameters substitution))
      ([] : List ProgramImplRule)
      (ProgramPredicate.applyParameters substitution goal)
      (StructuralSubstitution.applyTraitEvidence substitution
        (.assumption goal)) := by
  have valid : EvidenceValid [goal] [] goal (.assumption goal) :=
    .assumption (by simp)
  exact StructuralSubstitution.EvidenceValid.applyParameters substitution valid

end Solcore.Test.SourceSemanticsExecution
