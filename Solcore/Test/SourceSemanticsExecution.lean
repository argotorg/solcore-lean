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

/-- The form-indexed inversion view keeps both formation premises of a
generalized binding instead of retaining only its initializer typing. -/
theorem generalizedLetFormTypingRetainsFormation
    {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {binder : TypedBinder}
    {initializer : ExpressionId}
    (typing : SourceSemantics.Dynamic.StatementHasType.FormTyping
      source control context (.letDecl binder (some initializer)) final)
    (polymorphic : binder.scheme.quantified ≠ []) :
    LocalSchemeRequirementsWellFormed context binder ∧
      SchemeGeneralizesExcept context (localSchemeTemplateIds binder)
        binder.scheme := by
  cases typing with
  | letInitialized _ monomorphic _ =>
      exact (polymorphic monomorphic).elim
  | letInitializedGeneralized _ requirements_well_formed generalizes _ _ =>
      exact ⟨requirements_well_formed, generalizes⟩

/-- The statement dynamics allocates a canonical generalized direct lambda as
one principal descriptor, without evaluating it at a monomorphic type. -/
theorem generalizedStatementAllocatesDirectLambda
    {program : SourceSemantics.Program} {context final : SourceSemantics.Context}
    {evidence : SourceSemantics.Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : SourceSemantics.Dynamic.Environment}
    {before after : SourceSemantics.Dynamic.Heap} {statement : StatementId}
    {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {function : SourceSemantics.Dynamic.GeneralizedClosure}
    {location : SourceSemantics.Dynamic.Location}
    (contains : ContainsStatement source statement node)
    (form_eq : node.form = .letDecl binder (some initializer))
    (captures : SourceSemantics.Dynamic.GeneralizedClosureCaptures context source
      environment binder initializer function)
    (polymorphic : binder.scheme.quantified ≠ [])
    (extension : BinderExtends source.owner context binder final)
    (allocate : SourceSemantics.Dynamic.Heap.AllocatesGeneralized before function
      location after) :
    SourceSemantics.Dynamic.StatementExecutes program context evidence source
      environment before statement final
      (.fallthrough ((binder.id, location) :: environment)) after := by
  exact .letInitializedGeneralized contains form_eq captures polymorphic extension
    allocate

/-- The equivalent generalized `for` header rule uses the same descriptor
allocation and lexical-context extension. -/
theorem generalizedForItemAllocatesDirectLambda
    {program : SourceSemantics.Program} {context final : SourceSemantics.Context}
    {evidence : SourceSemantics.Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : SourceSemantics.Dynamic.Environment}
    {before after : SourceSemantics.Dynamic.Heap} {binder : TypedBinder}
    {initializer : ExpressionId}
    {function : SourceSemantics.Dynamic.GeneralizedClosure}
    {location : SourceSemantics.Dynamic.Location}
    (captures : SourceSemantics.Dynamic.GeneralizedClosureCaptures context source
      environment binder initializer function)
    (polymorphic : binder.scheme.quantified ≠ [])
    (extension : BinderExtends source.owner context binder final)
    (allocate : SourceSemantics.Dynamic.Heap.AllocatesGeneralized before function
      location after) :
    SourceSemantics.Dynamic.ForItemExecutes program context evidence source
      environment before (.letDecl binder (some initializer)) final
      ((binder.id, location) :: environment) after := by
  exact .letInitializedGeneralized captures polymorphic extension allocate

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
