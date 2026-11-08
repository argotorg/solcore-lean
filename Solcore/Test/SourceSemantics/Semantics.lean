import Solcore.SourceSemantics.Dynamic.Typing
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.Staging.Materialization
import Solcore.SourceSemantics
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure
import Solcore.SourceSemantics.Dynamic.Heap
import Solcore.SourceSemantics.Dynamic.Evidence
import Solcore.SourceSemantics.Dynamic.Program

/-!
# Source semantics tests

Whole-program admission and execution in the source semantics: captures, faults, generalized closures
and local schemes.
-/

section
-- leanmerge: from Solcore.Test.SourceSemanticsCaptureCopies
/-! The copies a closure makes of a captured environment, computed. A binding
whose identifier the closure's source copies (`CaptureBinders.copiedBinder?`)
gets a fresh cell at the end of the heap holding a copy of its cell; every
other binding keeps its location. When every binding holds a cell this is the
source semantics' `EnvironmentCopies`, so a hand-built trace can state its exact
heap over the copies made by a generalized `let` and by each closure call. -/
set_option autoImplicit false
namespace Tests.SourceSemanticsCaptureCopies
open Solcore Frontend SourceInference SourceSemantics

/-- Every binding of `environment` holds a cell of `heap`. -/
def Readable (heap : Dynamic.Heap) (environment : Dynamic.Environment) : Prop :=
  ∀ binding ∈ environment, ∃ cell, Dynamic.Heap.Reads heap binding.2 cell

/-- The cell copied for one binding: its cell, when the source copies the
identifier and the location holds a cell. -/
def copiedCell? (source : TypedSource) (id : Resolved.LocalId) (heap : Dynamic.Heap)
    (location : Dynamic.Location) : Option Dynamic.Cell :=
  if (CaptureBinders.copiedBinder? source id).isSome then heap.cells[location.index]? else none

/-- The copies of `environment` made from `heap`, most recent binding first,
and the heap after them. -/
def copies (source : TypedSource) : Dynamic.Environment → Dynamic.Heap → Dynamic.Environment × Dynamic.Heap
  | [], heap => ([], heap)
  | (id, location) :: rest, heap =>
    match copiedCell? source id heap location with
    | some cell =>
      ((id, ⟨heap.cells.length⟩) :: (copies source rest ⟨heap.cells ++ [cell]⟩).1,
        (copies source rest ⟨heap.cells ++ [cell]⟩).2)
    | none => ((id, location) :: (copies source rest heap).1, (copies source rest heap).2)

theorem cellAt_iff : ∀ {cells : List Dynamic.Cell} {index : Nat} {cell : Dynamic.Cell},
    Dynamic.Heap.CellAt cells index cell ↔ cells[index]? = some cell
  | [], _, _ => by
    constructor
    · intro selected; cases selected
    · intro found; simp at found
  | _ :: _, 0, _ => by
    constructor
    · intro selected; cases selected; rfl
    · intro found
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact .head
  | _ :: _, _ + 1, _ => by
    constructor
    · intro selected
      cases selected with
      | tail rest => simpa only [List.getElem?_cons_succ] using cellAt_iff.mp rest
    · intro found
      exact .tail (cellAt_iff.mpr (by simpa only [List.getElem?_cons_succ] using found))

theorem reads_iff {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell} :
    Dynamic.Heap.Reads heap location cell ↔ heap.cells[location.index]? = some cell :=
  ⟨fun | .intro selected => cellAt_iff.mp selected, fun found => .intro (cellAt_iff.mpr found)⟩

namespace Readable

theorem tail {heap : Dynamic.Heap} {binding : Resolved.LocalId × Dynamic.Location}
    {environment : Dynamic.Environment} (readable : Readable heap (binding :: environment)) :
    Readable heap environment :=
  fun other member => readable other (List.mem_cons_of_mem _ member)

theorem mono {before after : Dynamic.Heap} {environment : Dynamic.Environment}
    (readable : Readable before environment) (extension : Dynamic.HeapMetadataExtend before after) :
    Readable after environment := by
  intro binding member
  obtain ⟨cell, read⟩ := readable binding member
  obtain ⟨updated, updatedRead, _, _⟩ := extension _ _ read
  exact ⟨updated, updatedRead⟩

/-- A lexically agreeing environment holds a cell for every binding. -/
theorem of_agrees {heap : Dynamic.Heap} {scope : Resolved.LocalScope TypeSystem.Scheme}
    {environment : Dynamic.Environment} (agrees : Dynamic.EnvironmentAgrees heap scope environment) :
    Readable heap environment := by
  induction agrees with
  | nil => intro _ member; cases member
  | cons read _ _ _ ih =>
    intro binding member
    rcases List.mem_cons.mp member with same | rest
    · subst same; exact ⟨_, read⟩
    · exact ih binding rest

/-- The copies hold a cell for every binding: a copy holds its fresh cell and a
shared binding keeps its cell. -/
theorem of_copies {source : TypedSource} {environment copied : Dynamic.Environment}
    {before after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment before copied after)
    (readable : Readable before environment) : Readable after copied := by
  induction copy with
  | nil => exact readable
  | shared _ tail ih =>
    intro binding member
    rcases List.mem_cons.mp member with same | rest
    · subst same
      obtain ⟨cell, read⟩ := readable _ List.mem_cons_self
      exact ⟨cell, tail.preserves_read read⟩
    · exact ih readable.tail binding rest
  | copied _ _ allocate tail ih =>
    intro binding member
    rcases List.mem_cons.mp member with same | rest
    · subst same
      exact ⟨_, tail.preserves_read allocate.reads_new⟩
    · exact ih (readable.tail.mono (Dynamic.HeapMetadataExtend.of_copy allocate)) binding rest

end Readable

/-- Copying only appends cells. -/
theorem appends_of_copies {source : TypedSource} {environment copied : Dynamic.Environment}
    {before after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment before copied after) :
    ∃ added, after.cells = before.cells ++ added := by
  induction copy with
  | nil => exact ⟨[], by simp⟩
  | shared _ _ ih => exact ih
  | @copied _ _ _ _ cell _ _ _ _ _ _ _ allocate _ ih =>
    obtain ⟨added, same⟩ := ih
    cases allocate
    exact ⟨cell :: added, by simp [same]⟩

/-- A lookup in the copies reads an exact copy of the cell the original lookup
reads: copying never changes what a captured binding holds. -/
theorem copy_reads {source : TypedSource} {environment copied : Dynamic.Environment}
    {before after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment before copied after)
    {id : Resolved.LocalId} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment id location) (read : Dynamic.Heap.Reads before location cell) :
    ∃ copyLocation, Dynamic.Environment.LooksUp copied id copyLocation ∧ Dynamic.Heap.Reads after copyLocation cell := by
  induction copy generalizing location with
  | nil => cases lookup
  | shared _ tail ih =>
    cases lookup with
    | head => exact ⟨_, .head, tail.preserves_read read⟩
    | tail different rest =>
      obtain ⟨copyLocation, found, copyRead⟩ := ih rest read
      exact ⟨copyLocation, .tail different found, copyRead⟩
  | copied _ original allocate tail ih =>
    cases lookup with
    | head =>
      have same := original.functional read
      subst same
      exact ⟨_, .head, tail.preserves_read allocate.reads_new⟩
    | tail different rest =>
      obtain ⟨copyLocation, found, copyRead⟩ := ih rest (allocate.preserves_read read)
      exact ⟨copyLocation, .tail different found, copyRead⟩

theorem copies_some {source : TypedSource} {id : Resolved.LocalId} {location : Dynamic.Location}
    {rest : Dynamic.Environment} {heap : Dynamic.Heap} {cell : Dynamic.Cell}
    (found : copiedCell? source id heap location = some cell) :
    copies source ((id, location) :: rest) heap =
      ((id, ⟨heap.cells.length⟩) :: (copies source rest ⟨heap.cells ++ [cell]⟩).1,
        (copies source rest ⟨heap.cells ++ [cell]⟩).2) := by
  rw [copies, found]

theorem copies_none {source : TypedSource} {id : Resolved.LocalId} {location : Dynamic.Location}
    {rest : Dynamic.Environment} {heap : Dynamic.Heap}
    (absent : copiedCell? source id heap location = none) :
    copies source ((id, location) :: rest) heap =
      ((id, location) :: (copies source rest heap).1, (copies source rest heap).2) := by
  rw [copies, absent]

/-- When every binding holds a cell, the computed copies are the source
semantics' copies. -/
theorem copies_spec (source : TypedSource) : ∀ {environment : Dynamic.Environment} {heap : Dynamic.Heap},
    Readable heap environment →
      Dynamic.EnvironmentCopies source environment heap (copies source environment heap).1
        (copies source environment heap).2
  | [], heap, _ => .nil heap
  | (id, location) :: rest, heap, readable => by
    cases decision : CaptureBinders.copiedBinder? source id with
    | none =>
      have absent : copiedCell? source id heap location = none := by simp [copiedCell?, decision]
      rw [copies_none absent]
      exact .shared decision (copies_spec source readable.tail)
    | some binder =>
      obtain ⟨cell, read⟩ := readable (id, location) List.mem_cons_self
      have found : copiedCell? source id heap location = some cell := by
        simpa [copiedCell?, decision] using reads_iff.mp read
      rw [copies_some found]
      have allocate : Dynamic.Heap.AllocatesCopy heap cell ⟨heap.cells.length⟩ ⟨heap.cells ++ [cell]⟩ := .append
      exact .copied decision read allocate
        (copies_spec source (readable.tail.mono (Dynamic.HeapMetadataExtend.of_copy allocate)))

/-- Copying only appends cells. -/
theorem copies_appends (source : TypedSource) : ∀ (environment : Dynamic.Environment) (heap : Dynamic.Heap),
    ∃ added, (copies source environment heap).2.cells = heap.cells ++ added
  | [], heap => ⟨[], by simp [copies]⟩
  | (id, location) :: rest, heap => by
    cases found : copiedCell? source id heap location with
    | none =>
      rw [copies_none found]
      exact copies_appends source rest heap
    | some cell =>
      rw [copies_some found]
      obtain ⟨added, same⟩ := copies_appends source rest ⟨heap.cells ++ [cell]⟩
      exact ⟨cell :: added, by simp [same]⟩

/-- A substitution instance of a source copies the same bindings. -/
theorem copiedCell?_applySubstitution (substitution : TypeSystem.Substitution) (source : TypedSource)
    (id : Resolved.LocalId) (heap : Dynamic.Heap) (location : Dynamic.Location) :
    copiedCell? (source.applySubstitution substitution) id heap location = copiedCell? source id heap location := by
  simp only [copiedCell?, CaptureBinders.copied_isSome_applySubstitution]

theorem copies_applySubstitution (substitution : TypeSystem.Substitution) (source : TypedSource) :
    ∀ (environment : Dynamic.Environment) (heap : Dynamic.Heap),
      copies (source.applySubstitution substitution) environment heap = copies source environment heap
  | [], _ => rfl
  | (id, location) :: rest, heap => by
    cases found : copiedCell? source id heap location with
    | none =>
      rw [copies_none found, copies_none ((copiedCell?_applySubstitution substitution source id heap location).trans found),
        copies_applySubstitution substitution source rest heap]
    | some cell =>
      rw [copies_some found, copies_some ((copiedCell?_applySubstitution substitution source id heap location).trans found),
        copies_applySubstitution substitution source rest]

/-- The copies a call of an instantiated closure makes over a substituted source
are those of the original source. -/
theorem copies_spec_applySubstitution (substitution : TypeSystem.Substitution) (source : TypedSource)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} (readable : Readable heap environment) :
    Dynamic.EnvironmentCopies (source.applySubstitution substitution) environment heap
      (copies source environment heap).1 (copies source environment heap).2 := by
  rw [← copies_applySubstitution substitution source]
  exact copies_spec _ readable

end Tests.SourceSemanticsCaptureCopies
end

section
-- leanmerge: from Solcore.Test.SourceSemanticsExecution
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
one principal descriptor over a copy of its environment, without evaluating it
at a monomorphic type. -/
theorem generalizedStatementAllocatesDirectLambda
    {program : SourceSemantics.Program} {context final : SourceSemantics.Context}
    {evidence : SourceSemantics.Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment captured : SourceSemantics.Dynamic.Environment}
    {before middle after : SourceSemantics.Dynamic.Heap} {statement : StatementId}
    {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {function : SourceSemantics.Dynamic.GeneralizedClosure}
    {location : SourceSemantics.Dynamic.Location}
    (contains : ContainsStatement source statement node)
    (form_eq : node.form = .letDecl binder (some initializer))
    (snapshot : SourceSemantics.Dynamic.EnvironmentCopies source environment before captured middle)
    (captures : SourceSemantics.Dynamic.GeneralizedClosureCaptures context source
      captured binder initializer function)
    (polymorphic : binder.scheme.quantified ≠ [])
    (extension : BinderExtends source.owner context binder final)
    (allocate : SourceSemantics.Dynamic.Heap.AllocatesGeneralized middle function
      location after) :
    SourceSemantics.Dynamic.StatementExecutes program context evidence source
      environment before statement final
      (.fallthrough ((binder.id, location) :: environment)) after := by
  exact .letInitializedGeneralized contains form_eq snapshot captures polymorphic extension
    allocate

/-- The equivalent generalized `for` header rule uses the same descriptor
allocation and lexical-context extension. -/
theorem generalizedForItemAllocatesDirectLambda
    {program : SourceSemantics.Program} {context final : SourceSemantics.Context}
    {evidence : SourceSemantics.Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment captured : SourceSemantics.Dynamic.Environment}
    {before middle after : SourceSemantics.Dynamic.Heap} {binder : TypedBinder}
    {initializer : ExpressionId}
    {function : SourceSemantics.Dynamic.GeneralizedClosure}
    {location : SourceSemantics.Dynamic.Location}
    (snapshot : SourceSemantics.Dynamic.EnvironmentCopies source environment before captured middle)
    (captures : SourceSemantics.Dynamic.GeneralizedClosureCaptures context source
      captured binder initializer function)
    (polymorphic : binder.scheme.quantified ≠ [])
    (extension : BinderExtends source.owner context binder final)
    (allocate : SourceSemantics.Dynamic.Heap.AllocatesGeneralized middle function
      location after) :
    SourceSemantics.Dynamic.ForItemExecutes program context evidence source
      environment before (.letDecl binder (some initializer)) final
      ((binder.id, location) :: environment) after := by
  exact .letInitializedGeneralized snapshot captures polymorphic extension allocate

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
end

section
-- leanmerge: from Solcore.Test.SourceSemanticsFault
set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsFault

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic

/-- A structurally absent occurrence produces the public fault outcome. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (missing : ExpressionMissing source id) :
    ExpressionEvaluatesOutcome program context evidence source environment heap id
      (.fault (.missingExpression id)) heap :=
  .fault (.missing missing)

/-- An empty lexical frame gives a positive unbound-local derivation even
when the occurrence owns a nonempty generalized requirement segment. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (heap : Heap) (binder : Resolved.LocalId) (name : String)
    (owned : RequirementId) :
    ExpressionFormFaults program context evidence source [] heap
      (.reference name (.local binder)) [owned] [] (.unboundLocal binder) heap := by
  exact .localUnbound (owned := [owned]) rfl (.nil binder)

/-- A location past the empty heap is dangling without negating heap reads. -/
example (location : Location) : Heap.Dangling ⟨[]⟩ location := by
  exact .nil location.index

/-- A nonempty generalized requirement segment does not hide a dangling
local location. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (binder : Resolved.LocalId) (name : String) (owned : RequirementId) :
    ExpressionFormFaults program context evidence source
      [(binder, ⟨0⟩)] ⟨[]⟩
      (.reference name (.local binder)) [owned] []
      (.danglingLocation ⟨0⟩) ⟨[]⟩ := by
  exact .localDangling (owned := [owned]) rfl .head (.nil 0)

/-- A generalized local reports the first failed owned requirement after its
runtime substitution has been selected. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (node : ExpressionNode) (name : String) (binder : Resolved.LocalId)
    (owned : List RequirementId) (location : Location) (cell : Cell)
    (function : GeneralizedClosure) (substitution : TypeSystem.Substitution)
    (failed : RequirementId)
    (contains : ContainsExpression source id node)
    (form_eq : node.form = .reference name (.local binder))
    (layout : OrdinaryRequirementLayout node.requirements node.coercions owned)
    (lookup : Environment.LooksUp environment binder location)
    (read : Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function)
    (context_fields : RuntimeContextFields function.definitionContext context)
    (selection : LocalSchemeRuntimeSelection context function.binder
      node.rawType owned substitution)
    (fault : RequirementsFault context evidence owned
      (instantiateLocalSchemePredicates substitution function.binder) failed) :
    ExpressionFaults program context evidence source environment heap id
      (.unsatisfiedRequirement failed) heap := by
  exact .generalizedLocalRequirement contains form_eq layout lookup read
    descriptor context_fields selection fault

/-- Once generalized-local instantiation succeeds, its result coercion path
can still expose a concrete semantic fault. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (before after : Heap) (id : ExpressionId)
    (node : ExpressionNode) (name : String) (binder : Resolved.LocalId)
    (owned : List RequirementId) (location : Location) (cell : Cell)
    (function : GeneralizedClosure) (substitution : TypeSystem.Substitution)
    (produced : EvidenceEnvironment) (reason : SemanticFault)
    (contains : ContainsExpression source id node)
    (form_eq : node.form = .reference name (.local binder))
    (layout : OrdinaryRequirementLayout node.requirements node.coercions owned)
    (lookup : Environment.LooksUp environment binder location)
    (read : Heap.Reads before location cell)
    (descriptor : cell.generalized = some function)
    (context_fields : RuntimeContextFields function.definitionContext context)
    (instantiation : LocalSchemeRuntimeInstantiation context evidence
      function.binder node.rawType owned substitution produced)
    (fault : CoercionPathFaults program context evidence before node.coercions
      (.closure (function.instantiate substitution
        (produced ++ evidence.applySubstitution substitution))) reason after) :
    ExpressionFaults program context evidence source environment before id
      reason after := by
  exact .generalizedLocalCoercion contains form_eq layout lookup read descriptor
    context_fields instantiation fault

/-- Primitive operand faults name the exact source operator. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (heap : Heap) :
    UnaryOperationFaults program context evidence heap .logicalNot [] .unit
      (.invalidUnaryOperand .logicalNot) heap := by
  apply UnaryOperationFaults.primitive
  exact .logicalNot (by simp [BooleanValue])

/-- Non-callable values fault before any body can be postulated. -/
example (program : Program) (context : SourceSemantics.Context)
    (caller invocation : EvidenceEnvironment) (heap : Heap) :
    CallableFaults program context caller invocation heap (.bool true) []
      .notCallable heap := by
  exact .notCallable (by simp [CallableValue])

/-- Builtins expose their retained parameter count in arity faults. -/
example (program : Program) (context : SourceSemantics.Context)
    (caller invocation : EvidenceEnvironment) (heap : Heap) :
    CallableFaults program context caller invocation heap
      (.builtin ⟨.integerAdd⟩) []
      (.argumentArityMismatch 2 0) heap := by
  apply CallableFaults.builtinArity
  decide

/-- Correct-arity builtin calls diagnose the first wrong argument type. -/
example (program : Program) (context : SourceSemantics.Context)
    (caller invocation : EvidenceEnvironment) (heap : Heap) :
    CallableFaults program context caller invocation heap
      (.builtin ⟨.integerAdd⟩) [.bool true, .integer 0]
      (.typeMismatch .integer .bool) heap := by
  apply CallableFaults.builtinArgumentType
  · decide
  · apply ValuesFirstTypeMismatch.head (.bool true)
    decide

/-- Missing retained evidence names the exact unsatisfied requirement. -/
example (context : SourceSemantics.Context) (evidence : EvidenceEnvironment)
    (id : RequirementId) (missing : RequirementMissing context id) :
    RequirementUnavailable context evidence id :=
  .missing missing

/-- Closing retained evidence successfully rules out a closure fault for the
same open evidence tree. -/
example (environment : EvidenceEnvironment)
    (openEvidence closedEvidence : TraitEvidence)
    (closes : EvidenceCloses environment openEvidence closedEvidence)
    (fault : EvidenceClosureFaults environment openEvidence) : False :=
  closes.excludes_fault fault

/-- Every finite retained evidence tree has a constructive runtime outcome:
either all assumptions close or a missing assumption is identified. -/
example (environment : EvidenceEnvironment) (openEvidence : TraitEvidence) :
    (∃ closedEvidence,
      EvidenceCloses environment openEvidence closedEvidence) ∨
      EvidenceClosureFaults environment openEvidence :=
  EvidenceCloses.exists_or_fault environment openEvidence

/-- A dictionary covering the static context materializes a closed, valid
evidence tree from every valid open tree. -/
example (context : SourceSemantics.Context)
    (environment : EvidenceEnvironment) (goal : ProgramPredicate)
    (openEvidence : TraitEvidence)
    (covers : EvidenceEnvironment.Covers context environment)
    (valid : EvidenceValid context.assumptions
      context.signatures.resolutionRules goal openEvidence) :
    ∃ closedEvidence,
      EvidenceCloses environment openEvidence closedEvidence ∧
        EvidenceValid [] context.signatures.resolutionRules goal
          closedEvidence :=
  SourceSemantics.Dynamic.EvidenceValid.close_of_covers covers valid

/-- Under the static requirement-identity invariant, successful materialization
and runtime unavailability are mutually exclusive. -/
example (context : SourceSemantics.Context)
    (environment : EvidenceEnvironment) (id : RequirementId)
    (predicate : ProgramPredicate) (closedEvidence : TraitEvidence)
    (unique : RequirementIdsUnique context)
    (produces : RequirementProducesEvidence context environment id predicate
      closedEvidence)
    (unavailable : RequirementUnavailable context environment id) : False :=
  produces.excludes_unavailable unique unavailable

/-- A successfully materialized requirement spine cannot also report a first
fault for the same ordered identity/predicate inputs. -/
example (context : SourceSemantics.Context)
    (caller produced : EvidenceEnvironment)
    (requirements : List RequirementId)
    (predicates : List ProgramPredicate) (failed : RequirementId)
    (unique : RequirementIdsUnique context)
    (produces : RequirementsProduceEnvironment context caller requirements
      predicates produced)
    (fault : RequirementsFault context caller requirements predicates failed) :
    False :=
  produces.excludes_fault unique fault

/-- A well-formed requirement ledger and valid caller dictionary classify each
stable identity as either materializable or concretely unavailable. -/
example (context : SourceSemantics.Context)
    (environment : EvidenceEnvironment) (id : RequirementId)
    (ledger : RequirementLedgerWellFormed context)
    (valid : environment.Valid context.signatures.resolutionRules) :
    (∃ predicate evidence,
      RequirementProducesEvidence context environment id predicate evidence) ∨
      RequirementUnavailable context environment id :=
  requirement_produces_or_unavailable ledger valid id

/-- Static requirement sequence validity plus a covering dictionary is enough
to materialize the exact ordered runtime evidence environment. -/
example (context : SourceSemantics.Context)
    (environment : EvidenceEnvironment)
    (requirements : List RequirementId)
    (predicates : List ProgramPredicate)
    (covers : environment.Covers context)
    (proves : RequirementSequenceProves context requirements predicates) :
    ∃ produced,
      RequirementsProduceEnvironment context environment requirements
        predicates produced :=
  SourceSemantics.Dynamic.RequirementSequenceProves.produces_of_covers
    covers proves

/-- A malformed pattern is an explicit metadata fault, not a failed match. -/
example (context : SourceSemantics.Context) (value : Value)
    (arm : TypedMatchCase) (rest : List TypedMatchCase)
    (malformed : PatternMalformed context arm.pattern) :
    MatchCasesPatternFault context value (arm :: rest) :=
  .head malformed

/-- The closed Core-representable residualization boundary is the sole
staging-fault introduction rule. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (before after : Heap) (id : ExpressionId)
    (value : Int)
    (evaluates : ExpressionEvaluates program context evidence source environment
      before id (.integer value) after) :
    RuntimeExpressionEvaluatesOutcome program context evidence source environment
      before id (.fault .stagingViolation) after :=
  .stagingViolation evaluates (.integer value)

/-- Grouping preserves the exact child fault and its heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (inner : ExpressionId)
    (missing : ExpressionMissing source inner) :
    ExpressionFormFaults program context evidence source environment heap
      (.group inner) [] [] (.missingExpression inner) heap := by
  exact ExpressionFormFaults.group (coercions := []) rfl (.missing missing)

/-- Statement faults are reified as `ControlOutcome.fault`. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : StatementId)
    (missing : StatementMissing source id) :
    StatementExecutesOutcome program context evidence source environment heap id
      context (.fault (.missingStatement id)) heap :=
  .fault (.missing missing)

/-- A generalized statement binder reaches the explicit runtime boundary
before its initializer is evaluated. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : StatementId)
    (node : StatementNode) (binder : TypedBinder)
    (initializer : Option ExpressionId)
    (contains : ContainsStatement source id node)
    (form_eq : node.form = .letDecl binder initializer)
    (polymorphic : binder.scheme.quantified ≠ [])
    (unsupported : GeneralizedInitializerUnsupported source binder initializer) :
    StatementFaults program context evidence source environment heap id
      (.unsupportedPolymorphicBinder binder.id) heap := by
  exact .polymorphicLet contains form_eq polymorphic unsupported

/-- The same explicit boundary applies to generalized binders in a `for`
header. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (binder : TypedBinder)
    (initializer : Option ExpressionId)
    (polymorphic : binder.scheme.quantified ≠ [])
    (unsupported : GeneralizedInitializerUnsupported source binder initializer) :
    ForItemFaults program context evidence source environment heap
      (.letDecl binder initializer)
      (.unsupportedPolymorphicBinder binder.id) heap := by
  exact .polymorphicLet polymorphic unsupported

/-- A `for`-header vector stops at its first faulting item and preserves that
item's exact fault and heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (missing : ExpressionMissing source id) :
    ForItemsFault program context evidence source environment heap
      [.expression id] context (.missingExpression id) heap := by
  exact .head (.expression (.missing missing))

/-- Loop-condition failure is observable before any body iteration. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (missing : ExpressionMissing source id) :
    WhileFaults program context evidence source environment heap id []
      (.missingExpression id) heap := by
  exact .condition (.missing missing)

end Solcore.Test.SourceSemanticsFault
end

section
-- leanmerge: from Solcore.Test.SourceSemanticsGeneralizedClosure
/-! Focused checks for proof-facing generalized-closure materialization. -/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsGeneralizedClosure

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic
open TypeSystem

private def predicate (metavariable : TypeVarId) : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable metavariable)

private def requirement (id : RequirementId) (metavariable : TypeVarId) :
    LocalSchemeRequirement := {
  templateRequirement := id
  predicate := predicate metavariable
}

private def generalizedBinder (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) (requirementId : RequirementId) : TypedBinder := {
  id := ⟨owner, 20⟩
  name := "generalized"
  scheme := {
    quantified := [metavariable]
    body := .function (.variable metavariable) (.variable metavariable)
  }
  schemeRequirements := [requirement requirementId metavariable]
}

private def lambdaParameter (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) : TypedBinder := {
  id := ⟨owner, 21⟩
  name := "argument"
  scheme := .mono (.variable metavariable)
}

private def protectedBinder (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) : TypedBinder := {
  id := ⟨owner, 22⟩
  name := "protected"
  scheme := {
    quantified := [metavariable]
    body := .variable metavariable
  }
}

private def principalSource (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) : TypedSource := {
  owner
  inputs := [lambdaParameter owner metavariable,
    protectedBinder owner metavariable]
  roots := []
  nodes := []
}

private def definitionContext (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (metavariable : TypeVarId)
    (protectedRequirement : RequirementId) : SourceSemantics.Context :=
  ((Context.ofSignatures signatures).withAssumptions
      [predicate metavariable]).withLocal
    (protectedBinder owner metavariable).id
    (protectedBinder owner metavariable).scheme
    [requirement protectedRequirement metavariable]

private def principalClosure (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (metavariable : TypeVarId)
    (initializer : ExpressionId) (body : StatementId)
    (templateRequirement protectedRequirement : RequirementId) :
    GeneralizedClosure := {
  binder := generalizedBinder owner metavariable templateRequirement
  initializer
  parameters := [lambdaParameter owner metavariable]
  resultType := .variable metavariable
  body := [body]
  source := principalSource owner metavariable
  captured := [((protectedBinder owner metavariable).id, ⟨7⟩)]
  definitionContext := definitionContext signatures owner metavariable
    protectedRequirement
}

private def captureSourceId : Syntax.SourceId := {
  origin := .main
  path := "generalized_closure_capture.sol"
}

private def captureSpan : Syntax.SourceSpan := {
  source := captureSourceId
  startByte := 0
  endByte := 0
}

private def captureInitializer (owner : Resolved.DeclarationId) : ExpressionId :=
  ⟨⟨owner, 30⟩⟩

private def captureNode (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) (body : StatementId) : ExpressionNode := {
  id := captureInitializer owner
  span := captureSpan
  type := .function (.variable metavariable) (.variable metavariable)
  form := .lambda [lambdaParameter owner metavariable]
    (.variable metavariable) [body]
}

private def captureSource (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) (body : StatementId) : TypedSource := {
  owner
  inputs := []
  roots := [.expression (captureInitializer owner)]
  nodes := [.expression (captureNode owner metavariable body)]
}

/-- A concrete direct-lambda occurrence constructs exactly the canonical
principal descriptor retained by `GeneralizedClosureCaptures`. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) (body : StatementId)
    (templateRequirement : RequirementId) :
    GeneralizedClosureCaptures (Context.ofSignatures signatures)
      (captureSource owner metavariable body) []
      (generalizedBinder owner metavariable templateRequirement)
      (captureInitializer owner)
      (GeneralizedClosure.ofDirectLambda (Context.ofSignatures signatures)
        (captureSource owner metavariable body) []
        (generalizedBinder owner metavariable templateRequirement)
        (captureInitializer owner) [lambdaParameter owner metavariable]
        (.variable metavariable) [body]) := by
  apply GeneralizedClosureCaptures.directLambda
      (node := captureNode owner metavariable body)
  · exact ⟨by simp [captureSource], rfl⟩
  · rfl
  · simp [captureNode, ExpressionNode.rawType, generalizedBinder]
  · simp [captureNode, generalizedBinder]
  · rfl
  · rfl

/-- The runtime boundary is exhaustive once source occurrences are unique:
an initializer is either captured canonically or has positive unsupported
shape evidence. -/
example (context : SourceSemantics.Context) (source : TypedSource)
    (environment : SourceSemantics.Dynamic.Environment) (binder : TypedBinder)
    (initializer : Option ExpressionId)
    (unique : NodeOccurrencesUnique source) :
    (∃ initializerId function,
      initializer = some initializerId ∧
      GeneralizedClosureCaptures context source environment binder
        initializerId function) ∨
    GeneralizedInitializerUnsupported source binder initializer := by
  exact GeneralizedInitializerUnsupported.captures_or_unsupported
    context source environment binder initializer unique

/-- In particular, the unsupported classifier cannot reclassify a canonical
direct-lambda capture as a faulting initializer. -/
example (context : SourceSemantics.Context) (source : TypedSource)
    (environment : SourceSemantics.Dynamic.Environment) (binder : TypedBinder)
    (initializer : ExpressionId) (function : GeneralizedClosure)
    (unsupported : GeneralizedInitializerUnsupported source binder
      (some initializer))
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function) : False := by
  exact unsupported.not_captures captures

/-- Materialization closes direct-lambda types and initializer assumptions,
while the quantified variable of an existing lexical scheme (and its paired
requirement metadata) remains capture-protected.  Code identities, captured
locations, and use-site dictionaries are retained exactly. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) (initializer : ExpressionId)
    (body : StatementId) (templateRequirement protectedRequirement : RequirementId)
    (evidence : EvidenceEnvironment) :
    let function := principalClosure signatures owner metavariable initializer
      body templateRequirement protectedRequirement
    let materialized := function.instantiate [(metavariable, .word)] evidence
    materialized.parameters = [{
        lambdaParameter owner metavariable with scheme := .mono .word
      }] ∧
      materialized.resultType = .word ∧
      materialized.body = [body] ∧
      materialized.source.inputs = [
        { lambdaParameter owner metavariable with scheme := .mono .word },
        protectedBinder owner metavariable
      ] ∧
      materialized.captured =
        [((protectedBinder owner metavariable).id, ⟨7⟩)] ∧
      materialized.context.typeVariables = [] ∧
      materialized.context.locals = [
        ((protectedBinder owner metavariable).id,
          (protectedBinder owner metavariable).scheme)
      ] ∧
      materialized.context.localSchemeRequirements = [
        ((protectedBinder owner metavariable).id,
          [requirement protectedRequirement metavariable])
      ] ∧
      materialized.context.assumptions = [
        ProgramSignatures.builtinIntPredicate .word,
        ProgramSignatures.builtinIntPredicate .word
      ] ∧
      materialized.evidence = evidence := by
  simp [principalClosure, GeneralizedClosure.instantiate, principalSource,
    definitionContext, generalizedBinder, lambdaParameter, protectedBinder,
    requirement, predicate, Context.ofSignatures, Context.withAssumptions,
    Context.withLocal, localSchemeInitializerContext,
    Context.withTypeVariables, FlexibleSubstitution.closeContext,
    FlexibleSubstitution.applyContext,
    FlexibleSubstitution.applyLocals,
    FlexibleSubstitution.applyLocalSchemeRequirements,
    FlexibleSubstitution.forLocal, Resolved.LocalScope.lookup?,
    TypedSource.applySubstitution, TypedBinder.applySubstitution,
    Scheme.mono, Scheme.apply,
    LocalSchemeRequirement.applySubstitution,
    TypedTraitResolution.applySubstitution,
    ProgramSignatures.builtinIntPredicate, TypeSystem.Substitution.without,
    TypeSystem.Substitution.erase, TypeSystem.Substitution.apply,
    TypeSystem.Substitution.lookup?]

/-- A generalized allocation stores the untouched principal closure and no
ordinary value at the unique fresh location. -/
example (heap : Heap) (function : GeneralizedClosure) :
    let location : Location := ⟨heap.cells.length⟩
    let updated : Heap := ⟨heap.cells ++ [{
      type := function.binder.scheme.body
      value := none
      generalized := some function
    }]⟩
    Heap.AllocatesGeneralized heap function location updated ∧
      Heap.Reads updated location {
        type := function.binder.scheme.body
        value := none
        generalized := some function
      } := by
  exact ⟨.append, Heap.AllocatesGeneralized.reads_new .append⟩

/-- Generalized allocation and later ordinary writes compose without changing
the metadata of cells that were already present. -/
example {before middle after : Heap} {function : GeneralizedClosure}
    {fresh written : Location} {value : Option Value}
    (allocation : Heap.AllocatesGeneralized before function fresh middle)
    (write : Heap.Writes middle written value after) :
    HeapMetadataExtend before after :=
  (HeapMetadataExtend.of_generalized_allocation allocation).trans
    (HeapMetadataExtend.of_write write)

end Solcore.Test.SourceSemanticsGeneralizedClosure
end

section
-- leanmerge: from Solcore.Test.SourceSemanticsGeneralizedClosureTyping
/-! Focused proof consumers for generalized-closure cell typing. -/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsGeneralizedClosureTyping

open SourceSemantics
open SourceSemantics.Dynamic
open TypeSystem

private def ordinaryHeap : Heap := {
  cells := [{ type := .bool, value := some (.bool false) }]
}

/-- Descriptor-free storage is the ordinary monomorphic branch. -/
example {id : Resolved.LocalId} {scheme : Scheme} {cell : Cell}
    (monomorphic : scheme.quantified = [])
    (descriptor_empty : cell.generalized = none) :
    LocalCellStorage id scheme cell :=
  .ordinary monomorphic descriptor_empty

/-- Principal descriptors retain the stable local identity and scheme used by
the lexical environment. -/
example {cell : Cell} {function : GeneralizedClosure}
    (descriptor : cell.generalized = some function) :
    LocalCellStorage function.binder.id function.binder.scheme cell :=
  .generalized descriptor rfl rfl

/-- A descriptor-free runtime lookup can only select the monomorphic storage
branch of an agreeing environment. -/
example {heap : Heap} {scope : Resolved.LocalScope Scheme}
    {environment : SourceSemantics.Dynamic.Environment}
    {id : Resolved.LocalId} {scheme : Scheme}
    {location : Location} {cell : Cell}
    (agrees : EnvironmentAgrees heap scope environment)
    (staticLookup : Resolved.LocalScope.Lookup scope id scheme)
    (dynamicLookup : Environment.LooksUp environment id location)
    (read : Heap.Reads heap location cell)
    (descriptor_empty : cell.generalized = none) :
    scheme.quantified = [] :=
  agrees.lookup_monomorphic_of_descriptor_empty staticLookup dynamicLookup read
    descriptor_empty

/-- A present principal descriptor is aligned with the lexical local selected
at the same runtime location. -/
example {heap : Heap} {scope : Resolved.LocalScope Scheme}
    {environment : SourceSemantics.Dynamic.Environment}
    {id : Resolved.LocalId} {scheme : Scheme}
    {location : Location} {cell : Cell} {function : GeneralizedClosure}
    (agrees : EnvironmentAgrees heap scope environment)
    (staticLookup : Resolved.LocalScope.Lookup scope id scheme)
    (dynamicLookup : Environment.LooksUp environment id location)
    (read : Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function) :
    function.binder.id = id ∧ function.binder.scheme = scheme :=
  agrees.lookup_generalized staticLookup dynamicLookup read descriptor

/-- Adding generalized metadata to `CellWellTyped` leaves ordinary cells on
the existing value-typing path. -/
example (context : Context) : HeapWellTyped context ordinaryHeap := by
  intro cell member
  simp only [ordinaryHeap, List.mem_singleton] at member
  subst cell
  exact ⟨.some (.bool false), .none .bool⟩

/-- A deeply typed principal closure inhabits a descriptor cell exactly at its
scheme body. -/
example {context : Context} {heap : Heap} {function : GeneralizedClosure}
    (typed : GeneralizedClosureWellTyped context heap function) :
    CellWellTyped context heap {
      type := function.binder.scheme.body
      value := none
      generalized := some function
    } :=
  ⟨.none _, .some typed⟩

/-- Descriptor inversion recovers both the principal cell type and the
closure's deep typing witness. -/
example {context : Context} {heap : Heap} {function : GeneralizedClosure}
    (typed : GeneralizedClosureWellTyped context heap function) :
    function.binder.scheme.body = function.binder.scheme.body ∧
      GeneralizedClosureWellTyped context heap function := by
  exact OptionalGeneralizedClosureWellTyped.some_inv (.some typed)

/-- Fresh generalized allocation extends any well-typed heap when its
principal closure is already valid in the old heap world. -/
example {context : Context} {before after : Heap} {function : GeneralizedClosure}
    {location : Location}
    (before_typed : HeapWellTyped context before)
    (function_typed : GeneralizedClosureWellTyped context before function)
    (allocation : Heap.AllocatesGeneralized before function location after) :
    HeapWellTyped context after :=
  before_typed.allocateGeneralized function_typed allocation

/-- Metadata-preserving heap growth supplies the existing type-extension
interface without discarding its stronger descriptor guarantee. -/
example {before after : Heap}
    (extension : HeapMetadataExtend before after) :
    HeapTypesExtend before after :=
  extension.toTypes

/-- Generalized closure typing transports across both supported context
changes and type-preserving heap growth. -/
example {source target : Context} {before after : Heap}
    {function : GeneralizedClosure}
    (supports : TypeContextSupports source target)
    (extension : HeapTypesExtend before after)
    (typed : GeneralizedClosureWellTyped source before function) :
    GeneralizedClosureWellTyped target after function :=
  (typed.transportContext supports).mono extension

/-- Ordinary allocation preserves the complete descriptor of every older
cell, not only its declared type. -/
example {before after : Heap} {type : Ty} {value : Option Value}
    {fresh old : Location} {cell : Cell}
    (allocation : Heap.Allocates before type value fresh after)
    (read : Heap.Reads before old cell) :
    ∃ updatedCell,
      Heap.Reads after old updatedCell ∧
      updatedCell.type = cell.type ∧
      updatedCell.generalized = cell.generalized :=
  HeapTypesExtend.of_allocation allocation old cell read

/-- A value write leaves the selected cell's generalized descriptor intact. -/
example {before after : Heap} {written old : Location}
    {value : Option Value} {cell : Cell}
    (write : Heap.Writes before written value after)
    (read : Heap.Reads before old cell) :
    ∃ updatedCell,
      Heap.Reads after old updatedCell ∧
      updatedCell.type = cell.type ∧
      updatedCell.generalized = cell.generalized :=
  HeapTypesExtend.of_write write old cell read

/-- Descriptor preservation composes transitively across multiple heap
steps. -/
example {first middle last : Heap} {location : Location} {cell : Cell}
    (left : HeapTypesExtend first middle)
    (right : HeapTypesExtend middle last)
    (read : Heap.Reads first location cell) :
    ∃ updatedCell,
      Heap.Reads last location updatedCell ∧
      updatedCell.type = cell.type ∧
      updatedCell.generalized = cell.generalized :=
  left.trans right location cell read

end Solcore.Test.SourceSemanticsGeneralizedClosureTyping
end

section
-- leanmerge: from Solcore.Test.SourceSemanticsLocalSchemes
/-! Focused boundary tests for dynamic qualified-local instantiation. -/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsLocalSchemes

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic
open TypeSystem

private def templateId : RequirementId := ⟨200⟩
private def actualId : RequirementId := ⟨201⟩

private def templatePredicate (fresh : TypeVarId) : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable fresh)

private def actualPredicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate .word

private def templateRequirement (fresh : TypeVarId) :
    LocalSchemeRequirement := {
  templateRequirement := templateId
  predicate := templatePredicate fresh
}

private def binder (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) : TypedBinder := {
  id := ⟨owner, 200⟩
  name := "qualified"
  scheme := {
    quantified := [fresh]
    body := .function (.variable fresh) (.variable fresh)
  }
  schemeRequirements := [templateRequirement fresh]
}

private def templateRow (fresh : TypeVarId) : SolvedRequirement := {
  id := templateId
  predicate := templatePredicate fresh
  evidence := .assumption (templatePredicate fresh)
}

private def actualRow : SolvedRequirement := {
  id := actualId
  predicate := actualPredicate
  evidence := .assumption actualPredicate
}

private def useContext (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    Solcore.SourceSemantics.Context :=
  (((Context.ofSignatures signatures).withAssumptions
      [actualPredicate]).withSolvedRequirements
    [templateRow fresh, actualRow]).withLocal
      (binder owner fresh).id (binder owner fresh).scheme
      (binder owner fresh).schemeRequirements

private def callerEvidence : EvidenceEnvironment :=
  [(actualPredicate, .implementation actualPredicate
    ProgramSignatures.builtinIntWordRule.id [])]

private theorem formation (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    LocalSchemeRequirementsWellFormed (useContext signatures owner fresh)
      (binder owner fresh) := by
  constructor
  · simp [localSchemeTemplateIds, binder, templateRequirement]
  · intro requirement member
    simp [binder] at member
    subst requirement
    constructor
    · constructor
      · constructor
        · constructor
          · simp [useContext, localSchemeInitializerContext, binder,
              Context.ofSignatures, Context.withAssumptions,
              Context.withSolvedRequirements, Context.withLocal,
              Context.withTypeVariables]
          · intro parameter parameterMember
            simp [useContext, localSchemeInitializerContext, binder,
              Context.ofSignatures, Context.withAssumptions,
              Context.withSolvedRequirements, Context.withLocal,
              Context.withTypeVariables] at parameterMember
        · apply TypeWellScoped.variable
          simp [admissibleTypeVariables, useContext,
            localSchemeInitializerContext, binder, Context.ofSignatures,
            Context.withAssumptions, Context.withSolvedRequirements,
            Context.withLocal, Context.withTypeVariables]
      · intro argument argumentMember
        simp [templateRequirement, templatePredicate,
          ProgramSignatures.builtinIntPredicate] at argumentMember
      · rfl
    · refine ⟨fresh, by simp [binder], ?_⟩
      simp [templateRequirement, templatePredicate,
        ProgramSignatures.builtinIntPredicate,
        Frontend.TypedTraitResolution.predicateVariables,
        TypeSystem.Ty.freeVariables]
    · refine ⟨templateRow fresh, ?_, rfl, rfl, rfl⟩
      change [templateRow fresh, actualRow].filter
        (fun candidate => candidate.id == (templateRow fresh).id) =
          [templateRow fresh]
      rfl

private theorem schemeWellFormed (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    SchemeWellFormed (useContext signatures owner fresh)
      (binder owner fresh).scheme := by
  constructor
  · simp [TypeParameterBindersWellFormed, useContext, Context.ofSignatures,
      Context.withAssumptions, Context.withSolvedRequirements,
      Context.withLocal]
  · simp [binder]
  · apply TypeWellScoped.function <;> apply TypeWellScoped.variable <;>
      simp [binder, admissibleTypeVariables, useContext, Context.ofSignatures,
        Context.withAssumptions, Context.withSolvedRequirements,
        Context.withLocal]

private theorem builtinHeadInstantiates :
    ImplHeadInstantiates ProgramSignatures.builtinIntWordRule
      actualPredicate [] := by
  refine .intro { parameters := [], variables := [] } ?_ rfl rfl
  exact ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩

private theorem closedEvidenceValid (signatures : ProgramSignatures) :
    EvidenceValid [] signatures.resolutionRules actualPredicate
      (.implementation actualPredicate
        ProgramSignatures.builtinIntWordRule.id []) := by
  exact .implementation
    (by simp [ProgramSignatures.resolutionRules,
      ProgramSignatures.builtinResolutionRules])
    rfl builtinHeadInstantiates .nil

private theorem producesEvidence (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    RequirementsProduceEnvironment (useContext signatures owner fresh)
      callerEvidence [actualId] [actualPredicate] callerEvidence := by
  apply RequirementsProduceEnvironment.cons
  · apply RequirementProducesEvidence.intro
      (requirement := actualRow)
      (openEvidence := .assumption actualPredicate)
    · exact ⟨by simp [useContext, Context.withLocal,
        Context.withSolvedRequirements], rfl⟩
    · rfl
    · exact .assumption actualPredicate
    · apply SolvedRequirementValid.intro
      exact .intro (.assumption actualPredicate)
        (.assumption (by simp [useContext, Context.withLocal,
          Context.withSolvedRequirements, Context.withAssumptions,
          actualRow]))
    · exact .assumption .head
    · exact closedEvidenceValid signatures
  · exact .nil

private theorem runtimeInstantiation (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    LocalSchemeRuntimeInstantiation (useContext signatures owner fresh)
      callerEvidence (binder owner fresh) (.function .word .word) [actualId]
      [(fresh, .word)] callerEvidence := by
  refine {
    formation := formation signatures owner fresh
    scheme_well_formed := schemeWellFormed signatures owner fresh
    exact := ExactSubstitution.singleton fresh .word
    range := ?_
    result := ?_
    actual_requirements_unique := by simp [actualId]
    actual_templates_disjoint := ?_
    produces := ?_
  }
  · intro metavariable replacement member
    simp only [List.mem_cons, List.mem_nil_iff, or_false,
      Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact {
      binders := by
        simp [TypeParameterBindersWellFormed, useContext,
          Context.ofSignatures, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withLocal]
      typeWellScoped := .builtin .word
    }
  · simp [binder, TypeSystem.Substitution.apply,
      TypeSystem.Substitution.lookup?]
  · intro id actualMember templateMember
    have actualEq : id = actualId := by simpa using actualMember
    have templateEq : id = templateId := by
      simpa [localSchemeTemplateIds, binder, templateRequirement] using
        templateMember
    exact (show actualId ≠ templateId by decide) (actualEq.symm.trans templateEq)
  · simpa [instantiateLocalSchemePredicates, binder, templateRequirement,
      templatePredicate, actualPredicate,
      Frontend.TypedTraitResolution.applySubstitution,
      ProgramSignatures.builtinIntPredicate, TypeSystem.Substitution.apply,
      TypeSystem.Substitution.lookup?] using
      (producesEvidence signatures owner fresh)

private theorem callerCovers (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    callerEvidence.Covers (useContext signatures owner fresh) := by
  constructor
  · intro goal evidence found
    cases found with
    | head => exact closedEvidenceValid signatures
    | tail _ found => cases found
  · intro predicate member
    have same : predicate = actualPredicate := by
      simpa [useContext, Context.withLocal, Context.withSolvedRequirements,
        Context.withAssumptions] using member
    subst predicate
    exact ⟨_, .head⟩

/-- The dynamic witness projects back to the established static judgment. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    LocalSchemeRuntimeSelection (useContext signatures owner fresh)
      (binder owner fresh) (.function .word .word) [actualId]
      [(fresh, .word)] :=
  (runtimeInstantiation signatures owner fresh).toSelection

/-- Forgetting the explicit runtime selection still recovers the established
static local-scheme judgment. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    LocalSchemeInstantiationValid (useContext signatures owner fresh)
      (binder owner fresh) (.function .word .word) [actualId] :=
  (runtimeInstantiation signatures owner fresh).toLocalSchemeInstantiationValid

/-- The public projections expose arity, uniqueness, template separation, and
closed evidence validity without reopening the constructor. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    [actualId].length = (binder owner fresh).schemeRequirements.length ∧
      [actualId].Nodup ∧
      actualId ∉ localSchemeTemplateIds (binder owner fresh) ∧
      callerEvidence.Valid signatures.resolutionRules := by
  let instantiated := runtimeInstantiation signatures owner fresh
  exact ⟨instantiated.actual_requirements_length_eq,
    instantiated.actual_requirements_nodup,
    instantiated.actual_requirement_templates_disjoint actualId (by simp),
    instantiated.produced_evidence_valid⟩

/-- Local evidence is prepended to caller evidence.  This fixture deliberately
uses the same goal in both dictionaries, exercising the overlap fallback rather
than relying on a hidden disjointness premise. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    (callerEvidence ++ callerEvidence).Covers
      ((useContext signatures owner fresh).withAssumptions
        ((useContext signatures owner fresh).assumptions ++
          instantiateLocalSchemePredicates [(fresh, .word)]
            (binder owner fresh))) :=
  (runtimeInstantiation signatures owner fresh).combined_evidence_covers
    (callerCovers signatures owner fresh)

end Solcore.Test.SourceSemanticsLocalSchemes
end

section
-- leanmerge: from Solcore.Test.SourceSemanticsProgram
/-!
Focused construction tests for whole-program declarative admission.

The empty catalog is deliberately small, but it exercises every top-level
coverage and uniqueness field without relying on the executable frontend.
-/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsProgram

open Frontend
open SourceSemantics
open TypeSystem
open SourceSemantics.Dynamic

private def emptySignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
  contracts := []
}

private def emptyProgram : SourceSemantics.Program := {
  signatures := emptySignatures
  functions := []
  methods := []
}

theorem emptySignatureCatalogWellFormed :
    SignatureCatalogWellFormed emptySignatures := by
  constructor <;> simp [emptySignatures, signatureDeclarationIds]

theorem emptyProgramWellFormed : ProgramWellFormed emptyProgram := by
  refine {
    signatures := emptySignatureCatalogWellFormed
    function_ids := ?_
    method_ids := ?_
    functions_valid := ?_
    methods_valid := ?_
    functions_complete := ?_
    methods_complete := ?_
  } <;> simp [emptyProgram, emptySignatures]

theorem emptyProgramHasStages :
    SourceSemantics.Staging.ProgramHasStages emptyProgram := {
  staticallyValid := emptyProgramWellFormed
  functions := by simp [emptyProgram]
  methods := by simp [emptyProgram]
}

private def unitModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_semantics_program", by decide⟩], by decide⟩⟩

private def unitOwner : Resolved.DeclarationId := ⟨unitModule, 0⟩

private def unitSourceId : Syntax.SourceId := {
  origin := .main
  path := "source_semantics_program.sol"
}

private def unitSpan : Syntax.SourceSpan := {
  source := unitSourceId
  startByte := 0
  endByte := 0
}

/-- The parsed declaration is retained only as source metadata by the resolved
signature; the declarative semantic body below remains independently forgeable. -/
private def unitSyntax : Syntax.FunctionDecl := {
  span := unitSpan
  value := {
    signature := {
      span := unitSpan
      name := ⟨unitSpan, "unitMain"⟩
      genericParameters := none
      parameters := ⟨unitSpan, []⟩
      modifiers := ⟨none, none⟩
      returnsClause := none
      whereClause := none
    }
    body := ⟨unitSpan, []⟩
  }
}

private def genericContractOwner : Resolved.DeclarationId :=
  ⟨unitModule, 1⟩

private def genericContractSyntax : Syntax.ContractDecl := {
  span := unitSpan
  value := {
    name := ⟨unitSpan, "Vault"⟩
    genericParameters := some
      ⟨unitSpan, ⟨⟨unitSpan, "T"⟩, []⟩⟩
    bodySpan := unitSpan
    members := []
  }
}

private def genericContractSignature : ProgramContractSignature := {
  id := genericContractOwner
  name := "Vault"
  parameters := [{ owner := genericContractOwner, index := 0 }]
  source := genericContractSyntax
}

private def genericContractSignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
  contracts := [genericContractSignature]
}

theorem genericContractSignatureWellFormed :
    ContractSignatureWellFormed genericContractSignatures
      genericContractSignature := by
  refine {
    parameters_nodup := by simp [genericContractSignature]
    parameters_owned := ?_
    parameter_positions := ?_
  }
  · intro parameter member
    simp only [genericContractSignature, List.mem_singleton] at member
    subst parameter
    rfl
  · intro index
    have bound : index.val < 1 := by
      simpa [genericContractSignature] using index.isLt
    have value_eq : index.val = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
    have index_eq :
        index = ⟨0, by simp [genericContractSignature]⟩ := by
      apply Fin.ext
      exact value_eq
    subst index
    rfl

/-- Generic contracts form nominal source types through their own catalog,
without borrowing data-constructor status. -/
theorem genericContractNominalWellScoped :
    TypeWellScoped (Context.ofSignatures genericContractSignatures) []
      (Ty.nominal genericContractOwner [.word]) := by
  exact .contractNominal genericContractSignature [.word]
    (by simp [Context.ofSignatures, genericContractSignatures])
    (by simp [genericContractSignature])
    (.cons (.builtin .word) .nil)

theorem genericContractNotCatalogedAsData :
    ¬ ∃ dataType ∈ genericContractSignatures.dataTypes,
      dataType.id = genericContractOwner := by
  simp [genericContractSignatures]

private def unitSignature : ProgramFunctionSignature := {
  id := unitOwner
  name := "unitMain"
  parameters := []
  returnTypes := []
  returnComptime := false
  scheme := {
    parameters := []
    predicates := []
    body := .function .unit .unit
  }
  source := unitSyntax
}

private def unitSignatures : ProgramSignatures := {
  functions := [unitSignature]
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
  contracts := []
}

private def unitSource : Frontend.SourceInference.TypedSource := {
  owner := unitOwner
  inputs := []
  roots := []
  nodes := []
}

private def unitBody : BodyDefinition := {
  owner := unitOwner
  type := .function .unit .unit
  resultType := .unit
  returnComptime := false
  solvedRequirements := []
  source := unitSource
}

private def unitProgram : SourceSemantics.Program := {
  signatures := unitSignatures
  functions := [{ body := unitBody }]
  methods := []
}

theorem unitSignatureCatalogWellFormed :
    SignatureCatalogWellFormed unitSignatures := by
  refine {
    impl_rules_eq := by rfl
    declaration_ids := by
      simp [unitSignatures, signatureDeclarationIds, unitSignature]
    function_ids := by simp [unitSignatures, unitSignature]
    data_ids := by simp [unitSignatures]
    trait_ids := by simp [unitSignatures]
    implementation_ids := by simp [unitSignatures]
    contract_ids := by simp [unitSignatures]
    constructor_ids := by simp [unitSignatures]
    trait_method_ids := by simp [unitSignatures]
    implementation_method_ids := by simp [unitSignatures]
    function_parameters := by simp [unitSignatures, unitSignature]
    data_parameters := by simp [unitSignatures]
    trait_parameters := by simp [unitSignatures]
    implementation_parameters := by simp [unitSignatures]
    contract_parameters := by simp [unitSignatures]
    functions_semantic := ?_
    data_semantic := by simp [unitSignatures]
    traits_semantic := by simp [unitSignatures]
    implementations_semantic := by simp [unitSignatures]
    contracts_semantic := by simp [unitSignatures]
  }
  intro signature member
  simp only [unitSignatures, List.mem_singleton] at member
  subst signature
  refine {
    parameters_nodup := by simp [unitSignature]
    parameters_owned := by simp [unitSignature]
    parameter_positions := by
      intro index
      exact Fin.elim0 index
    parameter_names_nodup := by
      simp [ProgramFunctionSignature.parameterNames, unitSignature]
    parameter_types := by
      simp [TypesWellFormed, ProgramFunctionSignature.parameterTypes,
        unitSignature]
    return_types := by simp [TypesWellFormed, unitSignature]
    predicates := by simp [PredicatesWellFormed, unitSignature]
    scheme_body := by rfl
  }

theorem unitOccurrenceGraphClosed : OccurrenceGraphClosed unitSource := by
  refine {
    wellFormed := ?_
    rootsUnique := by simp [RootsUnique, unitSource]
    childSlotsUnique := by simp [ChildSlotsUnique, unitSource]
    childHasUniqueParent := by
      intro left right child leftEdge _
      rcases leftEdge with ⟨node, contains, _⟩
      simp [ContainsNode, unitSource] at contains
    rootsHaveNoParent := by simp [RootsHaveNoParent, unitSource]
    allNodesReachable := by simp [AllNodesReachable, unitSource]
    acyclic := by
      intro id descends
      cases descends with
      | direct edge =>
          rcases edge with ⟨node, contains, _⟩
          simp [ContainsNode, unitSource] at contains
      | step edge _ =>
          rcases edge with ⟨node, contains, _⟩
          simp [ContainsNode, unitSource] at contains
  }
  refine {
    nodeOccurrencesUnique := by simp [NodeOccurrencesUnique, nodeOccurrenceIds,
      unitSource]
    nodesOwned := by simp [NodesOwned, unitSource]
    rootsOwned := by simp [RootsOwned, unitSource]
    rootsExist := by simp [RootsExist, unitSource]
    childEdgesExist := by simp [ChildEdgesExist, unitSource]
  }

theorem unitLocalIdentityOwnership : LocalIdentityOwnership unitSource := by
  constructor <;> simp [definedLocalIds, unitSource]

theorem unitBodyHasType :
    BodyDefinitionHasType unitSignatures [] [] [] [] [] [] false unitBody
      .empty := by
  apply BodyDefinitionHasType.intro
      (lexicalContext := declarationContext unitSignatures unitOwner [] [] [])
  · rfl
  · simp [TypeParameterBindersWellFormed, declarationContext,
      Context.withSolvedRequirements, Context.withAssumptions,
      Context.withResidualTypeVariables, Context.forDeclaration,
      Context.ofSignatures]
  · simp [TypesWellFormed]
  · simp [TypesWellFormed]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact .nil _
  · exact unitOccurrenceGraphClosed
  · exact unitLocalIdentityOwnership
  · apply ScopedRequirementLedgerWellFormed.ofRequirementLedger
    · constructor
      · simp [RequirementIdsUnique, unitBody, declarationContext,
          Context.withSolvedRequirements, Context.withAssumptions,
          Context.withResidualTypeVariables, Context.forDeclaration,
          Context.ofSignatures]
      · intro requirement member
        simp [unitBody, declarationContext, Context.withSolvedRequirements,
          Context.withAssumptions, Context.withResidualTypeVariables,
          Context.forDeclaration,
          Context.ofSignatures] at member
    · simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
        initializedLetBindings, unitBody, unitSource]
  · constructor <;>
      simp [primaryRequirementIds, unitBody, unitSource, declarationContext,
        Context.withSolvedRequirements, Context.withAssumptions,
        Context.withResidualTypeVariables, Context.forDeclaration,
        Context.ofSignatures]
  · refine ⟨_, .nil _ _, ?_, ?_⟩
    · intro expression member
      simp [unitBody, unitSource] at member
    · simp [BodyCompletes, BodyFacts.empty, ControlSummary.ordinary,
        TypeSystem.Ty.productMany]
  · rfl

theorem unitFunctionValid :
    FunctionDefinition.Valid unitSignatures { body := unitBody } := by
  apply FunctionDefinition.Valid.intro (signature := unitSignature)
      (facts := .empty)
  · simp [unitSignatures]
  · rfl
  · exact unitBodyHasType

theorem unitProgramWellFormed : ProgramWellFormed unitProgram := by
  refine {
    signatures := unitSignatureCatalogWellFormed
    function_ids := by simp [unitProgram, unitBody]
    method_ids := by simp [unitProgram]
    functions_valid := ?_
    methods_valid := by simp [unitProgram]
    functions_complete := ?_
    methods_complete := by simp [unitProgram, unitSignatures]
  }
  · intro definition member
    simp only [unitProgram, List.mem_singleton] at member
    subst definition
    exact unitFunctionValid
  · intro signature signatureMember
    simp only [unitProgram, unitSignatures, List.mem_singleton] at signatureMember
    subst signature
    exact ⟨{ body := unitBody }, by simp [unitProgram], rfl⟩

theorem unitBodyHasStages :
    SourceSemantics.Staging.BodyDefinitionHasStages unitBody := by
  apply SourceSemantics.Staging.BodyDefinitionHasStages.intro
      (inputScope := []) (finalScope := [])
  · rfl
  · exact unitOccurrenceGraphClosed
  · exact unitLocalIdentityOwnership
  · apply SourceSemantics.Staging.FunctionInputsStage.ordinary
    · rfl
    · intro comptimeOnly
      cases comptimeOnly
    · exact .nil []
  · exact .nil []

theorem unitProgramHasStages :
    SourceSemantics.Staging.ProgramHasStages unitProgram := by
  refine {
    staticallyValid := unitProgramWellFormed
    functions := ?_
    methods := by simp [unitProgram]
  }
  intro definition member
  simp only [unitProgram, List.mem_singleton] at member
  subst definition
  exact unitBodyHasStages

private def unitInstantiation :
    Frontend.SourceInference.DeclarationInstantiation := {
  declaration := unitOwner
  parameterSubstitution := []
  type := .function .unit .unit
  predicates := []
  parameterComptime := []
  returnComptime := false
}

private def unitBodyInstance : BodyInstance := {
  context := declarationContext unitSignatures unitOwner [] [] []
  source := unitSource
  resultType := .unit
}

private def unitEntry : ProgramEntry := {
  instantiation := unitInstantiation
  evidence := []
  arguments := []
}

theorem unitInstantiationValid :
    SourceSemantics.DeclarationInstantiation.Valid
      (Context.ofSignatures unitSignatures) unitInstantiation := by
  apply SourceSemantics.DeclarationInstantiation.Valid.intro unitSignature
  · change unitSignature ∈ [unitSignature]
    simp
  · rfl
  · exact SourceSemantics.ParameterSubstitution.exact_empty
  · intro parameter replacement member
    change (parameter, replacement) ∈
      ([] : TypeSystem.ParameterSubstitution) at member
    simp at member
  · rfl
  · rfl
  · rfl
  · rfl

theorem unitFunctionInstantiates :
    FunctionInstantiates unitProgram unitInstantiation unitBodyInstance := by
  apply FunctionInstantiates.intro
      (signature := unitSignature) (definition := { body := unitBody })
  · simp [unitProgram, unitSignatures]
  · simp [unitProgram]
  · rfl
  · rfl
  · exact unitInstantiationValid
  · rfl
  · rfl
  · rfl

theorem unitEvidenceCovers :
    EvidenceEnvironment.Covers unitBodyInstance.context [] := by
  constructor
  · intro goal evidence lookup
    cases lookup
  · intro predicate member
    simp [unitBodyInstance, declarationContext, Context.withSolvedRequirements,
      Context.withAssumptions, Context.withResidualTypeVariables,
      Context.forDeclaration, Context.ofSignatures]
      at member

theorem emptyHeapWellTyped :
    HeapWellTyped unitBodyInstance.context ⟨[]⟩ := by
  intro cell member
  simp at member

theorem unitEntryValid :
    ProgramEntryValid unitProgram unitEntry ⟨[]⟩ unitBodyInstance := {
  instantiates := unitFunctionInstantiates
  evidence_covers := unitEvidenceCovers
  heap_typed := emptyHeapWellTyped
  arguments_typed := .nil
}

theorem unitBodyInvokes :
    BodyInvokes unitProgram unitBodyInstance [] ⟨[]⟩ [] .unit ⟨[]⟩ := by
  apply BodyInvokes.unit
      (inputTypes := [])
      (lexicalContext := unitBodyInstance.context)
      (finalContext := unitBodyInstance.context)
      (environment := []) (bound := ⟨[]⟩) (roots := [])
      (outcome := .fallthrough [])
  · exact unitEvidenceCovers
  · rfl
  · exact .nil
  · exact .nil _
  · exact .nil [] ⟨[]⟩
  · exact .nil
  · exact ⟨[], rfl⟩

/-- A nonempty semantic program can be admitted and run without consulting the
executable frontend or any backend evaluator. -/
theorem unitProgramEvaluates :
    ProgramEvaluates unitProgram unitEntry ⟨[]⟩ .unit ⟨[]⟩ := by
  exact .run unitProgramHasStages unitEntryValid unitBodyInvokes

/-- The public whole-program theorem closes a concrete nonempty semantic
program without accepting a preservation package as an extra premise. -/
theorem unitProgramEvaluationPreserved :
    ∃ bodyInstance,
      ProgramEntryValid unitProgram unitEntry ⟨[]⟩ bodyInstance ∧
        BodyInvocationPreserved bodyInstance ⟨[]⟩ ⟨[]⟩ .unit :=
  unitProgramEvaluates.preserves

end Solcore.Test.SourceSemanticsProgram
end

section
-- leanmerge: from Solcore.Test.SourceSemantics
set_option autoImplicit false

namespace Solcore.Test.SourceSemantics

open Frontend
open TypeSystem
open Solcore.SourceSemantics

/-- Extending a semantic context makes the new local available immediately. -/
example (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId)
    (scheme : Scheme) :
    (context.withLocal binder scheme).LocalLookup binder scheme := by
  exact Context.localLookup_withLocal_self context binder scheme

/-- A quantified local scheme can be instantiated independently at each
reference occurrence. -/
theorem polymorphicLocalReference
    (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId)
    (metavariable : TypeVarId)
    (context_binders : TypeParameterBindersWellFormed context) :
    ReferenceHasRawType
      (context.withLocal binder {
        quantified := [metavariable]
        body := .variable metavariable
      })
      (.local binder) .word := by
  let scheme : Scheme := {
    quantified := [metavariable]
    body := .variable metavariable
  }
  change ReferenceHasRawType (context.withLocal binder scheme)
    (.local binder) .word
  apply ReferenceHasRawType.local
  · exact Context.localLookup_withLocal_self _ _ _
  · refine SchemeInstantiatesAt.intro ?_
      [(metavariable, .word)] ?_ ?_ ?_
    · exact {
        binders := context_binders.withLocal binder scheme
        quantified_nodup := by simp [scheme]
        body := by
          apply TypeWellScoped.variable
          simp [scheme]
      }
    · exact ExactSubstitution.singleton metavariable .word
    · intro candidate replacement member
      simp only [List.mem_cons, List.mem_nil_iff, or_false,
        Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact {
        binders := context_binders.withLocal binder scheme
        typeWellScoped := .builtin .word
      }
    · simp [scheme, TypeSystem.Substitution.apply,
        TypeSystem.Substitution.lookup?]

/-- A quantified local can be instantiated at a flexible variable explicitly
scoped by an enclosing generalized initializer.  This is the compositional
case which a closed-only substitution range would reject. -/
theorem polymorphicLocalReferenceAtAmbientVariable
    (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId)
    (quantified ambient : TypeVarId)
    (context_binders : TypeParameterBindersWellFormed context) :
    ReferenceHasRawType
      ((context.withTypeVariables [ambient]).withLocal binder {
        quantified := [quantified]
        body := .variable quantified
      })
      (.local binder) (.variable ambient) := by
  let scheme : Scheme := {
    quantified := [quantified]
    body := .variable quantified
  }
  let ambientContext :=
    (context.withTypeVariables [ambient]).withLocal binder scheme
  change ReferenceHasRawType ambientContext (.local binder) (.variable ambient)
  apply ReferenceHasRawType.local
  · exact Context.localLookup_withLocal_self _ _ _
  · refine SchemeInstantiatesAt.intro ?_
      [(quantified, .variable ambient)] ?_ ?_ ?_
    · exact {
        binders := (context_binders.withTypeVariables [ambient]).withLocal
          binder scheme
        quantified_nodup := by simp [scheme]
        body := by
          apply TypeWellScoped.variable
          simp [ambientContext, scheme, Context.withTypeVariables,
            Context.withLocal]
      }
    · exact ExactSubstitution.singleton quantified (.variable ambient)
    · intro candidate replacement member
      simp only [List.mem_cons, List.mem_nil_iff, or_false,
        Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact {
        binders := (context_binders.withTypeVariables [ambient]).withLocal
          binder scheme
        typeWellScoped := by
          apply TypeWellScoped.variable
          simp [ambientContext, admissibleTypeVariables,
            Context.withTypeVariables, Context.withLocal,
            TypeSystem.Ty.freeVariables]
      }
    · simp [scheme, TypeSystem.Substitution.apply,
        TypeSystem.Substitution.lookup?]

/-- Opening residual scope admits a retained occurrence metavariable but does
not turn it into a closed source type. -/
theorem residualVariableAdmissible
    (context : Solcore.SourceSemantics.Context) (residual : TypeVarId)
    (context_binders : TypeParameterBindersWellFormed context) :
    TypeAdmissible context.withResidualTypeVariables (.variable residual) := {
  binders := context_binders.withResidualTypeVariables
  typeWellScoped := by
    apply TypeWellScoped.variable
    simp [admissibleTypeVariables, Context.withResidualTypeVariables,
      TypeSystem.Ty.freeVariables]
}

theorem residualVariableNotClosed
    (context : Solcore.SourceSemantics.Context) (residual : TypeVarId) :
    ¬ TypeWellFormed context.withResidualTypeVariables (.variable residual) := by
  intro wellFormed
  exact TypeWellFormed.variable_impossible residual wellFormed

private def canonicalIdentityVariable : TypeVarId := ⟨73⟩

private def canonicalIdentityScheme : Scheme := {
  quantified := [canonicalIdentityVariable]
  body := .function (.variable canonicalIdentityVariable)
    (.variable canonicalIdentityVariable)
}

/-- The executable fresh instantiator for a generic identity scheme directly
produces the declarative use-site instantiation certificate. -/
theorem canonicalFreshIdentityInstantiation
    (context : Solcore.SourceSemantics.Context)
    (context_binders : TypeParameterBindersWellFormed context) :
    SchemeInstantiatesAt context.withResidualTypeVariables
      canonicalIdentityScheme
      (.function (.variable ⟨10⟩) (.variable ⟨10⟩)) := by
  have schemeWellFormed :
      SchemeWellFormed context.withResidualTypeVariables
        canonicalIdentityScheme := {
    binders := context_binders.withResidualTypeVariables
    quantified_nodup := by simp [canonicalIdentityScheme]
    body := by
      apply TypeWellScoped.function <;> apply TypeWellScoped.variable <;>
        simp [canonicalIdentityScheme, canonicalIdentityVariable,
          admissibleTypeVariables, Context.withResidualTypeVariables,
          TypeSystem.Ty.freeVariables]
  }
  change SchemeInstantiatesAt context.withResidualTypeVariables
    canonicalIdentityScheme
      (canonicalIdentityScheme.instantiateWithSubstitution 10).body
  exact SchemeInstantiatesAt.of_instantiateWithSubstitution schemeWellFormed
    rfl 10

/-- A residual rigid-parameter replacement is accepted by the static
occurrence judgment but cannot cross the closed runtime-instantiation
boundary. -/
theorem residualDeclarationInstantiationIsStaticOnly
    (context : Solcore.SourceSemantics.Context)
    (signature : ProgramFunctionSignature)
    (signature_mem : signature ∈ context.signatures.functions)
    (parameter : TypeParameterId) (residual : TypeVarId)
    (parameters_eq : signature.scheme.parameters = [parameter])
    (body_eq : signature.scheme.body = .parameter parameter)
    (context_binders : TypeParameterBindersWellFormed context) :
    ∃ instantiation,
      DeclarationInstantiation.Admissible
        context.withResidualTypeVariables instantiation ∧
      ¬ DeclarationInstantiation.Valid
        context.withResidualTypeVariables instantiation := by
  let substitution : ParameterSubstitution :=
    [(parameter, .variable residual)]
  let instantiation : Frontend.SourceInference.DeclarationInstantiation := {
    declaration := signature.id
    parameterSubstitution := substitution
    type := .variable residual
    predicates := signature.scheme.predicates.map
      (ProgramPredicate.applyParameters substitution)
    parameterComptime := signature.parameterComptime
    returnComptime := signature.returnComptime
  }
  refine ⟨instantiation, ?_, ?_⟩
  · apply DeclarationInstantiation.Admissible.intro signature
    · simpa [Context.withResidualTypeVariables] using signature_mem
    · rfl
    · simpa [instantiation, substitution, parameters_eq] using
        ParameterSubstitution.exact_singleton parameter (.variable residual)
    · intro candidate replacement member
      simp only [instantiation, substitution, List.mem_cons,
        List.mem_nil_iff, or_false, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact residualVariableAdmissible context residual context_binders
    · simp [instantiation, substitution, body_eq,
        TypeSystem.ParameterSubstitution.apply,
        TypeSystem.ParameterSubstitution.lookup?]
    · rfl
    · rfl
    · rfl
  · intro valid
    cases valid with
    | intro selected selected_mem declaration_eq exact range type_eq
        predicates_eq parameterComptime_eq returnComptime_eq =>
        have member :
            (parameter, .variable residual) ∈
              instantiation.parameterSubstitution := by
          simp [instantiation, substitution]
        exact TypeWellFormed.variable_impossible residual
          (range parameter (.variable residual) member)

/-- A quantified local may be instantiated at an unconstrained occurrence
metavariable retained anywhere in a resolved body.  This is distinct from the
lexical flexible scope used inside generalized initializers. -/
theorem polymorphicLocalReferenceAtResidualVariable
    (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId)
    (quantified residual : TypeVarId)
    (context_binders : TypeParameterBindersWellFormed context) :
    ReferenceHasRawType
      (context.withResidualTypeVariables.withLocal binder {
        quantified := [quantified]
        body := .variable quantified
      })
      (.local binder) (.variable residual) := by
  let scheme : Scheme := {
    quantified := [quantified]
    body := .variable quantified
  }
  let residualContext :=
    context.withResidualTypeVariables.withLocal binder scheme
  change ReferenceHasRawType residualContext (.local binder)
    (.variable residual)
  apply ReferenceHasRawType.local
  · exact Context.localLookup_withLocal_self _ _ _
  · refine SchemeInstantiatesAt.intro ?_
      [(quantified, .variable residual)] ?_ ?_ ?_
    · exact {
        binders := context_binders.withLocal binder scheme
        quantified_nodup := by simp [scheme]
        body := by
          apply TypeWellScoped.variable
          simp [residualContext, scheme, admissibleTypeVariables,
            Context.withResidualTypeVariables, Context.withLocal]
      }
    · exact ExactSubstitution.singleton quantified (.variable residual)
    · intro candidate replacement member
      simp only [List.mem_cons, List.mem_nil_iff, or_false,
        Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact {
        binders := context_binders.withLocal binder scheme
        typeWellScoped := by
          apply TypeWellScoped.variable
          simp [residualContext, admissibleTypeVariables,
            Context.withResidualTypeVariables, Context.withLocal,
            TypeSystem.Ty.freeVariables]
      }
    · simp [scheme, TypeSystem.Substitution.apply,
        TypeSystem.Substitution.lookup?]

/-- Opening residual occurrence scope does not change the lexical
generalization barrier. -/
theorem residualScopeDoesNotBlockGeneralization
    (context : Solcore.SourceSemantics.Context) :
    GeneralizationBlockedVariables context.withResidualTypeVariables =
      GeneralizationBlockedVariables context := by
  rfl

/-- Free variables of preceding local schemes participate in the
generalization barrier. -/
theorem precedingLocalVariableBlocksGeneralization
    (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId) (blocked : TypeVarId) :
    blocked ∈ GeneralizationBlockedVariables
      (context.withLocal binder {
        quantified := []
        body := .variable blocked
      }) := by
  simp [GeneralizationBlockedVariables, GeneralizationBlockedVariablesExcept,
    Context.withLocal,
    TypeSystem.Scheme.freeVariables, TypeSystem.Ty.freeVariables]

/-- Variables retained by solved predicates also participate in the
generalization barrier. -/
theorem solvedRequirementVariableBlocksGeneralization
    (context : Solcore.SourceSemantics.Context) (blocked : TypeVarId) :
    let predicate : ProgramPredicate := {
      trait := .builtin .int
      subject := .variable blocked
      arguments := []
    }
    let requirement : Frontend.SourceInference.SolvedRequirement := {
      id := ⟨0⟩
      predicate
      evidence := .assumption predicate
    }
    blocked ∈ GeneralizationBlockedVariables
      (context.withSolvedRequirements [requirement]) := by
  simp [GeneralizationBlockedVariables, GeneralizationBlockedVariablesExcept,
    Context.withSolvedRequirements,
    Frontend.TypedTraitResolution.predicateVariables,
    TypeSystem.Ty.freeVariables]

/-- Rigid substitution preserves the body-wide residual scope exactly. -/
theorem rigidSubstitutionPreservesResidualScope
    (context : Solcore.SourceSemantics.Context)
    (substitution : ParameterSubstitution) :
    StructuralSubstitution.applyContext substitution
        (context.withResidualTypeVariables) =
      Context.withResidualTypeVariables
        (StructuralSubstitution.applyContext substitution context) := by
  rfl

/-- Generalization retains an ambient flexible variable while quantifying the
fresh variable of the initialized value. -/
theorem generalizesOnlyFreshVariable
    (context : Solcore.SourceSemantics.Context)
    (ambient fresh : TypeVarId)
    (different : fresh ≠ ambient)
    (blocked : GeneralizationBlockedVariables context = [ambient]) :
    SchemeGeneralizes context {
      quantified := [fresh]
      body := .product (.variable ambient) (.variable fresh)
    } := by
  unfold SchemeGeneralizes
  unfold SchemeGeneralizesExcept
  rw [GeneralizationBlockedVariablesExcept_nil, blocked]
  change [fresh] =
    (if fresh ∈ [ambient] then [ambient] else [ambient] ++ [fresh]).filter
      (fun metavariable => ![ambient].contains metavariable)
  simp [different]

private def qualifiedLocalTemplateId :
    Frontend.SourceInference.RequirementId :=
  ⟨100⟩

private def qualifiedLocalPredicate (fresh : TypeVarId) :
    ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable fresh)

private def qualifiedLocalTemplate (fresh : TypeVarId) :
    Frontend.SourceInference.SolvedRequirement := {
  id := qualifiedLocalTemplateId
  predicate := qualifiedLocalPredicate fresh
  evidence := .assumption (qualifiedLocalPredicate fresh)
}

private def qualifiedLocalRequirement (fresh : TypeVarId) :
    Frontend.SourceInference.LocalSchemeRequirement := {
  templateRequirement := qualifiedLocalTemplateId
  predicate := qualifiedLocalPredicate fresh
}

private def qualifiedLocalBinder
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    Frontend.SourceInference.TypedBinder := {
  id := ⟨owner, 100⟩
  name := "qualified"
  scheme := {
    quantified := [fresh]
    body := .function (.variable fresh) (.variable fresh)
  }
  schemeRequirements := [qualifiedLocalRequirement fresh]
}

private def qualifiedLocalContext
    (signatures : ProgramSignatures) (fresh : TypeVarId) :
    Solcore.SourceSemantics.Context :=
  (Context.ofSignatures signatures).withSolvedRequirements
    [qualifiedLocalTemplate fresh]

private def duplicateQualifiedLocalContext
    (signatures : ProgramSignatures) (fresh : TypeVarId) :
    Solcore.SourceSemantics.Context :=
  (Context.ofSignatures signatures).withSolvedRequirements
    [qualifiedLocalTemplate fresh, qualifiedLocalTemplate fresh]

/-- A qualified local predicate is formed in the initializer scope, where
the scheme variable is admissible and the exact retained assumption row is
identified by its stable template requirement ID. -/
theorem qualifiedLocalRequirementFormation
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    LocalSchemeRequirementWellFormed
      (qualifiedLocalContext signatures fresh)
      (qualifiedLocalBinder owner fresh)
      (qualifiedLocalRequirement fresh) := by
  constructor
  · constructor
    · constructor
      · constructor
        · simp [qualifiedLocalContext, localSchemeInitializerContext,
            qualifiedLocalBinder, Context.ofSignatures,
            Context.withSolvedRequirements, Context.withTypeVariables,
            Context.withAssumptions]
        · intro parameter member
          simp [qualifiedLocalContext, localSchemeInitializerContext,
            qualifiedLocalBinder, Context.ofSignatures,
            Context.withSolvedRequirements, Context.withTypeVariables,
            Context.withAssumptions] at member
      · apply TypeWellScoped.variable
        simp [admissibleTypeVariables, qualifiedLocalContext,
          localSchemeInitializerContext, qualifiedLocalBinder,
          Context.ofSignatures, Context.withSolvedRequirements,
          Context.withTypeVariables, Context.withAssumptions]
    · intro argument member
      simp [qualifiedLocalRequirement, qualifiedLocalPredicate,
        ProgramSignatures.builtinIntPredicate] at member
    · rfl
  · refine ⟨fresh, by simp [qualifiedLocalBinder], ?_⟩
    simp [qualifiedLocalRequirement, qualifiedLocalPredicate,
      ProgramSignatures.builtinIntPredicate,
      Frontend.TypedTraitResolution.predicateVariables,
      TypeSystem.Ty.freeVariables]
  · refine ⟨qualifiedLocalTemplate fresh, ?_, rfl, rfl, rfl⟩
    change [qualifiedLocalTemplate fresh].filter (fun candidate =>
      candidate.id == (qualifiedLocalTemplate fresh).id) =
        [qualifiedLocalTemplate fresh]
    have selected :
        ((qualifiedLocalTemplate fresh).id ==
          (qualifiedLocalTemplate fresh).id) = true :=
      by rfl
    rw [List.filter_cons, if_pos selected]
    rfl

/-- The source-ordered singleton set of qualified predicates satisfies the
binder-level uniqueness and pointwise-formation judgment. -/
theorem qualifiedLocalRequirementsFormation
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    LocalSchemeRequirementsWellFormed
      (qualifiedLocalContext signatures fresh)
      (qualifiedLocalBinder owner fresh) := by
  constructor
  · simp [localSchemeTemplateIds, qualifiedLocalBinder,
      qualifiedLocalRequirement]
  · intro requirement member
    simp [qualifiedLocalBinder] at member
    subst requirement
    exact qualifiedLocalRequirementFormation signatures owner fresh

/-- Abstracting a template requirement removes only that row from the exact
generalization barrier, so its predicate variable can be quantified. -/
theorem qualifiedLocalTemplateIsExemptFromGeneralization
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    SchemeGeneralizesExcept (qualifiedLocalContext signatures fresh)
      (localSchemeTemplateIds (qualifiedLocalBinder owner fresh))
      (qualifiedLocalBinder owner fresh).scheme := by
  have filtered :
      (qualifiedLocalContext signatures fresh).solvedRequirements.filter
          (fun requirement =>
            !(localSchemeTemplateIds
              (qualifiedLocalBinder owner fresh)).contains requirement.id) =
        [] := by
    change [qualifiedLocalTemplate fresh].filter _ = []
    simp only [List.filter_cons, List.filter_nil]
    have contained :
        (localSchemeTemplateIds (qualifiedLocalBinder owner fresh)).contains
            (qualifiedLocalTemplate fresh).id = true := by
      simp [localSchemeTemplateIds, qualifiedLocalBinder,
        qualifiedLocalRequirement, qualifiedLocalTemplate,
        qualifiedLocalTemplateId]
      exact beq_self_eq_true' (qualifiedLocalTemplate fresh).id
    rw [contained]
    rfl
  have blocked :
      GeneralizationBlockedVariablesExcept
          (qualifiedLocalContext signatures fresh)
          (localSchemeTemplateIds (qualifiedLocalBinder owner fresh)) = [] := by
    unfold GeneralizationBlockedVariablesExcept
    rw [filtered]
    simp [qualifiedLocalContext, Context.ofSignatures,
      Context.withSolvedRequirements]
  unfold SchemeGeneralizesExcept
  rw [blocked]
  change [fresh] =
    (if fresh ∈ [fresh] then [fresh] else [fresh] ++ [fresh]).filter
      (fun _ => true)
  simp

/-- The initializer-only assumption scope validates the retained template.
This deliberately does not claim whole-body `RequirementLedgerWellFormed`:
open template rows are integrated with that global judgment in a later step. -/
theorem qualifiedLocalInitializerProvesTemplate
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    RequirementProves
      (localSchemeInitializerContext (qualifiedLocalContext signatures fresh)
        (qualifiedLocalBinder owner fresh))
      qualifiedLocalTemplateId (qualifiedLocalPredicate fresh) := by
  refine ⟨qualifiedLocalTemplate fresh, ?_⟩
  constructor
  · constructor
    · simp [qualifiedLocalContext, localSchemeInitializerContext,
        qualifiedLocalBinder, Context.withSolvedRequirements,
        Context.withTypeVariables, Context.withAssumptions]
    · rfl
  · constructor
    · simp [qualifiedLocalTemplate]
    · unfold qualifiedLocalTemplate
      apply SolvedRequirementValid.intro
      apply RetainedEvidenceValid.intro (.assumption _)
      apply EvidenceValid.assumption
      simp [qualifiedLocalContext, localSchemeInitializerContext,
        qualifiedLocalBinder, qualifiedLocalRequirement,
        Context.ofSignatures, Context.withSolvedRequirements,
        Context.withTypeVariables, Context.withAssumptions]

/-- Duplicate template identities are rejected before use-site
instantiation. -/
theorem duplicateQualifiedLocalTemplatesRejected
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    ¬ LocalSchemeRequirementsWellFormed
      (qualifiedLocalContext signatures fresh)
      { (qualifiedLocalBinder owner fresh) with
        schemeRequirements :=
          [qualifiedLocalRequirement fresh, qualifiedLocalRequirement fresh] } := by
  intro wellFormed
  simpa [localSchemeTemplateIds, qualifiedLocalBinder,
    qualifiedLocalRequirement] using wellFormed.ids_unique

/-- A qualified predicate cannot cite a template row absent from the source
requirement ledger. -/
theorem missingQualifiedLocalTemplateRejected
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    ¬ LocalSchemeRequirementWellFormed
      (Context.ofSignatures signatures)
      (qualifiedLocalBinder owner fresh)
      (qualifiedLocalRequirement fresh) := by
  intro wellFormed
  rcases wellFormed.template with ⟨solved, member, _⟩
  simp [Context.ofSignatures] at member

/-- A template identity denotes exactly one ledger occurrence; duplicating
even an otherwise identical retained row is rejected. -/
theorem duplicateQualifiedLocalLedgerRowsRejected
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    ¬ LocalSchemeRequirementWellFormed
      (duplicateQualifiedLocalContext signatures fresh)
      (qualifiedLocalBinder owner fresh)
      (qualifiedLocalRequirement fresh) := by
  intro wellFormed
  rcases wellFormed.template with ⟨solved, exactOne, _⟩
  change
    [qualifiedLocalTemplate fresh, qualifiedLocalTemplate fresh].filter
      (fun candidate => candidate.id ==
        (qualifiedLocalTemplate fresh).id) = [solved] at exactOne
  have selected :
      ((qualifiedLocalTemplate fresh).id ==
        (qualifiedLocalTemplate fresh).id) = true :=
    by rfl
  rw [List.filter_cons, if_pos selected, List.filter_cons,
    if_pos selected] at exactOne
  have lengths := congrArg List.length exactOne
  simp at lengths

/-- Monomorphic binders cannot smuggle qualified-scheme metadata into
parameter, pattern, or ordinary-let positions. -/
theorem monomorphicQualifiedMetadataRejected
    (context : Solcore.SourceSemantics.Context)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    ¬ BinderWellFormed context owner
      { (qualifiedLocalBinder owner fresh) with scheme := .mono .word } := by
  intro wellFormed
  have empty := wellFormed.monomorphic_requirements_empty (by
    simp [TypeSystem.Scheme.mono])
  simp [qualifiedLocalBinder] at empty

private def generalizedLetExpressionId
    (owner : Resolved.DeclarationId) :
    Frontend.SourceInference.ExpressionId :=
  ⟨⟨owner, 0⟩⟩

private def generalizedLetStatementId
    (owner : Resolved.DeclarationId) :
    Frontend.SourceInference.StatementId :=
  ⟨⟨owner, 1⟩⟩

private def generalizedLetBinder
    (owner : Resolved.DeclarationId) (fresh : TypeVarId)
    (span : Syntax.SourceSpan) : Frontend.SourceInference.TypedBinder := {
  id := ⟨owner, 0⟩
  name := "generalized"
  scheme := {
    quantified := [fresh]
    body := .proxy (.variable fresh)
  }
  span := some span
}

private def generalizedLetSource
    (owner : Resolved.DeclarationId) (fresh : TypeVarId)
    (span : Syntax.SourceSpan) : Frontend.SourceInference.TypedSource := {
  owner
  inputs := []
  roots := [.statement (generalizedLetStatementId owner)]
  nodes := [
    .expression {
      id := generalizedLetExpressionId owner
      span
      type := .proxy (.variable fresh)
      form := .proxy (.variable fresh)
    },
    .statement {
      id := generalizedLetStatementId owner
      span
      type := .unit
      form := .letDecl (generalizedLetBinder owner fresh span)
        (some (generalizedLetExpressionId owner))
    }
  ]
}

/-- A concrete occurrence table containing a polymorphic initialized `let`
is admitted by the dedicated static rule.  The initializer is checked with
the scheme's quantified variable in lexical scope, while the resulting local
is installed in the surrounding context with its rank-1 scheme intact. -/
theorem generalizedInitializedLetHasType
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) (span : Syntax.SourceSpan) :
    StatementHasType (generalizedLetSource owner fresh span)
      { returnType := .unit }
      (Context.ofSignatures signatures)
      (generalizedLetStatementId owner)
      ((Context.ofSignatures signatures).withLocal
        (generalizedLetBinder owner fresh span).id
        (generalizedLetBinder owner fresh span).scheme) {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } := by
  let context := Context.ofSignatures signatures
  let binder := generalizedLetBinder owner fresh span
  let initializer := generalizedLetExpressionId owner
  let statement := generalizedLetStatementId owner
  let source := generalizedLetSource owner fresh span
  have binders : TypeParameterBindersWellFormed context :=
    TypeParameterBindersWellFormed.ofSignatures signatures
  have variableAdmissible :
      TypeAdmissible (context.withTypeVariables [fresh])
        (.variable fresh) := {
    binders := binders.withTypeVariables [fresh]
    typeWellScoped := by
      apply TypeWellScoped.variable
      simp [admissibleTypeVariables, Context.withTypeVariables, context,
        Context.ofSignatures]
  }
  have proxyAdmissible :
      TypeAdmissible (context.withTypeVariables [fresh])
        (.proxy (.variable fresh)) := {
    binders := binders.withTypeVariables [fresh]
    typeWellScoped := .proxy variableAdmissible.typeWellScoped
  }
  have initializerType : ExpressionHasType source
      (context.withTypeVariables [fresh]) initializer
      (.proxy (.variable fresh)) := by
    apply ExpressionHasType.intro
        (node := {
          id := initializer
          span := span
          type := .proxy (.variable fresh)
          form := .proxy (.variable fresh)
        })
        (rawType := .proxy (.variable fresh))
        (plan := .ordinary [])
    · simp [ContainsExpression, source, generalizedLetSource, initializer,
        generalizedLetExpressionId]
    · exact .proxy variableAdmissible
    · rfl
    · exact proxyAdmissible
    · exact proxyAdmissible
    · apply ExpressionRequirementPlan.Valid.ordinary
      · simp [RequirementIdsValid]
      · exact .nil _
      · rfl
  have generalizes : SchemeGeneralizesExcept context
      (localSchemeTemplateIds binder) binder.scheme := by
    simp [SchemeGeneralizesExcept, GeneralizationBlockedVariablesExcept,
      localSchemeTemplateIds, context,
      Context.ofSignatures, binder, generalizedLetBinder,
      TypeSystem.Ty.freeVariables]
  have extension : BinderExtends owner context binder
      (context.withLocal binder.id binder.scheme) := by
    apply BinderExtends.intro
    · refine {
        owned := by simp [binder, generalizedLetBinder]
        scheme := ?_
        quantified_fresh := ?_
        monomorphic_requirements_empty := ?_
      }
      · refine {
          binders
          quantified_nodup := by simp [binder, generalizedLetBinder]
          body := ?_
        }
        apply TypeWellScoped.proxy
        apply TypeWellScoped.variable
        simp [admissibleTypeVariables, context, Context.ofSignatures, binder,
          generalizedLetBinder]
      · intro metavariable quantified
        simp [context, Context.ofSignatures] at quantified ⊢
      · intro quantifiedEmpty
        simp [binder, generalizedLetBinder] at quantifiedEmpty
    · simp [LocalFresh, context, Context.ofSignatures]
  change StatementHasType source { returnType := .unit } context statement
    (context.withLocal binder.id binder.scheme) _
  apply StatementHasType.letInitializedGeneralized
      (node := {
        id := statement
        span := span
        type := .unit
        form := .letDecl binder (some initializer)
      })
      (binder := binder) (initializer := initializer)
  · simp [ContainsStatement, source, generalizedLetSource, statement,
      generalizedLetStatementId, binder, generalizedLetBinder, initializer,
      generalizedLetExpressionId]
  · rfl
  · simp [binder, generalizedLetBinder]
  · exact LocalSchemeRequirementsWellFormed.empty context binder (by
      simp [binder, generalizedLetBinder])
  · exact generalizes
  · simpa [localSchemeInitializerContext, context, binder,
      generalizedLetBinder, Context.withTypeVariables,
      Context.withAssumptions] using initializerType
  · exact extension
  · rfl

/-- The same concrete generalized binding is admitted as a complete unit
body, so the regression also covers root extraction and statement-sequence
typing rather than only the isolated statement constructor. -/
theorem generalizedInitializedLetBodyHasType
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) (span : Syntax.SourceSpan) :
    BodyHasType (generalizedLetSource owner fresh span)
      (Context.ofSignatures signatures) .unit
      (.singleton {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      }) := by
  let source := generalizedLetSource owner fresh span
  let context := Context.ofSignatures signatures
  let statement := generalizedLetStatementId owner
  let final := context.withLocal
    (generalizedLetBinder owner fresh span).id
    (generalizedLetBinder owner fresh span).scheme
  refine ⟨final, ?_, ?_, ?_⟩
  · change StatementsHaveType source { returnType := .unit } context
      [statement] final _
    apply StatementsHaveType.singleton
    exact generalizedInitializedLetHasType signatures owner fresh span
  · intro expression member
    simp [generalizedLetSource] at member
  · simp [BodyCompletes, BodyFacts.singleton, ControlSummary.ordinary]

/-- Closed completion is recovered uniformly from sequence typing and its
retained result annotation; callers do not need to reconstruct the control
summary case by case. -/
theorem generalizedInitializedLetBodyCompletes
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) (span : Syntax.SourceSpan) :
    BodyCompletes .unit
      (.singleton {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      }) := by
  let source := generalizedLetSource owner fresh span
  let context := Context.ofSignatures signatures
  let statement := generalizedLetStatementId owner
  let final := context.withLocal
    (generalizedLetBinder owner fresh span).id
    (generalizedLetBinder owner fresh span).scheme
  have typing : StatementsHaveType source { returnType := .unit } context
      [statement] final
      (.singleton {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      }) := by
    apply StatementsHaveType.singleton
    exact generalizedInitializedLetHasType signatures owner fresh span
  exact typing.bodyCompletes_of_closed rfl rfl

/-- An exact rigid-parameter substitution validates the complete retained
top-level declaration instantiation. -/
theorem genericDeclarationReference
    (context : Solcore.SourceSemantics.Context)
    (signature : ProgramFunctionSignature)
    (signature_mem : signature ∈ context.signatures.functions)
    (substitution : ParameterSubstitution)
    (exact : Solcore.SourceSemantics.ParameterSubstitution.Exact substitution
      signature.scheme.parameters)
    (range : Solcore.SourceSemantics.ParameterSubstitution.RangeWellFormed
      context substitution) :
    ReferenceHasRawType context
      (.declaration {
        declaration := signature.id
        parameterSubstitution := substitution
        type := substitution.apply signature.scheme.body
        predicates := signature.scheme.predicates.map
          (ProgramPredicate.applyParameters substitution)
        parameterComptime := signature.parameterComptime
        returnComptime := signature.returnComptime
      })
      (substitution.apply signature.scheme.body) := by
  apply ReferenceHasRawType.declaration
  exact .intro signature signature_mem rfl exact range.toAdmissible
    rfl rfl rfl rfl

/-- Declarative expression membership determines executable lookup only after
the occurrence-uniqueness invariant is supplied. -/
theorem expressionMembershipLookup
    (source : Frontend.SourceInference.TypedSource)
    (id : Frontend.SourceInference.ExpressionId)
    (node : Frontend.SourceInference.ExpressionNode)
    (unique : NodeOccurrencesUnique source)
    (contains : ContainsExpression source id node) :
    source.lookupExpression? id = some node :=
  lookupExpression?_complete unique contains

/-- Explicit assumption evidence validates without invoking trait search. -/
theorem assumptionEvidenceValid
    (context : Solcore.SourceSemantics.Context)
    (goal : ProgramPredicate) :
    EvidenceValid
      (context.withAssumption goal).assumptions
      (context.withAssumption goal).signatures.resolutionRules
      goal (.assumption goal) := by
  exact .assumption (Context.hasAssumption_withAssumption_self context goal)

/-- A monomorphic builtin implementation head is related to its goal by the
empty exact simultaneous substitution. -/
theorem builtinIntWordHeadInstantiates :
    ImplHeadInstantiates ProgramSignatures.builtinIntWordRule
      (ProgramSignatures.builtinIntPredicate .word) [] := by
  refine .intro { parameters := [], variables := [] } ?_ rfl rfl
  exact ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩

/-- An empty-premise semantic implementation tree is valid when its catalog
rule declaratively instantiates to the goal. -/
theorem emptyPremiseImplementationValid
    (rule : ProgramImplRule) (goal : ProgramPredicate)
    (headInstantiation : ImplHeadInstantiates rule goal []) :
    EvidenceValid [] [rule] goal
      (.implementation goal rule.id []) := by
  exact .implementation (by simp) rfl headInstantiation .nil

/-- The frontend's retained implementation carrier can be related explicitly
to the independently validated semantic evidence tree. -/
theorem builtinIntWordRetainedEvidenceValid :
    RetainedEvidenceValid [] [ProgramSignatures.builtinIntWordRule]
      (ProgramSignatures.builtinIntPredicate .word)
      (.implementation (.byImpl
        (ProgramSignatures.builtinIntPredicate .word)
        ProgramSignatures.builtinIntWordRule.id [])) := by
  apply RetainedEvidenceValid.intro
  · exact .implementation (.byImpl .nil)
  · exact emptyPremiseImplementationValid _ _
      builtinIntWordHeadInstantiates

private def qualifiedLocalActualId :
    Frontend.SourceInference.RequirementId :=
  ⟨101⟩

private def qualifiedLocalActualWord :
    Frontend.SourceInference.SolvedRequirement := {
  id := qualifiedLocalActualId
  predicate := ProgramSignatures.builtinIntPredicate .word
  evidence := .implementation (.byImpl
    (ProgramSignatures.builtinIntPredicate .word)
    ProgramSignatures.builtinIntWordRule.id [])
}

private def qualifiedLocalUseContext
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) : Solcore.SourceSemantics.Context :=
  ((Context.ofSignatures signatures).withSolvedRequirements
      [qualifiedLocalTemplate fresh, qualifiedLocalActualWord]).withLocal
    (qualifiedLocalBinder owner fresh).id
    (qualifiedLocalBinder owner fresh).scheme
    (qualifiedLocalBinder owner fresh).schemeRequirements

private theorem qualifiedLocalUseFormation
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    LocalSchemeRequirementsWellFormed
      (qualifiedLocalUseContext signatures owner fresh)
      (qualifiedLocalBinder owner fresh) := by
  constructor
  · simp [localSchemeTemplateIds, qualifiedLocalBinder,
      qualifiedLocalRequirement]
  · intro requirement member
    simp [qualifiedLocalBinder] at member
    subst requirement
    constructor
    · constructor
      · constructor
        · constructor
          · simp [qualifiedLocalUseContext, localSchemeInitializerContext,
              qualifiedLocalBinder, Context.ofSignatures,
              Context.withSolvedRequirements, Context.withLocal,
              Context.withTypeVariables, Context.withAssumptions]
          · intro parameter parameterMember
            simp [qualifiedLocalUseContext, localSchemeInitializerContext,
              qualifiedLocalBinder, Context.ofSignatures,
              Context.withSolvedRequirements, Context.withLocal,
              Context.withTypeVariables, Context.withAssumptions] at parameterMember
        · apply TypeWellScoped.variable
          simp [admissibleTypeVariables, qualifiedLocalUseContext,
            localSchemeInitializerContext, qualifiedLocalBinder,
            Context.ofSignatures, Context.withSolvedRequirements,
            Context.withLocal, Context.withTypeVariables,
            Context.withAssumptions]
      · intro argument argumentMember
        simp [qualifiedLocalRequirement, qualifiedLocalPredicate,
          ProgramSignatures.builtinIntPredicate] at argumentMember
      · rfl
    · refine ⟨fresh, by simp [qualifiedLocalBinder], ?_⟩
      simp [qualifiedLocalRequirement, qualifiedLocalPredicate,
        ProgramSignatures.builtinIntPredicate,
        Frontend.TypedTraitResolution.predicateVariables,
        TypeSystem.Ty.freeVariables]
    · refine ⟨qualifiedLocalTemplate fresh, ?_, rfl, rfl, rfl⟩
      change
        [qualifiedLocalTemplate fresh, qualifiedLocalActualWord].filter
            (fun candidate => candidate.id ==
              (qualifiedLocalTemplate fresh).id) =
          [qualifiedLocalTemplate fresh]
      rfl

private theorem qualifiedLocalUseSchemeWellFormed
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    SchemeWellFormed (qualifiedLocalUseContext signatures owner fresh)
      (qualifiedLocalBinder owner fresh).scheme := by
  constructor
  · simp [TypeParameterBindersWellFormed, qualifiedLocalUseContext,
      Context.ofSignatures, Context.withSolvedRequirements, Context.withLocal]
  · simp [qualifiedLocalBinder]
  · apply TypeWellScoped.function
    · apply TypeWellScoped.variable
      simp [qualifiedLocalBinder, admissibleTypeVariables,
        qualifiedLocalUseContext, Context.ofSignatures,
        Context.withSolvedRequirements, Context.withLocal]
    · apply TypeWellScoped.variable
      simp [qualifiedLocalBinder, admissibleTypeVariables,
        qualifiedLocalUseContext, Context.ofSignatures,
        Context.withSolvedRequirements, Context.withLocal]

private theorem qualifiedLocalActualWordProves
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    RequirementProves (qualifiedLocalUseContext signatures owner fresh)
      qualifiedLocalActualId
      (ProgramSignatures.builtinIntPredicate .word) := by
  refine ⟨qualifiedLocalActualWord, ?_⟩
  constructor
  · constructor
    · simp [qualifiedLocalUseContext, Context.withLocal,
        Context.withSolvedRequirements]
    · rfl
  · constructor
    · rfl
    · apply SolvedRequirementValid.intro
      apply RetainedEvidenceValid.intro
      · exact .implementation (.byImpl .nil)
      · exact .implementation
          (by simp [ProgramSignatures.resolutionRules,
            ProgramSignatures.builtinResolutionRules])
          rfl builtinIntWordHeadInstantiates .nil

/-- A qualified local reference uses one substitution for both `α → α` and
its ordered `Int<α>` predicate, producing `Word → Word` and `Int<Word>` at the
same occurrence. -/
theorem qualifiedLocalReferenceUseValid
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    ReferenceUseValid (qualifiedLocalUseContext signatures owner fresh)
      (.local (qualifiedLocalBinder owner fresh).id)
      (.function .word .word) [qualifiedLocalActualId] := by
  apply ReferenceUseValid.local
  · exact .head
  · exact .head
  · refine .intro
      (qualifiedLocalUseFormation signatures owner fresh)
      (qualifiedLocalUseSchemeWellFormed signatures owner fresh)
      [(fresh, .word)] (ExactSubstitution.singleton fresh .word) ?_ ?_ ?_ ?_ ?_
    · intro metavariable replacement member
      simp only [List.mem_cons, List.mem_nil_iff, or_false,
        Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact {
        binders := by
          simp [TypeParameterBindersWellFormed, qualifiedLocalUseContext,
            Context.ofSignatures, Context.withSolvedRequirements,
            Context.withLocal]
        typeWellScoped := .builtin .word
      }
    · simp [qualifiedLocalBinder, TypeSystem.Substitution.apply,
        TypeSystem.Substitution.lookup?]
    · simp [qualifiedLocalActualId]
    · intro id actualMember templateMember
      have actualEq : id = qualifiedLocalActualId := by
        simpa using actualMember
      have templateEq : id = qualifiedLocalTemplateId := by
        simpa [localSchemeTemplateIds, qualifiedLocalBinder,
          qualifiedLocalRequirement] using templateMember
      exact (show qualifiedLocalActualId ≠ qualifiedLocalTemplateId by decide)
        (actualEq.symm.trans templateEq)
    · exact .cons (by
        simpa [instantiateLocalSchemePredicates, qualifiedLocalBinder,
          qualifiedLocalRequirement, qualifiedLocalPredicate,
          ProgramSignatures.builtinIntPredicate,
          Frontend.TypedTraitResolution.applySubstitution,
          TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?] using
          (qualifiedLocalActualWordProves signatures owner fresh)) .nil

/-- Repeating one actual requirement identity cannot fabricate a two-item
qualified evidence spine. -/
theorem duplicateLocalActualRequirementsRejected
    (context : Solcore.SourceSemantics.Context)
    (binder : Frontend.SourceInference.TypedBinder)
    (type : Ty) (requirement : Frontend.SourceInference.RequirementId) :
    ¬ LocalSchemeInstantiationValid context binder type
      [requirement, requirement] := by
  intro valid
  simpa using valid.actual_requirements_nodup

/-- An initializer-only template identity cannot be recycled as evidence for
the corresponding local use. -/
theorem localTemplateCannotBeActualRequirement
    (context : Solcore.SourceSemantics.Context)
    (binder : Frontend.SourceInference.TypedBinder)
    (type : Ty) (template : Frontend.SourceInference.RequirementId)
    (templateMember : template ∈ localSchemeTemplateIds binder) :
    ¬ LocalSchemeInstantiationValid context binder type [template] := by
  intro valid
  exact valid.actual_templates_disjoint template (by simp) templateMember

/-- With a unique ledger, reversing two distinct actual evidence IDs cannot
validate an ordered two-predicate local-scheme instance. -/
theorem reversedLocalActualRequirementsRejected
    (context : Solcore.SourceSemantics.Context)
    (binder : Frontend.SourceInference.TypedBinder) (type : Ty)
    (firstId secondId : Frontend.SourceInference.RequirementId)
    (firstPredicate secondPredicate : ProgramPredicate)
    (ledger : RequirementLedgerWellFormed context)
    (different : firstPredicate ≠ secondPredicate)
    (ordered : ∀ substitution,
      ExactSubstitution substitution binder.scheme.quantified →
        instantiateLocalSchemePredicates substitution binder =
          [firstPredicate, secondPredicate])
    (_firstProves : RequirementProves context firstId firstPredicate)
    (secondProves : RequirementProves context secondId secondPredicate) :
    ¬ LocalSchemeInstantiationValid context binder type [secondId, firstId] := by
  intro valid
  rcases valid.has_shared_substitution with
    ⟨substitution, exact, _, _, proves⟩
  rw [ordered substitution exact] at proves
  have reversedHead : RequirementProves context secondId firstPredicate :=
    proves.head
  have predicatesEq :=
    ledger.proves_predicate_eq secondProves reversedHead
  exact different predicatesEq.symm

/-- A contextual assumption can discharge a nested where premise, rather than
being restricted to the root of the evidence tree. -/
theorem assumedPremiseImplementationValid
    (rule : ProgramImplRule)
    (goal premise : ProgramPredicate)
    (headInstantiation : ImplHeadInstantiates rule goal [premise]) :
    EvidenceValid [premise] [rule] goal
      (.implementation goal rule.id [.assumption premise]) := by
  exact .implementation (by simp) rfl headInstantiation
    (.cons (.assumption (by simp)) .nil)

/-- A solved requirement carrying explicit assumption evidence is validated by
the independent source judgment. -/
example (context : Solcore.SourceSemantics.Context)
    (goal : ProgramPredicate)
    (requirementId : Frontend.SourceInference.RequirementId) :
    SolvedRequirementValid (context.withAssumption goal) {
      id := requirementId
      predicate := goal
      evidence := .assumption goal
    } := by
  apply SolvedRequirementValid.intro
  exact RetainedEvidenceValid.intro (.assumption goal)
    (assumptionEvidenceValid context goal)

/-- Entailment exposes evidence whose stored goal is the requested goal. -/
example (context : Solcore.SourceSemantics.Context)
    (goal : ProgramPredicate) :
    ∃ evidence,
      EvidenceValid
        (context.withAssumption goal).assumptions
        (context.withAssumption goal).signatures.resolutionRules
        goal evidence ∧
      evidence.goal = goal := by
  let valid := assumptionEvidenceValid context goal
  exact ⟨.assumption goal, valid, valid.evidence_goal_eq⟩

/-- Canonical defaults are source values with the exact declared type. -/
example :
    Dynamic.DefaultValue (.product .bool .integer)
      (.product (.bool false) (.integer 0)) := by
  exact .product .bool .integer

/-- Mathematical integer primitives include the operations which have no
fixed-width Core interpretation. -/
example :
    Dynamic.BinaryPrimitiveApplies .add
      (.integer 19) (.integer 23) (.integer 42) := by
  exact .integerAdd 19 23

/-- Lazy Boolean source operators need not evaluate an unselected operand. -/
example :
    Dynamic.ShortCircuits .logicalAnd (.bool false) (.bool false) := by
  exact .andFalse

/-- Multi-argument calls use the same right-associated product convention as
source types. -/
example :
    Dynamic.ValuesPack [.integer 1, .bool true]
      (.product (.integer 1) (.bool true)) := by
  exact .cons (.singleton (.bool true))

/-- A deferred input dominates a collection with no runtime input. -/
example :
    Staging.StagesJoin [.comptime, .deferred] .deferred := by
  exact .deferred (by simp) (by simp)

/-- Only the closed residual-data fragment crosses the materialization
boundary. -/
example :
    Staging.Materializes
      (.product (.bool true) (.word Core.Word.zero))
      (.product (.bool true) (.word Core.Word.zero)) := by
  exact .product (.bool true) (.word Core.Word.zero)

theorem integerDoesNotMaterialize (value : Int) :
    ¬ Staging.Materializable (.integer value) := by
  intro admitted
  cases admitted

/-- A retained, requirement-free literal occurrence executes directly under
the declarative big-step relation; no frontend evaluator result is a premise. -/
theorem literalExpressionEvaluates
    (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment)
    (source : Frontend.SourceInference.TypedSource)
    (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) (id : Frontend.SourceInference.ExpressionId)
    (node : Frontend.SourceInference.ExpressionNode)
    (literal : Syntax.CoreLiteralValue) (value : Dynamic.Value)
    (contains : ContainsExpression source id node)
    (form_eq : node.form =
      Frontend.SourceInference.ExpressionForm.literal literal)
    (requirements_eq : node.requirements = [])
    (coercions_eq : node.coercions = [])
    (constructs : Dynamic.LiteralConstructs literal value) :
    Dynamic.ExpressionEvaluates program context evidence source environment
      heap id value heap := by
  apply Dynamic.ExpressionEvaluates.intro contains
  · rw [form_eq, requirements_eq, coercions_eq]
    exact .literal rfl constructs
  · rw [coercions_eq]
    exact .nil

end Solcore.Test.SourceSemantics
end
