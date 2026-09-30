import Solcore.SourceSemantics.CoreLowering.GenericHeap
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes

/-! Source lexical presence is separate from the compiler scope: generated
hidden slots have Core references but are absent from the source environment.
This invariant supplies only first-match source locations, not value typing,
source body correctness or permission to read an uninitialized cell. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericLexicalContext
open Frontend Frontend.SourceInference

def LocalsPresent (context : Context) (environment : Dynamic.Environment) : Prop :=
  ∀ {id scheme}, (id, scheme) ∈ context.locals → ∃ location, Dynamic.Environment.LooksUp environment id location

theorem LocalsPresent.empty (signatures : ProgramSignatures) (environment : Dynamic.Environment) :
    LocalsPresent (Context.ofSignatures signatures) environment := by
  intro id scheme member
  cases member

theorem LocalsPresent.bind {context : Context} {environment : Dynamic.Environment}
    (present : LocalsPresent context environment) (binder : TypedBinder) (location : Dynamic.Location) :
    LocalsPresent (context.withLocal binder.id binder.scheme binder.schemeRequirements) ((binder.id, location) :: environment) := by
  intro id scheme member
  by_cases same : binder.id = id
  · subst id
    exact ⟨location, .head⟩
  · have old : (id, scheme) ∈ context.locals := by
      simp only [Context.withLocal, List.mem_cons] at member
      rcases member with equal | member
      · exact False.elim (same (congrArg Prod.fst equal).symm)
      · exact member
    obtain ⟨found, lookup⟩ := present old
    exact ⟨found, .tail same lookup⟩

theorem LocalsPresent.binders {owner : Resolved.DeclarationId} {context finalContext : Context}
    {environment finalEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    {binders : List TypedBinder} {values : List Dynamic.Value}
    (present : LocalsPresent context environment)
    (extended : BindersExtend owner context binders finalContext)
    (allocated : Dynamic.BindersAllocate environment before binders values finalEnvironment after) :
    LocalsPresent finalContext finalEnvironment := by
  induction extended generalizing environment before values with
  | nil => cases allocated; exact present
  | cons head tail ih =>
    cases head
    cases allocated with
    | cons _ allocated => exact ih (present.bind _ _) allocated

/-- Pattern typing certifies every allocated arm binder as monomorphic without
assuming that the scrutinee value has a separate source value-typing proof. -/
theorem arm_monomorphic {source : TypedSource} {control : ControlContext} {context : Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase} {caseFacts : List BodyFacts}
    {fallback : Option (List StatementId)} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)}
    (typed : MatchCasesHaveType source control context scrutineeType cases caseFacts)
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.arm body bindings)) :
    ∀ binder, binder ∈ bindings.map Prod.fst → binder.scheme.quantified = [] := by
  cases selected with
  | head matched =>
    cases typed with
    | cons head tail =>
      cases head with
      | intro patternTyped extended bodyTyped =>
        rw [DataMatchSourceScopes.PatternMatches.binders patternTyped matched]
        exact Dynamic.TypedMatchPatternHasType.patternBinders_monomorphic patternTyped
  | tail notMatched selected =>
    cases typed with
    | cons head tail => exact arm_monomorphic tail selected
termination_by cases.length
decreasing_by simp_all

/-- Allocation retains the metadata of all previously existing source cells. -/
theorem binders_metadata {environment finalEnvironment : Dynamic.Environment}
    {before after : Dynamic.Heap} {binders : List TypedBinder} {values : List Dynamic.Value}
    (allocated : Dynamic.BindersAllocate environment before binders values finalEnvironment after) :
    Dynamic.HeapMetadataExtend before after := by
  induction allocated with
  | nil => exact .refl _
  | cons allocation tail ih => exact (Dynamic.HeapMetadataExtend.of_allocation allocation).trans ih

/-- Exact source environment/storage agreement survives the source-order arm
allocations. Pattern typing supplies the monomorphic binder premise. -/
theorem binders_agree {owner : Resolved.DeclarationId} {context finalContext : Context}
    {environment finalEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    {binders : List TypedBinder} {values : List Dynamic.Value}
    (extension : BindersExtend owner context binders finalContext)
    (monomorphic : ∀ binder, binder ∈ binders → binder.scheme.quantified = [])
    (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (allocated : Dynamic.BindersAllocate environment before binders values finalEnvironment after) :
    Dynamic.EnvironmentAgrees after finalContext.locals finalEnvironment := by
  induction allocated generalizing context finalContext with
  | nil => cases extension; exact agrees
  | cons allocation tail ih =>
    cases extension with
    | cons head rest =>
      cases head
      exact ih rest (fun binder member => monomorphic binder (by simp [member]))
        (.cons allocation.reads_new rfl (.ordinary (monomorphic _ (by simp)) rfl)
          (agrees.mono (.of_allocation allocation)))

end Solcore.SourceSemantics.CoreLowering.GenericLexicalContext
