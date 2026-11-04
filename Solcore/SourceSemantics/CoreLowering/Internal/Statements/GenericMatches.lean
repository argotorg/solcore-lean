import Solcore.SourceSemantics.CoreLowering.Internal.Data.Matches
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GenericHeaps
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopLayouts

/-!
# Generic matches

Allocation, prefixes, scrutinee, selection and meaning of matches.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericMatchAllocation
/-! Generic-heap continuation correspondence for the binder-allocation prefix emitted
by bindArm. The proof constructs source allocation and follows the actual Core
let/case temporaries. The continuation is arbitrary: no exact closure-renaming
or first-order-store theorem is assumed for the selected arm's body. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchAllocation
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreDataMatches DataPatternBindings DataPatternValues DataEquality CoreProof
open ReadOnly

open DataMatchCoreAllocation

/-- Inclusion of the authenticated finite pattern values in an arbitrary
world-indexed payload model. It does not authenticate non-finite payloads or
assert any source function-call semantics. -/
def IncludesFinite {catalog : SourceCoreDataCatalog.Catalog} (signatures : ProgramSignatures)
    (model : GenericHeap.PayloadModel catalog) : Prop :=
  ∀ {mapping world sourceType source value payload},
    catalog.project sourceType = .ok payload →
    DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value →
    model.Represents mapping world sourceType source value payload

theorem finite_includes {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures} :
    IncludesFinite signatures (GenericHeap.finitePayload catalog signatures) := fun projection represented =>
  ⟨projection, represented⟩

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var lookup => exact .var (agrees lookup)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index foundValue found
  exact agrees found

/-- Both directions of the generated allocation prefix reach the same related
heap and continuation. The continuation's execution is not a premise: wrap and
unwrap quantify over every finite continuation evaluation. -/
theorem BindingsRep.prefix {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {model : GenericHeap.PayloadModel catalog} (includes : IncludesFinite signatures model)
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {κ ξ : Renaming}
    {start : Nat} {allTypes : List Ty} {allValues : List Value} {outputType : Ty} {tail : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree κ canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (bundleSlot : logical[start]? = some (packValues allValues))
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (sources.map Prod.fst) (sources.map Prod.snd)
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (liftMany bindings.length κ) finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      ContinuationAgreement actual store ((allocationCode bindings start allTypes outputType tail).rename ξ)
        finalActual finalStore (tail.rename finalEmbedding) := by
  induction represented generalizing mapping world scope environment canonical logical actual heap store κ ξ start with
  | nil =>
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, sourceLayout, actualLayout, .refl _ _ _⟩
  | @cons binder payload sourceValue value bindings sources values projection head rest ih =>
    have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
    have projectionPath := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
    have initializer : Evaluates actual store
        ((LanguageResult.success (SourceCoreDataExpressions.projectPacked start allTypes (.var start))).rename ξ)
        (.inRight .word value) store := .inRight ((selects_rename projectionPath actualLayout).evaluates store)
    let reference := Value.cellRef (OptionalCell.cellType payload) store.length
    obtain ⟨nextEnvironments, nextHeaps⟩ := GenericHeap.bind (id := binder.id) environments heaps (.initialized (includes projection head))
      (Dynamic.Heap.Allocates.append (type := binder.scheme.body) (value := some sourceValue))
    have nextSourceLayout : EnvironmentsAgree κ.lift (reference :: canonical) (reference :: logical) := sourceLayout.lift reference
    have insertedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) :=
      agree_insert actualLayout value
    have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
        (reference :: logical) (reference :: value :: actual) := insertedLayout.lift reference
    have nextSelected : ∀ {index selectedValue}, values[index]? = some selectedValue →
        allValues[(start + 1) + index]? = some selectedValue := by
      intro index selectedValue found
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
    obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
      finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
      finalSourceLayout, finalActualLayout, agreement⟩ :=
      ih nextEnvironments nextHeaps nextSourceLayout nextActualLayout
        (show (reference :: logical)[start + 1]? = some (packValues allValues) from bundleSlot) nextSelected
    refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnv, finalHeapRep,
      (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      (AdministrativePreserved.allocate mapping store (.inRight .unit value)).trans frame,
      finalSourceLayout, finalActualLayout, ?_⟩
    have allocation : Evaluates (value :: actual) store (OptionalCell.allocateInitialized payload (.var 0))
        reference (store ++ [.inRight .unit value]) := OptionalCell.allocateInitialized_evaluates (.var rfl)
    simp only [LoopStatements.rename_insert_lift] at agreement
    simp only [allocationCode, List.zipIdx_cons, List.foldr_cons, LoopRenaming.letInitialized]
    apply ContinuationAgreement.trans ?_ agreement
    exact (ContinuationAgreement.bind initializer).trans (ContinuationAgreement.letE allocation)
private theorem liftMany_twoInsertions (count cutoff : Nat) :
    liftMany count (Renaming.comp (Renaming.insertion cutoff) (Renaming.insertion cutoff)) =
      Renaming.comp (Renaming.insertion (cutoff + count)) (Renaming.insertion (cutoff + count)) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [liftMany, Renaming.lift_comp, Renaming.lift_insertion, ih]
    congr 2 <;> omega

/-- This is exactly the successful branch emitted by `attempt`, including its
two hidden lexical slots. The result relates the arm's ordinary lexical scope
to its actual Core environment and transforms the body syntax with the same
embedding. Both finite evaluation directions retain the exact final store. -/
theorem bindArm_prefix {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {model : GenericHeap.PayloadModel catalog} (includes : IncludesFinite signatures model)
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {scrutinee : Value} {outputType : Ty} {body : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (sources.map Prod.fst) (sources.map Prod.snd)
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store
        ((bindArm bindings outputType (body.weakenAt bindings.length)).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  let κ := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
  have sourceLayout : EnvironmentsAgree κ canonical (packValues values :: scrutinee :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by
    simpa using DataPatternExecution.BindingsRep.length represented.erase
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
    finalSourceLayout, finalActualLayout, agreement⟩ :=
    BindingsRep.prefix includes represented (tail := (body.weakenAt bindings.length).weakenAt bindings.length)
      environments heaps sourceLayout actualLayout (start := 0) rfl length
      (fun {_ _} found => by simpa using found)
  refine ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, Renaming.comp finalEmbedding (liftMany bindings.length κ), allocated, finalEnv,
    finalHeapRep, maps, worlds, frame, ?_, ?_⟩
  · intro index value found
    exact finalActualLayout (finalSourceLayout found)
  · have same : ((body.weakenAt bindings.length).weakenAt bindings.length).rename finalEmbedding =
        body.rename (Renaming.comp finalEmbedding (liftMany bindings.length κ)) := by
      simp only [κ, liftMany_twoInsertions, Nat.zero_add]
      rw [← Expr.rename_insertion, ← Expr.rename_insertion, Expr.rename_comp, Expr.rename_comp]
      rfl
    rw [same] at agreement
    exact agreement

end Solcore.SourceSemantics.CoreLowering.GenericMatchAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericLexicalContext
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericMatchPrefix
/-! Under an arbitrary payload model containing the finite pattern values, the
emitted ordered match branches reach exactly the selected arm/default
continuation, allocating only the successful arm's binders. This is a complete
prefix correspondence (wrap and unwrap), not a supplied child evaluation. The
selected body's own statement correspondence is a separate structural proof. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchPrefix
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreDataMatches DataPatternValues DataPatternLeaves DataPatternExecution
open DataMatchCertificates DataMatchDecision CoreProof ReadOnly

open DataMatchBranchPrefix GenericMatchAllocation

private theorem case_right {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  constructor
  · intro result finalStore body; exact .caseRight evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_right evaluated
    exact body.sound

private theorem case_left {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {rightType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inLeft rightType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle left := by
  constructor
  · intro result finalStore body; exact .caseLeft evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_left evaluated
    exact body.sound

/-- The entire attempted-arm fold has no other finite result than execution
of its selected, related continuation. The initial store may contain arbitrary
typed administrative functions, and the body itself is unrestricted syntax. -/
theorem Decision.prefix {compilation : DataPatternCertificates.Compilation} {context : SourceSemantics.Context}
    {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection)
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (value :: canonical) actual) :
    ∃ finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding body,
      SelectedBody bodyCertificate scope environment heap resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents compilation.checked.catalog finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store
        ((arms.foldr (fun (pattern, body) next => attempt pattern (LocalLoop.controlType resultType) body next)
          (fallbackCode.weakenAt 0)).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  induction decision generalizing actual ξ with
  | @head arm rest pattern body arms fallback fallbackCode bindings values matched bindingsRepresented runs certified =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have matchedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inRight .unit (packValues values)) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact runs actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, agreement⟩ :=
        GenericMatchAllocation.bindArm_prefix includes bindingsRepresented environments heaps (actualLayout.lift (packValues values))
      exact ⟨_, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, body, .arm (DataMatchAllocation.BindingsRep.binders bindingsRepresented) allocated certified,
        finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, (case_right matchedCore).trans agreement⟩
  | @tail arm rest pattern body arms fallback fallbackCode selection notMatched fails next ih =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have failedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inLeft (bundleType pattern.bindingTypes) .unit) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact fails actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ)
          (value :: canonical) (.unit :: actual) := by
        intro index foundValue found
        exact actualLayout found
      obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, agreement⟩ :=
        ih tail nextLayout
      refine ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, ?_⟩
      simp only [LoopStatements.rename_insert] at agreement
      simp only [List.foldr_cons, attempt, Expr.rename, LoopRenaming.weakenZero]
      exact (case_left failedCore).trans agreement
  | default certified =>
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), _, .default certified, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [List.foldr_nil, ← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _
  | noBranch =>
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), _, .noBranch, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [List.foldr_nil, ← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _

end Solcore.SourceSemantics.CoreLowering.GenericMatchPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericMatchScrutinee
/-! The successful scrutinee prefix of the actual match layout. This allocates
the hidden source cell once, keeps it out of the source lexical environment,
and reaches the independently selected branch. A child expression's finite
evaluation is an explicit compositional boundary; this module does not assert
that arbitrary source expressions terminate or that their compiler is sound. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchScrutinee
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open DataMatchCertificates DataMatchDecision DataMatchBranchPrefix GenericMatchAllocation
open SourceCoreDataMatches

private theorem case_right {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  constructor
  · intro result finalStore body; exact .caseRight evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_right evaluated
    exact body.sound

/-- Exact lexical layout after the scrutinee result, hidden optional cell and
loaded value. Its syntax is the compiler's existing letInitialized/case fold. -/
theorem initialized_prefix {actual : Environment} {before middle : Store}
    {computation branches : Expr} {outputType payload : Ty} {value : Value}
    {internalReason : Word} {ξ : Renaming}
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) middle) :
    ContinuationAgreement actual before
      ((LocalSequence.letInitialized outputType payload computation
        (.caseE (.loadCell (.var 0)) (LanguageResult.failure outputType (.word internalReason)) branches)).rename ξ)
      (value :: .cellRef (OptionalCell.cellType payload) middle.length :: value :: actual)
      (middle ++ [.inRight .unit value])
      (branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) := by
  rw [LoopRenaming.letInitialized]
  unfold LocalSequence.letInitialized
  apply (ContinuationAgreement.bind evaluated).trans
  have allocation : Evaluates (value :: actual) middle (OptionalCell.allocateInitialized payload (.var 0))
      (.cellRef (OptionalCell.cellType payload) middle.length) (middle ++ [.inRight .unit value]) :=
    OptionalCell.allocateInitialized_evaluates (.var rfl)
  apply (ContinuationAgreement.letE allocation).trans
  simp only [← Expr.rename_insertion, Expr.rename_comp, Expr.rename]
  have loaded : Evaluates (.cellRef (OptionalCell.cellType payload) middle.length :: value :: actual)
      (middle ++ [.inRight .unit value]) (.loadCell (.var 0)) (.inRight .unit value)
      (middle ++ [.inRight .unit value]) :=
    .loadCell (.var rfl) (Store.allocate_fresh_lookup middle (.inRight .unit value))
  simpa [Renaming.lift_comp, Renaming.lift, Renaming.insertion] using
    (case_right (left := (LanguageResult.failure outputType (.word internalReason)).rename
      (Renaming.comp (Renaming.insertion 1) ξ.lift).lift)
      (right := branches.rename (Renaming.comp (Renaming.insertion 1) ξ.lift).lift) loaded)

/-- A successful scrutinee plus static match certificates constructs source
selection, the hidden and arm allocations, and a two-way continuation
agreement. There is no selected-body evaluation premise. -/
theorem success_prefix
    {compilation : DataPatternCertificates.Compilation} {context : SourceSemantics.Context}
    {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {source : TypedSource} {id : StatementId} {resolution : MatchResolution} {scope : Scope}
    {scrutineeNode : ExpressionNode} {payload resultType : Ty} {computation : Expr}
    {bodyCertificate : BodyCertificate} {arms : List (Pattern × Expr)} {fallback : Expr} {internalReason : Word}
    (fresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) = false)
    (projection : compilation.checked.catalog.project scrutineeNode.type = .ok payload)
    (armsCertified : Arms compilation source id ((resolution.hiddenScrutinee, payload) :: scope)
      scrutineeNode.type bodyCertificate resolution.cases arms)
    (fallbackCertified : Fallback bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope)
      resultType resolution.defaultBody fallback)
    (valid : DataPatternLeaves.ContextValid compilation context)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {before store : Store} {ξ : Renaming}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : DataPatternTypedValues.TypedValueRep compilation.checked.catalog compilation.signatures
      scrutineeNode.type sourceValue value)
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext
      scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding body,
      Dynamic.Heap.Allocates heap scrutineeNode.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents compilation.checked.catalog finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual before
        ((LocalSequence.letInitialized (LocalLoop.controlType resultType) payload computation
          (.caseE (.loadCell (.var 0))
            (LanguageResult.failure (LocalLoop.controlType resultType) (.word internalReason))
            (arms.foldr (fun (pattern, body) next => attempt pattern (LocalLoop.controlType resultType) body next)
              (fallback.weakenAt 0)))).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenEnv, hiddenHeapRep⟩ := GenericHeap.bind_internal environments heaps fresh
    (.initialized (includes projection represented)) (Dynamic.Heap.Allocates.append (value := some sourceValue))
  obtain ⟨selection, decision⟩ := DataMatchDecision.Arms.decides armsCertified fallbackCertified valid represented
  let reference := Value.cellRef (OptionalCell.cellType payload) store.length
  have hiddenLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
      (value :: reference :: canonical) (value :: reference :: value :: actual) := by
    intro index foundValue found
    cases index with
    | zero => exact found
    | succ index => cases index with
      | zero => exact found
      | succ index => exact layout found
  obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, body, selected, finalEnv, finalHeapRep, maps, worlds, frame,
    finalLayout, agreement⟩ :=
    GenericMatchPrefix.Decision.prefix includes decision armsCertified hiddenEnv hiddenHeapRep hiddenLayout
  exact ⟨_, _, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, body, .append, decision.source, selected, finalEnv, finalHeapRep,
    (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
    (show WorldExtends world (world ++ [OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
    (AdministrativePreserved.allocate mapping store (.inRight .unit value)).trans frame,
    finalLayout, (initialized_prefix evaluated).trans agreement⟩

end Solcore.SourceSemantics.CoreLowering.GenericMatchScrutinee
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericMatchMeaning
/-! A compositional match reflection interface. Child obligations are universal
semantic theorems for their static compiler certificates, not supplied source
executions. The match theorem constructs its source trace from Core evaluation.
This does not instantiate a general function compiler theorem: expression and
statement child correspondences remain explicit obligations. Pattern inputs
remain in the authenticated finite-value profile; unrelated heap payloads may
use the full supplied world-indexed model. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchMeaning
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open DataMatchCertificates DataMatchDecision DataMatchBranchPrefix GenericMatchAllocation
open SourceCoreDataMatches GenericLexicalContext

abbrev FaultRep := Dynamic.SemanticFault → Word → Prop

inductive ExpressionOutcomeRepresents (catalog : SourceCoreDataCatalog.Catalog)
    (signatures : ProgramSignatures) (sourceType : TypeSystem.Ty) (payload : Ty) (faults : FaultRep) :
    Dynamic.ExpressionOutcome → Value → Prop where
  | value {source value}
      (represented : DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value) :
      ExpressionOutcomeRepresents catalog signatures sourceType payload faults (.value source) (.inRight .word value)
  | fault {reason token} (represented : faults reason token) :
      ExpressionOutcomeRepresents catalog signatures sourceType payload faults (.fault reason) (.inLeft payload (.word token))

inductive OutcomeRepresents {catalog : SourceCoreDataCatalog.Catalog} (model : GenericHeap.PayloadModel catalog)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty) (type : Ty) (faults : FaultRep) :
    Dynamic.ControlOutcome → Value → Prop where
  | fallthrough (environment) : OutcomeRepresents model mapping world sourceType type faults
      (.fallthrough environment) (.inRight .word (.inLeft LocalLoop.transferType (.inLeft type .unit)))
  | returned {source value} (represented : model.Represents mapping world sourceType source value type) :
      OutcomeRepresents model mapping world sourceType type faults (.returned source)
        (.inRight .word (.inLeft LocalLoop.transferType (.inRight .unit value)))
  | breaking (environment) : OutcomeRepresents model mapping world sourceType type faults (.breaking environment)
      (.inRight .word (.inRight (LocalControl.controlType type) (.inLeft .unit .unit)))
  | continuing (environment) : OutcomeRepresents model mapping world sourceType type faults (.continuing environment)
      (.inRight .word (.inRight (LocalControl.controlType type) (.inRight .unit .unit)))
  | fault {reason token} (represented : faults reason token) :
      OutcomeRepresents model mapping world sourceType type faults (.fault reason) (.inLeft (LocalLoop.controlType type) (.word token))

theorem OutcomeRepresents.restore {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {outcome : Dynamic.ControlOutcome} {value : Value}
    (represented : OutcomeRepresents model mapping world sourceType type faults outcome value)
    (environment : Dynamic.Environment) :
    OutcomeRepresents model mapping world sourceType type faults (Dynamic.restoreControl environment outcome) value := by
  cases represented with
  | fallthrough => exact .fallthrough _
  | returned value => exact .returned value
  | breaking => exact .breaking _
  | continuing => exact .continuing _
  | fault value => exact .fault value

/-- The expression compiler's universally quantified reflection obligation.
It includes exact source metadata type, effects, heap correspondence, map/world
extension and preservation of pre-existing administrative cells. -/
def ExpressionReflects (compilation : DataPatternCertificates.Compilation)
    (model : GenericHeap.PayloadModel compilation.checked.catalog) (program : Program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : ExpressionCertificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      ExpressionOutcomeRepresents compilation.checked.catalog compilation.signatures node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- The selected-body compiler's universal reflection obligation. Its source
context is supplied by independent declarative statement typing. There is no
premise giving a source body evaluation. -/
def BodyReflects (compilation : DataPatternCertificates.Compilation)
    (model : GenericHeap.PayloadModel compilation.checked.catalog) (program : Program)
    (control : ControlContext) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : BodyCertificate) (resultSource : TypeSystem.Ty) (resultType : Ty) (faults : FaultRep) : Prop :=
  ∀ {scope statements code}, certificate scope statements code →
  ∀ {context staticFinal facts}, StatementsHaveType source control context statements staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (code.rename ξ) value finalStore →
    ∃ finalContext outcome after finalMap finalWorld,
      Dynamic.StatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

private theorem read_contains {checked : SourceCoreDataCatalog.Checked} {source : TypedSource} {id : StatementId}
    {node : StatementNode} {type : Ty}
    (read : SourceCoreGeneralTypes.readStatement checked source id = .ok (node, type)) : ContainsStatement source id node := by
  by_cases owned : id.occurrence.owner = source.owner
  · simp only [SourceCoreGeneralTypes.readStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte,
      pure, Except.pure, bind, Except.bind] at read
    cases found : source.lookupStatement? id with
    | none => simp [found] at read
    | some selected =>
      simp only [found] at read
      cases projected : SourceCoreGeneralTypes.projectType checked (.occurrence id.occurrence) selected.type with
      | error => simp [projected] at read
      | ok projectedType =>
        simp only [projected, Except.ok.injEq, Prod.mk.injEq] at read
        rcases read with ⟨rfl, rfl⟩
        exact lookupStatement?_sound found
  · simp [SourceCoreGeneralTypes.readStatement, owned, bind, Except.bind] at read

private theorem initial_evaluation {actual : Environment} {before after : Store}
    {code body : Expr} {type payload : Ty} {ξ : Renaming} {result : Value}
    (evaluation : Evaluates actual before ((LocalSequence.letInitialized type payload code body).rename ξ) result after) :
    ∃ value middle, Evaluates actual before (code.rename ξ) value middle := by
  rw [LoopRenaming.letInitialized] at evaluation
  cases evaluation with
  | caseLeft evaluated _ => exact ⟨_, _, evaluated⟩
  | caseRight evaluated _ => exact ⟨_, _, evaluated⟩

private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ next => exact default_selected next
termination_by cases.length
decreasing_by simp_all

/-- Core-only reflection for one accepted match certificate. Expression and
body compiler correctness are explicit universal induction hypotheses. The
source scrutinee trace, arm choice and binder allocations are all constructed.
The result carries effects and restores the match's entry lexical scope. -/
theorem Certificate.reflects
    {compilation : DataPatternCertificates.Compilation} {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {program : Program} {context : SourceSemantics.Context} {control : ControlContext}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultSource : TypeSystem.Ty} {resultType : Ty}
    {internalReason : Word} {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    {faults : FaultRep} {code : Expr}
    (certificate : DataMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (expressionMeaning : ExpressionReflects compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyReflects compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {result : Value}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.rename ξ) result finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome result ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases certificate with
  | @matchWith node statementType certifiedNode payload computation arms fallback read allowed form requirements
      hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression sameType armsCertified fallbackCertified =>
    have same := Option.some.inj (found.symm.trans scrutineeFound)
    subst certifiedNode
    have contains := read_contains read
    have scrutineeContains := lookupExpression?_sound found
    obtain ⟨value, middleStore, initialEval⟩ := initial_evaluation evaluated
    obtain ⟨sourceOutcome, middleHeap, middleMap, middleWorld, sourceEval, outcomeRep,
      middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
      expressionMeaning expression found environments heaps locals layout initialEval
    cases outcomeRep with
    | @fault reason token faultRepresented =>
      cases sourceEval with
      | fault sourceFault =>
        have failed : Evaluates actual store
            ((LocalSequence.letInitialized (LocalLoop.controlType resultType) payload computation.expression
              (.caseE (.loadCell (.var 0))
                (LanguageResult.failure (LocalLoop.controlType resultType) (.word internalReason))
                (arms.foldr (fun (pattern, body) next => attempt pattern (LocalLoop.controlType resultType) body next)
                  (fallback.weakenAt 0)))).rename ξ)
            (.inLeft (LocalLoop.controlType resultType) (.word token)) middleStore := by
          rw [LoopRenaming.letInitialized]
          exact LocalSequence.letInitialized_failure _ _ (by simpa only [← sameType] using initialEval)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated failed
        exact ⟨_, middleHeap, middleMap, middleWorld, .fault (.matchScrutinee contains form sourceFault),
          .fault faultRepresented, middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata⟩
    | @value sourceValue value represented =>
      cases sourceEval with
      | value sourceEval =>
        obtain ⟨hiddenHeap, location, selection, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
          selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
          hiddenAllocated, selected, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
          secondFrame, selectedLayout, agreement⟩ :=
          GenericMatchScrutinee.success_prefix includes hiddenFresh (DataPatternBindings.projected_raw projection)
            armsCertified fallbackCertified valid represented (environments.extend firstMaps firstWorlds)
            middleRelated layout initialEval
        have bodyEval := agreement.unwrap evaluated
        cases selectedBody with
        | @arm statements bindings compiledBindings finalEnvironment finalHeap body binders allocated bodyCertified =>
          obtain ⟨armContext, staticFinal, facts, extended, typed, _⟩ :=
            DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
          obtain ⟨finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
            finalHeapRep, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata⟩ :=
            bodyMeaning bodyCertified typed selectedEnv selectedRelated (binders_agree extended
                (arm_monomorphic casesTyped selected)
                (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) allocated) selectedLayout bodyEval
          have sourceMatch : Dynamic.StatementExecutesOutcome program context evidence source environment before id context
              (Dynamic.restoreControl environment outcome) after := by
            cases sourceBody with
            | control executes =>
              exact .control (.matchArm contains form scrutineeContains sourceEval hiddenAllocated selected
                rfl rfl extended allocated executes)
            | fault fault =>
              exact .fault (.matchArmBody contains form scrutineeContains sourceEval hiddenAllocated selected
                rfl rfl extended allocated fault)
          exact ⟨_, after, finalMap, finalWorld, sourceMatch, related.restore environment, finalHeapRep,
            firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame),
            firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans
              ((binders_metadata allocated).trans thirdMetadata))⟩
        | @default statements body bodyCertified =>
          have defaultSelected := default_selected selected
          obtain ⟨staticFinal, facts, typed⟩ := defaultTyped defaultSelected
          obtain ⟨finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
            finalHeapRep, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata⟩ :=
            bodyMeaning bodyCertified typed selectedEnv selectedRelated
              (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) selectedLayout bodyEval
          have sourceMatch : Dynamic.StatementExecutesOutcome program context evidence source environment before id context
              (Dynamic.restoreControl environment outcome) after := by
            cases sourceBody with
            | control executes => exact .control (.matchDefault contains form scrutineeContains sourceEval hiddenAllocated selected executes)
            | fault fault => exact .fault (.matchDefaultBody contains form scrutineeContains sourceEval hiddenAllocated selected fault)
          exact ⟨_, after, finalMap, finalWorld, sourceMatch, related.restore environment, finalHeapRep,
            firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
            firstFrame.trans (secondFrame.trans thirdFrame),
            firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans thirdMetadata)⟩
        | noBranch =>
          have finished : Evaluates selectedActual selectedStore
              ((LocalLoop.fallthrough resultType).rename selectedEmbedding)
              (.inRight .word (.inLeft LocalLoop.transferType (.inLeft resultType .unit))) selectedStore :=
            .inRight (.inLeft (.inLeft .unit))
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyEval finished
          exact ⟨.fallthrough environment, hiddenHeap, selectedMap, selectedWorld,
            .control (.matchNoBranch contains form scrutineeContains sourceEval hiddenAllocated selected),
            .fallthrough environment, selectedRelated, firstMaps.trans secondMaps, firstWorlds.trans secondWorlds,
            firstFrame.trans secondFrame, firstMetadata.trans (.of_allocation hiddenAllocated)⟩

/-- Actual successful lowering feeds the static certificate extractor and the
match reflection theorem. Callback extraction and child semantics are exposed
separately, so no semantic premise is hidden inside compiler acceptance. -/
theorem lowerWithReasons_reflects
    {compilation : DataPatternCertificates.Compilation} {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {program : Program} {context : SourceSemantics.Context} {control : ControlContext}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultSource : TypeSystem.Ty} {resultType : Ty}
    {internalReason : Word} {reasonAt : ExpressionId → Word}
    {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer} {fuel : Nat}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {faults : FaultRep} {code : Expr}
    (expressionExtract : ∀ childFuel scope id result,
      lowerExpression childFuel source scope id reasonAt = .ok result → expressionCertificate scope id result)
    (bodyExtract : ∀ childFuel scope statements code,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code)
    (expressionMeaning : ExpressionReflects compilation model program context evidence source expressionCertificate faults)
    (bodyMeaning : BodyReflects compilation model program control evidence source bodyCertificate resultSource resultType faults)
    (valid : DataPatternLeaves.ContextValid compilation context)
    {scrutineeNode : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {result : Value}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.rename ξ) result finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after ∧
      OutcomeRepresents model finalMap finalWorld resultSource resultType faults outcome result ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  Certificate.reflects includes
    (certificate_of_lowerWithReasons expressionExtract bodyExtract accepted)
    expressionMeaning bodyMeaning valid found casesTyped defaultTyped environments heaps locals layout evaluated

end Solcore.SourceSemantics.CoreLowering.GenericMatchMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericMatchSelection
/-! The source-ordered selection can drive the same certified Core branch
prefix. These lemmas provide the forward direction without assuming global
source determinism or changing how malformed patterns are specified. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchSelection
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves
open DataPatternExecution DataPatternSuccess DataPatternTypedValues DataMatchCertificates DataMatchDecision

private theorem pattern_success {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : DataPatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) {sourceValue : Dynamic.Value} {value : Value}
    {bindings : List (TypedBinder × Dynamic.Value)}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    (matched : Dynamic.PatternMatches context pattern sourceValue bindings) :
    ∃ values, DataPatternBindings.BindingsRep compilation.checked.catalog compilation.signatures compiled.bindings bindings values ∧
      MatcherRuns compiled value values := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures _ _ _ root
  have originalMatch := matched
  cases matched with
  | intro matchedSource instructionMatch =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep matchedSource
    subst arityEq
    subst instructions
    obtain ⟨values, _, bindingsRep, evaluates⟩ := Tree.success tree sourceValue value bindings [] represented.erase instructionMatch
    exact ⟨values, DataPatternBindings.Certificate.bindings_typed certificate valid.signatures represented originalMatch bindingsRep, evaluates⟩

/-- An independently selected source arm has the matching certified Core
prefix, with its exact source binder values authenticated. -/
theorem Arms.selects {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : ContextValid compilation context) {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value)
    {selection : Dynamic.MatchCaseSelection}
    (selected : Dynamic.MatchCasesSelect context sourceValue cases fallback selection) :
    Decision compilation context scope bodyCertificate resultType sourceValue value cases arms fallback fallbackCode selection := by
  induction selected generalizing arms with
  | head matched =>
    cases certificates with
    | cons certificate typed bodyCertified tail =>
      obtain ⟨values, related, runs⟩ := pattern_success certificate valid represented matched
      exact .head matched related runs bodyCertified
  | tail notMatched selected ih =>
    cases certificates with
    | cons certificate typed bodyCertified tail =>
      cases pattern_decides certificate valid represented with
      | inl found =>
        obtain ⟨_, _, matched, _⟩ := found
        exact False.elim (notMatched.excludes matched)
      | inr failed => exact .tail notMatched failed.2 (ih tail fallbackCertificate)
  | default => cases certificates; cases fallbackCertificate with
    | some certified => exact .default certified
  | noBranch => cases certificates; cases fallbackCertificate; exact .noBranch

private theorem pattern_not_malformed {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : DataPatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) : ¬ Dynamic.PatternMalformed context pattern := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures _ _ _ root
  intro malformed
  cases malformed with
  | source absent => exact absent arity sourceRep
  | «prefix» other absent =>
    have arityEq := Dynamic.MatchPatternSourceRepresents.rootArity_eq sourceRep other
    subst arityEq
    subst instructions
    exact absent (DataPatternCertificates.Tree.skips tree)

theorem Arms.not_pattern_fault {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (valid : ContextValid compilation context) (value : Dynamic.Value) :
    ¬ Dynamic.MatchCasesPatternFault context value cases := by
  induction certificates with
  | nil => intro fault; cases fault
  | cons certificate typed body tail ih =>
    intro fault
    cases fault with
    | head malformed => exact pattern_not_malformed certificate valid malformed
    | tail _ next => exact ih next

end Solcore.SourceSemantics.CoreLowering.GenericMatchSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericMatchSelectedPrefix
/-! Forward use of the exact match prefix for an already finite independent
source arm selection. No determinism of the complete source evaluator or of
its arbitrary children is required. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchSelectedPrefix
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open DataMatchCertificates DataMatchDecision DataMatchBranchPrefix GenericMatchAllocation
open SourceCoreDataMatches

theorem selected_prefix
    {compilation : DataPatternCertificates.Compilation} {context : SourceSemantics.Context}
    {model : GenericHeap.PayloadModel compilation.checked.catalog}
    (includes : IncludesFinite compilation.signatures model)
    {source : TypedSource} {id : StatementId} {resolution : MatchResolution} {scope : Scope}
    {scrutineeNode : ExpressionNode} {payload resultType : Ty} {computation : Expr}
    {bodyCertificate : BodyCertificate} {arms : List (Pattern × Expr)} {fallback : Expr} {internalReason : Word}
    (fresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) = false)
    (projection : compilation.checked.catalog.project scrutineeNode.type = .ok payload)
    (armsCertified : Arms compilation source id ((resolution.hiddenScrutinee, payload) :: scope)
      scrutineeNode.type bodyCertificate resolution.cases arms)
    (fallbackCertified : Fallback bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope)
      resultType resolution.defaultBody fallback)
    (valid : DataPatternLeaves.ContextValid compilation context)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {before store : Store} {ξ : Renaming}
    {sourceValue : Dynamic.Value} {value : Value} {selection : Dynamic.MatchCaseSelection}
    (represented : DataPatternTypedValues.TypedValueRep compilation.checked.catalog compilation.signatures
      scrutineeNode.type sourceValue value)
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext
      scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual before (computation.rename ξ) (.inRight .word value) store)
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding body,
      Dynamic.Heap.Allocates heap scrutineeNode.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents compilation.checked.catalog finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual before
        ((LocalSequence.letInitialized (LocalLoop.controlType resultType) payload computation
          (.caseE (.loadCell (.var 0))
            (LanguageResult.failure (LocalLoop.controlType resultType) (.word internalReason))
            (arms.foldr (fun (pattern, body) next => attempt pattern (LocalLoop.controlType resultType) body next)
              (fallback.weakenAt 0)))).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenEnv, hiddenHeapRep⟩ := GenericHeap.bind_internal environments heaps fresh
    (.initialized (includes projection represented)) (Dynamic.Heap.Allocates.append (value := some sourceValue))
  have decision := GenericMatchSelection.Arms.selects armsCertified fallbackCertified valid represented selectedSource
  let reference := Value.cellRef (OptionalCell.cellType payload) store.length
  have hiddenLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 1) ξ.lift).lift
      (value :: reference :: canonical) (value :: reference :: value :: actual) := by
    intro index foundValue found
    cases index with
    | zero => exact found
    | succ index => cases index with
      | zero => exact found
      | succ index => exact layout found
  obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, body, selected, finalEnv, finalHeapRep, maps, worlds, frame,
    finalLayout, agreement⟩ :=
    GenericMatchPrefix.Decision.prefix includes decision armsCertified hiddenEnv hiddenHeapRep hiddenLayout
  exact ⟨_, _, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, body, .append, decision.source, selected, finalEnv, finalHeapRep,
    (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
    (show WorldExtends world (world ++ [OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
    (AdministrativePreserved.allocate mapping store (.inRight .unit value)).trans frame,
    finalLayout, (GenericMatchScrutinee.initialized_prefix evaluated).trans agreement⟩


end Solcore.SourceSemantics.CoreLowering.GenericMatchSelectedPrefix
end
