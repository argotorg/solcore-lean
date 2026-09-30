import Solcore.SourceSemantics.CoreLowering.DataMatchAllocation
import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement
import Solcore.SourceSemantics.CoreLowering.LoopStatementLayout

/-! Exact continuation correspondence for the binder-allocation prefix emitted
by bindArm. The proof constructs source allocation and follows the actual Core
let/case temporaries. The continuation is arbitrary: no exact closure-renaming
or first-order-store theorem is assumed for the selected arm's body. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchCoreAllocation
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreDataMatches DataPatternBindings DataPatternValues DataEquality CoreProof
open ReadOnly

def liftMany : Nat → Renaming → Renaming
  | 0, embedding => embedding
  | count + 1, embedding => liftMany count embedding.lift

/-- A proof-facing name for the existing fold, with a starting index so its
structural induction also covers the suffix after an allocated binder. -/
def allocationCode (bindings : List (TypedBinder × Ty)) (start : Nat) (types : List Ty)
    (outputType : Ty) (tail : Expr) : Expr :=
  (bindings.zipIdx start).foldr (fun (binding, index) continuation =>
    LocalSequence.letInitialized outputType binding.2
      (LanguageResult.success (SourceCoreDataExpressions.projectPacked index types (.var index))) continuation) tail

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
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {κ ξ : Renaming}
    {start : Nat} {allTypes : List Ty} {allValues : List Value} {outputType : Ty} {tail : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : DataHeap.HeapRepresents catalog signatures mapping world heap store)
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
      DataHeap.HeapRepresents catalog signatures finalMap finalWorld finalHeap finalStore ∧
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
    obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind (id := binder.id) heaps (.initialized projection head)
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
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {scrutinee : Value} {outputType : Ty} {body : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : DataHeap.HeapRepresents catalog signatures mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (sources.map Prod.fst) (sources.map Prod.snd)
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical ∧
      DataHeap.HeapRepresents catalog signatures finalMap finalWorld finalHeap finalStore ∧
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
    BindingsRep.prefix represented (tail := (body.weakenAt bindings.length).weakenAt bindings.length)
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

end Solcore.SourceSemantics.CoreLowering.DataMatchCoreAllocation
