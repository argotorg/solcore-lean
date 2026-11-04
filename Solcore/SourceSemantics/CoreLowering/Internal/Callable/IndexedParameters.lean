import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation

/-!
# Indexed callables: parameters

Certificates, meaning and typing of parameters.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterCertificates
/-! Static receipts for the actual common parameter fold. The tree records
only emitted allocation sites, their real layout receipts and binder insertion.
It contains neither source nor Core execution premises. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterCertificates
open Core Frontend SourceInference
open CallableIndexedAllocationCompletion
abbrev Binding := TypedBinder × Ty
abbrev Scope := SourceCoreSourceCells.Scope

def request (source : TypedSource) (scope : Scope) (index : Nat) (binding : Binding) : SourceCoreSourceCells.Request :=
  ⟨source, scope, Renaming.comp (Renaming.insertion 0) (Renaming.insertion index),
    binding.1, binding.2, some (.var 0)⟩

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (total : Nat) (output : Ty) (body : Expr) :
    Scope → Nat → List Binding → Expr → Prop where
  | nil {scope index} : Tree layouts owner active layout globals onError source total output body scope index [] body
  | cons {scope index binder payload bindings code}
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope index (binder, payload)))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals
        (layouts.allocatorAt owner active onError) (request source scope index (binder, payload)))
      (same : annotation.original = allocation.expression)
      (tail : Tree layouts owner active layout globals onError source total output body
        ((binder.id, payload) :: scope) (index + 1) bindings code) :
      Tree layouts owner active layout globals onError source total output body scope index ((binder, payload) :: bindings)
        (LanguageResult.bind output
          (LanguageResult.success (SourceCoreFunctions.argumentProjection index total (.var index)))
          (.letE annotation.expression (code.weakenAt 1)))

private def step (allocate : SourceCoreSourceCells.Allocator) (source : TypedSource) (scope : Scope)
    (all : List Binding) (output : Ty) (item : Binding × Nat) (body : Expr) : Except SourceCoreBasic.Error Expr :=
  SourceCoreSourceCells.letInitialized (some allocate) source
    ((all.take item.2).reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (Renaming.insertion item.2) item.1.1 output item.1.2
    (LanguageResult.success (SourceCoreFunctions.argumentProjection item.2 all.length (.var item.2))) body

private theorem of_fold {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (scope : Scope) (all done bindings : List Binding)
    (split : all = done ++ bindings) (output : Ty) (body : Expr) {code : Expr}
    (accepted : (bindings.zipIdx done.length).foldrM
      (step (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)) source scope all output) body = .ok code) :
    Tree layouts owner active layout globals onError source all.length output body
      (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length bindings code := by
  induction bindings generalizing done code with
  | nil =>
    simp only [List.zipIdx_nil, List.foldrM_nil] at accepted
    cases accepted
    exact .nil
  | cons binding rest ih =>
    simp only [List.zipIdx_cons, List.foldrM_cons] at accepted
    cases tail : (rest.zipIdx (done.length + 1)).foldrM
        (step (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)) source scope all output) body with
    | error error => simp [tail, bind, Except.bind] at accepted
    | ok next =>
      simp only [tail, bind, Except.bind] at accepted
      have nextTree := ih (done := done ++ [binding]) (by simpa [List.append_assoc] using split)
        (by simpa using tail)
      have prior : all.take done.length = done := by rw [split]; simp
      simp only [step, prior, SourceCoreSourceCells.letInitialized, bind, Except.bind] at accepted
      change (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)
          (request source (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length binding) >>= fun v =>
          pure (LanguageResult.bind output
            (LanguageResult.success (SourceCoreFunctions.argumentProjection done.length all.length (.var done.length)))
            (.letE v (next.weakenAt 1)))) = .ok code at accepted
      cases allocationAccepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)
          (request source (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length binding) with
      | error error => simp only [allocationAccepted, bind, Except.bind, reduceCtorEq] at accepted
      | ok allocationCode =>
        have accepted' : LanguageResult.bind output
            (LanguageResult.success (SourceCoreFunctions.argumentProjection done.length all.length (.var done.length)))
            (.letE allocationCode (next.weakenAt 1)) = code := by
          simpa only [allocationAccepted, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using accepted
        obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError allocationAccepted
        rw [← accepted', emitted]
        apply Tree.cons allocation annotation same
        simpa using nextTree

/-- Successful production compilation extracts every parameter allocation
receipt and the exact nested temporary-binder structure. -/
theorem of_accepted {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : Scope} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      source scope bindings output SourceCoreFunctions.argumentProjection body = .ok code) :
    Tree layouts owner active layout globals onError source bindings.length output body scope 0 bindings code := by
  exact of_fold onError source scope bindings [] bindings rfl output body accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterMeaning
/-! Finite agreement of the real marked parameter prefix. Every allocator
execution is derived from its static receipt. The body remains an arbitrary
continuation reached under an explicit lexical embedding; it is not presumed
to preserve closure capture values under an insertion. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterMeaning
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly DataEquality
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedAllocationCompletion

inductive Arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    (model : GenericHeap.PayloadModel catalog projects nativeDefinitions) (mapping : LocationMap) (world : StoreTyping) :
    List Binding → List Dynamic.Value → List Value → Prop where
  | nil : Arguments model mapping world [] [] []
  | cons {binder : TypedBinder} {payload : Ty} {source : Dynamic.Value} {value : Value}
      {bindings : List Binding} {sources : List Dynamic.Value} {values : List Value}
      (head : model.Represents mapping world binder.scheme.body source value payload)
      (tail : Arguments model mapping world bindings sources values) :
      Arguments model mapping world ((binder, payload) :: bindings) (source :: sources) (value :: values)

theorem Arguments.length {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions} {mapping : LocationMap} {world : StoreTyping}
    {bindings : List Binding} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values) :
    bindings.length = sources.length ∧ bindings.length = values.length := by
  induction represented with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

theorem Arguments.extend {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {bindings : List Binding} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Arguments model futureMapping futureWorld bindings sources values := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons (model.extend head maps worlds) ih

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var found => exact .var (agrees found)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index selected found
  exact agrees found

/-- Prefix completion constructs independent binder allocation, the represented
heap, and a two-way finite continuation agreement. Source arguments may contain
closures and the initial store may contain arbitrary typed administrative cells. -/
theorem Tree.prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {total : Nat} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source total output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion start) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (total_eq : total = allTypes.length)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.insertion start))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  induction tree generalizing mapping world environment canonical logical actual heap store ξ sources values with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, sourceLayout, actualLayout, ⟨[], rfl, rfl, rfl⟩, .refl _ _ _⟩
  | @cons scope start binder payload bindings next allocation annotation same tail ih =>
    cases represented with
    | @cons _ _ sourceValue value _ sourceValues nativeValues head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projection := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      rw [← FunctionArguments.argumentProjection_eq, ← total_eq] at projection
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreFunctions.argumentProjection start total (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projection actualLayout).evaluates store)
      have canonicalLayout : EnvironmentsAgree (request source scope start (binder, payload)).references
          canonical (value :: logical) := agree_insert sourceLayout value
      have referenceAt : (value :: logical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
          (request source scope start (binder, payload))]? = some (.cellRef layout.type contextLocation) := by
        have found := canonicalLayout reference
        have kind := kinds (binder, payload) (by simp)
        change source.inputs.any (fun input => decide (input.id = binder.id)) = named at kind
        have isNamed : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope start (binder, payload)) = named := kind
        simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, isNamed]
        exact found
      obtain ⟨captured, allocationEval, nextHeaps, nextReference, frame⟩ :=
        CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments
          canonicalLayout heaps referenceAt read (.initialized rfl rfl) (.initialized head) Dynamic.Heap.Allocates.append
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      have nextEnvironments := CallableIndexedOrdinaryAllocation.bind_environment (id := binder.id) environments nextReference
      have nextSourceLayout : EnvironmentsAgree (Renaming.insertion (start + 1))
          (nextRef :: canonical) (nextRef :: logical) := by
        intro index selectedValue found
        have selected := sourceLayout.lift nextRef found
        simpa only [Renaming.lift_insertion] using selected
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (nextRef :: logical) (nextRef :: value :: actual) := by
        have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) := agree_insert actualLayout value
        intro index selectedValue found
        exact inserted.lift nextRef found
      have renamedAllocation := CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
        allocationEval (actualLayout.lift value)
      have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped bound
      have nextRead := stillRead.trans read
      have nextSelected : ∀ {index selectedValue}, nativeValues[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
        finalFrame, finalSourceLayout, finalActualLayout, spine, agreement⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
          (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩))
          nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show (nextRef :: logical)[start + 1]? = some (DataPatternValues.packValues allValues) from bundleSlot)
          nextSelected (fun binding member => kinds binding (List.mem_cons_of_mem _ member))
          (show (nextRef :: canonical)[(((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals)]? =
            some (.cellRef layout.type contextLocation) from by
              have nextIndex : (((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals) =
                  (scope.length + (if named then 0 else 1) + globals) + 1 := by simp only [List.length_cons]; omega
              rw [nextIndex]
              exact reference)
          nextRead stillUnmapped
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnvironments, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        frame.trans finalFrame, ?_, finalActualLayout, ?_, ?_⟩
      · intro index selectedValue found
        simpa only [List.length_cons, DataMatchCoreAllocation.liftMany, Renaming.lift_insertion] using finalSourceLayout found
      · obtain ⟨added, length, canonicalEq, logicalEq⟩ := spine
        exact ⟨added ++ [nextRef], by simp [length], by simpa [List.append_assoc, nextRef, request] using canonicalEq,
          by simpa [List.append_assoc, nextRef, request] using logicalEq⟩
      · simp only [LoopStatements.rename_insert_lift] at agreement
        apply ContinuationAgreement.trans ?_ agreement
        simpa only [LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne, nextRef, request] using
          (ContinuationAgreement.bind initializer).trans (ContinuationAgreement.letE renamedAllocation)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedParameters
/-! A named function enters with a packed argument slot followed by its
administrative environment. The actual common parameter compiler allocates all
source inputs, then reaches the unchanged body with that bundle retained in
its administrative suffix. Allocation receipts and argument representations
supply the prefix; no body execution is a premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedParameters
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning

private theorem insert_at_suffix (added tail : Environment) (value : Value) :
    Environment.insertAt (added ++ tail) added.length value = added ++ value :: tail := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head rest ih => simpa [Environment.insertAt] using congrArg (head :: ·) ih

private theorem insert_administrative {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type nativeDefinitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) nativeDefinitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

theorem scope_eq (bindings : List Binding) (scope : Scope) :
    bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope =
      bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih => simp [ih, List.append_assoc]

theorem inputKinds {source : TypedSource} {bindings : List Binding}
    (inputs : source.inputs = bindings.map Prod.fst) :
    ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = true := by
  intro binding member
  rw [inputs]
  exact List.any_eq_true.mpr ⟨binding.1, List.mem_map.mpr ⟨binding, member, rfl⟩, by simp⟩

/-- The retained bundle is typed directly from represented arguments, even
when a payload is a closure that captures mutable cells. -/
theorem Arguments.pack_typed {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions} {mapping : LocationMap} {world : StoreTyping}
    {bindings : List Binding} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values) :
    RuntimeValueHasType world (DataPatternValues.packValues values)
      (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) nativeDefinitions := by
  induction represented with
  | nil => exact .unit
  | @cons binder payload source value bindings sources values head rest ih =>
    cases rest with
    | nil => exact model.runtime_hasType head
    | cons => exact .pair (model.runtime_hasType head) ih

/-- Successful actual named-input compilation reaches a body whose lexical
relation includes the surviving packed-argument administrative slot. The
agreement wraps and inverts every finite body execution. -/
theorem named_prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      source [] bindings output SourceCoreFunctions.argumentProjection body = .ok code)
    (inputs : source.inputs = bindings.map Prod.fst)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative : Core.Context} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative [] [] canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues values :: canonical) actual)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical (DataPatternValues.packValues values :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by simpa using represented.length.2
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
    frame, _, finalActualLayout, spine, agreement⟩ :=
    CallableIndexedParameterMeaning.Tree.prefix tree definitions registered represented environments heaps sourceLayout actualLayout
      (allTypes := bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (inputKinds inputs) (by simpa using reference) read unmapped
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have typed := (Arguments.pack_typed represented).weaken worlds
  have finalEnvironmentWithBundle := insert_administrative finalEnvironments typed
  have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = bindings.length := by
    simp
  have exactEnvironment : Environment.insertAt finalCanonical bindings.length (DataPatternValues.packValues values) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, scope_eq] at finalEnvironmentWithBundle
  exact ⟨finalEnvironment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, by simpa using finalEnvironmentWithBundle, finalHeaps, maps, worlds,
    frame, finalActualLayout, agreement⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedParameters
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped
/-! Type preservation through the actual indexed parameter prefix. The
argument projection, snapshot, marker and source cell are the emitted prefix's
real operations. The final actual environment includes every retained argument
temporary; its typing is derived from the initial environment and allocations.
No continuation execution or final environment typing is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly DataEquality
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedAllocationCompletion
open CallableIndexedParameterMeaning

/-- Each parameter leaves its payload temporary below its source-cell reference. -/
def prefixContext (bindings : List Binding) (initial : Core.Context) : Core.Context :=
  bindings.foldl (fun context binding => OptionalCell.referenceType binding.2 :: binding.2 :: context) initial

theorem prefixContext_length (bindings : List Binding) (initial : Core.Context) :
    (prefixContext bindings initial).length = 2 * bindings.length + initial.length := by
  induction bindings generalizing initial with
  | nil => simp [prefixContext]
  | cons binding rest ih =>
    simpa [prefixContext, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (OptionalCell.referenceType binding.2 :: binding.2 :: initial)

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var found => exact .var (agrees found)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index selected found
  exact agrees found

/- Prefix completion constructs independent binder allocation, the represented
heap, and a two-way finite continuation agreement. Source arguments may contain
closures and the initial store may contain arbitrary typed administrative cells. -/
namespace Stateful

theorem prefix_typed {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {total : Nat} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source total output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts layout model)
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion start) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (total_eq : total = allTypes.length)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.insertion start))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (prefixContext bindings actualContext) nativeDefinitions ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
          finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩ := by
  induction tree generalizing mapping world environment canonical logical actual heap store ξ sources values actualContext with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, sourceLayout, actualLayout, ⟨[], rfl, rfl, rfl⟩, actualTyped, .refl _ _ _, ⟨initial, protocol.refl initial⟩⟩
  | @cons scope start binder payload bindings next allocation annotation same tail ih =>
    cases represented with
    | @cons _ _ sourceValue value _ sourceValues nativeValues head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projection := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      rw [← FunctionArguments.argumentProjection_eq, ← total_eq] at projection
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreFunctions.argumentProjection start total (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projection actualLayout).evaluates store)
      have canonicalLayout : EnvironmentsAgree (request source scope start (binder, payload)).references
          canonical (value :: logical) := agree_insert sourceLayout value
      have referenceAt : (value :: logical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
          (request source scope start (binder, payload))]? = some (.cellRef layout.type contextLocation) := by
        have found := canonicalLayout reference
        have kind := kinds (binder, payload) (by simp)
        change source.inputs.any (fun input => decide (input.id = binder.id)) = named at kind
        have isNamed : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope start (binder, payload)) = named := kind
        simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, isNamed]
        exact found
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextHeaps, nextReference, frame,
        nextState, nextRelated⟩ :=
        producer.complete allocation annotation same definitions registered environments
          canonicalLayout heaps referenceAt read (.initialized rfl rfl) (.initialized head) Dynamic.Heap.Allocates.append
          initial (readyAt initial read)
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      have nextEnvironments := CallableIndexedOrdinaryAllocation.bind_environment (id := binder.id) environments nextReference
      have nextSourceLayout : EnvironmentsAgree (Renaming.insertion (start + 1))
          (nextRef :: canonical) (nextRef :: logical) := by
        intro index selectedValue found
        have selected := sourceLayout.lift nextRef found
        simpa only [Renaming.lift_insertion] using selected
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (nextRef :: logical) (nextRef :: value :: actual) := by
        have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) := agree_insert actualLayout value
        intro index selectedValue found
        exact inserted.lift nextRef found
      have renamedAllocation := CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
        allocationEval (actualLayout.lift value)
      have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped bound
      have nextRead := stillRead.trans read
      have nextSelected : ∀ {index selectedValue}, nativeValues[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
        finalFrame, finalSourceLayout, finalActualLayout, spine, finalTyped, agreement, finalState, finalRelated⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
          (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩))
          nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show RuntimeEnvironmentHasTypes
              (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
              (nextRef :: value :: actual) (OptionalCell.referenceType payload :: payload :: actualContext) nativeDefinitions from
            .cons (.cellRef nextReference.typed)
              (.cons ((model.runtime_hasType head).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)))
          (show (nextRef :: logical)[start + 1]? = some (DataPatternValues.packValues allValues) from bundleSlot)
          nextSelected (fun binding member => kinds binding (List.mem_cons_of_mem _ member))
          (show (nextRef :: canonical)[(((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals)]? =
            some (.cellRef layout.type contextLocation) from by
              have nextIndex : (((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals) =
                  (scope.length + (if named then 0 else 1) + globals) + 1 := by simp only [List.length_cons]; omega
              rw [nextIndex]
              exact reference)
          nextRead stillUnmapped nextState
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnvironments, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        frame.trans finalFrame, ?_, finalActualLayout, ?_, finalTyped, ?_, ⟨finalState, protocol.trans nextRelated finalRelated⟩⟩
      · intro index selectedValue found
        simpa only [List.length_cons, DataMatchCoreAllocation.liftMany, Renaming.lift_insertion] using finalSourceLayout found
      · obtain ⟨added, length, canonicalEq, logicalEq⟩ := spine
        exact ⟨added ++ [nextRef], by simp [length], by simpa [List.append_assoc, nextRef, request] using canonicalEq,
          by simpa [List.append_assoc, nextRef, request] using logicalEq⟩
      · simp only [LoopStatements.rename_insert_lift] at agreement
        apply ContinuationAgreement.trans ?_ agreement
        simpa only [LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne, nextRef, request] using
          (ContinuationAgreement.bind initializer).trans (ContinuationAgreement.letE renamedAllocation)

end Stateful

theorem prefix_typed {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {total : Nat} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source total output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion start) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (total_eq : total = allTypes.length)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.insertion start))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (prefixContext bindings actualContext) nativeDefinitions ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
    frame, sourceAgreement, actualAgreement, spine, typed, agreement, _transition⟩ :=
    Stateful.prefix_typed tree ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts layout model)
      definitions registered represented environments heaps sourceLayout actualLayout actualTyped
      bundleSlot total_eq bundleLength valuesSelected kinds reference read unmapped () (by intro index state read; trivial)
  exact ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
    frame, sourceAgreement, actualAgreement, spine, typed, agreement⟩


private theorem insert_at_suffix (added tail : Environment) (value : Value) :
    Environment.insertAt (added ++ tail) added.length value = added ++ value :: tail := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head rest ih => simpa [Environment.insertAt] using congrArg (head :: ·) ih

private theorem insert_administrative {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type nativeDefinitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) nativeDefinitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

/-- Successful actual named-input compilation reaches a body whose lexical
relation includes the surviving packed-argument administrative slot. The
agreement wraps and inverts every finite body execution. -/
theorem named_prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      source [] bindings output SourceCoreFunctions.argumentProjection body = .ok code)
    (inputs : source.inputs = bindings.map Prod.fst)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative [] [] canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues values :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (prefixContext bindings actualContext) nativeDefinitions ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical (DataPatternValues.packValues values :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by simpa using represented.length.2
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
    frame, _, finalActualLayout, spine, finalTyped, agreement⟩ :=
    prefix_typed tree definitions registered represented environments heaps sourceLayout actualLayout actualTyped
      (allTypes := bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds inputs) (by simpa using reference) read unmapped
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have typed := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalEnvironmentWithBundle := insert_administrative finalEnvironments typed
  have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = bindings.length := by
    simp
  have exactEnvironment : Environment.insertAt finalCanonical bindings.length (DataPatternValues.packValues values) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalEnvironmentWithBundle
  exact ⟨finalEnvironment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, by simpa using finalEnvironmentWithBundle, finalHeaps, maps, worlds,
    frame, finalActualLayout, finalTyped, agreement⟩


/-- Public packaging receipt for the original ordered canonical insertion. -/
theorem insert_at_suffix_receipt (added tail : Environment) (value : Value) :
    Environment.insertAt (added ++ tail) added.length value = added ++ value :: tail :=
  insert_at_suffix added tail value

/-- The original lexical representation inserts one typed administrative slot
at its scope boundary. This wrapper retains the unchanged existing proof. -/
theorem insert_administrative_receipt {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type nativeDefinitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) nativeDefinitions :=
  insert_administrative related typed


end Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeTyping
/-! Static typing of the real marked parameter fold. The packed argument and
lexical references retain their actual insertion indices. This result concerns
generated expressions, not equality of closure values under weakening. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeTyping
open Core Frontend SourceInference CallableIndexedParameterCertificates

def packed : List Ty → Ty
  | [] => .unit
  | [type] => type
  | type :: next :: rest => .product type (packed (next :: rest))

theorem projection_typed {definitions : DataEnvironment} {context : Core.Context}
    {types : List Ty} {index : Nat} {type : Ty} {bundle : Expr}
    (found : types[index]? = some type)
    (typed : HasType context bundle (packed types) definitions) :
    HasType context (SourceCoreFunctions.argumentProjection index types.length bundle) type definitions := by
  induction types generalizing index bundle with
  | nil => cases found
  | cons head rest ih =>
    cases rest with
    | nil =>
      cases index with
      | zero => cases found; exact typed
      | succ index => simp at found
    | cons next tail =>
      cases index with
      | zero => cases found; exact .first typed
      | succ index =>
        simpa [SourceCoreFunctions.argumentProjection] using ih (by simpa using found) (HasType.second typed)

def finalContext (bindings : List Binding) (context : Core.Context) : Core.Context :=
  (bindings.map (fun binding => OptionalCell.referenceType binding.2)).reverse ++ context

theorem tree_native {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {all : List Ty} {output : Ty} {body : Expr}
    {scope : Scope} {index : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active frame globals onError source all.length output body scope index bindings code)
    (registered : frame.Registered layouts.definitions)
    (outputWF : output.WellFormed layouts.definitions)
    (payloadWF : ∀ binding ∈ bindings, binding.2.WellFormed layouts.definitions)
    (ordinary : ∀ binding ∈ bindings,
      source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (selected : ∀ position binding, bindings[position]? = some binding → all[index + position]? = some binding.2)
    {context : Core.Context}
    (bundle : context[index]? = some (packed all))
    (references : ∀ position binding, scope[position]? = some binding →
      context[Renaming.insertion index position]? = some (OptionalCell.referenceType binding.2))
    (current : context[Renaming.insertion index (scope.length + 1 + globals)]? = some (.cell frame.type))
    (continuation : HasType (finalContext bindings context) body (LanguageResult.resultType output) layouts.definitions) :
    HasType context code (LanguageResult.resultType output) layouts.definitions := by
  induction tree generalizing context with
  | nil => exact continuation
  | @cons scope index binder payload bindings code allocation annotation same tail ih =>
    have member : (binder, payload) ∈ (binder, payload) :: bindings := by simp
    have next := ih (fun binding h => payloadWF binding (List.mem_cons_of_mem _ h))
      (fun binding h => ordinary binding (List.mem_cons_of_mem _ h))
      (fun position binding h => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using selected (position + 1) binding h)
      (context := OptionalCell.referenceType payload :: context)
      (by simpa using bundle) ?_ ?_ ?_
    · have captured : HasType (payload :: context)
          (SourceCoreSourceCells.captures (request source scope index (binder, payload)).references scope)
          (SourceCoreSourceCells.captureType scope) layouts.definitions := by
        apply SourceCoreSourceCells.captures_hasType
        intro position binding found
        simpa [request, Renaming.comp, Renaming.insertion] using references position binding found
      have allocated := allocation.hasType (payloadWF _ member) captured
        (by intro expression found; cases found; exact .var rfl)
      have annotated : HasType (payload :: context) annotation.expression
          (OptionalCell.referenceType payload) layouts.definitions := by
        rw [annotation.exact, same]
        apply SourceCoreCallableIndexedAllocationFrames.snapshotBefore_hasType registered
        · apply HasType.var
          have ordinaryHead := ordinary _ member
          change (payload :: context)[Renaming.comp (Renaming.insertion 0) (Renaming.insertion index)
            (scope.length + (if source.inputs.any (fun input => decide (input.id = binder.id)) then 0 else 1) + globals)]? = _
          rw [ordinaryHead]
          exact current
        · exact allocated
      apply LanguageResult.bind_hasType outputWF
      · exact LanguageResult.success_hasType (projection_typed (by simpa using selected 0 _ rfl) (.var bundle))
      · apply HasType.letE annotated
        simpa [Core.Context.insertAt] using next.weakenAt (inserted := payload) 1
    · intro position binding found
      cases position with
      | zero => cases found; simp [Renaming.insertion]
      | succ position =>
        rw [← Renaming.lift_insertion]
        exact references position binding found
    · have arithmetic : ((binder.id, payload) :: scope).length + 1 + globals =
          (scope.length + 1 + globals) + 1 := by simp; omega
      rw [arithmetic, ← Renaming.lift_insertion]
      exact current
    · simpa [finalContext, List.reverse_cons, List.append_assoc] using continuation

private theorem insertAt_append (front suffix : Core.Context) (type : Ty) :
    (front ++ suffix).insertAt front.length type = front ++ type :: suffix := by
  induction front with
  | nil => cases suffix <;> rfl
  | cons head rest ih => simp [Core.Context.insertAt, ih]

/-- The exact accepted allocation fold is typed from its body in the actual
source-reference context. No type of the completed prefix is assumed. -/
theorem of_accepted {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : Scope} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError))
      source scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok code)
    (registered : frame.Registered layouts.definitions)
    (outputWF : output.WellFormed layouts.definitions)
    (payloadWF : ∀ binding ∈ bindings, binding.2.WellFormed layouts.definitions)
    (ordinary : ∀ binding ∈ bindings,
      source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (administrative : Core.Context)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + globals]? = some (.cell frame.type))
    (bodyTyped : HasType (SourceCoreLocalCell.coreContext
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
      body (LanguageResult.resultType output) layouts.definitions) :
    HasType (packed (bindings.map Prod.snd) :: SourceCoreLocalCell.coreContext scope ++ administrative)
      code (LanguageResult.resultType output) layouts.definitions := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have selected : ∀ position binding, bindings[position]? = some binding →
      (bindings.map Prod.snd)[0 + position]? = some binding.2 := by
    intro position binding found
    simp [found]
  apply tree_native (all := bindings.map Prod.snd) (by simpa using tree) registered outputWF payloadWF ordinary selected rfl
  · intro position binding found
    change (SourceCoreLocalCell.coreContext scope ++ administrative)[position]? = _
    rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using (List.getElem?_eq_some_iff.mp found).1)]
    simp [SourceCoreLocalCell.coreContext, found, OptionalCell.referenceType]
  · exact current
  · have typed := bodyTyped.weakenAt (inserted := packed (bindings.map Prod.snd)) bindings.length
    have contextEq : (SourceCoreLocalCell.coreContext
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative).insertAt
        bindings.length (packed (bindings.map Prod.snd)) =
        finalContext bindings (packed (bindings.map Prod.snd) :: SourceCoreLocalCell.coreContext scope ++ administrative) := by
      simp only [SourceCoreLocalCell.coreContext, List.map_append, List.map_map, List.map_reverse, List.append_assoc, finalContext]
      have length : (List.map (fun binding : Binding => OptionalCell.referenceType binding.2) bindings).reverse.length = bindings.length := by simp
      change Core.Context.insertAt ((bindings.map (fun binding => OptionalCell.referenceType binding.2)).reverse ++
        (SourceCoreLocalCell.coreContext scope ++ administrative)) bindings.length _ = _
      rw [← length, insertAt_append]
      rfl
    rw [contextEq] at typed
    exact typed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeTyping
end
