import Solcore.Frontend.RuntimeValueOwner

/- Finite structural representation laws preserve all inert payloads and ordered
captures. They impose no typing, scope alignment, store validity or execution premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem owner_identity : ownerLocalIdMap id = id := by
  funext localId
  cases localId
  rfl

namespace RuntimeValue

/-- Relabeling with the identity retains the complete original runtime value. -/
theorem mapOwners_id (value : RuntimeValue) : value.mapOwners id = value := by
  cases value with
  | unit | bool | word | hostFunction | cellRef => simp only [mapOwners]
  | pair left right => simp only [mapOwners,mapOwners_id left,mapOwners_id right]
  | inLeft ty payload | inRight ty payload | constructed ty payload =>
    simp only [mapOwners,mapOwners_id payload]
  | coreClosure parameter result body captured =>
    rw [mapOwners_coreClosure]
    congr 1
    calc
      captured.map (mapOwners id) = captured.map id :=
        List.map_congr_left (fun child member => mapOwners_id child)
      _ = captured := List.map_id captured
  | sourceClosure source owner names captured =>
    simp only [mapOwners_sourceClosure,owner_identity,id_eq,LocalNameTable.mapIds_id,mapRuntimeCapturedOwners]
    congr 1
    calc
      captured.map (fun row => (row.1,mapOwners id row.2)) = captured.map id := by
        apply List.map_congr_left
        intro row member
        rw [mapOwners_id row.2]
        rfl
      _ = captured := List.map_id captured
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals first
    | have smaller := List.sizeOf_lt_of_mem member; omega
    | have smaller := List.sizeOf_lt_of_mem member
      have pairSize : sizeOf row = 1 + sizeOf row.1 + sizeOf row.2 := by cases row; rfl
      omega

/-- Composition reaches every nested owner while preserving all non-owner fields. -/
theorem mapOwners_comp (value : RuntimeValue)
    (first second : Resolved.DeclarationId → Resolved.DeclarationId) :
    (value.mapOwners first).mapOwners second = value.mapOwners (second ∘ first) := by
  cases value with
  | unit | bool | word | hostFunction | cellRef => simp only [mapOwners]
  | pair left right =>
    simp only [mapOwners,mapOwners_comp left first second,mapOwners_comp right first second]
  | inLeft ty payload | inRight ty payload | constructed ty payload =>
    simp only [mapOwners,mapOwners_comp payload first second]
  | coreClosure parameter result body captured =>
    simp only [mapOwners_coreClosure,List.map_map]
    congr 1
    exact List.map_congr_left (fun child member => mapOwners_comp child first second)
  | sourceClosure source owner names captured =>
    simp only [mapOwners_sourceClosure,LocalNameTable.mapIds_comp,
      mapRuntimeCapturedOwners,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro row member
    rw [mapOwners_comp row.2 first second]
    rfl
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals first
    | have smaller := List.sizeOf_lt_of_mem member; omega
    | have smaller := List.sizeOf_lt_of_mem member
      have pairSize : sizeOf row = 1 + sizeOf row.1 + sizeOf row.2 := by cases row; rfl
      omega

/-- Core values contain no declaration owners, including within closure captures. -/
theorem mapOwners_ofCore (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (value : Core.Value) : (ofCore value).mapOwners mapping = ofCore value := by
  cases value with
  | unit | bool | word | hostFunction | cellRef => simp only [ofCore,mapOwners]
  | pair left right =>
    simp only [ofCore,mapOwners,mapOwners_ofCore mapping left,mapOwners_ofCore mapping right]
  | inLeft ty payload | inRight ty payload | constructed ty payload =>
    simp only [ofCore,mapOwners,mapOwners_ofCore mapping payload]
  | closure parameter result body captured =>
    simp only [ofCore,List.attach_map_val,mapOwners_coreClosure,List.map_map]
    congr 1
    exact List.map_congr_left (fun child member => mapOwners_ofCore mapping child)
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have smaller := List.sizeOf_lt_of_mem member
  omega

private theorem project_attached (values : List RuntimeValue) :
    values.attach.mapM (fun value => toCore? value.val) = values.mapM toCore? := by
  change values.attach.mapM (toCore? ∘ Subtype.val) = _
  rw [← List.mapM_map,List.attach_map_subtype_val]

private theorem project_mapped_list (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (values : List RuntimeValue)
    (same : ∀ value ∈ values, toCore? (mapOwners mapping value) = toCore? value) :
    (values.map (mapOwners mapping)).mapM toCore? = values.mapM toCore? := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons,List.mapM_cons,same head (by simp),
      ih (fun value member => same value (by simp [member]))]

/-- Both successful Core projection and failure are invariant under owner relabeling. -/
theorem toCore?_mapOwners (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (value : RuntimeValue) : (value.mapOwners mapping).toCore? = value.toCore? := by
  cases value with
  | unit | bool | word | hostFunction | cellRef => simp only [mapOwners,toCore?]
  | pair left right =>
    simp only [mapOwners,toCore?,toCore?_mapOwners mapping left,toCore?_mapOwners mapping right]
  | inLeft ty payload | inRight ty payload | constructed ty payload =>
    simp only [mapOwners,toCore?,toCore?_mapOwners mapping payload]
  | sourceClosure source owner names captured => simp only [mapOwners_sourceClosure,toCore?]
  | coreClosure parameter result body captured =>
    simp only [mapOwners_coreClosure,toCore?,project_attached]
    rw [project_mapped_list mapping captured (fun child member => toCore?_mapOwners mapping child)]
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have smaller := List.sizeOf_lt_of_mem member
  omega

/-- An injective owner map loses no part of a complete finite runtime value. -/
theorem mapOwners_injective (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) : Function.Injective (mapOwners mapping) := by
  classical
  let undo := fun owner => if found : ∃ original, mapping original = owner then Classical.choose found else owner
  have leftInverse (owner : Resolved.DeclarationId) : undo (mapping owner) = owner := by
    dsimp [undo]
    have existsOriginal : ∃ original, mapping original = mapping owner := ⟨owner,rfl⟩
    rw [dif_pos existsOriginal]
    exact injective (Classical.choose_spec existsOriginal)
  have composition : undo ∘ mapping = id := funext leftInverse
  intro left right same
  have recovered := congrArg (mapOwners undo) same
  simpa only [mapOwners_comp,composition,mapOwners_id] using recovered

end RuntimeValue

/-- The complete ordered runtime capture table is unchanged by identity relabeling. -/
theorem mapRuntimeCapturedOwners_id (captured : Resolved.LocalScope RuntimeValue) :
    mapRuntimeCapturedOwners id captured = captured := by
  simp only [mapRuntimeCapturedOwners,owner_identity,id_eq,RuntimeValue.mapOwners_id]
  exact List.map_id captured

/-- Successive capture-table relabelings compose without deduplication or reordering. -/
theorem mapRuntimeCapturedOwners_comp (captured : Resolved.LocalScope RuntimeValue)
    (first second : Resolved.DeclarationId → Resolved.DeclarationId) :
    mapRuntimeCapturedOwners second (mapRuntimeCapturedOwners first captured) =
      mapRuntimeCapturedOwners (second ∘ first) captured := by
  simp only [mapRuntimeCapturedOwners,List.map_map,Function.comp_def,RuntimeValue.mapOwners_comp]
  rfl

end Solcore.Frontend
