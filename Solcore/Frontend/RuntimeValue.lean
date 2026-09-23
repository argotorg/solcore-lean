import Solcore.Core.Syntax
import Solcore.Syntax.Term
import Solcore.Resolved.Identity
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Frontend.LocalName

/-!
Mixed values retain original source code and complete captures as inert data.
These definitions neither assign source-closure types nor evaluate or elaborate code.
Projection traverses finite value structure, not locations in a store.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- All Core forms mirror their recursive payloads; source code may have any original
syntax shape and carries exact ordered names/captures without validity assumptions. -/
inductive RuntimeValue where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | hostFunction (function : Core.HostFunction)
  | pair (left right : RuntimeValue)
  | coreClosure (parameterType resultType : Core.Ty) (body : Core.Expr) (captured : List RuntimeValue)
  | inLeft (rightType : Core.Ty) (payload : RuntimeValue)
  | inRight (leftType : Core.Ty) (payload : RuntimeValue)
  | cellRef (elementType : Core.Ty) (location : Core.Location)
  | constructed (constructor : Core.ConstructorId) (payload : RuntimeValue)
  | sourceClosure (source : Syntax.Expr) (owner : Resolved.DeclarationId)
      (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue))
  deriving Repr

/-- Preserve every old value, including arbitrary tags, bodies, captures and locations. -/
def RuntimeValue.ofCore (value : Core.Value) : RuntimeValue :=
  match value with
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .hostFunction function => .hostFunction function
  | .pair left right => .pair (ofCore left) (ofCore right)
  | .closure parameterType resultType body captured =>
      .coreClosure parameterType resultType body (captured.attach.map (fun value => ofCore value.val))
  | .inLeft rightType payload => .inLeft rightType (ofCore payload)
  | .inRight leftType payload => .inRight leftType (ofCore payload)
  | .cellRef elementType location => .cellRef elementType location
  | .constructed constructor payload => .constructed constructor (ofCore payload)
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have member := List.sizeOf_lt_of_mem value.property
  omega

/-- Project exactly Core-shaped finite data. Every source closure fails, even inside
an unused capture; cell references are copied without dereferencing a store. -/
def RuntimeValue.toCore? (value : RuntimeValue) : Option Core.Value :=
  match value with
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .hostFunction function => some (.hostFunction function)
  | .pair left right => do return .pair (← toCore? left) (← toCore? right)
  | .coreClosure parameterType resultType body captured =>
      (captured.attach.mapM (fun value => toCore? value.val)).map (.closure parameterType resultType body)
  | .inLeft rightType payload => (toCore? payload).map (.inLeft rightType)
  | .inRight leftType payload => (toCore? payload).map (.inRight leftType)
  | .cellRef elementType location => some (.cellRef elementType location)
  | .constructed constructor payload => (toCore? payload).map (.constructed constructor)
  | .sourceClosure _ _ _ _ => none
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have member := List.sizeOf_lt_of_mem value.property
  omega

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeValueOwner`
-/

/- Owner relabeling reaches every finite nested source closure. Core syntax,
types, locations and source spans remain literal; no runtime object is executed. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Relabel saved declaration owners and local IDs, preserving every ordered payload. -/
def RuntimeValue.mapOwners (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (value : RuntimeValue) : RuntimeValue :=
  match value with
  | .unit => .unit
  | .bool b => .bool b
  | .word w => .word w
  | .hostFunction f => .hostFunction f
  | .pair left right => .pair (mapOwners mapping left) (mapOwners mapping right)
  | .coreClosure parameter result body captured =>
      .coreClosure parameter result body (captured.attach.map (fun v => mapOwners mapping v.val))
  | .inLeft ty payload => .inLeft ty (mapOwners mapping payload)
  | .inRight ty payload => .inRight ty (mapOwners mapping payload)
  | .cellRef ty location => .cellRef ty location
  | .constructed constructor payload => .constructed constructor (mapOwners mapping payload)
  | .sourceClosure source owner names captured =>
      .sourceClosure source (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (captured.attach.map (fun row => (ownerLocalIdMap mapping row.val.1,mapOwners mapping row.val.2)))
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals first
    | have smaller := List.sizeOf_lt_of_mem v.property; omega
    | have smaller := List.sizeOf_lt_of_mem row.property
      have pairSize : sizeOf row.val = 1 + sizeOf row.val.1 + sizeOf row.val.2 := by
        cases row.val; rfl
      omega

/-- Relabel both keys and complete values of an ordered runtime capture table. -/
def mapRuntimeCapturedOwners (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (captured : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  captured.map (fun row => (ownerLocalIdMap mapping row.1,row.2.mapOwners mapping))

/-- Core bodies and types are unchanged; source closures nested in captures are reached. -/
theorem RuntimeValue.mapOwners_coreClosure
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (parameter result : Core.Ty) (body : Core.Expr) (captured : List RuntimeValue) :
    (.coreClosure parameter result body captured : RuntimeValue).mapOwners mapping =
      .coreClosure parameter result body (captured.map (RuntimeValue.mapOwners mapping)) := by
  simp only [mapOwners,List.attach_map_val]

/-- Saved syntax and row order are literal; every owner, key and captured value is mapped. -/
theorem RuntimeValue.mapOwners_sourceClosure
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (source : Syntax.Expr) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) :
    (.sourceClosure source owner names captured : RuntimeValue).mapOwners mapping =
      .sourceClosure source (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) := by
  simp only [mapOwners,mapRuntimeCapturedOwners]
  congr 1
  change captured.attach.map
    ((fun row : Resolved.LocalId × RuntimeValue => (ownerLocalIdMap mapping row.1,mapOwners mapping row.2)) ∘ Subtype.val) = _
  rw [← List.map_map,List.attach_map_subtype_val]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeValueOwnerProperties`
-/

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

private theorem project_owner_attached (values : List RuntimeValue) :
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
    simp only [mapOwners_coreClosure, toCore?, project_owner_attached]
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

/-!
## Consolidated module: `Solcore.Frontend.RuntimeValueProperties`
-/

/-!
Exact representation laws have no typing, checking, execution or world premises.
Private list proofs preserve every ordered capture; successful projection loses no data.
-/

set_option autoImplicit false

namespace Solcore.Frontend

namespace RuntimeValue

private theorem project_value_attached (values : List RuntimeValue) :
    values.attach.mapM (fun value => toCore? value.val) = values.mapM toCore? := by
  change values.attach.mapM (toCore? ∘ Subtype.val) = _
  rw [← List.mapM_map, List.attach_map_subtype_val]

private theorem project_embedded_list (values : List Core.Value)
    (roundtrip : ∀ value ∈ values, toCore? (ofCore value) = some value) :
    (values.map ofCore).mapM toCore? = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.mapM_cons, roundtrip head (by simp),
        ih (fun value member => roundtrip value (by simp [member])),
        bind, Option.bind_some, pure]

/-- Embedding and then projecting returns the identical original Core value. -/
theorem toCore?_ofCore (value : Core.Value) : toCore? (ofCore value) = some value := by
  cases value with
  | unit | bool | word | hostFunction | cellRef => simp only [ofCore, toCore?]
  | pair left right =>
      simp only [ofCore, toCore?, toCore?_ofCore left, toCore?_ofCore right,
        bind, Option.bind_some, pure]
  | inLeft type payload | inRight type payload | constructed type payload =>
      simp only [ofCore, toCore?, toCore?_ofCore payload, Option.map_some]
  | closure parameterType resultType body captured =>
      simp only [ofCore, toCore?, List.attach_map_val, project_value_attached]
      rw [project_embedded_list captured (fun value member => toCore?_ofCore value)]
      rfl
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have smaller := List.sizeOf_lt_of_mem member
  omega

private theorem project_list_reflect (values : List RuntimeValue)
    (reflection : ∀ value ∈ values, ∀ core, toCore? value = some core → value = ofCore core)
    {cores : List Core.Value} (projected : values.mapM toCore? = some cores) :
    values = cores.map ofCore := by
  induction values generalizing cores with
  | nil =>
      have equality : [] = cores := Option.some.inj projected
      subst cores
      rfl
  | cons head tail ih =>
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at projected
      obtain ⟨core, headProjected, rest, tailProjected, equality⟩ := projected
      cases Option.some.inj equality
      change head :: tail = ofCore core :: rest.map ofCore
      rw [reflection head (by simp) core headProjected,
        ih (fun value member => reflection value (by simp [member])) tailProjected]

private theorem project_reflect (value : RuntimeValue) {core : Core.Value}
    (projected : toCore? value = some core) : value = ofCore core := by
  cases value with
  | unit | bool | word | hostFunction | cellRef =>
      simp only [toCore?, Option.some.injEq] at projected
      subst core
      simp only [ofCore]
  | pair left right =>
      simp only [toCore?, bind, Option.bind_eq_some_iff] at projected
      obtain ⟨leftCore, leftProjected, rightCore, rightProjected, equality⟩ := projected
      cases Option.some.inj equality
      simp only [ofCore]
      rw [project_reflect left leftProjected, project_reflect right rightProjected]
  | inLeft type payload | inRight type payload | constructed type payload =>
      simp only [toCore?, Option.map_eq_some_iff] at projected
      obtain ⟨payloadCore, payloadProjected, rfl⟩ := projected
      simp only [ofCore]
      congr 1
      exact project_reflect payload payloadProjected
  | coreClosure parameterType resultType body captured =>
      simp only [toCore?, project_value_attached, Option.map_eq_some_iff] at projected
      obtain ⟨cores, capturesProjected, rfl⟩ := projected
      simp only [ofCore, List.attach_map_val]
      congr 1
      exact project_list_reflect captured
        (fun value member core projected => project_reflect value projected) capturesProjected
  | sourceClosure source owner names captured =>
      simp only [toCore?, reduceCtorEq] at projected
termination_by sizeOf value
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  have smaller := List.sizeOf_lt_of_mem member
  omega

/-- Successful structural projection characterizes precisely the embedded Core-value image. -/
theorem toCore?_eq_some_iff {value : RuntimeValue} {core : Core.Value} :
    toCore? value = some core ↔ value = ofCore core := by
  constructor
  · exact project_reflect value
  · intro equality
    subst value
    exact toCore?_ofCore core

/-- Distinct original values remain distinct after embedding. -/
theorem ofCore_injective : Function.Injective ofCore := by
  intro left right equality
  have projected := congrArg toCore? equality
  simpa only [toCore?_ofCore, Option.some.injEq] using projected

end RuntimeValue

end Solcore.Frontend
