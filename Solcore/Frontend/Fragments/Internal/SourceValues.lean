import Solcore.Core.Syntax
import Solcore.Syntax.Term
import Solcore.Resolved.Identity
import Solcore.Frontend.Fragments.Internal.Foundations
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Resolved.LocalScope
import Solcore.Frontend.Fragments.Internal.Computation

/-!
# Source fragment values

Mixed values that retain source closures, with their application and matching.
-/

section
-- leanmerge: from Solcore.Frontend.RuntimeValue
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
  | integer (value : Int)
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
  | .integer value => .integer value
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
  | .integer value => some (.integer value)
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
  | .integer value => .integer value
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
  | unit | bool | word | integer | hostFunction | cellRef => simp only [mapOwners]
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
  | unit | bool | word | integer | hostFunction | cellRef => simp only [mapOwners]
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
  | unit | bool | word | integer | hostFunction | cellRef => simp only [ofCore,mapOwners]
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
  | unit | bool | word | integer | hostFunction | cellRef => simp only [mapOwners,toCore?]
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
  | unit | bool | word | integer | hostFunction | cellRef => simp only [ofCore, toCore?]
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
  | unit | bool | word | integer | hostFunction | cellRef =>
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
end

section
-- leanmerge: from Solcore.Frontend.RuntimeWordMatch
/-! Original ordered choice over mixed values. Only visited literal cases require
actual Words; wildcard/default never project values or inspect unvisited cases. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Preserve first-match order and original selected syntax; only literal cases
require a Word, while wildcard/default accept every actual mixed value. -/
inductive RuntimeWordMatchChooses :
    RuntimeValue → List Syntax.MatchCase → Option Syntax.Block → Syntax.Block → Nat → Prop where
  | fallback {value : RuntimeValue} {defaultBody : Syntax.Block} :
      RuntimeWordMatchChooses value [] (some defaultBody) defaultBody 0
  | wildcard {value : RuntimeValue} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (meaning : WordMatchPatternClassifies first.value.pattern none) :
      RuntimeWordMatchChooses value (first :: rest) defaultBody first.value.body 0
  | hit {word : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (meaning : WordMatchPatternClassifies first.value.pattern (some word)) :
      RuntimeWordMatchChooses (.word word) (first :: rest) defaultBody first.value.body 1
  | miss {word literal : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
      (meaning : WordMatchPatternClassifies first.value.pattern (some literal))
      (different : word ≠ literal)
      (tail : RuntimeWordMatchChooses (.word word) rest defaultBody selected tests) :
      RuntimeWordMatchChooses (.word word) (first :: rest) defaultBody selected (tests + 1)

/-- The original selected block and literal comparison count are unique. -/
theorem RuntimeWordMatchChooses.deterministic
    {value : RuntimeValue} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
    {left right : Syntax.Block}
    {leftTests rightTests : Nat}
    (first : RuntimeWordMatchChooses value cases defaultBody left leftTests)
    (second : RuntimeWordMatchChooses value cases defaultBody right rightTests) :
    left = right ∧ leftTests = rightTests := by
  induction first generalizing right rightTests with
  | fallback => cases second; exact ⟨rfl, rfl⟩
  | wildcard shape =>
      cases second with
      | wildcard _ => exact ⟨rfl, rfl⟩
      | hit meaning => cases shape.tag_unique meaning
      | miss meaning _ _ => cases shape.tag_unique meaning
  | hit meaning =>
      cases second with
      | wildcard shape => cases meaning.tag_unique shape
      | hit _ => exact ⟨rfl, rfl⟩
      | miss other different _ => exact False.elim (different (meaning.value_unique other))
  | miss meaning different _ ih =>
      cases second with
      | wildcard shape => cases meaning.tag_unique shape
      | hit other => exact False.elim (different (other.value_unique meaning))
      | miss _ _ tail =>
          obtain ⟨rfl, rfl⟩ := ih tail
          exact ⟨rfl, rfl⟩

private theorem choice_reflect {actual : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (choice : RuntimeWordMatchChooses actual cases defaultBody selected tests) :
    ∀ value : Core.Value, actual = RuntimeValue.ofCore value →
      WordMatchChooses value cases defaultBody selected tests := by
  induction choice with
  | fallback => intro value same; exact .fallback
  | wildcard meaning => intro value same; exact .wildcard meaning
  | @hit word first rest defaultBody meaning =>
      intro value same
      have valueSame : Core.Value.word word = value := RuntimeValue.ofCore_injective
        (by simpa only [RuntimeValue.ofCore] using same)
      subst value
      exact .hit meaning
  | @miss word literal first rest defaultBody selected tests meaning different tail ih =>
      intro value same
      have valueSame : Core.Value.word word = value := RuntimeValue.ofCore_injective
        (by simpa only [RuntimeValue.ofCore] using same)
      subst value
      exact .miss meaning different (ih _ (by simp only [RuntimeValue.ofCore]))

/-- Every embedded old value has exactly its old original-choice derivations,
including arbitrary non-Word values and uninspected suffixes. -/
theorem runtimeWordMatchChooses_ofCore_iff {value : Core.Value}
    {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
    {selected : Syntax.Block} {tests : Nat} :
    RuntimeWordMatchChooses (RuntimeValue.ofCore value) cases defaultBody selected tests ↔
      WordMatchChooses value cases defaultBody selected tests := by
  constructor
  · intro choice
    exact choice_reflect choice value rfl
  · intro choice
    induction choice with
    | fallback => exact .fallback
    | wildcard meaning => exact .wildcard meaning
    | hit meaning => simpa only [RuntimeValue.ofCore] using RuntimeWordMatchChooses.hit meaning
    | miss meaning different _ ih =>
        simp only [RuntimeValue.ofCore] at ih ⊢
        exact .miss meaning different ih

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeWordMatchSelection`
-/

/- Original ordered selection only. Counts are visited literal comparisons,
not evaluator depth or execution cost. No projection or suffix inspection. -/

set_option autoImplicit false
namespace Solcore.Frontend

/-- Select an original body and count only visited literal comparisons. -/
def chooseRuntimeWordMatch? (value : RuntimeValue) (cases : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) : Option (Syntax.Block × Nat) :=
  match cases with
  | [] => defaultBody.map (fun body => (body, 0))
  | first :: rest =>
      match interpretWordMatchPattern? first.value.pattern with
      | none => none
      | some none => some (first.value.body, 0)
      | some (some literal) =>
          match value with
          | .word word =>
              if word = literal then some (first.value.body, 1)
              else (chooseRuntimeWordMatch? value rest defaultBody).map (fun pair => (pair.1, pair.2 + 1))
          | _ => none

private theorem selection_sound {value : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (accepted : chooseRuntimeWordMatch? value cases defaultBody = some (selected, tests)) :
    RuntimeWordMatchChooses value cases defaultBody selected tests := by
  induction cases generalizing value selected tests with
  | nil =>
      cases defaultBody with
      | none => simp [chooseRuntimeWordMatch?] at accepted
      | some body =>
          simp only [chooseRuntimeWordMatch?, Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact .fallback
  | cons first rest ih =>
      cases pattern : interpretWordMatchPattern? first.value.pattern with
      | none => simp [chooseRuntimeWordMatch?, pattern] at accepted
      | some tag =>
          have meaning := interpretWordMatchPattern?_iff.mp pattern
          cases tag with
          | none =>
              simp only [chooseRuntimeWordMatch?, pattern, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact .wildcard meaning
          | some literal =>
              cases value <;> simp only [chooseRuntimeWordMatch?, pattern, reduceCtorEq] at accepted
              rename_i word
              by_cases same : word = literal
              · subst literal
                simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at accepted
                obtain ⟨rfl, rfl⟩ := accepted
                exact .hit meaning
              · simp only [same, ↓reduceIte] at accepted
                obtain ⟨⟨body, count⟩, tail, equal⟩ := Option.map_eq_some_iff.mp accepted
                cases equal
                exact .miss meaning same (ih tail)

/-- Executable selection agrees with the independent original-body/count judgment. -/
theorem chooseRuntimeWordMatch?_iff {value : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat} :
    chooseRuntimeWordMatch? value cases defaultBody = some (selected, tests) ↔
      RuntimeWordMatchChooses value cases defaultBody selected tests := by
  constructor
  · exact selection_sound
  · intro choice
    induction choice with
    | fallback => simp only [chooseRuntimeWordMatch?, Option.map_some]
    | wildcard meaning =>
        simp only [chooseRuntimeWordMatch?, interpretWordMatchPattern?_iff.mpr meaning]
    | hit meaning =>
        simp only [chooseRuntimeWordMatch?, interpretWordMatchPattern?_iff.mpr meaning, ↓reduceIte]
    | miss meaning different _ ih =>
        simp only [chooseRuntimeWordMatch?, interpretWordMatchPattern?_iff.mpr meaning,
          different, ↓reduceIte, ih, Option.map_some]

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.RuntimeCapturedOwnerProperties
/- First-match rows are transported without uniqueness or runtime typing.
Injective owner maps preserve key distinctions and the exact fresh binder index. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Lookup returns the mapped complete payload, or the same absence, at the mapped key. -/
theorem lookup?_mapRuntimeCapturedOwners
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (captured : Resolved.LocalScope RuntimeValue) (id : Resolved.LocalId) :
    Resolved.LocalScope.lookup? (mapRuntimeCapturedOwners mapping captured) (ownerLocalIdMap mapping id) =
      (Resolved.LocalScope.lookup? captured id).map (RuntimeValue.mapOwners mapping) := by
  have keyInjective := ownerLocalIdMap_injective mapping injective
  induction captured with
  | nil => rfl
  | cons row tail ih =>
    rcases row with ⟨candidate,value⟩
    by_cases same : candidate=id
    · simp only [mapRuntimeCapturedOwners,List.map_cons,Resolved.LocalScope.lookup?,
        keyInjective.eq_iff,if_pos same,Option.map_some]
    · simpa only [mapRuntimeCapturedOwners,List.map_cons,Resolved.LocalScope.lookup?,
        keyInjective.eq_iff,if_neg same] using ih

/-- An independent first-match witness selects the same row and structurally mapped value. -/
theorem mapRuntimeCapturedOwners_lookup
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    {captured : Resolved.LocalScope RuntimeValue} {id : Resolved.LocalId} {value : RuntimeValue}
    (found : Resolved.LocalScope.Lookup captured id value) :
    Resolved.LocalScope.Lookup (mapRuntimeCapturedOwners mapping captured) (ownerLocalIdMap mapping id)
      (value.mapOwners mapping) := by
  apply Resolved.LocalScope.lookup?_iff.mp
  rw [lookup?_mapRuntimeCapturedOwners mapping injective,Resolved.LocalScope.lookup?_iff.mpr found]
  rfl

/-- Fresh allocation commutes with owner relabeling of the exact saved name rows. -/
theorem freshLocalId_mapRuntimeNamesOwners
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) :
    Resolved.freshLocalId (mapping owner)
        ((LocalNameTable.mapIds (ownerLocalIdMap mapping) names).map Prod.snd) =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner (names.map Prod.snd)) := by
  simpa only [LocalNameTable.mapIds,List.map_map,Function.comp_def,ownerLocalIdMap,
    Resolved.freshLocalId_owner] using
    Resolved.freshLocalId_map_owner mapping injective owner (names.map Prod.snd)

/-- Owner relabeling preserves exact selected syntax and visited literal count, including absence. -/
theorem chooseRuntimeWordMatch?_mapOwners
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (value : RuntimeValue)
    (cases : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) :
    chooseRuntimeWordMatch? (value.mapOwners mapping) cases defaultBody =
      chooseRuntimeWordMatch? value cases defaultBody := by
  cases cases with
  | nil => rfl
  | cons first rest =>
    cases pattern : interpretWordMatchPattern? first.value.pattern with
    | none => simp only [chooseRuntimeWordMatch?,pattern]
    | some tag =>
      cases tag with
      | none => simp only [chooseRuntimeWordMatch?,pattern]
      | some literal =>
        cases value <;> simp only [chooseRuntimeWordMatch?,pattern,RuntimeValue.mapOwners]

/-- Independent original choice has the same selected body/count after mapping mixed values. -/
theorem runtimeWordMatchChooses_mapOwners_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) {value : RuntimeValue}
    {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat} :
    RuntimeWordMatchChooses (value.mapOwners mapping) cases defaultBody selected tests ↔
      RuntimeWordMatchChooses value cases defaultBody selected tests := by
  simp only [← chooseRuntimeWordMatch?_iff,chooseRuntimeWordMatch?_mapOwners]

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.SourceComputationBody
/-! Source computation-body evaluation and embedding properties. -/

/-!
## Consolidated module: `Solcore.Frontend.SourceComputationBodyEvaluation`
-/

/-! Nine original raw body forms over mixed values with explicit-owner child
evaluation. Annotations and unselected branches are unchecked; no scope guard,
heap snapshot, closed evaluator, execution cost or failure classification is added. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Original successful body rules with actual mixed stores and ordered rows.
Initializers precede binding; branches use current stores without static guards. -/
inductive SourceComputationBodyEvaluates
    (ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
      RuntimeValue → List RuntimeValue → Prop)
    (owner : Resolved.DeclarationId) :
    List (String × Resolved.LocalId) → List (Resolved.LocalId × RuntimeValue) →
    List RuntimeValue → Syntax.Block → RuntimeValue → List RuntimeValue → Prop where
  | bare {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : List RuntimeValue} :
      SourceComputationBodyEvaluates ChildEval owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (child : ChildEval owner table environment initialStore source value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore
  | block {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (child : SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore
  | binding {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {boundValue value : RuntimeValue}
      (initializerEvaluation : ChildEval owner table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : SourceComputationBodyEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore
  | inferred {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {boundValue value : RuntimeValue}
      (initializerEvaluation : ChildEval owner table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : SourceComputationBodyEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ value finalStore
  | discard {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {discardedValue value : RuntimeValue}
      (expressionEvaluation : ChildEval owner table environment initialStore expression discardedValue middleStore)
      (tailEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment middleStore
        ⟨blockSpan, rest⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ value finalStore
  | ifTrue {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (conditionEvaluation : ChildEval owner table environment initialStore condition (.bool true) middleStore)
      (branchEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment middleStore thenBody value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (conditionEvaluation : ChildEval owner table environment initialStore condition (.bool false) middleStore)
      (branchEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment middleStore elseBody value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

  | wordMatch {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block}
      {initialStore middleStore finalStore : List RuntimeValue} {scrutineeValue value : RuntimeValue} {tests : Nat}
      (scrutineeEvaluation : ChildEval owner table environment initialStore scrutinee scrutineeValue middleStore)
      (choice : RuntimeWordMatchChooses scrutineeValue cases defaultBody selected tests)
      (branchEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment
        middleStore selected value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩
          ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩ value finalStore

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.SourceComputationBodyEvaluationProperties`
-/

/-! Body value/store determinism requires only the fixed owner's child law.
No cost, checking, typing, image or world assumption is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Value/store uniqueness follows solely from the fixed owner's child law;
no typing, child completeness, image or execution-cost premise is required. -/
theorem SourceComputationBodyEvaluates.deterministic
    {ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
      RuntimeValue → List RuntimeValue → Prop}
    {owner : Resolved.DeclarationId}
    (childDeterministic : ∀ {table environment initialStore source left right leftStore rightStore},
      ChildEval owner table environment initialStore source left leftStore →
      ChildEval owner table environment initialStore source right rightStore →
      left = right ∧ leftStore = rightStore)
    {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
    {initialStore : List RuntimeValue} {body : Syntax.Block} {left right : RuntimeValue}
    {leftStore rightStore : List RuntimeValue}
    (first : SourceComputationBodyEvaluates ChildEval owner table environment initialStore body left leftStore)
    (second : SourceComputationBodyEvaluates ChildEval owner table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first generalizing right rightStore with
  | bare => cases second; exact ⟨rfl, rfl⟩
  | expression child =>
      cases second with
      | expression other => exact childDeterministic child other
  | block _ ih =>
      cases second with
      | block other => exact ih other
  | binding initializer _ ih =>
      cases second with
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := childDeterministic initializer otherInitializer
          exact ih otherTail
  | inferred initializer _ ih =>
      cases second with
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := childDeterministic initializer otherInitializer
          exact ih otherTail
  | discard expression _ ih =>
      cases second with
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl⟩ := childDeterministic expression otherExpression
          exact ih otherTail
  | ifTrue condition _ ih =>
      cases second with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := childDeterministic condition otherCondition
          exact ih otherBranch
      | ifFalse otherCondition _ => cases (childDeterministic condition otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | ifTrue otherCondition _ => cases (childDeterministic condition otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := childDeterministic condition otherCondition
          exact ih otherBranch
  | wordMatch scrutinee choice _ ih =>
      cases second with
      | wordMatch otherScrutinee otherChoice otherBranch =>
          obtain ⟨rfl, rfl⟩ := childDeterministic scrutinee otherScrutinee
          obtain ⟨rfl, rfl⟩ := choice.deterministic otherChoice
          exact ih otherBranch

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.SourceComputationBodyEmbeddingProperties`
-/

/-! One-way child embedding permits extra mixed behavior. Exact reflection needs
all actual mixed child outputs/stores to factor through the old image; endpoint-only
image agreement is insufficient. This is not full enriched-language conservativity. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {OldChild : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr →
  Core.Value → Core.Store → Prop}
variable {MixedChild : Resolved.DeclarationId → LocalNameTable →
  List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
  RuntimeValue → List RuntimeValue → Prop}
variable {owner : Resolved.DeclarationId}

/-- Embed each old body derivation under a one-way child embedding law.
The mixed child may have additional successful behavior outside the old image. -/
theorem SourceComputationBodyEvaluates.ofCore
    (childEmbed : ∀ {table environment initialStore source value finalStore},
      OldChild table environment initialStore source value finalStore →
      MixedChild owner table
        (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
        (initialStore.map RuntimeValue.ofCore) source (RuntimeValue.ofCore value)
        (finalStore.map RuntimeValue.ofCore))
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ComputationReturnTreeEvaluates OldChild owner table environment
      initialStore body value finalStore) :
    SourceComputationBodyEvaluates MixedChild owner table
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body (RuntimeValue.ofCore value)
      (finalStore.map RuntimeValue.ofCore) := by
  induction evaluation with
  | bare => simp only [RuntimeValue.ofCore]; exact .bare
  | expression child => exact .expression (childEmbed child)
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding (childEmbed initializer) ih
  | inferred initializer _ ih => exact .inferred (childEmbed initializer) ih
  | discard child _ ih => exact .discard (childEmbed child) ih
  | ifTrue child _ ih =>
      exact .ifTrue (by simpa only [RuntimeValue.ofCore] using childEmbed child) ih
  | ifFalse child _ ih =>
      exact .ifFalse (by simpa only [RuntimeValue.ofCore] using childEmbed child) ih
  | wordMatch child choice _ ih =>
      exact .wordMatch (childEmbed child) (runtimeWordMatchChooses_ofCore_iff.mpr choice) ih

private theorem body_reflect
    (childExact : ∀ {table environment initialStore source mixedValue mixedFinal},
      MixedChild owner table
        (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
        (initialStore.map RuntimeValue.ofCore) source mixedValue mixedFinal ↔
      ∃ value finalStore,
        mixedValue = RuntimeValue.ofCore value ∧
        mixedFinal = finalStore.map RuntimeValue.ofCore ∧
        OldChild table environment initialStore source value finalStore)
    {table : LocalNameTable} {mixedEnvironment : List (Resolved.LocalId × RuntimeValue)}
    {mixedInitial mixedFinal : List RuntimeValue} {body : Syntax.Block} {mixedValue : RuntimeValue}
    (evaluation : SourceComputationBodyEvaluates MixedChild owner table mixedEnvironment
      mixedInitial body mixedValue mixedFinal) :
    ∀ (environment : Resolved.Environment) (initialStore : Core.Store),
      mixedEnvironment = environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)) →
      mixedInitial = initialStore.map RuntimeValue.ofCore →
      ∃ value finalStore,
        mixedValue = RuntimeValue.ofCore value ∧
        mixedFinal = finalStore.map RuntimeValue.ofCore ∧
        ComputationReturnTreeEvaluates OldChild owner table environment initialStore body value finalStore := by
  induction evaluation with
  | bare =>
      intro environment initialStore environmentSame storeSame
      exact ⟨.unit, initialStore, by simp only [RuntimeValue.ofCore], storeSame, .bare⟩
  | expression child =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨value, finalStore, valueSame, finalSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      exact ⟨value, finalStore, valueSame, finalSame, .expression oldChild⟩
  | block _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨value, finalStore, valueSame, finalSame, oldBody⟩ :=
        ih environment initialStore environmentSame storeSame
      exact ⟨value, finalStore, valueSame, finalSame, .block oldBody⟩
  | binding initializer _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨bound, middleStore, boundSame, middleSame, oldInitializer⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ initializer)
      obtain ⟨value, finalStore, valueSame, finalSame, oldTail⟩ :=
        ih ((_, bound) :: environment) middleStore
          (by rw [environmentSame, boundSame]; rfl) middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .binding oldInitializer oldTail⟩
  | inferred initializer _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨bound, middleStore, boundSame, middleSame, oldInitializer⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ initializer)
      obtain ⟨value, finalStore, valueSame, finalSame, oldTail⟩ :=
        ih ((_, bound) :: environment) middleStore
          (by rw [environmentSame, boundSame]; rfl) middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .inferred oldInitializer oldTail⟩
  | discard child _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨discarded, middleStore, discardedSame, middleSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      obtain ⟨value, finalStore, valueSame, finalSame, oldTail⟩ :=
        ih environment middleStore environmentSame middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .discard oldChild oldTail⟩
  | ifTrue child _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨condition, middleStore, conditionSame, middleSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      have actualBool : Core.Value.bool true = condition := RuntimeValue.ofCore_injective
        (by simpa only [RuntimeValue.ofCore] using conditionSame)
      cases actualBool
      obtain ⟨value, finalStore, valueSame, finalSame, oldBranch⟩ :=
        ih environment middleStore environmentSame middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .ifTrue oldChild oldBranch⟩
  | ifFalse child _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨condition, middleStore, conditionSame, middleSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      have actualBool : Core.Value.bool false = condition := RuntimeValue.ofCore_injective
        (by simpa only [RuntimeValue.ofCore] using conditionSame)
      cases actualBool
      obtain ⟨value, finalStore, valueSame, finalSame, oldBranch⟩ :=
        ih environment middleStore environmentSame middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .ifFalse oldChild oldBranch⟩
  | wordMatch child choice _ ih =>
      intro environment initialStore environmentSame storeSame
      obtain ⟨scrutinee, middleStore, scrutineeSame, middleSame, oldChild⟩ :=
        childExact.mp (environmentSame ▸ storeSame ▸ child)
      have oldChoice := runtimeWordMatchChooses_ofCore_iff.mp (scrutineeSame ▸ choice)
      obtain ⟨value, finalStore, valueSame, finalSame, oldBranch⟩ :=
        ih environment middleStore environmentSame middleSame
      exact ⟨value, finalStore, valueSame, finalSame, .wordMatch oldChild oldChoice oldBranch⟩

/-- Exact image reflection quantifies over every actual mixed result and store.
Its stronger child premise is not generally satisfied by source-creating extensions;
old-image endpoint agreement alone cannot recover discarded intermediate values. -/
theorem sourceComputationBodyEvaluates_ofCore_inputs_iff
    (childExact : ∀ {table environment initialStore source mixedValue mixedFinal},
      MixedChild owner table
        (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
        (initialStore.map RuntimeValue.ofCore) source mixedValue mixedFinal ↔
      ∃ value finalStore,
        mixedValue = RuntimeValue.ofCore value ∧
        mixedFinal = finalStore.map RuntimeValue.ofCore ∧
        OldChild table environment initialStore source value finalStore)
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {mixedValue : RuntimeValue} {mixedFinal : List RuntimeValue} :
    SourceComputationBodyEvaluates MixedChild owner table
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body mixedValue mixedFinal ↔
    ∃ value finalStore,
      mixedValue = RuntimeValue.ofCore value ∧
      mixedFinal = finalStore.map RuntimeValue.ofCore ∧
      ComputationReturnTreeEvaluates OldChild owner table environment initialStore body value finalStore := by
  constructor
  · intro evaluated
    exact body_reflect childExact evaluated environment initialStore rfl rfl
  · rintro ⟨value, finalStore, rfl, rfl, oldBody⟩
    exact SourceComputationBodyEvaluates.ofCore
      (fun child => childExact.mpr ⟨_, _, rfl, rfl, child⟩) oldBody

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.SourceLambdaEvaluation
/-!
Opt-in original source closure construction and unary call sequencing over mixed values.
Unmarked syntax does not establish canonical runtime staging: annotation meanings are
never inspected. These success rules do not close the supplied callbacks recursively
or classify failures, divergence, costs or effects of unsuccessful computations.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Unmarked unary syntax only; annotation meaning and canonical staging are not checked. -/
inductive SourceUnaryLambdaShape : Syntax.Expr → Syntax.Identifier → Syntax.Block → Prop where
  | inferred {span keyword parametersSpan parameterSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {body : Syntax.Block} :
      SourceUnaryLambdaShape
        ⟨span, .lambda keyword ⟨parametersSpan, [⟨parameterSpan, .inferred name⟩]⟩ annotation body⟩
        name body
  | typed {span keyword parametersSpan parameterSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {parameterAnnotation : Syntax.TypeExpr}
      {annotation : Option Syntax.TypeExpr} {body : Syntax.Block} :
      SourceUnaryLambdaShape
        ⟨span, .lambda keyword
          ⟨parametersSpan, [⟨parameterSpan, .typed none name parameterAnnotation⟩]⟩ annotation body⟩
        name body

/-- Decode only the original direct unary shape, retaining the name/body verbatim.
Unsupported syntax is absent from this profile, not classified as a runtime fault. -/
def sourceUnaryLambdaShape? (source : Syntax.Expr) : Option (Syntax.Identifier × Syntax.Block) :=
  match source.value with
  | .lambda _ ⟨_, [parameter]⟩ _ body =>
      match parameter.value with
      | .inferred name => some (name, body)
      | .typed none name _ => some (name, body)
      | _ => none
  | _ => none

/-- Creation captures every original row without running the body or taking a heap
snapshot. Calls sequence actual stores through caller callee/argument evaluation and
then the saved source body. Fresh IDs depend on saved name rows only. -/
inductive SourceLambdaEvaluates
    (ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
      RuntimeValue → List RuntimeValue → Prop)
    (BodyEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Block →
      RuntimeValue → List RuntimeValue → Prop)
    (owner : Resolved.DeclarationId) (names : List (String × Resolved.LocalId))
    (captured : List (Resolved.LocalId × RuntimeValue)) :
    List RuntimeValue → Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | creation {store : List RuntimeValue} {source : Syntax.Expr}
      {name : Syntax.Identifier} {body : Syntax.Block}
      (shape : SourceUnaryLambdaShape source name body) :
      SourceLambdaEvaluates ChildEval BodyEval owner names captured store source
        (.sourceClosure source owner names captured) store
  | call {initialStore calleeStore argumentStore finalStore : List RuntimeValue}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument source : Syntax.Expr}
      {savedOwner : Resolved.DeclarationId} {savedNames : List (String × Resolved.LocalId)}
      {savedCaptured : List (Resolved.LocalId × RuntimeValue)}
      {name : Syntax.Identifier} {body : Syntax.Block} {argumentValue result : RuntimeValue}
      (shape : SourceUnaryLambdaShape source name body)
      (calleeEvaluation : ChildEval owner names captured initialStore callee
        (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore)
      (argumentEvaluation : ChildEval owner names captured calleeStore argument argumentValue argumentStore)
      (bodyEvaluation : BodyEval savedOwner
        ((name.value, Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)) :: savedNames)
        ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd), argumentValue) :: savedCaptured)
        argumentStore body result finalStore) :
      SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.SourceLambdaEvaluationProperties`
-/

/-!
Exact independent shape/operational decomposition and conditional determinism.
No typing, staging, elaboration, row alignment or world assumptions are added.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Shape decoding is exactly the independent original-source judgment. -/
theorem sourceUnaryLambdaShape?_iff {source : Syntax.Expr} {name : Syntax.Identifier}
    {body : Syntax.Block} :
    sourceUnaryLambdaShape? source = some (name, body) ↔ SourceUnaryLambdaShape source name body := by
  constructor
  · intro accepted
    rcases source with ⟨span, source⟩
    cases source <;> simp only [sourceUnaryLambdaShape?, reduceCtorEq] at accepted
    rename_i keyword parameters annotation body
    rcases parameters with ⟨parametersSpan, parameters⟩
    cases parameters with
    | nil => cases accepted
    | cons parameter rest =>
        cases rest with
        | cons next rest => cases accepted
        | nil =>
            rcases parameter with ⟨parameterSpan, parameter⟩
            cases parameter with
            | inferred inferredName =>
                cases Option.some.inj accepted
                exact .inferred
            | typed marker typedName parameterAnnotation =>
                cases marker with
                | some marker => cases accepted
                | none =>
                    cases Option.some.inj accepted
                    exact .typed
            | error => cases accepted
  · intro shape
    cases shape <;> rfl

private theorem shape_unique {source : Syntax.Expr} {leftName rightName : Syntax.Identifier}
    {leftBody rightBody : Syntax.Block}
    (left : SourceUnaryLambdaShape source leftName leftBody)
    (right : SourceUnaryLambdaShape source rightName rightBody) :
    leftName = rightName ∧ leftBody = rightBody :=
  Prod.mk.inj (Option.some.inj
    ((sourceUnaryLambdaShape?_iff.mpr left).symm.trans (sourceUnaryLambdaShape?_iff.mpr right)))

variable {ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
  List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
  RuntimeValue → List RuntimeValue → Prop}
variable {BodyEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
  List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Block →
  RuntimeValue → List RuntimeValue → Prop}

/-- A supported original lambda creates precisely its full captured datum and keeps
the store unchanged, irrespective of the supplied expression/body relations. -/
theorem SourceLambdaEvaluates.creation_iff
    {owner : Resolved.DeclarationId} {names : List (String × Resolved.LocalId)}
    {captured : List (Resolved.LocalId × RuntimeValue)} {initialStore finalStore : List RuntimeValue}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block} {value : RuntimeValue}
    (shape : SourceUnaryLambdaShape source name body) :
    SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore source value finalStore ↔
      value = .sourceClosure source owner names captured ∧ finalStore = initialStore := by
  constructor
  · intro evaluated
    cases shape <;> cases evaluated <;> exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .creation shape

/-- Original unary calls expose both caller-side intermediate stores and the exact
saved lexical scope used for the original body with its one fresh argument row. -/
theorem SourceLambdaEvaluates.call_iff
    {owner : Resolved.DeclarationId} {names : List (String × Resolved.LocalId)}
    {captured : List (Resolved.LocalId × RuntimeValue)} {initialStore finalStore : List RuntimeValue}
    {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr} {result : RuntimeValue} :
    SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore
      ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore ↔
      ∃ source savedOwner savedNames savedCaptured name body calleeStore argumentValue argumentStore,
        SourceUnaryLambdaShape source name body ∧
        ChildEval owner names captured initialStore callee
          (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore ∧
        ChildEval owner names captured calleeStore argument argumentValue argumentStore ∧
        BodyEval savedOwner
          ((name.value, Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)) :: savedNames)
          ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd), argumentValue) :: savedCaptured)
          argumentStore body result finalStore := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | call shape calleeEvaluation argumentEvaluation bodyEvaluation =>
        exact ⟨_, _, _, _, _, _, _, _, _, shape, calleeEvaluation, argumentEvaluation, bodyEvaluation⟩
  · rintro ⟨_, _, _, _, _, _, _, _, _, shape, calleeEvaluation, argumentEvaluation, bodyEvaluation⟩
    exact .call shape calleeEvaluation argumentEvaluation bodyEvaluation

/-- Value/store determinism follows only when each fixed callback is deterministic.
This success-only law says nothing about failing or diverging effect prefixes. -/
theorem SourceLambdaEvaluates.deterministic
    (childDeterministic : ∀ {owner names captured initialStore source left leftStore right rightStore},
      ChildEval owner names captured initialStore source left leftStore →
      ChildEval owner names captured initialStore source right rightStore →
      left = right ∧ leftStore = rightStore)
    (bodyDeterministic : ∀ {owner names captured initialStore source left leftStore right rightStore},
      BodyEval owner names captured initialStore source left leftStore →
      BodyEval owner names captured initialStore source right rightStore →
      left = right ∧ leftStore = rightStore)
    {owner : Resolved.DeclarationId} {names : List (String × Resolved.LocalId)}
    {captured : List (Resolved.LocalId × RuntimeValue)} {initialStore : List RuntimeValue}
    {source : Syntax.Expr} {left right : RuntimeValue} {leftStore rightStore : List RuntimeValue}
    (first : SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore source left leftStore)
    (second : SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  cases first with
  | creation shape =>
      obtain ⟨value, store⟩ := (creation_iff shape).mp second
      exact ⟨value.symm, store.symm⟩
  | call shape calleeEvaluation argumentEvaluation bodyEvaluation =>
      obtain ⟨_, _, _, _, _, _, _, _, _, otherShape, otherCallee, otherArgument, otherBody⟩ :=
        call_iff.mp second
      obtain ⟨sameCallee, sameCalleeStore⟩ := childDeterministic calleeEvaluation otherCallee
      cases sameCallee
      cases sameCalleeStore
      obtain ⟨sameArgument, sameArgumentStore⟩ := childDeterministic argumentEvaluation otherArgument
      cases sameArgument
      cases sameArgumentStore
      obtain ⟨sameName, sameBody⟩ := shape_unique shape otherShape
      cases sameName
      cases sameBody
      exact bodyDeterministic bodyEvaluation otherBody

end Solcore.Frontend
end
