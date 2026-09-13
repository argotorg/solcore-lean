import Solcore.Frontend.RuntimeValueOwner
import Solcore.Resolved.FreshIdentity
import Solcore.Resolved.LocalScopeProperties
import Solcore.Frontend.RuntimeWordMatchSelection

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
