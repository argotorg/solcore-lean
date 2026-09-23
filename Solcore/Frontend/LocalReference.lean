import Solcore.Syntax.Term
import Solcore.Resolved.Expr
import Solcore.Resolved.Typing
import Solcore.Resolved.LoweringProperties
import Solcore.Resolved.Eval
import Solcore.Core.Machine
import Solcore.Core.Safety

/-! A deliberately narrow canonical-syntax adapter. The caller supplies the
ordered name table; first match specifies table behavior, not a source-language
shadowing or allocation policy. No global, import, or class resolution occurs. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Explicit caller-supplied spellings and already assigned local identities. -/
abbrev LocalNameTable := List (String × Resolved.LocalId)

namespace LocalNameTable

/-- Exact spelling lookup; neither source ranges nor spelling normalization participate. -/
def lookup? : LocalNameTable → String → Option Resolved.LocalId
  | [], _ => none
  | (candidate, id) :: table, spelling =>
      if candidate = spelling then some id else lookup? table spelling

/-- Independent first-occurrence lookup, including repeated caller-supplied names. -/
inductive Lookup : LocalNameTable → String → Resolved.LocalId → Prop where
  | head {table spelling id} : Lookup ((spelling, id) :: table) spelling id
  | tail {table spelling candidate id candidateId}
      (different : candidate ≠ spelling) (found : Lookup table spelling id) :
      Lookup ((candidate, candidateId) :: table) spelling id

end LocalNameTable

/-- Only a named reference, optionally grouped, is supported here. `none` means
unmapped or unsupported by this adapter, not rejection by the source language.
`Identifier.value` contains the exact spelling; no lexical or span validity is assumed. -/
def resolveLocalReference? (table : LocalNameTable) (source : Syntax.Expr) :
    Option Resolved.Expr :=
  match source with
  | ⟨_, .identifier name⟩ => (table.lookup? name.value).map Resolved.Expr.var
  | ⟨_, .group inner⟩ => resolveLocalReference? table inner
  | _ => none
termination_by sizeOf source

/-- A parser-independent bridge from canonical reference syntax to a supplied ID. -/
inductive ResolvesLocalReference (table : LocalNameTable) :
    Syntax.Expr → Resolved.LocalId → Prop where
  | identifier {span : Syntax.SourceSpan} {name : Syntax.Identifier} {id : Resolved.LocalId}
      (found : LocalNameTable.Lookup table name.value id) :
      ResolvesLocalReference table { span, value := .identifier name } id
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr} {id : Resolved.LocalId}
      (resolved : ResolvesLocalReference table inner id) :
      ResolvesLocalReference table { span, value := .group inner } id

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalReferenceElaboration`
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Resolve a supported canonical reference, locate its identity in the supplied
context, and return its Core variable and type. `none` is adapter failure, not a
source-language rejection. No identity receives a default index or type. -/
def elaborateLocalReference? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) := do
  let resolved ← resolveLocalReference? table source
  let core ← resolved.lower? (Resolved.LocalScope.ids context)
  let type ← Core.infer? (Resolved.LocalScope.values context) core
  return (core, type)

/-- Independent typing of the supported canonical reference fragment against
two explicit first-match tables. No lexical validity or source shadowing policy
is assumed, and no typing rule for unsupported expression forms is introduced. -/
inductive LocalReferenceHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | resolved {source : Syntax.Expr} {id : Resolved.LocalId} {type : Core.Ty}
      (reference : ResolvesLocalReference table source id)
      (found : Resolved.LocalScope.Lookup context id type) :
      LocalReferenceHasType table context source type

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalReferenceProperties`
-/

/-! Exact first-match lookup and the identifier/group bridge. These laws do not
assume lexical validity, source-span validity, or any source scope policy. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace LocalNameTable

theorem lookup?_iff {table : LocalNameTable} {spelling : String} {id : Resolved.LocalId} :
    lookup? table spelling = some id ↔ Lookup table spelling id := by
  constructor
  · intro result
    induction table with
    | nil => simp [lookup?] at result
    | cons entry rest ih =>
        rcases entry with ⟨candidate, candidateId⟩
        by_cases same : candidate = spelling
        · subst candidate
          simp only [lookup?, ↓reduceIte, Option.some.injEq] at result
          subst candidateId
          exact .head
        · exact .tail same (ih (by simpa only [lookup?, if_neg same] using result))
  · intro found
    induction found with
    | head => simp [lookup?]
    | tail different _ ih => simpa only [lookup?, if_neg different] using ih

theorem Lookup.id_unique {table : LocalNameTable} {spelling : String}
    {left right : Resolved.LocalId} (leftFound : Lookup table spelling left)
    (rightFound : Lookup table spelling right) : left = right :=
  Option.some.inj ((lookup?_iff.mpr leftFound).symm.trans (lookup?_iff.mpr rightFound))

theorem Lookup.mem {table : LocalNameTable} {spelling : String} {id : Resolved.LocalId}
    (found : Lookup table spelling id) : (spelling, id) ∈ table := by
  induction found with
  | head => exact List.mem_cons_self
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih

theorem lookup?_eq_none_iff {table : LocalNameTable} {spelling : String} :
    lookup? table spelling = none ↔ spelling ∉ table.map Prod.fst := by
  induction table with
  | nil => simp [lookup?]
  | cons entry rest ih =>
      rcases entry with ⟨candidate, candidateId⟩
      by_cases same : candidate = spelling
      · subst candidate; simp [lookup?]
      · simpa [lookup?, same, Ne.symm same] using ih

end LocalNameTable

theorem ResolvesLocalReference.complete {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (resolved : ResolvesLocalReference table source id) :
    resolveLocalReference? table source = some (.var id) := by
  induction resolved with
  | identifier found =>
      simp only [resolveLocalReference?, LocalNameTable.lookup?_iff.mpr found, Option.map_some]
  | group _ ih => simpa only [resolveLocalReference?] using ih

/-- Every successful result is a variable with an independent source/table derivation. -/
theorem resolveLocalReference?_sound {table : LocalNameTable}
    {source : Syntax.Expr} {output : Resolved.Expr}
    (result : resolveLocalReference? table source = some output) :
    ∃ id, output = .var id ∧ ResolvesLocalReference table source id := by
  cases source with
  | mk span payload =>
      cases payload <;> simp only [resolveLocalReference?, reduceCtorEq] at result
      case identifier name =>
        cases found : table.lookup? name.value with
        | none => simp only [found, Option.map_none, reduceCtorEq] at result
        | some id =>
            simp only [found, Option.map_some, Option.some.injEq] at result
            exact ⟨id, result.symm, .identifier (LocalNameTable.lookup?_iff.mp found)⟩
      case group inner =>
        obtain ⟨id, outputEq, child⟩ := resolveLocalReference?_sound result
        exact ⟨id, outputEq, .group child⟩
termination_by sizeOf source

theorem resolveLocalReference?_iff {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId} :
    resolveLocalReference? table source = some (.var id) ↔
      ResolvesLocalReference table source id := by
  constructor
  · intro result
    obtain ⟨actual, same, resolved⟩ := resolveLocalReference?_sound result
    cases same
    exact resolved
  · exact ResolvesLocalReference.complete

theorem resolveLocalReference?_eq_some_iff {table : LocalNameTable}
    {source : Syntax.Expr} {output : Resolved.Expr} :
    resolveLocalReference? table source = some output ↔
      ∃ id, ResolvesLocalReference table source id ∧ output = .var id := by
  constructor
  · intro result
    obtain ⟨id, same, resolved⟩ := resolveLocalReference?_sound result
    exact ⟨id, resolved, same⟩
  · rintro ⟨id, resolved, rfl⟩
    exact resolved.complete

theorem ResolvesLocalReference.id_unique {table : LocalNameTable}
    {source : Syntax.Expr} {left right : Resolved.LocalId}
    (leftResolved : ResolvesLocalReference table source left)
    (rightResolved : ResolvesLocalReference table source right) : left = right :=
  Resolved.Expr.var.inj (Option.some.inj (leftResolved.complete.symm.trans rightResolved.complete))

/-- A successful adapter result comes from an actual supplied name/ID entry. -/
theorem ResolvesLocalReference.mem {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (resolved : ResolvesLocalReference table source id) :
    ∃ spelling, (spelling, id) ∈ table := by
  induction resolved with
  | identifier found => exact ⟨_, found.mem⟩
  | group _ ih => exact ih

theorem resolveLocalReference?_eq_none_iff {table : LocalNameTable} {source : Syntax.Expr} :
    resolveLocalReference? table source = none ↔ ¬ ∃ id, ResolvesLocalReference table source id := by
  constructor
  · intro result ⟨id, resolved⟩
    have accepted := resolved.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : resolveLocalReference? table source with
    | none => rfl
    | some output =>
        obtain ⟨id, _, resolved⟩ := resolveLocalReference?_sound result
        exact False.elim (absent ⟨id, resolved⟩)

/-- Replacing only the expression's outer source range has no semantic effect. -/
theorem resolveLocalReference?_span (table : LocalNameTable) (source : Syntax.Expr)
    (span : Syntax.SourceSpan) :
    resolveLocalReference? table { source with span } = resolveLocalReference? table source := by
  cases source with
  | mk sourceSpan payload => cases payload <;> simp only [resolveLocalReference?]

/-- Both occurrence ranges are ignored; equality of exact spellings is sufficient. -/
theorem resolveLocalReference?_identifier_value_eq (table : LocalNameTable)
    {left right : Syntax.Identifier} (same : left.value = right.value)
    (leftSpan rightSpan : Syntax.SourceSpan) :
    resolveLocalReference? table { span := leftSpan, value := .identifier left } =
      resolveLocalReference? table { span := rightSpan, value := .identifier right } := by
  simp only [resolveLocalReference?, same]

theorem resolveLocalReference?_group (table : LocalNameTable) (span : Syntax.SourceSpan)
    (inner : Syntax.Expr) :
    resolveLocalReference? table { span, value := .group inner } = resolveLocalReference? table inner := by
  simp only [resolveLocalReference?]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalReferenceElaborationProperties`
-/

/-! Exact typed elaboration for canonical identifiers and grouping. Both tables
remain arbitrary ordered inputs, including duplicate names and identities. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateLocalReference?_sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalReference? table context source = some (core, type)) :
    ∃ id index, ResolvesLocalReference table source id ∧
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids context) id index ∧
      Resolved.LocalScope.Lookup context id type ∧ core = .var index := by
  simp only [elaborateLocalReference?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨resolved, resolution, actualCore, lowering, actualType, inferred, result⟩ := accepted
  cases result
  obtain ⟨id, reference, rfl⟩ := resolveLocalReference?_eq_some_iff.mp resolution
  change (Resolved.LocalScope.index? (Resolved.LocalScope.ids context) id).map Core.Expr.var =
    some core at lowering
  simp only [Option.map_eq_some_iff] at lowering
  obtain ⟨index, indexResult, rfl⟩ := lowering
  have indexed := Resolved.LocalScope.index?_iff.mp indexResult
  have typed := Core.infer_sound inferred
  cases typed with
  | var atType =>
      exact ⟨id, index, reference, indexed,
        Resolved.LocalScope.lookup_of_indexed indexed atType, rfl⟩

theorem elaborateLocalReference?_complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {id : Resolved.LocalId} {index : Nat} {type : Core.Ty}
    (reference : ResolvesLocalReference table source id)
    (indexed : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids context) id index)
    (found : Resolved.LocalScope.Lookup context id type) :
    elaborateLocalReference? table context source = some (.var index, type) := by
  have lowering := (Resolved.Lowers.var indexed).complete
  have inferred := Core.infer_complete
    (Core.HasType.var ((Resolved.LocalScope.lookup_iff_getElem? indexed).mp found)
      (definitions := []))
  simp [elaborateLocalReference?, reference.complete, lowering, inferred]

theorem elaborateLocalReference?_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalReference? table context source = some (core, type) ↔
      ∃ id index, ResolvesLocalReference table source id ∧
        Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids context) id index ∧
        Resolved.LocalScope.Lookup context id type ∧ core = .var index := by
  constructor
  · exact elaborateLocalReference?_sound
  · rintro ⟨id, index, reference, indexed, found, rfl⟩
    exact elaborateLocalReference?_complete reference indexed found

/-- Independent reference typing is exactly the existence of a checked elaboration. -/
theorem localReferenceHasType_iff_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty} :
    LocalReferenceHasType table context source type ↔
      ∃ core, elaborateLocalReference? table context source = some (core, type) := by
  constructor
  · intro typing
    cases typing with
    | resolved reference found =>
        obtain ⟨index, indexed, _⟩ := found.indexed
        exact ⟨_, elaborateLocalReference?_complete reference indexed found⟩
  · rintro ⟨core, accepted⟩
    obtain ⟨id, index, reference, _, found, _⟩ := elaborateLocalReference?_sound accepted
    exact .resolved reference found

/-- Every returned type has the existing declarative Core typing derivation. -/
theorem elaborateLocalReference?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalReference? table context source = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  obtain ⟨id, index, _, indexed, found, rfl⟩ := elaborateLocalReference?_sound accepted
  exact .var ((Resolved.LocalScope.lookup_iff_getElem? indexed).mp found)

/-- A resolved name does not suffice: its ID must occur in the supplied context. -/
theorem elaborateLocalReference?_eq_none_of_missing_id {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {id : Resolved.LocalId}
    (reference : ResolvesLocalReference table source id)
    (missing : id ∉ Resolved.LocalScope.ids context) :
    elaborateLocalReference? table context source = none := by
  have indexMissing := Resolved.LocalScope.index?_eq_none_iff.mpr missing
  simp [elaborateLocalReference?, reference.complete, Resolved.Expr.lower?, indexMissing]

/-- Adapter failure is exactly absence of an independent supported-reference type. -/
theorem elaborateLocalReference?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} :
    elaborateLocalReference? table context source = none ↔
      ¬ ∃ type, LocalReferenceHasType table context source type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := localReferenceHasType_iff_elaborates.mp typing
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateLocalReference? table context source with
    | none => rfl
    | some pair =>
        exact False.elim (missing ⟨pair.2,
          localReferenceHasType_iff_elaborates.mpr ⟨pair.1, result⟩⟩)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalReferenceEvaluation`
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Independent evaluation of a supported canonical reference. Looking up a
local value does not call a closure, dereference a cell, or modify a store. -/
inductive LocalReferenceEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Syntax.Expr → Core.Value → Prop where
  | reference {source : Syntax.Expr} {id : Resolved.LocalId} {value : Core.Value}
      (resolved : ResolvesLocalReference table source id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      LocalReferenceEvaluates table environment source value

theorem LocalReferenceEvaluates.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {left right : Core.Value}
    (first : LocalReferenceEvaluates table environment source left)
    (second : LocalReferenceEvaluates table environment source right) : left = right := by
  cases first with
  | reference leftResolved leftFound =>
      cases second with
      | reference rightResolved rightFound =>
          cases leftResolved.id_unique rightResolved
          exact leftFound.value_unique rightFound

/-- Named reference evaluation selects an exact positional Core variable. -/
theorem LocalReferenceEvaluates.toCore
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {value : Core.Value} (evaluation : LocalReferenceEvaluates table environment source value)
    (store : Core.Store) :
    ∃ id index, ResolvesLocalReference table source id ∧
      Resolved.Lowers (Resolved.LocalScope.ids environment) (.var id) (.var index) ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store (.var index) value store := by
  cases evaluation with
  | reference resolved found =>
      obtain ⟨index, indexed, atValue⟩ := found.indexed
      exact ⟨_, index, resolved, .var indexed, .var atValue⟩

/-- References cost exactly one Core transition, independently of grouping
depth, source ranges, and the supplied store. At zero fuel the initial state is retained. -/
theorem LocalReferenceEvaluates.exact_run
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {value : Core.Value} (evaluation : LocalReferenceEvaluates table environment source value)
    (store : Core.Store) :
    ∃ id index, ResolvesLocalReference table source id ∧
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index ∧
      Core.runStateful 0
        (Core.State.initial (.var index) (Resolved.LocalScope.values environment) store) =
        .outOfFuel (Core.State.initial (.var index) (Resolved.LocalScope.values environment) store) ∧
      ∀ fuel, Core.runStateful (fuel + 1)
        (Core.State.initial (.var index) (Resolved.LocalScope.values environment) store) =
        .done value store := by
  cases evaluation with
  | reference resolved found =>
      obtain ⟨index, indexed, atValue⟩ := found.indexed
      refine ⟨_, index, resolved, indexed, ?_, ?_⟩
      · simp [Core.runStateful, Core.State.initial, Core.advance, atValue]
      · intro fuel
        simp [Core.runStateful, Core.State.initial, Core.advance, atValue]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalReferenceExecutionProperties`
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A checked source reference and its Core variable have exactly the same
evaluation. Context and environment must agree on identity order, including duplicates. -/
theorem elaborateLocalReference?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    {initialStore finalStore : Core.Store} {value : Core.Value}
    (accepted : elaborateLocalReference? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore ↔
      LocalReferenceEvaluates table environment source value ∧ finalStore = initialStore := by
  obtain ⟨id, index, reference, indexed, _, rfl⟩ := elaborateLocalReference?_sound accepted
  have envIndex : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index := by
    rw [sameIds]
    exact indexed
  constructor
  · intro evaluation
    cases evaluation with
    | var atValue =>
        exact ⟨.reference reference (Resolved.LocalScope.lookup_of_indexed envIndex atValue), rfl⟩
  · rintro ⟨evaluation, rfl⟩
    cases evaluation with
    | reference actual found =>
        cases reference.id_unique actual
        exact .var ((Resolved.LocalScope.lookup_iff_getElem? envIndex).mp found)

/-- An independently typed reference has a value in any matching typed environment. -/
theorem LocalReferenceHasType.evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalReferenceHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    ∃ value, LocalReferenceEvaluates table environment source value ∧ Core.ValueHasType value type := by
  cases typing with
  | resolved reference found =>
      rename_i id
      obtain ⟨index, indexed, atType⟩ := found.indexed
      obtain ⟨value, atValue, valueTyped⟩ := environmentTyped.lookup atType
      have envIndex : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index := by
        rw [sameIds]
        exact indexed
      exact ⟨value, .reference reference
        (Resolved.LocalScope.lookup_of_indexed envIndex atValue), valueTyped⟩

theorem LocalReferenceEvaluates.preserves_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty} {value : Core.Value}
    (evaluation : LocalReferenceEvaluates table environment source value)
    (typing : LocalReferenceHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    Core.ValueHasType value type := by
  obtain ⟨other, evaluated, valueTyped⟩ := typing.evaluates sameIds environmentTyped
  cases evaluation.deterministic evaluated
  exact valueTyped

/-- Checked grouping has no execution overhead: zero fuel retains the initial
state, and every positive Core fuel returns the independently selected value. -/
theorem elaborateLocalReference?_exact_run
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} {value : Core.Value}
    (accepted : elaborateLocalReference? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (evaluation : LocalReferenceEvaluates table environment source value)
    (store : Core.Store) :
    Core.runStateful 0 (Core.State.initial core (Resolved.LocalScope.values environment) store) =
      .outOfFuel (Core.State.initial core (Resolved.LocalScope.values environment) store) ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  have coreEvaluation := (elaborateLocalReference?_evaluates_iff accepted sameIds).mpr
    (show LocalReferenceEvaluates table environment source value ∧ store = store from ⟨evaluation, rfl⟩)
  obtain ⟨_, _, _, _, _, rfl⟩ := elaborateLocalReference?_sound accepted
  cases coreEvaluation with
  | var atValue =>
      constructor
      · simp [Core.runStateful, Core.State.initial, Core.advance, atValue]
      · intro fuel
        simp [Core.runStateful, Core.State.initial, Core.advance, atValue]

/-- The checked endpoint has a typed, store-preserving execution for every positive fuel. -/
theorem elaborateLocalReference?_typed_execution
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalReference? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) :
    ∃ value, LocalReferenceEvaluates table environment source value ∧
      Core.ValueHasType value type ∧
      ∀ fuel, Core.runStateful (fuel + 1)
        (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  have typing := localReferenceHasType_iff_elaborates.mpr ⟨core, accepted⟩
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates sameIds environmentTyped
  exact ⟨value, evaluation, valueTyped,
    (elaborateLocalReference?_exact_run accepted sameIds evaluation store).2⟩

end Solcore.Frontend
