import Solcore.Syntax.Operator
import Solcore.Core.Syntax
import Solcore.Resolved.Identity
import Solcore.Syntax.Term
import Solcore.Resolved.Expr
import Solcore.Resolved.Typing
import Solcore.Resolved.Eval
import Solcore.Core.Machine
import Solcore.Core.Safety
import Solcore.Core.Primitive
import Solcore.Syntax.Type
import Solcore.Frontend.WordLiteral

/-!
# Fragment foundations

Word binaries, word matches, named and structural types, and local references.
-/

section
-- leanmerge: from Solcore.Frontend.DirectWordBinary
/-! The fixed Word interpretation of the ten directly lowered source operators.
The finite relation is independent of checking and runtime evaluation. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive DirectWordBinary : Syntax.BinaryOp → Core.BinaryOp → Prop where
  | add : DirectWordBinary .add .wordAdd
  | subtract : DirectWordBinary .subtract .wordSub
  | multiply : DirectWordBinary .multiply .wordMul
  | divide : DirectWordBinary .divide .wordDiv
  | modulo : DirectWordBinary .modulo .wordMod
  | bitAnd : DirectWordBinary .bitAnd .wordAnd
  | bitOr : DirectWordBinary .bitOr .wordOr
  | bitXor : DirectWordBinary .bitXor .wordXor
  | greater : DirectWordBinary .greater .wordGt
  | equal : DirectWordBinary .equal .wordEq

def directWordBinary? : Syntax.BinaryOp → Option Core.BinaryOp
  | .add => some .wordAdd
  | .subtract => some .wordSub
  | .multiply => some .wordMul
  | .divide => some .wordDiv
  | .modulo => some .wordMod
  | .bitAnd => some .wordAnd
  | .bitOr => some .wordOr
  | .bitXor => some .wordXor
  | .greater => some .wordGt
  | .equal => some .wordEq
  | _ => none

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.DirectWordBinaryProperties`
-/

/-! One exact correspondence for the finite direct-operator interpretation. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem directWordBinary?_iff {source : Syntax.BinaryOp} {op : Core.BinaryOp} :
    directWordBinary? source = some op ↔ DirectWordBinary source op := by
  constructor
  · intro accepted
    cases source <;> simp only [directWordBinary?, Option.some.injEq, reduceCtorEq] at accepted
    all_goals subst op; constructor
  · intro operator
    cases operator <;> rfl

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.LocalOwnerRenaming
/-! Owner-only local identity relabeling shared by value-free declarations and
actual runtime binding. Binder indices are retained without an allocator claim. -/

set_option autoImplicit false

namespace Solcore.Frontend

def ownerLocalIdMap (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (id : Resolved.LocalId) : Resolved.LocalId :=
  ⟨mapping id.owner, id.binderIndex⟩

theorem ownerLocalIdMap_injective
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    Function.Injective (ownerLocalIdMap mapping) := by
  intro left right same
  have owners := injective (congrArg Resolved.LocalId.owner same)
  have indices := congrArg Resolved.LocalId.binderIndex same
  cases left
  cases right
  cases owners
  cases indices
  rfl

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.LocalReference
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
end

section
-- leanmerge: from Solcore.Frontend.StrictWordBinary
/- Independent meanings of the fourteen strict source Word binary operators
other than the shifts and the unchecked arithmetic, which this fragment does
not cover.
Both arguments are actual Words; comparison results are Boolean values.
The two short-circuit operators are excluded. Division and remainder at zero
retain the existing total unsigned Word conventions. -/
set_option autoImplicit false
namespace Solcore.Frontend

inductive StrictWordBinaryDenotes :
    Syntax.BinaryOp → Core.Word → Core.Word → Core.Value → Prop where
  | add {left right : Core.Word} :
      StrictWordBinaryDenotes .add left right (.word (left.add right))
  | subtract {left right : Core.Word} :
      StrictWordBinaryDenotes .subtract left right (.word (left.sub right))
  | multiply {left right : Core.Word} :
      StrictWordBinaryDenotes .multiply left right (.word (left.mul right))
  | divide {left right : Core.Word} :
      StrictWordBinaryDenotes .divide left right (.word (left.udiv right))
  | modulo {left right : Core.Word} :
      StrictWordBinaryDenotes .modulo left right (.word (left.umod right))
  | bitAnd {left right : Core.Word} :
      StrictWordBinaryDenotes .bitAnd left right (.word (left.bitAnd right))
  | bitOr {left right : Core.Word} :
      StrictWordBinaryDenotes .bitOr left right (.word (left.bitOr right))
  | bitXor {left right : Core.Word} :
      StrictWordBinaryDenotes .bitXor left right (.word (left.bitXor right))
  | greater {left right : Core.Word} :
      StrictWordBinaryDenotes .greater left right (.bool (decide (left > right)))
  | less {left right : Core.Word} :
      StrictWordBinaryDenotes .less left right (.bool (decide (left < right)))
  | equal {left right : Core.Word} :
      StrictWordBinaryDenotes .equal left right (.bool (left == right))
  | notEqual {left right : Core.Word} :
      StrictWordBinaryDenotes .notEqual left right (.bool (!(left == right)))
  | lessEqual {left right : Core.Word} :
      StrictWordBinaryDenotes .lessEqual left right (.bool (!(decide (left > right))))
  | greaterEqual {left right : Core.Word} :
      StrictWordBinaryDenotes .greaterEqual left right (.bool (!(decide (left < right))))

def evaluateStrictWordBinary? (operator : Syntax.BinaryOp) (left right : Core.Word) :
    Option Core.Value :=
  match operator with
  | .add => some (.word (left.add right))
  | .subtract => some (.word (left.sub right))
  | .multiply => some (.word (left.mul right))
  | .divide => some (.word (left.udiv right))
  | .modulo => some (.word (left.umod right))
  | .bitAnd => some (.word (left.bitAnd right))
  | .bitOr => some (.word (left.bitOr right))
  | .bitXor => some (.word (left.bitXor right))
  | .greater => some (.bool (decide (left > right)))
  | .less => some (.bool (decide (left < right)))
  | .equal => some (.bool (left == right))
  | .notEqual => some (.bool (!(left == right)))
  | .lessEqual => some (.bool (!(decide (left > right))))
  | .greaterEqual => some (.bool (!(decide (left < right))))
  | .shiftLeft | .shiftRight | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply
  | .logicalAnd | .logicalOr => none

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.StrictWordBinaryProperties`
-/

/- Exact successful results and operator support of the independent Word relation. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateStrictWordBinary?_iff
    {operator : Syntax.BinaryOp} {left right : Core.Word} {value : Core.Value} :
    evaluateStrictWordBinary? operator left right = some value ↔
      StrictWordBinaryDenotes operator left right value := by
  constructor
  · intro accepted
    cases operator <;>
      simp only [evaluateStrictWordBinary?, Option.some.injEq, reduceCtorEq] at accepted
    all_goals subst value; constructor
  · intro meaning
    cases meaning <;> rfl

theorem StrictWordBinaryDenotes.value_unique
    {operator : Syntax.BinaryOp} {left right : Core.Word} {first second : Core.Value}
    (firstMeaning : StrictWordBinaryDenotes operator left right first)
    (secondMeaning : StrictWordBinaryDenotes operator left right second) :
    first = second := by
  cases firstMeaning <;> cases secondMeaning <;> rfl

theorem StrictWordBinaryDenotes.operator_is_strict
    {operator : Syntax.BinaryOp} {left right : Core.Word} {value : Core.Value}
    (meaning : StrictWordBinaryDenotes operator left right value) :
    operator ≠ .logicalAnd ∧ operator ≠ .logicalOr := by
  cases meaning <;> constructor <;> intro impossible <;> cases impossible

theorem evaluateStrictWordBinary?_isSome_iff
    (operator : Syntax.BinaryOp) (left right : Core.Word) :
    (evaluateStrictWordBinary? operator left right).isSome = true ↔
      operator ≠ .logicalAnd ∧ operator ≠ .logicalOr ∧
        operator ≠ .shiftLeft ∧ operator ≠ .shiftRight ∧ operator ≠ .uncheckedAdd ∧
          operator ≠ .uncheckedSubtract ∧ operator ≠ .uncheckedMultiply := by
  cases operator <;> simp [evaluateStrictWordBinary?]

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.TypeName
/-! Explicit interpretation of canonical named types without type arguments.
Qualified spelling components remain separate, and no spelling is reserved. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Ordered caller meanings for exact qualified spelling-component lists. -/
abbrev TypeNameTable := List (List String × Core.Ty)

namespace TypeNameTable

def lookup? : TypeNameTable → List String → Option Core.Ty
  | [], _ => none
  | (candidate, type) :: table, key =>
      if candidate = key then some type else lookup? table key

/-- The first matching key determines meaning, independently of `lookup?`. -/
inductive Lookup : TypeNameTable → List String → Core.Ty → Prop where
  | head {table : TypeNameTable} {key : List String} {type : Core.Ty} :
      Lookup ((key, type) :: table) key type
  | tail {table : TypeNameTable} {key candidate : List String}
      {type candidateType : Core.Ty}
      (different : candidate ≠ key) (found : Lookup table key type) :
      Lookup ((candidate, candidateType) :: table) key type

end TypeNameTable

/-- Exact component strings in written order; occurrence ranges are ignored. -/
def qualifiedTypeNameKey (name : Syntax.QualifiedName) : List String :=
  name.value.components.toList.map (·.value)

/-- `none` means unmapped or outside this adapter, not general source invalidity. -/
def interpretTypeName? (table : TypeNameTable) (source : Syntax.TypeExpr) : Option Core.Ty :=
  match source with
  | ⟨_, .named name none⟩ => table.lookup? (qualifiedTypeNameKey name)
  | _ => none

/-- Independent canonical meaning for this deliberately restricted type fragment. -/
inductive TypeNameDenotes (table : TypeNameTable) : Syntax.TypeExpr → Core.Ty → Prop where
  | named {span : Syntax.SourceSpan} {name : Syntax.QualifiedName} {type : Core.Ty}
      (found : TypeNameTable.Lookup table (qualifiedTypeNameKey name) type) :
      TypeNameDenotes table ⟨span, .named name none⟩ type

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypeNameProperties`
-/

/-! Exact first-match type-name interpretation, without lexical or range validity
premises and without assigning built-in meaning to any source spelling. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace TypeNameTable

theorem lookup?_iff {table : TypeNameTable} {key : List String} {type : Core.Ty} :
    lookup? table key = some type ↔ Lookup table key type := by
  constructor
  · intro result
    induction table with
    | nil => simp [lookup?] at result
    | cons entry rest ih =>
        rcases entry with ⟨candidate, candidateType⟩
        by_cases same : candidate = key
        · subst candidate
          simp only [lookup?, ↓reduceIte, Option.some.injEq] at result
          subst candidateType
          exact .head
        · exact .tail same (ih (by simpa only [lookup?, if_neg same] using result))
  · intro found
    induction found with
    | head => simp [lookup?]
    | tail different _ ih => simpa only [lookup?, if_neg different] using ih

theorem Lookup.type_unique {table : TypeNameTable} {key : List String}
    {left right : Core.Ty} (leftFound : Lookup table key left)
    (rightFound : Lookup table key right) : left = right :=
  Option.some.inj ((lookup?_iff.mpr leftFound).symm.trans (lookup?_iff.mpr rightFound))

theorem Lookup.mem {table : TypeNameTable} {key : List String} {type : Core.Ty}
    (found : Lookup table key type) : (key, type) ∈ table := by
  induction found with
  | head => exact List.mem_cons_self
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih

theorem lookup?_eq_none_iff {table : TypeNameTable} {key : List String} :
    lookup? table key = none ↔ key ∉ table.map Prod.fst := by
  induction table with
  | nil => simp [lookup?]
  | cons entry rest ih =>
      rcases entry with ⟨candidate, candidateType⟩
      by_cases same : candidate = key
      · subst candidate; simp [lookup?]
      · simpa [lookup?, same, Ne.symm same] using ih

end TypeNameTable

theorem TypeNameDenotes.complete {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : TypeNameDenotes table source type) :
    interpretTypeName? table source = some type := by
  cases meaning with
  | named found => exact TypeNameTable.lookup?_iff.mpr found

theorem interpretTypeName?_sound {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (result : interpretTypeName? table source = some type) :
    TypeNameDenotes table source type := by
  cases source with
  | mk span payload =>
      cases payload <;> simp only [interpretTypeName?, reduceCtorEq] at result
      case named name arguments =>
        cases arguments with
        | none => exact .named (TypeNameTable.lookup?_iff.mp result)
        | some arguments => simp only [reduceCtorEq] at result

theorem interpretTypeName?_iff {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} :
    interpretTypeName? table source = some type ↔ TypeNameDenotes table source type :=
  ⟨interpretTypeName?_sound, TypeNameDenotes.complete⟩

theorem TypeNameDenotes.type_unique {table : TypeNameTable} {source : Syntax.TypeExpr}
    {left right : Core.Ty} (leftMeaning : TypeNameDenotes table source left)
    (rightMeaning : TypeNameDenotes table source right) : left = right :=
  Option.some.inj (leftMeaning.complete.symm.trans rightMeaning.complete)

/-- Every denoted type is an actual entry in the caller's table. -/
theorem TypeNameDenotes.mem {table : TypeNameTable} {source : Syntax.TypeExpr} {type : Core.Ty}
    (meaning : TypeNameDenotes table source type) : ∃ key, (key, type) ∈ table := by
  cases meaning with
  | named found => exact ⟨_, found.mem⟩

theorem interpretTypeName?_eq_none_iff {table : TypeNameTable} {source : Syntax.TypeExpr} :
    interpretTypeName? table source = none ↔ ¬ ∃ type, TypeNameDenotes table source type := by
  constructor
  · intro result ⟨type, meaning⟩
    have accepted := meaning.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : interpretTypeName? table source with
    | none => rfl
    | some type => exact False.elim (absent ⟨type, interpretTypeName?_sound result⟩)

/-- Replacing only the outer type range cannot change this adapter's result. -/
theorem interpretTypeName?_span (table : TypeNameTable) (source : Syntax.TypeExpr)
    (span : Syntax.SourceSpan) :
    interpretTypeName? table { source with span } = interpretTypeName? table source := by
  cases source with
  | mk sourceSpan payload =>
      cases payload <;> try rfl
      case named name arguments => cases arguments <;> rfl

/-- Exact component keys suffice, regardless of outer, name, or component ranges. -/
theorem interpretTypeName?_key_eq (table : TypeNameTable)
    {left right : Syntax.QualifiedName}
    (same : qualifiedTypeNameKey left = qualifiedTypeNameKey right)
    (leftSpan rightSpan : Syntax.SourceSpan) :
    interpretTypeName? table ⟨leftSpan, .named left none⟩ =
      interpretTypeName? table ⟨rightSpan, .named right none⟩ := by
  simp only [interpretTypeName?, same]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypeNameTableExtensionProperties`
-/

/-! Semantic extension retains every existing first-match type meaning.
New keys may gain meanings; only mutual extension preserves lookup absence. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace TypeNameTable

/-- Preserve original meanings, not merely membership in the list of entries. -/
def Extends (old next : TypeNameTable) : Prop :=
  ∀ {key type}, Lookup old key type → Lookup next key type

theorem Extends.refl (table : TypeNameTable) : Extends table table := by
  intro key type found
  exact found

theorem Extends.trans {old middle next : TypeNameTable}
    (first : Extends old middle) (second : Extends middle next) : Extends old next := by
  intro key type found
  exact second (first found)

/-- Later duplicate entries cannot override the first original match. -/
theorem Extends.append_right (table extras : TypeNameTable) : Extends table (table ++ extras) := by
  intro key type found
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

/-- Freshness is sufficient, not necessary: a same-meaning duplicate can also
be safe, but a prefix that changes an existing meaning is not an extension. -/
theorem Extends.cons_fresh (table : TypeNameTable) (key : List String) (type : Core.Ty)
    (fresh : key ∉ table.map Prod.fst) : Extends table ((key, type) :: table) := by
  intro original originalType found
  apply Lookup.tail ?_ found
  intro same
  apply fresh
  rw [same]
  exact List.mem_map.mpr ⟨(original, originalType), found.mem, rfl⟩

theorem lookup?_eq_of_mutual_extends {left right : TypeNameTable}
    (forward : Extends left right) (backward : Extends right left) (key : List String) :
    lookup? left key = lookup? right key := by
  cases leftResult : lookup? left key with
  | none =>
      cases rightResult : lookup? right key with
      | none => rfl
      | some type =>
          have accepted := lookup?_iff.mpr (backward (lookup?_iff.mp rightResult))
          rw [leftResult] at accepted
          cases accepted
  | some type => exact (lookup?_iff.mpr (forward (lookup?_iff.mp leftResult))).symm

end TypeNameTable

theorem TypeNameDenotes.extend_types {old next : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : TypeNameDenotes old source type)
    (extension : TypeNameTable.Extends old next) : TypeNameDenotes next source type := by
  cases meaning with
  | named found => exact .named (extension found)

theorem interpretTypeName?_some_of_extends {old next : TypeNameTable}
    (extension : TypeNameTable.Extends old next) {source : Syntax.TypeExpr} {type : Core.Ty}
    (accepted : interpretTypeName? old source = some type) :
    interpretTypeName? next source = some type :=
  ((interpretTypeName?_sound accepted).extend_types extension).complete

theorem interpretTypeName?_eq_of_mutual_extends {left right : TypeNameTable}
    (forward : TypeNameTable.Extends left right) (backward : TypeNameTable.Extends right left)
    (source : Syntax.TypeExpr) : interpretTypeName? left source = interpretTypeName? right source := by
  rcases source with ⟨span, payload⟩
  cases payload <;> try rfl
  case named name arguments =>
    cases arguments with
    | none => exact TypeNameTable.lookup?_eq_of_mutual_extends forward backward _
    | some _ => rfl

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.StructuralType
/-! Structural type meanings over original canonical syntax, shared by entry annotations.
The separate named-only interpreter and its whole-result membership law stay unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Exact named leaves, Unit, singleton identity, right-associated products and unary
function annotations. Original child nesting and source parameter arity are retained. -/
def interpretStructuralType? (table : TypeNameTable) (source : Syntax.TypeExpr) : Option Core.Ty :=
  match source with
  | ⟨_, .named name none⟩ => table.lookup? (qualifiedTypeNameKey name)
  | ⟨_, .tuple []⟩ => some .unit
  | ⟨_, .tuple [child]⟩ => interpretStructuralType? table child
  | ⟨_, .tuple [left, right]⟩ => do
      let first ← interpretStructuralType? table left
      let second ← interpretStructuralType? table right
      return .product first second
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ => do
      let headType ← interpretStructuralType? table first
      let tailType ← interpretStructuralType? table ⟨span, .tuple (second :: third :: rest)⟩
      return .product headType tailType
  | ⟨_, .function _ ⟨_, [parameter]⟩ none⟩ => do
      let parameterType ← interpretStructuralType? table parameter
      return .function parameterType .unit
  | ⟨_, .function _ ⟨_, [parameter]⟩ (some ⟨returnsSpan, results⟩)⟩ => do
      let parameterType ← interpretStructuralType? table parameter
      let returnType ← interpretStructuralType? table ⟨returnsSpan, .tuple results⟩
      return .function parameterType returnType
  | _ => none
termination_by sizeOf source

/-- Source meaning is specified independently of the executable interpreter.
Every child keeps the same table, including duplicate first-match priorities. -/
inductive StructuralTypeDenotes (table : TypeNameTable) : Syntax.TypeExpr → Core.Ty → Prop where
  | named {span : Syntax.SourceSpan} {name : Syntax.QualifiedName} {type : Core.Ty}
      (found : TypeNameTable.Lookup table (qualifiedTypeNameKey name) type) :
      StructuralTypeDenotes table ⟨span, .named name none⟩ type
  | unit {span : Syntax.SourceSpan} : StructuralTypeDenotes table ⟨span, .tuple []⟩ .unit
  | single {span : Syntax.SourceSpan} {child : Syntax.TypeExpr} {type : Core.Ty}
      (meaning : StructuralTypeDenotes table child type) :
      StructuralTypeDenotes table ⟨span, .tuple [child]⟩ type
  | pair {span : Syntax.SourceSpan} {left right : Syntax.TypeExpr} {leftType rightType : Core.Ty}
      (first : StructuralTypeDenotes table left leftType)
      (second : StructuralTypeDenotes table right rightType) :
      StructuralTypeDenotes table ⟨span, .tuple [left, right]⟩ (.product leftType rightType)
  | many {span : Syntax.SourceSpan} {first second third : Syntax.TypeExpr}
      {rest : List Syntax.TypeExpr} {firstType tailType : Core.Ty}
      (headMeaning : StructuralTypeDenotes table first firstType)
      (tailMeaning : StructuralTypeDenotes table ⟨span, .tuple (second :: third :: rest)⟩ tailType) :
      StructuralTypeDenotes table ⟨span, .tuple (first :: second :: third :: rest)⟩ (.product firstType tailType)
  | functionDefault {span keyword parametersSpan : Syntax.SourceSpan}
      {parameter : Syntax.TypeExpr} {parameterType : Core.Ty}
      (parameterMeaning : StructuralTypeDenotes table parameter parameterType) :
      StructuralTypeDenotes table ⟨span, .function keyword ⟨parametersSpan, [parameter]⟩ none⟩
        (.function parameterType .unit)
  | functionReturns {span keyword parametersSpan returnsSpan : Syntax.SourceSpan}
      {parameter : Syntax.TypeExpr} {results : List Syntax.TypeExpr} {parameterType returnType : Core.Ty}
      (parameterMeaning : StructuralTypeDenotes table parameter parameterType)
      (returnMeaning : StructuralTypeDenotes table ⟨returnsSpan, .tuple results⟩ returnType) :
      StructuralTypeDenotes table
        ⟨span, .function keyword ⟨parametersSpan, [parameter]⟩ (some ⟨returnsSpan, results⟩)⟩
        (.function parameterType returnType)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.StructuralTypeProperties`
-/

/-! Exact correspondence for the independent structural type fragment.
Named-only interpretation and its whole-result table membership law remain unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem StructuralTypeDenotes.complete {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (meaning : StructuralTypeDenotes table source type) :
    interpretStructuralType? table source = some type := by
  induction meaning with
  | named found =>
      simpa only [interpretStructuralType?] using TypeNameTable.lookup?_iff.mpr found
  | unit => simp only [interpretStructuralType?]
  | single _ ih => simpa only [interpretStructuralType?] using ih
  | pair _ _ leftIH rightIH =>
      simp only [interpretStructuralType?, leftIH, rightIH, bind, Option.bind_some, pure]
  | many _ _ headIH tailIH =>
      rw [interpretStructuralType?]
      simp only [headIH, tailIH, bind, Option.bind_some, pure]
  | functionDefault _ parameterIH =>
      simp only [interpretStructuralType?, parameterIH, bind, Option.bind_some, pure]
  | functionReturns _ _ parameterIH returnIH =>
      simp only [interpretStructuralType?, parameterIH, returnIH, bind, Option.bind_some, pure]

theorem interpretStructuralType?_sound {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (result : interpretStructuralType? table source = some type) :
    StructuralTypeDenotes table source type := by
  cases source with
  | mk span payload =>
      cases payload <;> try simp only [interpretStructuralType?, reduceCtorEq] at result
      case named name arguments =>
        cases arguments with
        | none =>
            exact .named (TypeNameTable.lookup?_iff.mp
              (by simpa only [interpretStructuralType?] using result))
        | some arguments => simp only [interpretStructuralType?, reduceCtorEq] at result
      case function keyword parameters returns =>
        cases parameters with
        | mk parametersSpan parameters =>
          cases parameters with
          | nil => simp only [interpretStructuralType?, reduceCtorEq] at result
          | cons parameter rest =>
              cases rest with
              | cons next rest => simp only [interpretStructuralType?, reduceCtorEq] at result
              | nil =>
                  cases returns with
                  | none =>
                      simp only [interpretStructuralType?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq] at result
                      obtain ⟨parameterType, parameterResult, rfl⟩ := result
                      exact .functionDefault (interpretStructuralType?_sound parameterResult)
                  | some returns =>
                      cases returns with
                      | mk returnsSpan results =>
                        rw [interpretStructuralType?] at result
                        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at result
                        obtain ⟨parameterType, parameterResult, returnType, returnResult, rfl⟩ := result
                        exact .functionReturns (interpretStructuralType?_sound parameterResult)
                          (interpretStructuralType?_sound returnResult)
      case tuple elements =>
        cases elements with
        | nil =>
            simp only [interpretStructuralType?, Option.some.injEq] at result
            cases result
            exact .unit
        | cons left remaining =>
            cases remaining with
            | nil =>
                exact .single (interpretStructuralType?_sound
                  (by simpa only [interpretStructuralType?] using result))
            | cons right tail =>
                cases tail with
                | cons third rest =>
                    rw [interpretStructuralType?] at result
                    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at result
                    obtain ⟨firstType, firstResult, tailType, tailResult, rfl⟩ := result
                    exact .many (interpretStructuralType?_sound firstResult)
                      (interpretStructuralType?_sound tailResult)
                | nil =>
                    simp only [interpretStructuralType?, bind, Option.bind_eq_some_iff,
                      pure, Option.some.injEq] at result
                    obtain ⟨leftType, leftResult, rightType, rightResult, rfl⟩ := result
                    exact .pair (interpretStructuralType?_sound leftResult)
                      (interpretStructuralType?_sound rightResult)
termination_by sizeOf source

theorem interpretStructuralType?_iff {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} :
    interpretStructuralType? table source = some type ↔ StructuralTypeDenotes table source type :=
  ⟨interpretStructuralType?_sound, StructuralTypeDenotes.complete⟩

theorem StructuralTypeDenotes.type_unique {table : TypeNameTable}
    {source : Syntax.TypeExpr} {left right : Core.Ty}
    (leftMeaning : StructuralTypeDenotes table source left)
    (rightMeaning : StructuralTypeDenotes table source right) : left = right :=
  Option.some.inj (leftMeaning.complete.symm.trans rightMeaning.complete)

theorem interpretStructuralType?_eq_none_iff {table : TypeNameTable}
    {source : Syntax.TypeExpr} :
    interpretStructuralType? table source = none ↔
      ¬ ∃ type, StructuralTypeDenotes table source type := by
  constructor
  · intro result ⟨type, meaning⟩
    have accepted := meaning.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : interpretStructuralType? table source with
    | none => rfl
    | some type => exact False.elim (absent ⟨type, interpretStructuralType?_sound result⟩)

/-- Only the outer occurrence range changes; recursive child ranges are untouched. -/
theorem interpretStructuralType?_span (table : TypeNameTable) (source : Syntax.TypeExpr)
    (span : Syntax.SourceSpan) :
    interpretStructuralType? table { source with span } = interpretStructuralType? table source := by
  cases source with
  | mk sourceSpan payload =>
      cases payload <;> try simp only [interpretStructuralType?]
      case named name arguments => cases arguments <;> simp only [interpretStructuralType?]
      case function keyword parameters returns =>
        rcases parameters with ⟨parametersSpan, parameters⟩
        cases parameters with
        | nil => simp only [interpretStructuralType?]
        | cons parameter rest =>
            cases rest with
            | cons next rest => simp only [interpretStructuralType?]
            | nil =>
                cases returns with
                | none => simp only [interpretStructuralType?]
                | some returns => cases returns; simp only [interpretStructuralType?]
      case tuple elements =>
        cases elements with
        | nil => simp only [interpretStructuralType?]
        | cons left remaining =>
            cases remaining with
            | nil => simp only [interpretStructuralType?]
            | cons right tail =>
                cases tail with
                | nil => simp only [interpretStructuralType?]
                | cons third rest =>
                    have tailSame := interpretStructuralType?_span table
                      ⟨sourceSpan, .tuple (right :: third :: rest)⟩ span
                    change interpretStructuralType? table ⟨span, .tuple (right :: third :: rest)⟩ =
                      interpretStructuralType? table ⟨sourceSpan, .tuple (right :: third :: rest)⟩ at tailSame
                    conv => lhs; rw [interpretStructuralType?]
                    conv => rhs; rw [interpretStructuralType?]
                    rw [tailSame]
termination_by sizeOf source

theorem TypeNameDenotes.structural {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : TypeNameDenotes table source type) :
    StructuralTypeDenotes table source type := by
  cases meaning with
  | named found => exact .named found

theorem interpretStructuralType?_of_typeName {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (accepted : interpretTypeName? table source = some type) :
    interpretStructuralType? table source = some type :=
  (interpretTypeName?_sound accepted).structural.complete

/-- Full optional-result agreement on the old named/no-arguments shape. -/
theorem interpretStructuralType?_named_eq_typeName (table : TypeNameTable)
    (name : Syntax.QualifiedName) (span : Syntax.SourceSpan) :
    interpretStructuralType? table ⟨span, .named name none⟩ =
      interpretTypeName? table ⟨span, .named name none⟩ := by
  simp only [interpretStructuralType?, interpretTypeName?]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.StructuralTypeTableProperties`
-/

/-! Structural interpretation depends on first-match named-leaf meanings.
One-way extension preserves successful results; only lookup equality or mutual
extension preserves the entire optional result, including rejection. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem StructuralTypeDenotes.extend_types {old next : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : StructuralTypeDenotes old source type)
    (extension : TypeNameTable.Extends old next) : StructuralTypeDenotes next source type := by
  induction meaning with
  | named found => exact .named (extension found)
  | unit => exact .unit
  | single _ ih => exact .single ih
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | many _ _ headIH tailIH => exact .many headIH tailIH
  | functionDefault _ parameterIH => exact .functionDefault parameterIH
  | functionReturns _ _ parameterIH returnIH => exact .functionReturns parameterIH returnIH

theorem interpretStructuralType?_some_of_extends {old next : TypeNameTable}
    (extension : TypeNameTable.Extends old next) {source : Syntax.TypeExpr} {type : Core.Ty}
    (accepted : interpretStructuralType? old source = some type) :
    interpretStructuralType? next source = some type :=
  ((interpretStructuralType?_sound accepted).extend_types extension).complete

/-- Equality of every visible lookup, not row membership or uniqueness, is enough.
Hidden duplicate entries, table lengths and source occurrence ranges are unrestricted. -/
theorem interpretStructuralType?_congr_lookup (left right : TypeNameTable)
    (sameLookup : ∀ key, left.lookup? key = right.lookup? key) (source : Syntax.TypeExpr) :
    interpretStructuralType? left source = interpretStructuralType? right source := by
  have forward : TypeNameTable.Extends left right := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [← sameLookup key]
    exact TypeNameTable.lookup?_iff.mpr found
  have backward : TypeNameTable.Extends right left := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [sameLookup key]
    exact TypeNameTable.lookup?_iff.mpr found
  cases leftResult : interpretStructuralType? left source with
  | none =>
      cases rightResult : interpretStructuralType? right source with
      | none => rfl
      | some type =>
          have accepted := interpretStructuralType?_some_of_extends backward rightResult
          rw [leftResult] at accepted
          cases accepted
  | some type => exact (interpretStructuralType?_some_of_extends forward leftResult).symm

theorem interpretStructuralType?_eq_of_mutual_extends {left right : TypeNameTable}
    (forward : TypeNameTable.Extends left right) (backward : TypeNameTable.Extends right left)
    (source : Syntax.TypeExpr) : interpretStructuralType? left source = interpretStructuralType? right source :=
  interpretStructuralType?_congr_lookup left right
    (TypeNameTable.lookup?_eq_of_mutual_extends forward backward) source

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.WordMatch
/-! Ordered source-level case selection is independent of checking, stores
and Core lowering. Only the selected original body is returned. -/

set_option autoImplicit false

namespace Solcore.Frontend

def WordMatchPatternDenotes (pattern : Syntax.Pattern) (word : Core.Word) : Prop :=
  ∃ literal, pattern.value = .literal literal ∧ WordLiteralDenotes literal word

def interpretWordMatchPattern? (pattern : Syntax.Pattern) : Option (Option Core.Word) :=
  match pattern with
  | ⟨_, .literal literal⟩ => (interpretWordLiteral? literal).map some
  | ⟨_, .wildcard _⟩ => some none
  | ⟨_, .group inner⟩ => interpretWordMatchPattern? inner
  | _ => none
termination_by sizeOf pattern

inductive WordMatchPatternClassifies : Syntax.Pattern → Option Core.Word → Prop where
  | literal {pattern : Syntax.Pattern} {word : Core.Word}
      (meaning : WordMatchPatternDenotes pattern word) :
      WordMatchPatternClassifies pattern (some word)
  | wildcard {pattern : Syntax.Pattern} {marker : Syntax.SourceSpan}
      (shape : pattern.value = .wildcard marker) :
      WordMatchPatternClassifies pattern none
  | group {span : Syntax.SourceSpan} {inner : Syntax.Pattern} {tag : Option Core.Word}
      (child : WordMatchPatternClassifies inner tag) :
      WordMatchPatternClassifies ⟨span, .group inner⟩ tag

/-- Only literal cases compare actual Words. A wildcard or literal hit ignores
later cases; fallback requires an original default. Tests count literal comparisons. -/
inductive WordMatchChooses :
    Core.Value → List Syntax.MatchCase → Option Syntax.Block → Syntax.Block → Nat → Prop where
  | fallback {value : Core.Value} {defaultBody : Syntax.Block} :
      WordMatchChooses value [] (some defaultBody) defaultBody 0
  | wildcard {value : Core.Value} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (meaning : WordMatchPatternClassifies first.value.pattern none) :
      WordMatchChooses value (first :: rest) defaultBody first.value.body 0
  | hit {word : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (meaning : WordMatchPatternClassifies first.value.pattern (some word)) :
      WordMatchChooses (.word word) (first :: rest) defaultBody first.value.body 1
  | miss {word literal : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
      (meaning : WordMatchPatternClassifies first.value.pattern (some literal))
      (different : word ≠ literal)
      (tail : WordMatchChooses (.word word) rest defaultBody selected tests) :
      WordMatchChooses (.word word) (first :: rest) defaultBody selected (tests + 1)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.WordMatchProperties`
-/

/-! Independent pattern meaning and original ordered choice are deterministic.
No checker, lowering, typing or Core execution assumption is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem WordMatchPatternDenotes.value_unique {pattern : Syntax.Pattern} {left right : Core.Word}
    (first : WordMatchPatternDenotes pattern left)
    (second : WordMatchPatternDenotes pattern right) : left = right := by
  obtain ⟨leftLiteral, leftShape, leftMeaning⟩ := first
  obtain ⟨rightLiteral, rightShape, rightMeaning⟩ := second
  have literals := Syntax.PatternValue.literal.inj (leftShape.symm.trans rightShape)
  subst rightLiteral
  exact leftMeaning.value_unique rightMeaning

theorem WordMatchPatternClassifies.tag_unique
    {pattern : Syntax.Pattern} {left right : Option Core.Word}
    (first : WordMatchPatternClassifies pattern left)
    (second : WordMatchPatternClassifies pattern right) : left = right := by
  induction first generalizing right with
  | @literal pattern word meaning =>
      cases second with
      | literal other => exact congrArg some (meaning.value_unique other)
      | wildcard shape =>
          obtain ⟨literal, literalShape, _⟩ := meaning
          rw [shape] at literalShape
          cases literalShape
      | group _ => obtain ⟨literal, shape, _⟩ := meaning; cases shape
  | wildcard shape =>
      cases second with
      | literal meaning =>
          obtain ⟨literal, literalShape, _⟩ := meaning
          rw [shape] at literalShape
          cases literalShape
      | wildcard _ => rfl
      | group _ => cases shape
  | group _ ih =>
      cases second with
      | literal meaning => obtain ⟨literal, shape, _⟩ := meaning; cases shape
      | wildcard shape => cases shape
      | group other => exact ih other

theorem WordMatchPatternClassifies.value_unique
    {pattern : Syntax.Pattern} {left right : Core.Word}
    (first : WordMatchPatternClassifies pattern (some left))
    (second : WordMatchPatternClassifies pattern (some right)) : left = right :=
  Option.some.inj (first.tag_unique second)

private theorem classified_checks {pattern : Syntax.Pattern} {tag : Option Core.Word}
    (meaning : WordMatchPatternClassifies pattern tag) :
    interpretWordMatchPattern? pattern = some tag := by
  induction meaning with
  | @literal pattern word meaning =>
      obtain ⟨literal, shape, denotes⟩ := meaning
      rcases pattern with ⟨span, value⟩
      change value = .literal literal at shape
      subst value
      simp [interpretWordMatchPattern?, interpretWordLiteral?_iff.mpr denotes]
  | @wildcard pattern marker shape =>
      rcases pattern with ⟨span, value⟩
      change value = .wildcard marker at shape
      subst value
      simp only [interpretWordMatchPattern?]
  | group _ ih => simpa only [interpretWordMatchPattern?] using ih

private theorem checked_classifies (pattern : Syntax.Pattern) (tag : Option Core.Word)
    (checked : interpretWordMatchPattern? pattern = some tag) :
    WordMatchPatternClassifies pattern tag := by
  cases pattern with
  | mk span value =>
      cases value <;> simp only [interpretWordMatchPattern?] at checked
      all_goals try cases checked
      case literal literal =>
        obtain ⟨word, found, rfl⟩ := Option.map_eq_some_iff.mp checked
        exact .literal ⟨literal, rfl, interpretWordLiteral?_iff.mp found⟩
      case wildcard.refl marker => exact .wildcard rfl
      case group inner => exact .group (checked_classifies inner tag checked)
termination_by sizeOf pattern

theorem interpretWordMatchPattern?_iff {pattern : Syntax.Pattern} {tag : Option Core.Word} :
    interpretWordMatchPattern? pattern = some tag ↔ WordMatchPatternClassifies pattern tag :=
  ⟨checked_classifies pattern tag, classified_checks⟩

theorem WordMatchChooses.deterministic
    {value : Core.Value} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
    {left right : Syntax.Block}
    {leftTests rightTests : Nat}
    (first : WordMatchChooses value cases defaultBody left leftTests)
    (second : WordMatchChooses value cases defaultBody right rightTests) :
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

end Solcore.Frontend
end
