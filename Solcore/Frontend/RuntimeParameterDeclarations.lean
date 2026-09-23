import Solcore.Frontend.StructuralType
import Solcore.Frontend.LocalTypeInputs
import Solcore.Syntax.Declaration
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Frontend.LocalReference
import Solcore.Resolved.LocalScope
import Solcore.Frontend.ReturnBody

/-! Restricted runtime parameter annotations declare static inputs without
supplying values. Public declaration begins empty and rejects repeated names. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RuntimeParametersDeclareFrom (types : TypeNameTable)
    (owner : Resolved.DeclarationId) : LocalTypeInputs →
      List Syntax.FunctionParameter → LocalTypeInputs → Prop
  | nil {initial} : RuntimeParametersDeclareFrom types owner initial [] initial
  | cons {initial final span name annotation type params}
      (meaning : StructuralTypeDenotes types annotation type)
      (unused : name.value ∉ initial.names.map Prod.fst)
      (tail : RuntimeParametersDeclareFrom types owner
        (initial.bindFresh owner name.value type) params final) :
      RuntimeParametersDeclareFrom types owner initial
        (⟨span, .typed none name annotation⟩ :: params) final

abbrev RuntimeParametersDeclare (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) (output : LocalTypeInputs) : Prop :=
  RuntimeParametersDeclareFrom types owner .empty params output

private def declareRuntimeParametersFrom? (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (initial : LocalTypeInputs) :
    List Syntax.FunctionParameter → Option LocalTypeInputs
  | [] => some initial
  | ⟨_, .typed none name annotation⟩ :: params =>
      if name.value ∉ initial.names.map Prod.fst then do
        let type ← interpretStructuralType? types annotation
        declareRuntimeParametersFrom? types owner (initial.bindFresh owner name.value type) params
      else none
  | _ => none

/-- Annotation-only preparation preserves the existing runtime parameter
profile; `none` is not a language-wide judgment about the source. -/
def declareRuntimeParameters? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) : Option LocalTypeInputs :=
  declareRuntimeParametersFrom? types owner .empty params

private theorem declareRuntimeParametersFrom?_complete {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial output : LocalTypeInputs}
    {params : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom types owner initial params output) :
    declareRuntimeParametersFrom? types owner initial params = some output := by
  induction declared with
  | nil => rfl
  | cons meaning unused _ ih =>
      simpa only [declareRuntimeParametersFrom?, if_pos unused, meaning.complete,
        bind, Option.bind_some] using ih

private theorem declareRuntimeParametersFrom?_sound {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial output : LocalTypeInputs}
    {params : List Syntax.FunctionParameter}
    (result : declareRuntimeParametersFrom? types owner initial params = some output) :
    RuntimeParametersDeclareFrom types owner initial params output := by
  induction params generalizing initial with
  | nil =>
      simp only [declareRuntimeParametersFrom?, Option.some.injEq] at result
      subst output
      exact .nil
  | cons parameter params ih =>
      rcases parameter with ⟨span, payload⟩
      cases payload with
      | error => simp only [declareRuntimeParametersFrom?, reduceCtorEq] at result
      | typed comptime name annotation =>
          cases comptime with
          | some marker => simp only [declareRuntimeParametersFrom?, reduceCtorEq] at result
          | none =>
              by_cases unused : name.value ∉ initial.names.map Prod.fst
              · cases interpreted : interpretStructuralType? types annotation with
                | none =>
                    simp only [declareRuntimeParametersFrom?, if_pos unused, interpreted,
                      bind, Option.bind_none, reduceCtorEq] at result
                | some type =>
                    exact .cons (interpretStructuralType?_sound interpreted) unused
                      (ih (by simpa only [declareRuntimeParametersFrom?, if_pos unused,
                        interpreted, bind, Option.bind_some] using result))
              · simp only [declareRuntimeParametersFrom?, if_neg unused, reduceCtorEq] at result

theorem RuntimeParametersDeclare.complete {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter}
    {output : LocalTypeInputs} (declared : RuntimeParametersDeclare types owner params output) :
    declareRuntimeParameters? types owner params = some output :=
  declareRuntimeParametersFrom?_complete declared

theorem declareRuntimeParameters?_sound {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter}
    {output : LocalTypeInputs}
    (result : declareRuntimeParameters? types owner params = some output) :
    RuntimeParametersDeclare types owner params output :=
  declareRuntimeParametersFrom?_sound result

theorem declareRuntimeParameters?_iff {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter}
    {output : LocalTypeInputs} :
    declareRuntimeParameters? types owner params = some output ↔
      RuntimeParametersDeclare types owner params output :=
  ⟨declareRuntimeParameters?_sound, RuntimeParametersDeclare.complete⟩

theorem declareRuntimeParameters?_eq_none_iff {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter} :
    declareRuntimeParameters? types owner params = none ↔
      ¬ ∃ output, RuntimeParametersDeclare types owner params output := by
  constructor
  · intro rejected ⟨output, declared⟩
    have accepted := declared.complete
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases result : declareRuntimeParameters? types owner params with
    | none => rfl
    | some output => exact False.elim (absent ⟨output, declareRuntimeParameters?_sound result⟩)

/-- Independent declarations determine an exact static bundle even when the
initial inputs are not empty. No runtime inhabitant is used for uniqueness. -/
theorem RuntimeParametersDeclareFrom.result_unique {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial left right : LocalTypeInputs}
    {params : List Syntax.FunctionParameter}
    (first : RuntimeParametersDeclareFrom types owner initial params left)
    (second : RuntimeParametersDeclareFrom types owner initial params right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons meaning _ _ ih =>
      cases second with
      | cons otherMeaning _ otherTail =>
          have sameType := meaning.type_unique otherMeaning
          cases sameType
          exact ih otherTail

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParameterDeclarationBindingProperties`
-/

/-! Runtime binding erases to static declaration. Conversely, matching actual
typed arguments reconstruct exactly the declared static bundle. No inhabitance
assumption or fabricated runtime value is used, including for arbitrary Core types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeParametersBindFrom.erase_values {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalInputs} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom types owner initial parameters arguments final) :
    RuntimeParametersDeclareFrom types owner initial.toTypeInputs parameters final.toTypeInputs := by
  induction bound with
  | nil => exact .nil
  | cons meaning unused _ ih =>
      exact .cons meaning (by simpa only [LocalInputs.toTypeInputs_names] using unused)
        (by simpa only [LocalInputs.toTypeInputs_bindFresh] using ih)

theorem RuntimeParametersBind.erase_values {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalInputs} {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBind types owner parameters arguments inputs) :
    RuntimeParametersDeclare types owner parameters inputs.toTypeInputs := by
  simpa only [LocalInputs.toTypeInputs_empty] using RuntimeParametersBindFrom.erase_values bound

/-- The existential list records only annotation types. Its reconstruction
clause must still be supplied every actual argument and its structural evidence. -/
private theorem declaration_restore_data {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom types owner initial parameters final) :
    ∃ addedTypes : List Core.Ty,
      Resolved.LocalScope.values final.context = addedTypes.reverse ++ Resolved.LocalScope.values initial.context ∧
      ∀ (runtimeInitial : LocalInputs) (arguments : List TypedRuntimeArgument),
        runtimeInitial.toTypeInputs = initial → arguments.map (·.type) = addedTypes →
        ∃ runtimeFinal, RuntimeParametersBindFrom types owner runtimeInitial parameters arguments runtimeFinal ∧
          runtimeFinal.toTypeInputs = final := by
  induction declared with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      intro runtimeInitial arguments erased matching
      cases arguments with
      | nil => exact ⟨runtimeInitial, .nil, erased⟩
      | cons argument arguments => simp only [List.map_cons, reduceCtorEq] at matching
  | @cons initial final span name annotation type parameters meaning unused _ ih =>
      obtain ⟨tailTypes, finalTypes, restoreTail⟩ := ih
      refine ⟨type :: tailTypes, ?_, ?_⟩
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
          LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values, List.map_cons] using finalTypes
      · intro runtimeInitial arguments erased matching
        cases arguments with
        | nil => simp only [List.map_nil, reduceCtorEq] at matching
        | cons argument arguments =>
            obtain ⟨sameHead, sameTail⟩ := List.cons.inj (by simpa only [List.map_cons] using matching)
            have nextErased :
                (runtimeInitial.bindFresh owner name.value argument.type argument.value argument.valueTyped).toTypeInputs =
                  initial.bindFresh owner name.value type := by
              rw [LocalInputs.toTypeInputs_bindFresh, erased, sameHead]
            obtain ⟨runtimeFinal, tailBound, finalErased⟩ := restoreTail
              (runtimeInitial.bindFresh owner name.value argument.type argument.value argument.valueTyped)
              arguments nextErased sameTail
            have namesEq : runtimeInitial.names = initial.names := by
              rw [← LocalInputs.toTypeInputs_names, erased]
            exact ⟨runtimeFinal, .cons (sameHead.symm ▸ meaning)
              (by simpa only [namesEq] using unused) tailBound, finalErased⟩

/-- General initial inputs are retained. The type-list equation includes their
source-order prefix and all newly supplied types, hence also fixes arity. -/
theorem RuntimeParametersDeclareFrom.bind_typed_arguments
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom types owner initial parameters final)
    (runtimeInitial : LocalInputs) (initialErased : runtimeInitial.toTypeInputs = initial)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : (Resolved.LocalScope.values initial.context).reverse ++ arguments.map (·.type) =
      (Resolved.LocalScope.values final.context).reverse) :
    ∃ runtimeFinal, RuntimeParametersBindFrom types owner runtimeInitial parameters arguments runtimeFinal ∧
      runtimeFinal.toTypeInputs = final := by
  obtain ⟨addedTypes, finalTypes, restore⟩ := declaration_restore_data declared
  have argumentTypes : arguments.map (·.type) = addedTypes :=
    List.append_cancel_left (by
      simpa only [finalTypes, List.reverse_append, List.reverse_reverse] using matchingTypes)
  exact restore runtimeInitial arguments initialErased argumentTypes

/-- Static declaration alone does not produce values. An exactly matching list
of supplied typed arguments is what reconstructs the independent runtime binding. -/
theorem RuntimeParametersDeclare.bind_typed_arguments
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclare types owner parameters inputs)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values inputs.context).reverse) :
    ∃ runtimeInputs, RuntimeParametersBind types owner parameters arguments runtimeInputs ∧
      runtimeInputs.toTypeInputs = inputs :=
  RuntimeParametersDeclareFrom.bind_typed_arguments declared .empty rfl arguments
    (by simpa only [LocalTypeInputs.empty_context, Resolved.LocalScope.values, List.map_nil,
      List.reverse_nil, List.nil_append] using matchingTypes)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParameterDeclarationsLayout`
-/

/-! Exact annotation-only parameter rows and owner-relative allocation layout.
Source order and generated identities do not require runtime inhabitants. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Annotation meaning fixes the spelling and type, but not the generated ID.
Allocation is justified separately by independent declaration evidence. -/
inductive RuntimeParameterDeclarationRow (types : TypeNameTable) :
    Syntax.FunctionParameter → LocalTypeBinding → Prop where
  | typed {span : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {type : Core.Ty} {id : Resolved.LocalId}
      (meaning : StructuralTypeDenotes types annotation type) :
      RuntimeParameterDeclarationRow types ⟨span, .typed none name annotation⟩
        { name := name.value, id, type }

/-- Rows correspond to the original parameters position by position. -/
inductive RuntimeParameterDeclarationRows (types : TypeNameTable) :
    List Syntax.FunctionParameter → List LocalTypeBinding → Prop where
  | nil : RuntimeParameterDeclarationRows types [] []
  | cons {parameter : Syntax.FunctionParameter} {row : LocalTypeBinding}
      {parameters : List Syntax.FunctionParameter} {rows : List LocalTypeBinding}
      (head : RuntimeParameterDeclarationRow types parameter row)
      (tail : RuntimeParameterDeclarationRows types parameters rows) :
      RuntimeParameterDeclarationRows types (parameter :: parameters) (row :: rows)

theorem RuntimeParameterDeclarationRows.arity {types : TypeNameTable}
    {parameters : List Syntax.FunctionParameter} {rows : List LocalTypeBinding}
    (paired : RuntimeParameterDeclarationRows types parameters rows) :
    parameters.length = rows.length := by
  induction paired with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem RuntimeParameterDeclarationRows.row_at {types : TypeNameTable}
    {parameters : List Syntax.FunctionParameter} {rows : List LocalTypeBinding}
    (paired : RuntimeParameterDeclarationRows types parameters rows)
    {index : Nat} {parameter : Syntax.FunctionParameter}
    (parameterAt : parameters[index]? = some parameter) :
    ∃ row, rows[index]? = some row ∧ RuntimeParameterDeclarationRow types parameter row := by
  induction paired generalizing index with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at parameterAt
  | cons head _ ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at parameterAt
          subst parameter
          exact ⟨_, rfl, head⟩
      | succ index => exact ih parameterAt

namespace RuntimeParametersDeclareFrom

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {initial final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}

theorem rows (declared : RuntimeParametersDeclareFrom types owner initial parameters final) :
    ∃ added, final.bindings = added.reverse ++ initial.bindings ∧
      RuntimeParameterDeclarationRows types parameters added := by
  induction declared with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons initial _ _ _ _ _ _ meaning _ _ ih =>
      obtain ⟨added, finalEq, paired⟩ := ih
      refine ⟨_ :: added, ?_, .cons
        (.typed (id := Resolved.freshLocalId owner initial.ids) meaning) paired⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        LocalTypeInputs.bindFresh_bindings] using finalEq

theorem bindings_length
    (declared : RuntimeParametersDeclareFrom types owner initial parameters final) :
    final.bindings.length = parameters.length + initial.bindings.length := by
  obtain ⟨added, finalEq, paired⟩ := declared.rows
  simp only [finalEq, List.length_append, List.length_reverse, ← paired.arity]

/-- Static bundles require unique IDs, not unique names. The initial spelling
premise is therefore essential when the starting inputs are arbitrary. -/
theorem names_nodup
    (declared : RuntimeParametersDeclareFrom types owner initial parameters final)
    (initialDistinct : (initial.names.map Prod.fst).Nodup) :
    (final.names.map Prod.fst).Nodup := by
  revert initialDistinct
  induction declared with
  | nil => exact id
  | cons _ unused _ ih =>
      intro distinct
      apply ih
      simpa only [LocalTypeInputs.bindFresh_names, List.map_cons] using
        List.nodup_cons.mpr ⟨unused, distinct⟩

/-- Only same-owner indices determine the start; all original rows remain.
This formula handles sparse and mixed-owner initial identity tables. -/
theorem generated_ids
    (declared : RuntimeParametersDeclareFrom types owner initial parameters final) :
    final.ids =
      (List.range' (Resolved.freshLocalId owner initial.ids).binderIndex
        parameters.length).reverse.map (fun i => (⟨owner, i⟩ : Resolved.LocalId)) ++ initial.ids := by
  induction declared with
  | nil => simp
  | cons _ _ _ ih =>
      simp only [LocalTypeInputs.bindFresh_ids,
        Resolved.freshLocalId_cons_fresh_binderIndex] at ih
      simp only [List.length_cons, List.range'_succ, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      simpa only [Resolved.freshLocalId] using ih

end RuntimeParametersDeclareFrom

namespace RuntimeParametersDeclare

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}

theorem rows (declared : RuntimeParametersDeclare types owner parameters final) :
    RuntimeParameterDeclarationRows types parameters final.bindings.reverse := by
  obtain ⟨added, finalEq, paired⟩ := RuntimeParametersDeclareFrom.rows declared
  rw [finalEq]
  simpa only [LocalTypeInputs.empty, List.append_nil, List.reverse_reverse] using paired

theorem bindings_length (declared : RuntimeParametersDeclare types owner parameters final) :
    final.bindings.length = parameters.length := by
  simpa only [LocalTypeInputs.empty, List.length_nil, Nat.add_zero] using
    RuntimeParametersDeclareFrom.bindings_length declared

theorem names_nodup (declared : RuntimeParametersDeclare types owner parameters final) :
    (final.names.map Prod.fst).Nodup :=
  RuntimeParametersDeclareFrom.names_nodup declared (by simp)

theorem generated_ids (declared : RuntimeParametersDeclare types owner parameters final) :
    final.ids = (List.range parameters.length).reverse.map
      (fun i => (⟨owner, i⟩ : Resolved.LocalId)) := by
  simpa only [LocalTypeInputs.empty_ids, Resolved.freshLocalId_empty, List.append_nil,
    ← List.range_eq_range'] using RuntimeParametersDeclareFrom.generated_ids declared

end RuntimeParametersDeclare

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParameterDeclarationsOwnerProperties`
-/

/-! Empty-start static declarations commute with injective owner relabeling.
The fresh-index induction uses annotation types only, without runtime values. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem map_bindFresh (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    (sameFresh : Resolved.freshLocalId (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).ids =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner inputs.ids))
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) =
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).bindFresh (mapping owner) name type := by
  cases inputs
  simp only [LocalTypeInputs.mapIds, LocalTypeInputs.bindFresh, List.map_cons,
    LocalTypeBinding.mapIds, LocalTypeInputs.mk.injEq]
  congr 2
  exact sameFresh.symm

private theorem transport_from {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom types owner initial parameters final)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    (sameIndex : (Resolved.freshLocalId (mapping owner)
        (initial.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).ids).binderIndex =
      (Resolved.freshLocalId owner initial.ids).binderIndex) :
    RuntimeParametersDeclareFrom types (mapping owner)
      (initial.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) parameters
      (final.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) := by
  induction declared with
  | nil => exact .nil
  | @cons initial final span name annotation type parameters meaning unused tail ih =>
      have sameFresh : Resolved.freshLocalId (mapping owner)
          (initial.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).ids =
          ownerLocalIdMap mapping (Resolved.freshLocalId owner initial.ids) := by
        change Resolved.LocalId.mk (mapping owner) _ = Resolved.LocalId.mk (mapping owner) _
        exact congrArg (Resolved.LocalId.mk (mapping owner)) sameIndex
      have nextInputs := map_bindFresh initial owner mapping injective sameFresh name.value type
      have nextIndex : (Resolved.freshLocalId (mapping owner)
          ((initial.bindFresh owner name.value type).mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).ids).binderIndex =
          (Resolved.freshLocalId owner (initial.bindFresh owner name.value type).ids).binderIndex := by
        rw [nextInputs]
        simp only [LocalTypeInputs.bindFresh_ids, Resolved.freshLocalId_cons_fresh_binderIndex, sameIndex]
      have mappedUnused : name.value ∉
          (initial.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).names.map Prod.fst := by
        simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds,
          List.map_map, Function.comp_def] using unused
      exact .cons meaning mappedUnused (nextInputs ▸ ih nextIndex)

/-- Exact annotation-only inputs are relabeled without constructing values.
The public empty-start profile needs no extra fresh-index premise. -/
theorem RuntimeParametersDeclare.map_owner {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {inputs : LocalTypeInputs} (declared : RuntimeParametersDeclare types owner parameters inputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    RuntimeParametersDeclare types (mapping owner) parameters
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) :=
  transport_from declared mapping injective rfl

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParameterDeclarationsPositionProperties`
-/

/-! A genuine source position determines an exact static row, annotation type,
generated identity and first-match Core index, without a runtime argument. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem name_lookup_of_mem {table : LocalNameTable} {spelling : String}
    {id : Resolved.LocalId} (unique : (table.map Prod.fst).Nodup) (member : (spelling, id) ∈ table) :
    LocalNameTable.Lookup table spelling id := by
  induction table with
  | nil => cases member
  | cons entry rest ih =>
      rcases entry with ⟨candidate, candidateId⟩
      have parts := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact .head
      · have different : candidate ≠ spelling := by
          intro same
          apply parts.1
          rw [same]
          exact List.mem_map.mpr ⟨(spelling, id), member, rfl⟩
        exact .tail different (ih parts.2 member)

private theorem index_of_getElem {ids : List Resolved.LocalId} {id : Resolved.LocalId} {index : Nat}
    (unique : ids.Nodup) (atId : ids[index]? = some id) :
    Resolved.LocalScope.IndexOf ids id index := by
  induction ids generalizing index with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at atId
  | cons candidate rest ih =>
      have parts := List.nodup_cons.mp unique
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at atId
          subst candidate
          exact .head
      | succ index =>
          have different : candidate ≠ id := by
            intro same
            apply parts.1
            rw [same]
            exact List.mem_of_getElem? atId
          exact .tail different (ih parts.2 atId)

/-- Empty-start declaration fixes both indices. A real source lookup supplies
the bound for reversed subtraction; annotation meaning supplies no value. -/
theorem RuntimeParametersDeclare.position {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {parameters : List Syntax.FunctionParameter} {inputs : LocalTypeInputs}
    (declared : RuntimeParametersDeclare types owner parameters inputs)
    {index : Nat} {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr}
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩) :
    index < parameters.length ∧ ∃ type, StructuralTypeDenotes types annotation type ∧
      inputs.bindings[parameters.length - 1 - index]? = some
        { name := name.value, id := ⟨owner, index⟩, type } ∧
      LocalNameTable.Lookup inputs.names name.value ⟨owner, index⟩ ∧
      Resolved.LocalScope.Lookup inputs.context ⟨owner, index⟩ type ∧
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids inputs.context)
        ⟨owner, index⟩ (parameters.length - 1 - index) := by
  have indexLt := (List.getElem?_eq_some_iff.mp parameterAt).1
  obtain ⟨row, reverseRowAt, paired⟩ := declared.rows.row_at parameterAt
  have rowAt : inputs.bindings[parameters.length - 1 - index]? = some row := by
    have reverseEq := List.getElem?_reverse (l := inputs.bindings)
      (i := index) (by simpa only [declared.bindings_length] using indexLt)
    rw [declared.bindings_length] at reverseEq
    exact reverseEq.symm.trans reverseRowAt
  have generatedAt : inputs.ids[parameters.length - 1 - index]? = some ⟨owner, index⟩ := by
    rw [declared.generated_ids, List.getElem?_map]
    have reversed : (List.range parameters.length).reverse[parameters.length - 1 - index]? =
        (List.range parameters.length)[index]? :=
      List.getElem?_reverse' (by simp only [List.length_range]; omega)
    rw [reversed, List.getElem?_range indexLt]
    rfl
  have rowIdAt : inputs.ids[parameters.length - 1 - index]? = some row.id := by
    simp only [LocalTypeInputs.ids, List.getElem?_map, rowAt, Option.map_some]
  have sameId := Option.some.inj (rowIdAt.symm.trans generatedAt)
  have indexed : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids inputs.context)
      ⟨owner, index⟩ (parameters.length - 1 - index) := by
    rw [LocalTypeInputs.context_ids]
    exact index_of_getElem inputs.ids_nodup generatedAt
  have typedAt : inputs.context.values[parameters.length - 1 - index]? = some row.type := by
    simp only [LocalTypeInputs.context, Resolved.LocalScope.values, List.map_map,
      Function.comp_def, List.getElem?_map, rowAt, Option.map_some]
  cases paired with
  | typed meaning =>
      cases sameId
      have named := name_lookup_of_mem declared.names_nodup
        (List.mem_map.mpr ⟨_, List.mem_of_getElem? rowAt, rfl⟩)
      exact ⟨indexLt, _, meaning, rowAt, named,
        Resolved.LocalScope.lookup_of_indexed indexed typedAt, indexed⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParameterDeclarationReferenceProperties`
-/

/-! Static parameter positions resolve and lower references exactly, even when
their annotation types have no inhabitants. All occurrence spans remain arbitrary. -/

set_option autoImplicit false

namespace Solcore.Frontend.RuntimeParametersDeclare

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {parameters : List Syntax.FunctionParameter} {inputs : LocalTypeInputs}
  {index : Nat} {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
  {annotation : Syntax.TypeExpr} {type : Core.Ty}

theorem reference_resolves_at
    (declared : RuntimeParametersDeclare types owner parameters inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (span nameSpan : Syntax.SourceSpan) :
    ResolvesLocalExpression inputs.names ⟨span, .identifier ⟨nameSpan, name.value⟩⟩
      (.var ⟨owner, index⟩) := by
  obtain ⟨_, _, _, _, named, _, _⟩ := declared.position parameterAt
  exact .identifier named

theorem reference_elaborates_at
    (declared : RuntimeParametersDeclare types owner parameters inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type) (span nameSpan : Syntax.SourceSpan) :
    elaborateLocalExpression? inputs.names inputs.context
      ⟨span, .identifier ⟨nameSpan, name.value⟩⟩ =
        some (.var (parameters.length - 1 - index), type) := by
  obtain ⟨_, _, actualMeaning, _, named, found, indexed⟩ := declared.position parameterAt
  cases actualMeaning.type_unique meaning.structural
  exact elaborateLocalExpression?_complete (.identifier named) (.var indexed) (.var found)

/-- Singleton return embeds the same positional resolution, lowering and type
evidence. The existing terminal union can wrap this judgment with `.single`. -/
theorem reference_return_elaborates_at
    (declared : RuntimeParametersDeclare types owner parameters inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (blockSpan returnSpan span nameSpan : Syntax.SourceSpan) :
    ReturnBodyElaborates inputs.names inputs.context
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩
      (.var (parameters.length - 1 - index)) type := by
  obtain ⟨_, _, actualMeaning, _, named, found, indexed⟩ := declared.position parameterAt
  cases actualMeaning.type_unique meaning.structural
  exact .expression (.identifier named) (.var indexed) (.var found)

end Solcore.Frontend.RuntimeParametersDeclare

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParameterDeclarationsTypeExtensionProperties`
-/

/-! Meaning-preserving table extension retains exact static declarations,
including arbitrary initial inputs and every generated identity. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Only annotation evidence changes; the same types drive the same identity
allocation, and the original initial and final bundles remain untouched. -/
theorem RuntimeParametersDeclareFrom.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial final : LocalTypeInputs}
    {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom old owner initial parameters final)
    (extension : TypeNameTable.Extends old new) :
    RuntimeParametersDeclareFrom new owner initial parameters final := by
  induction declared with
  | nil => exact .nil
  | cons meaning unused _ ih => exact .cons (meaning.extend_types extension) unused ih

theorem RuntimeParametersDeclare.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {inputs : LocalTypeInputs}
    (declared : RuntimeParametersDeclare old owner parameters inputs)
    (extension : TypeNameTable.Extends old new) :
    RuntimeParametersDeclare new owner parameters inputs :=
  RuntimeParametersDeclareFrom.extend_types declared extension

theorem declareRuntimeParameters?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {inputs : LocalTypeInputs} (extension : TypeNameTable.Extends old new)
    (accepted : declareRuntimeParameters? old owner parameters = some inputs) :
    declareRuntimeParameters? new owner parameters = some inputs :=
  (RuntimeParametersDeclare.extend_types (declareRuntimeParameters?_sound accepted) extension).complete

/-- Mutual preservation includes rejection. One-way extension alone may make
a previously unknown annotation available and turn rejection into success. -/
theorem declareRuntimeParameters?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (parameters : List Syntax.FunctionParameter) :
    declareRuntimeParameters? old owner parameters = declareRuntimeParameters? new owner parameters := by
  cases oldResult : declareRuntimeParameters? old owner parameters with
  | none =>
      cases newResult : declareRuntimeParameters? new owner parameters with
      | none => rfl
      | some inputs =>
          have preserved := declareRuntimeParameters?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some inputs => exact (declareRuntimeParameters?_some_of_extends forward oldResult).symm

end Solcore.Frontend
