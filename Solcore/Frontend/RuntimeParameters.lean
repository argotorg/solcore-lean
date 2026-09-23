import Solcore.Frontend.StructuralType
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalOwnerRenaming

/-! Explicit runtime parameter input preparation. This restricted adapter starts
from empty inputs, pairs parameters and arguments in written order, and rejects
repeated spellings. Its output uses the existing prepend-based fresh binding
primitive; it does not implement source function calls or argument decoding. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Caller-supplied structural typing evidence validates a closure's body and
captured environment, but does not assert allocation for a cell reference. -/
structure TypedRuntimeArgument where
  type : Core.Ty
  value : Core.Value
  valueTyped : Core.ValueHasType value type

/-- Independent paired-list binding. The initial inputs supply all earlier
names, and the tail sees the freshly prepended row. -/
inductive RuntimeParametersBindFrom (types : TypeNameTable)
    (owner : Resolved.DeclarationId) : LocalInputs → List Syntax.FunctionParameter →
      List TypedRuntimeArgument → LocalInputs → Prop
  | nil {initial} : RuntimeParametersBindFrom types owner initial [] [] initial
  | cons {initial final span name annotation params argument args}
      (meaning : StructuralTypeDenotes types annotation argument.type)
      (unused : name.value ∉ initial.names.map Prod.fst)
      (tail : RuntimeParametersBindFrom types owner
        (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped)
        params args final) :
      RuntimeParametersBindFrom types owner initial
        (⟨span, .typed none name annotation⟩ :: params) (argument :: args) final

/-- The public parameter profile always starts from empty typed inputs. -/
abbrev RuntimeParametersBind (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument)
    (output : LocalInputs) : Prop :=
  RuntimeParametersBindFrom types owner .empty params args output

private def bindRuntimeParametersFrom? (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (initial : LocalInputs) :
    List Syntax.FunctionParameter → List TypedRuntimeArgument → Option LocalInputs
  | [], [] => some initial
  | ⟨_, .typed none name annotation⟩ :: params, argument :: args =>
      if name.value ∉ initial.names.map Prod.fst then
        if interpretStructuralType? types annotation = some argument.type then
          bindRuntimeParametersFrom? types owner
            (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped)
            params args
        else none
      else none
  | _, _ => none

/-- Bind runtime-only, explicitly annotated parameters to equally many supplied
typed arguments. `none` means outside this adapter profile, not a language error. -/
def bindRuntimeParameters? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) :
    Option LocalInputs :=
  bindRuntimeParametersFrom? types owner .empty params args

private theorem bindRuntimeParametersFrom?_complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial output : LocalInputs}
    {params : List Syntax.FunctionParameter} {args : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom types owner initial params args output) :
    bindRuntimeParametersFrom? types owner initial params args = some output := by
  induction bound with
  | nil => rfl
  | cons meaning unused _ ih =>
      simpa only [bindRuntimeParametersFrom?, if_pos unused, if_pos meaning.complete] using ih

private theorem bindRuntimeParametersFrom?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial output : LocalInputs}
    {params : List Syntax.FunctionParameter} {args : List TypedRuntimeArgument}
    (result : bindRuntimeParametersFrom? types owner initial params args = some output) :
    RuntimeParametersBindFrom types owner initial params args output := by
  induction params generalizing initial args with
  | nil =>
      cases args with
      | nil =>
          simp only [bindRuntimeParametersFrom?, Option.some.injEq] at result
          subst output
          exact .nil
      | cons argument args => simp only [bindRuntimeParametersFrom?, reduceCtorEq] at result
  | cons parameter params ih =>
      rcases parameter with ⟨span, payload⟩
      cases payload with
      | error => simp only [bindRuntimeParametersFrom?, reduceCtorEq] at result
      | typed comptime name annotation =>
          cases comptime with
          | some comptime => simp only [bindRuntimeParametersFrom?, reduceCtorEq] at result
          | none =>
              cases args with
              | nil => simp only [bindRuntimeParametersFrom?, reduceCtorEq] at result
              | cons argument args =>
                  by_cases unused : name.value ∉ initial.names.map Prod.fst
                  · by_cases meaning : interpretStructuralType? types annotation = some argument.type
                    · exact .cons (interpretStructuralType?_sound meaning) unused
                        (ih (by simpa only [bindRuntimeParametersFrom?, if_pos unused,
                          if_pos meaning] using result))
                    · simp only [bindRuntimeParametersFrom?, if_pos unused, if_neg meaning,
                        reduceCtorEq] at result
                  · simp only [bindRuntimeParametersFrom?, if_neg unused, reduceCtorEq] at result

/-- Exactness of the empty-start adapter against independent paired binding. -/
theorem bindRuntimeParameters?_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {params : List Syntax.FunctionParameter} {args : List TypedRuntimeArgument}
    {output : LocalInputs} :
    bindRuntimeParameters? types owner params args = some output ↔
      RuntimeParametersBind types owner params args output :=
  ⟨bindRuntimeParametersFrom?_sound, bindRuntimeParametersFrom?_complete⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParametersLayout`
-/

/-! Ordered parameter/argument correspondence. Rows are kept together, so equal
argument types cannot hide a permutation of the supplied values. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- One runtime parameter and its corresponding supplied argument determine
the complete row apart from the separately specified generated identity. -/
inductive RuntimeParameterRow (types : TypeNameTable) :
    Syntax.FunctionParameter → TypedRuntimeArgument → TypedLocalBinding → Prop where
  | typed {span : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument} {id : Resolved.LocalId}
      (meaning : StructuralTypeDenotes types annotation argument.type) :
      RuntimeParameterRow types ⟨span, .typed none name annotation⟩ argument
        { name := name.value, id, type := argument.type, value := argument.value,
          valueTyped := argument.valueTyped }

/-- The three lists have exact position-by-position correspondence. -/
inductive RuntimeParameterRows (types : TypeNameTable) : List Syntax.FunctionParameter →
    List TypedRuntimeArgument → List TypedLocalBinding → Prop where
  | nil : RuntimeParameterRows types [] [] []
  | cons {parameter : Syntax.FunctionParameter} {argument : TypedRuntimeArgument}
      {row : TypedLocalBinding} {parameters : List Syntax.FunctionParameter}
      {arguments : List TypedRuntimeArgument} {rows : List TypedLocalBinding}
      (head : RuntimeParameterRow types parameter argument row)
      (tail : RuntimeParameterRows types parameters arguments rows) :
      RuntimeParameterRows types (parameter :: parameters) (argument :: arguments) (row :: rows)

theorem RuntimeParameterRows.arity {types : TypeNameTable}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    {rows : List TypedLocalBinding} (paired : RuntimeParameterRows types parameters arguments rows) :
    parameters.length = arguments.length ∧ rows.length = arguments.length := by
  induction paired with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

theorem RuntimeParameterRows.argument_types {types : TypeNameTable}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    {rows : List TypedLocalBinding} (paired : RuntimeParameterRows types parameters arguments rows) :
    rows.map (·.type) = arguments.map (·.type) := by
  induction paired with
  | nil => rfl
  | cons head _ ih => cases head; exact congrArg (List.cons _) ih

theorem RuntimeParameterRows.argument_values {types : TypeNameTable}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    {rows : List TypedLocalBinding} (paired : RuntimeParameterRows types parameters arguments rows) :
    rows.map (·.value) = arguments.map (·.value) := by
  induction paired with
  | nil => rfl
  | cons head _ ih => cases head; exact congrArg (List.cons _) ih

/-- Equal positions, not merely equal types, select the corresponding row. -/
theorem RuntimeParameterRows.row_at {types : TypeNameTable}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    {rows : List TypedLocalBinding} (paired : RuntimeParameterRows types parameters arguments rows)
    {index : Nat} {parameter : Syntax.FunctionParameter} {argument : TypedRuntimeArgument}
    (parameterAt : parameters[index]? = some parameter)
    (argumentAt : arguments[index]? = some argument) :
    ∃ row, rows[index]? = some row ∧ RuntimeParameterRow types parameter argument row := by
  induction paired generalizing index with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at parameterAt
  | cons head _ ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at parameterAt argumentAt
          subst parameter
          subst argument
          exact ⟨_, rfl, head⟩
      | succ index => exact ih parameterAt argumentAt

namespace RuntimeParametersBindFrom

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {initial final : LocalInputs} {parameters : List Syntax.FunctionParameter}
  {arguments : List TypedRuntimeArgument}

theorem rows (bound : RuntimeParametersBindFrom types owner initial parameters arguments final) :
    ∃ added, final.bindings = added.reverse ++ initial.bindings ∧
      RuntimeParameterRows types parameters arguments added := by
  induction bound with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons initial _ _ _ _ _ _ _ meaning _ _ ih =>
      obtain ⟨added, finalEq, paired⟩ := ih
      refine ⟨_ :: added, ?_, .cons
        (.typed (id := Resolved.freshLocalId owner initial.ids) meaning) paired⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        LocalInputs.bindFresh_bindings] using finalEq

theorem arity (bound : RuntimeParametersBindFrom types owner initial parameters arguments final) :
    parameters.length = arguments.length := by
  obtain ⟨_, _, paired⟩ := bound.rows
  exact paired.arity.1

theorem bindings_length
    (bound : RuntimeParametersBindFrom types owner initial parameters arguments final) :
    final.bindings.length = arguments.length + initial.bindings.length := by
  obtain ⟨added, finalEq, paired⟩ := bound.rows
  simp only [finalEq, List.length_append, List.length_reverse, paired.arity.2]

theorem argument_types
    (bound : RuntimeParametersBindFrom types owner initial parameters arguments final) :
    final.bindings.map (·.type) = arguments.reverse.map (·.type) ++ initial.bindings.map (·.type) := by
  obtain ⟨added, finalEq, paired⟩ := bound.rows
  simp only [finalEq, List.map_append, List.map_reverse, paired.argument_types]

theorem argument_values
    (bound : RuntimeParametersBindFrom types owner initial parameters arguments final) :
    final.bindings.map (·.value) = arguments.reverse.map (·.value) ++ initial.bindings.map (·.value) := by
  obtain ⟨added, finalEq, paired⟩ := bound.rows
  simp only [finalEq, List.map_append, List.map_reverse, paired.argument_values]

theorem names_nodup
    (bound : RuntimeParametersBindFrom types owner initial parameters arguments final)
    (initialDistinct : (initial.names.map Prod.fst).Nodup) :
    (final.names.map Prod.fst).Nodup := by
  revert initialDistinct
  induction bound with
  | nil => exact id
  | cons _ unused _ ih =>
      intro distinct
      apply ih
      simpa only [LocalInputs.bindFresh_names, List.map_cons] using
        List.nodup_cons.mpr ⟨unused, distinct⟩

/-- General initial inputs retain their IDs after the newly allocated suffix
of same-owner indices, shown in the final table's reverse order. -/
theorem generated_ids
    (bound : RuntimeParametersBindFrom types owner initial parameters arguments final) :
    final.ids =
      (List.range' (Resolved.freshLocalId owner initial.ids).binderIndex
        arguments.length).reverse.map (fun i => (⟨owner, i⟩ : Resolved.LocalId)) ++ initial.ids := by
  induction bound with
  | nil => simp
  | cons _ _ _ ih =>
      simp only [LocalInputs.bindFresh_ids,
        Resolved.freshLocalId_cons_fresh_binderIndex] at ih
      simp only [List.length_cons, List.range'_succ, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      simpa only [Resolved.freshLocalId] using ih

end RuntimeParametersBindFrom

namespace RuntimeParametersBind

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {final : LocalInputs} {parameters : List Syntax.FunctionParameter}
  {arguments : List TypedRuntimeArgument}

theorem rows (bound : RuntimeParametersBind types owner parameters arguments final) :
    RuntimeParameterRows types parameters arguments final.bindings.reverse := by
  obtain ⟨added, finalEq, paired⟩ := RuntimeParametersBindFrom.rows bound
  rw [finalEq]
  simpa only [LocalInputs.empty, List.append_nil, List.reverse_reverse] using paired

theorem arity (bound : RuntimeParametersBind types owner parameters arguments final) :
    parameters.length = arguments.length := RuntimeParametersBindFrom.arity bound

theorem bindings_length (bound : RuntimeParametersBind types owner parameters arguments final) :
    final.bindings.length = arguments.length := by
  simpa only [LocalInputs.empty, List.length_nil, Nat.add_zero] using
    RuntimeParametersBindFrom.bindings_length bound

theorem argument_types (bound : RuntimeParametersBind types owner parameters arguments final) :
    final.bindings.map (·.type) = arguments.reverse.map (·.type) := by
  simpa only [LocalInputs.empty, List.map_nil, List.append_nil] using
    RuntimeParametersBindFrom.argument_types bound

theorem argument_values (bound : RuntimeParametersBind types owner parameters arguments final) :
    final.bindings.map (·.value) = arguments.reverse.map (·.value) := by
  simpa only [LocalInputs.empty, List.map_nil, List.append_nil] using
    RuntimeParametersBindFrom.argument_values bound

theorem names_nodup (bound : RuntimeParametersBind types owner parameters arguments final) :
    (final.names.map Prod.fst).Nodup :=
  RuntimeParametersBindFrom.names_nodup bound (by simp)

theorem generated_ids (bound : RuntimeParametersBind types owner parameters arguments final) :
    final.ids = (List.range arguments.length).reverse.map
      (fun i => (⟨owner, i⟩ : Resolved.LocalId)) := by
  simpa only [LocalInputs.empty_ids, Resolved.freshLocalId_empty, List.append_nil,
    ← List.range_eq_range'] using RuntimeParametersBindFrom.generated_ids bound

end RuntimeParametersBind

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParametersOwnerProperties`
-/

/-! Empty-start runtime parameter binding commutes with injective owner
relabeling that leaves binder indices fixed. The proof follows the existing
fresh-allocation chain, not arbitrary local-ID allocator covariance. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem map_bindFresh (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    (sameFresh : Resolved.freshLocalId (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).ids =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner inputs.ids))
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) =
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).bindFresh
          (mapping owner) name type value valueTyped := by
  cases inputs
  simp only [LocalInputs.mapIds, LocalInputs.bindFresh, List.map_cons,
    TypedLocalBinding.mapIds, LocalInputs.mk.injEq]
  congr 2
  exact sameFresh.symm

private theorem transport_from {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalInputs} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom types owner initial parameters arguments final)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    (sameIndex : (Resolved.freshLocalId (mapping owner)
        (initial.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).ids).binderIndex =
      (Resolved.freshLocalId owner initial.ids).binderIndex) :
    RuntimeParametersBindFrom types (mapping owner)
      (initial.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) parameters arguments
      (final.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) := by
  induction bound with
  | nil => exact .nil
  | @cons initial final span name annotation parameters argument arguments
      meaning unused tail ih =>
      have sameFresh : Resolved.freshLocalId (mapping owner)
          (initial.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).ids =
          ownerLocalIdMap mapping (Resolved.freshLocalId owner initial.ids) := by
        change Resolved.LocalId.mk (mapping owner) _ = Resolved.LocalId.mk (mapping owner) _
        exact congrArg (Resolved.LocalId.mk (mapping owner)) sameIndex
      have nextInputs := map_bindFresh initial owner mapping injective sameFresh
        name.value argument.type argument.value argument.valueTyped
      have nextIndex : (Resolved.freshLocalId (mapping owner)
          ((initial.bindFresh owner name.value argument.type argument.value
            argument.valueTyped).mapIds (ownerLocalIdMap mapping)
              (ownerLocalIdMap_injective mapping injective)).ids).binderIndex =
          (Resolved.freshLocalId owner
            (initial.bindFresh owner name.value argument.type argument.value
              argument.valueTyped).ids).binderIndex := by
        rw [nextInputs]
        simp only [LocalInputs.bindFresh_ids, Resolved.freshLocalId_cons_fresh_binderIndex,
          sameIndex]
      have mappedUnused : name.value ∉
          (initial.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).names.map Prod.fst := by
        simpa only [LocalInputs.mapIds_names, LocalNameTable.mapIds,
          List.map_map, Function.comp_def] using unused
      exact .cons meaning mappedUnused (nextInputs ▸ ih nextIndex)

/-- Relabeling an owner preserves the exact ordered typed input bundle produced
by independent empty-start binding. Runtime values and binder indices are unchanged. -/
theorem RuntimeParametersBind.map_owner {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument} {inputs : LocalInputs}
    (bound : RuntimeParametersBind types owner parameters arguments inputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    RuntimeParametersBind types (mapping owner) parameters arguments
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) :=
  transport_from bound mapping injective rfl

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParametersPositionProperties`
-/

/-! One positional witness links a source parameter to its exact generated ID,
runtime row, type, value, and first-match Core position. Real list lookups
provide the bound needed for reversed natural-number indices. -/

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

/-- A source/argument position selects one exact row. Unique names justify
first-match name lookup; unique IDs justify its reversed positional lowering.
Neither mere membership nor a truncated subtraction is sufficient. -/
theorem RuntimeParametersBind.position {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    {inputs : LocalInputs} (bound : RuntimeParametersBind types owner parameters arguments inputs)
    {index : Nat} {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument}
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument) :
    index < arguments.length ∧ StructuralTypeDenotes types annotation argument.type ∧
      inputs.bindings[arguments.length - 1 - index]? = some
        { name := name.value, id := ⟨owner, index⟩, type := argument.type,
          value := argument.value, valueTyped := argument.valueTyped } ∧
      LocalNameTable.Lookup inputs.names name.value ⟨owner, index⟩ ∧
      Resolved.LocalScope.Lookup inputs.context ⟨owner, index⟩ argument.type ∧
      Resolved.LocalScope.Lookup inputs.environment ⟨owner, index⟩ argument.value ∧
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids inputs.context)
        ⟨owner, index⟩ (arguments.length - 1 - index) := by
  have indexLt := (List.getElem?_eq_some_iff.mp argumentAt).1
  obtain ⟨row, reverseRowAt, paired⟩ := bound.rows.row_at parameterAt argumentAt
  have rowAt : inputs.bindings[arguments.length - 1 - index]? = some row := by
    have reverseEq := List.getElem?_reverse (l := inputs.bindings)
      (i := index) (by simpa only [bound.bindings_length] using indexLt)
    rw [bound.bindings_length] at reverseEq
    exact reverseEq.symm.trans reverseRowAt
  have generatedAt : inputs.ids[arguments.length - 1 - index]? = some ⟨owner, index⟩ := by
    rw [bound.generated_ids, List.getElem?_map]
    have reversed : (List.range arguments.length).reverse[arguments.length - 1 - index]? =
        (List.range arguments.length)[index]? :=
      List.getElem?_reverse' (by simp only [List.length_range]; omega)
    rw [reversed, List.getElem?_range indexLt]
    rfl
  have rowIdAt : inputs.ids[arguments.length - 1 - index]? = some row.id := by
    simp only [LocalInputs.ids, List.getElem?_map, rowAt, Option.map_some]
  have sameId := Option.some.inj (rowIdAt.symm.trans generatedAt)
  have indexed : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids inputs.context)
      ⟨owner, index⟩ (arguments.length - 1 - index) := by
    rw [LocalInputs.context_ids]
    exact index_of_getElem inputs.ids_nodup generatedAt
  cases paired with
  | @typed _ _ _ _ id meaning =>
      change id = ⟨owner, index⟩ at sameId
      subst id
      have member := List.mem_of_getElem? rowAt
      have named := name_lookup_of_mem bound.names_nodup
        (List.mem_map.mpr ⟨_, member, rfl⟩)
      exact ⟨indexLt, meaning, rowAt, named, inputs.context_lookup_of_mem member,
        inputs.environment_lookup_of_mem member, indexed⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParametersProperties`
-/

/-! Exact success, failure, and independent result uniqueness for the explicit
runtime parameter profile. No executable binding premise enters the judgment. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeParametersBind.complete {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter}
    {args : List TypedRuntimeArgument} {output : LocalInputs}
    (bound : RuntimeParametersBind types owner params args output) :
    bindRuntimeParameters? types owner params args = some output :=
  bindRuntimeParameters?_iff.mpr bound

theorem bindRuntimeParameters?_sound {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter}
    {args : List TypedRuntimeArgument} {output : LocalInputs}
    (result : bindRuntimeParameters? types owner params args = some output) :
    RuntimeParametersBind types owner params args output :=
  bindRuntimeParameters?_iff.mp result

theorem bindRuntimeParameters?_eq_none_iff {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter}
    {args : List TypedRuntimeArgument} :
    bindRuntimeParameters? types owner params args = none ↔
      ¬ ∃ output, RuntimeParametersBind types owner params args output := by
  constructor
  · intro result ⟨output, bound⟩
    have accepted := bound.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : bindRuntimeParameters? types owner params args with
    | none => rfl
    | some output => exact False.elim (absent ⟨output, bindRuntimeParameters?_sound result⟩)

/-- Uniqueness holds even when the initial inputs contain repeated names;
the new parameters themselves must still avoid every earlier spelling. -/
theorem RuntimeParametersBindFrom.result_unique {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial left right : LocalInputs}
    {params : List Syntax.FunctionParameter} {args : List TypedRuntimeArgument}
    (leftBound : RuntimeParametersBindFrom types owner initial params args left)
    (rightBound : RuntimeParametersBindFrom types owner initial params args right) :
    left = right := by
  induction leftBound with
  | nil => cases rightBound; rfl
  | cons _ _ _ ih =>
      cases rightBound with
      | cons _ _ tail => exact ih tail

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParametersStaticProperties`
-/

/-! Replacing supplied values while retaining their ordered structural types
preserves parameter-binding names and contexts. Runtime values need not agree. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeParametersBindFrom.transport_types {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {leftInitial leftFinal : LocalInputs}
    {parameters : List Syntax.FunctionParameter} {leftArguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom types owner leftInitial parameters leftArguments leftFinal)
    {rightInitial : LocalInputs} {rightArguments : List TypedRuntimeArgument}
    (sameNames : leftInitial.names = rightInitial.names)
    (sameContext : leftInitial.context = rightInitial.context)
    (sameArgumentTypes : leftArguments.map (·.type) = rightArguments.map (·.type)) :
    ∃ rightFinal, RuntimeParametersBindFrom types owner rightInitial parameters rightArguments rightFinal ∧
      rightFinal.names = leftFinal.names ∧ rightFinal.context = leftFinal.context := by
  induction bound generalizing rightInitial rightArguments with
  | nil =>
      cases rightArguments with
      | nil => exact ⟨rightInitial, .nil, sameNames.symm, sameContext.symm⟩
      | cons argument rest => simp only [List.map_nil, List.map_cons, reduceCtorEq] at sameArgumentTypes
  | @cons initial final span name annotation parameters argument arguments meaning unused tail ih =>
      cases rightArguments with
      | nil => simp only [List.map_cons, List.map_nil, reduceCtorEq] at sameArgumentTypes
      | cons rightArgument rightArguments =>
          obtain ⟨sameHead, sameTail⟩ := List.cons.inj (by simpa only [List.map_cons] using sameArgumentTypes)
          have sameIds : initial.ids = rightInitial.ids := by
            rw [← LocalInputs.context_ids, ← LocalInputs.context_ids, sameContext]
          have nextNames :
              (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped).names =
                (rightInitial.bindFresh owner name.value rightArgument.type rightArgument.value
                  rightArgument.valueTyped).names := by
            simp only [LocalInputs.bindFresh_names, sameNames, sameIds]
          have nextContext :
              (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped).context =
                (rightInitial.bindFresh owner name.value rightArgument.type rightArgument.value
                  rightArgument.valueTyped).context := by
            simp only [LocalInputs.bindFresh_context, sameContext, sameIds, sameHead]
          obtain ⟨rightFinal, rightTail, finalNames, finalContext⟩ := ih nextNames nextContext sameTail
          refine ⟨rightFinal, .cons ?_ ?_ rightTail, finalNames, finalContext⟩
          · exact sameHead ▸ meaning
          · simpa only [← sameNames] using unused

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeParametersTypeExtensionProperties`
-/

/-! Preserve the complete actual binding, not just its value-free projection.
Only annotation evidence changes; original values and generated IDs do not. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Arbitrary initial rows, including repeated spellings, remain exactly the
same. The original arguments supply all types, values and typing evidence. -/
theorem RuntimeParametersBindFrom.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial final : LocalInputs}
    {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom old owner initial parameters arguments final)
    (extension : TypeNameTable.Extends old new) :
    RuntimeParametersBindFrom new owner initial parameters arguments final := by
  induction bound with
  | nil => exact .nil
  | cons meaning unused _ ih => exact .cons (meaning.extend_types extension) unused ih

theorem RuntimeParametersBind.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument} {inputs : LocalInputs}
    (bound : RuntimeParametersBind old owner parameters arguments inputs)
    (extension : TypeNameTable.Extends old new) :
    RuntimeParametersBind new owner parameters arguments inputs :=
  RuntimeParametersBindFrom.extend_types bound extension

theorem bindRuntimeParameters?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument} {inputs : LocalInputs}
    (extension : TypeNameTable.Extends old new)
    (accepted : bindRuntimeParameters? old owner parameters arguments = some inputs) :
    bindRuntimeParameters? new owner parameters arguments = some inputs :=
  (RuntimeParametersBind.extend_types (bindRuntimeParameters?_sound accepted) extension).complete

/-- Mutual extension retains rejection as well as every actual output row.
One-way extension can supply an unknown annotation and enable binding. -/
theorem bindRuntimeParameters?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (parameters : List Syntax.FunctionParameter)
    (arguments : List TypedRuntimeArgument) :
    bindRuntimeParameters? old owner parameters arguments =
      bindRuntimeParameters? new owner parameters arguments := by
  cases oldResult : bindRuntimeParameters? old owner parameters arguments with
  | none =>
      cases newResult : bindRuntimeParameters? new owner parameters arguments with
      | none => rfl
      | some inputs =>
          have preserved := bindRuntimeParameters?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some inputs => exact (bindRuntimeParameters?_some_of_extends forward oldResult).symm

end Solcore.Frontend
