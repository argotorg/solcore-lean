import Solcore.Frontend.RuntimeParametersLayout
import Solcore.Frontend.LocalInputsLookupProperties

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
