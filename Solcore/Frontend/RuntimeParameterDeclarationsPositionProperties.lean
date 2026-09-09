import Solcore.Frontend.RuntimeParameterDeclarationsLayout
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Resolved.LocalScopeProperties

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
