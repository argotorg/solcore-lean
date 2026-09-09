import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalInputsProperties

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
