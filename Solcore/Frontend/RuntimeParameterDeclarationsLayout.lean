import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.LocalTypeInputsProperties

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
      (meaning : TypeNameDenotes types annotation type) :
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
