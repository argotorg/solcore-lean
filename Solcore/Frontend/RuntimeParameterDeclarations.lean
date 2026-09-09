import Solcore.Frontend.StructuralTypeProperties
import Solcore.Frontend.LocalTypeInputs
import Solcore.Syntax.Declaration

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
