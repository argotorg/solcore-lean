import Solcore.Frontend.StructuralTypeProperties
import Solcore.Frontend.LocalInputs

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
