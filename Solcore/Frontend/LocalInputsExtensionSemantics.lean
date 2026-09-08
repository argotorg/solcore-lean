import Solcore.Frontend.LocalInputsLookupProperties
import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.LocalNameAvoidanceProperties

/-! Adding a differently named fresh typed input preserves existing source
typing and evaluation. No source binding syntax or global allocation rule is
introduced; the exact value and both store endpoints are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem fresh_ne_of_named (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    {spelling : String} {id : Resolved.LocalId}
    (named : LocalNameTable.Lookup inputs.names spelling id) :
    Resolved.freshLocalId owner inputs.ids ≠ id := by
  obtain ⟨binding, member, _, idEq, _⟩ :=
    inputs.lookup?_binding (LocalNameTable.lookup?_iff.mpr named)
  intro same
  apply inputs.bindFresh_id_fresh owner
  exact List.mem_map.mpr ⟨binding, member, idEq.trans same.symm⟩

private theorem identity_lookup_cons_iff {α : Type} {scope : Resolved.LocalScope α}
    {id newId : Resolved.LocalId} {value newValue : α} (different : newId ≠ id) :
    Resolved.LocalScope.Lookup ((newId, newValue) :: scope) id value ↔
      Resolved.LocalScope.Lookup scope id value := by
  constructor
  · intro found
    cases found with
    | head => exact False.elim (different rfl)
    | tail _ found => exact found
  · exact Resolved.LocalScope.Lookup.tail different

theorem AvoidsLocalName.bindFresh_hasType_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs)
    (owner : Resolved.DeclarationId) (newType : Core.Ty) (newValue : Core.Value)
    (valueTyped : Core.ValueHasType newValue newType) {resultType : Core.Ty} :
    LocalExpressionHasType (inputs.bindFresh owner name newType newValue valueTyped).names
        (inputs.bindFresh owner name newType newValue valueTyped).context source resultType ↔
      LocalExpressionHasType inputs.names inputs.context source resultType := by
  induction avoids generalizing resultType with
  | identifier different =>
      constructor
      · intro typing
        cases typing with
        | identifier named found =>
            have oldNamed := (LocalNameTable.lookup_cons_iff_of_ne different).mp named
            exact .identifier oldNamed
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner oldNamed)).mp found)
      · intro typing
        cases typing with
        | identifier named found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mpr named)
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner named)).mpr found)
  | group _ ih =>
      constructor
      · intro typing
        cases typing with
        | group child => exact .group (ih.mp child)
      · intro typing
        cases typing with
        | group child => exact .group (ih.mpr child)
  | logicalNot _ ih =>
      constructor
      · intro typing
        cases typing with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro typing
        cases typing with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro typing
        cases typing with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mp condition) (thenIH.mp thenBranch) (elseIH.mp elseBranch)
      · intro typing
        cases typing with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mpr condition) (thenIH.mpr thenBranch) (elseIH.mpr elseBranch)

/-- Avoidance preserves and reflects raw source evaluation. Missing names in
an unselected branch need not resolve or type-check for this exact-store law. -/
theorem AvoidsLocalName.bindFresh_evaluates_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs)
    (owner : Resolved.DeclarationId) (newType : Core.Ty) (newValue : Core.Value)
    (valueTyped : Core.ValueHasType newValue newType)
    {initialStore finalStore : Core.Store} {result : Core.Value} :
    LocalExpressionEvaluates (inputs.bindFresh owner name newType newValue valueTyped).names
        (inputs.bindFresh owner name newType newValue valueTyped).environment
        initialStore source result finalStore ↔
      LocalExpressionEvaluates inputs.names inputs.environment initialStore source result finalStore := by
  induction avoids generalizing initialStore finalStore result with
  | identifier different =>
      constructor
      · intro evaluation
        cases evaluation with
        | identifier named found =>
            have oldNamed := (LocalNameTable.lookup_cons_iff_of_ne different).mp named
            exact .identifier oldNamed
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner oldNamed)).mp found)
      · intro evaluation
        cases evaluation with
        | identifier named found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mpr named)
              ((identity_lookup_cons_iff (fresh_ne_of_named inputs owner named)).mpr found)
  | group _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mp child)
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mpr child)
  | logicalNot _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mp condition) (thenIH.mp branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mp condition) (elseIH.mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mpr condition) (thenIH.mpr branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mpr condition) (elseIH.mpr branch)

end Solcore.Frontend
