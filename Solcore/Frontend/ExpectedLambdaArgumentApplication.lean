import Solcore.Frontend.ExpectedComputationLambda
import Solcore.Frontend.RecursiveLocalComputationProperties

/-!
An opt-in adapter for a unary call whose argument is an expected-type
computation lambda. It deliberately does not change the recursive inference
checker or any parser/diagnostic entry point.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A locally inferred unary callee supplies the exact expected type for a
literal computation-lambda argument. -/
inductive ExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {functionCore argumentCore : Core.Expr} {parameterType resultType : Core.Ty}
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (argumentElaboration : ExpectedComputationLambdaElaborates
        RecursiveLocalComputationElaborates types owner inputs argument argumentCore parameterType) :
      ExpectedLambdaArgumentApplicationElaborates types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩
        (.apply functionCore argumentCore) resultType

/-- Infer the callee, then check the sole argument as a computation lambda at
the callee's parameter type. -/
def elaborateExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [argument]⟩⟩ => do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let argumentCore ← elaborateExpectedComputationLambda?
            elaborateRecursiveLocalComputation? types owner inputs argument parameterType
          some (.apply functionCore argumentCore, resultType)
      | _ => none
  | _ => none

/-- Exact executable/declarative correspondence for the opt-in adapter. -/
theorem elaborateExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateExpectedLambdaArgumentApplication? types owner inputs source = some (core, type) ↔
      ExpectedLambdaArgumentApplicationElaborates types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateExpectedLambdaArgumentApplication?] at accepted
          | cons argument tail =>
            cases tail with
            | cons second rest => simp [elaborateExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases calleeChecked : elaborateRecursiveLocalComputation?
                  inputs.names inputs.context callee with
              | none =>
                  simp [elaborateExpectedLambdaArgumentApplication?, calleeChecked] at accepted
              | some calleeResult =>
                rcases calleeResult with ⟨functionCore, functionType⟩
                have calleeElaboration := elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                cases functionType <;>
                  try { simp [elaborateExpectedLambdaArgumentApplication?, calleeChecked] at accepted }
                case function parameterType resultType =>
                  cases argumentChecked : elaborateExpectedComputationLambda?
                      elaborateRecursiveLocalComputation? types owner inputs argument parameterType with
                  | none =>
                      simp [elaborateExpectedLambdaArgumentApplication?, calleeChecked,
                        argumentChecked] at accepted
                  | some argumentCore =>
                    have argumentElaboration :=
                      (elaborateExpectedComputationLambda?_iff
                        (@elaborateRecursiveLocalComputation?_iff)).mp argumentChecked
                    simp [elaborateExpectedLambdaArgumentApplication?, calleeChecked,
                      argumentChecked] at accepted
                    rcases accepted with ⟨rfl, rfl⟩
                    exact .application calleeElaboration argumentElaboration
  · intro elaboration
    cases elaboration with
    | application calleeElaboration argumentElaboration =>
      simp [elaborateExpectedLambdaArgumentApplication?,
        elaborateRecursiveLocalComputation?_iff.mpr calleeElaboration,
        (elaborateExpectedComputationLambda?_iff
          (@elaborateRecursiveLocalComputation?_iff)).mpr argumentElaboration]

/-- Rejection is precisely absence of adapter evidence. -/
theorem elaborateExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateExpectedLambdaArgumentApplication? types owner inputs source = none ↔
      ¬ ∃ core type,
        ExpectedLambdaArgumentApplicationElaborates types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := elaborateExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateExpectedLambdaArgumentApplication? types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- The adapter preserves the inferred result type in Core. -/
theorem ExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application calleeElaboration argumentElaboration =>
      exact .apply calleeElaboration.core_hasType
        (argumentElaboration.core_hasType
          (@RecursiveLocalComputationElaborates.core_hasType))

/-- Concise inversion retains both original children and the exact Core apply. -/
theorem ExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan callee argument functionCore argumentCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
        types owner inputs argument argumentCore parameterType ∧
      core = .apply functionCore argumentCore := by
  cases elaboration with
  | application calleeElaboration argumentElaboration =>
      exact ⟨_, _, _, _, _, _, _, rfl, calleeElaboration, argumentElaboration, rfl⟩

end Solcore.Frontend
