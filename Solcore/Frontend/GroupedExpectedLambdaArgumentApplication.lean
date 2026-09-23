import Solcore.Frontend.Expected

/-!
One opt-in adapter passes a locally inferred parameter type through exactly one
source group to a direct computation-lambda argument.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Exact source evidence retains the call, argument-list and group spans while
the group is transparent in the resulting Core application. -/
inductive GroupedExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan groupSpan : Syntax.SourceSpan}
      {callee argument : Syntax.Expr} {functionCore argumentCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (argumentElaboration : ExpectedComputationLambdaElaborates
        RecursiveLocalComputationElaborates types owner inputs argument argumentCore parameterType) :
      GroupedExpectedLambdaArgumentApplicationElaborates types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [⟨groupSpan, .group argument⟩]⟩⟩
        (.apply functionCore argumentCore) resultType

/-- Infer the callee, unwrap exactly one group and check its immediate child as
an expected computation lambda. -/
def elaborateGroupedExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [⟨_, .group argument⟩]⟩⟩ => do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let argumentCore ← elaborateExpectedComputationLambda?
            elaborateRecursiveLocalComputation? types owner inputs argument parameterType
          some (.apply functionCore argumentCore, resultType)
      | _ => none
  | _ => none

/-- Exact executable/declarative correspondence for the grouped adapter. -/
theorem elaborateGroupedExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs source =
        some (core, type) ↔
      GroupedExpectedLambdaArgumentApplicationElaborates types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;>
        try { simp [elaborateGroupedExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateGroupedExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateGroupedExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases grouped with
              | mk groupSpan groupedKind =>
                cases groupedKind <;>
                  try { simp [elaborateGroupedExpectedLambdaArgumentApplication?] at accepted }
                case group argument =>
                  cases calleeChecked : elaborateRecursiveLocalComputation?
                      inputs.names inputs.context callee with
                  | none =>
                      simp [elaborateGroupedExpectedLambdaArgumentApplication?, calleeChecked]
                        at accepted
                  | some calleeResult =>
                    rcases calleeResult with ⟨functionCore, functionType⟩
                    have calleeElaboration :=
                      elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                    cases functionType <;>
                      try {
                        simp [elaborateGroupedExpectedLambdaArgumentApplication?, calleeChecked]
                          at accepted }
                    case function parameterType resultType =>
                      cases argumentChecked : elaborateExpectedComputationLambda?
                          elaborateRecursiveLocalComputation? types owner inputs argument
                            parameterType with
                      | none =>
                          simp [elaborateGroupedExpectedLambdaArgumentApplication?, calleeChecked,
                            argumentChecked] at accepted
                      | some argumentCore =>
                        have argumentElaboration :=
                          (elaborateExpectedComputationLambda?_iff
                            (@elaborateRecursiveLocalComputation?_iff)).mp argumentChecked
                        simp [elaborateGroupedExpectedLambdaArgumentApplication?, calleeChecked,
                          argumentChecked] at accepted
                        rcases accepted with ⟨rfl, rfl⟩
                        exact .application calleeElaboration argumentElaboration
  · intro elaboration
    cases elaboration with
    | application calleeElaboration argumentElaboration =>
      simp [elaborateGroupedExpectedLambdaArgumentApplication?,
        elaborateRecursiveLocalComputation?_iff.mpr calleeElaboration,
        (elaborateExpectedComputationLambda?_iff
          (@elaborateRecursiveLocalComputation?_iff)).mpr argumentElaboration]

/-- Rejection is precisely absence of grouped adapter evidence. -/
theorem elaborateGroupedExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs source = none ↔
      ¬ ∃ core type,
        GroupedExpectedLambdaArgumentApplicationElaborates
          types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := elaborateGroupedExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted :
        elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateGroupedExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- Removing the source group preserves the inferred result type in Core. -/
theorem GroupedExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : GroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application calleeElaboration argumentElaboration =>
      exact .apply calleeElaboration.core_hasType
        (argumentElaboration.core_hasType
          (@RecursiveLocalComputationElaborates.core_hasType))

/-- Inversion exposes every original span, both children and the exact Core apply. -/
theorem GroupedExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : GroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan groupSpan callee argument functionCore argumentCore parameterType,
      source =
        ⟨span, .call callee ⟨argumentsSpan, [⟨groupSpan, .group argument⟩]⟩⟩ ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
        types owner inputs argument argumentCore parameterType ∧
      core = .apply functionCore argumentCore := by
  cases elaboration with
  | application calleeElaboration argumentElaboration =>
      exact ⟨_, _, _, _, _, _, _, _, rfl, calleeElaboration, argumentElaboration, rfl⟩

end Solcore.Frontend
