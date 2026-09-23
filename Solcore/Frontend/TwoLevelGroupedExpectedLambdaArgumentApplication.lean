import Solcore.Frontend.Expected

/-!
One opt-in adapter passes a locally inferred parameter type through exactly two
source groups to a direct computation-lambda argument.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Exact source evidence retains the call, argument-list and both group spans
while both groups are transparent in the resulting Core application. -/
inductive TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan outerGroupSpan innerGroupSpan : Syntax.SourceSpan}
      {callee argument : Syntax.Expr} {functionCore argumentCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (argumentElaboration : ExpectedComputationLambdaElaborates
        RecursiveLocalComputationElaborates types owner inputs argument argumentCore parameterType) :
      TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs
        ⟨span, .call callee ⟨argumentsSpan,
          [⟨outerGroupSpan, .group ⟨innerGroupSpan, .group argument⟩⟩]⟩⟩
        (.apply functionCore argumentCore) resultType

/-- Infer the callee, unwrap exactly two groups and check the immediate child as
an expected computation lambda. -/
def elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [⟨_, .group ⟨_, .group argument⟩⟩]⟩⟩ => do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let argumentCore ← elaborateExpectedComputationLambda?
            elaborateRecursiveLocalComputation? types owner inputs argument parameterType
          some (.apply functionCore argumentCore, resultType)
      | _ => none
  | _ => none

/-- Exact executable/declarative correspondence for the two-level adapter. -/
theorem elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;>
        try { simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil =>
              simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?] at accepted
          | cons outerGrouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases outerGrouped with
              | mk outerGroupSpan outerKind =>
                cases outerKind <;>
                  try {
                    simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?] at accepted }
                case group innerGrouped =>
                  cases innerGrouped with
                  | mk innerGroupSpan innerKind =>
                    cases innerKind <;>
                      try {
                        simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?]
                          at accepted }
                    case group argument =>
                      cases calleeChecked : elaborateRecursiveLocalComputation?
                          inputs.names inputs.context callee with
                      | none =>
                          simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?,
                            calleeChecked] at accepted
                      | some calleeResult =>
                        rcases calleeResult with ⟨functionCore, functionType⟩
                        have calleeElaboration :=
                          elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                        cases functionType <;>
                          try {
                            simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?,
                              calleeChecked] at accepted }
                        case function parameterType resultType =>
                          cases argumentChecked : elaborateExpectedComputationLambda?
                              elaborateRecursiveLocalComputation? types owner inputs argument
                                parameterType with
                          | none =>
                              simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?,
                                calleeChecked, argumentChecked] at accepted
                          | some argumentCore =>
                            have argumentElaboration :=
                              (elaborateExpectedComputationLambda?_iff
                                (@elaborateRecursiveLocalComputation?_iff)).mp argumentChecked
                            simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?,
                              calleeChecked, argumentChecked] at accepted
                            rcases accepted with ⟨rfl, rfl⟩
                            exact .application calleeElaboration argumentElaboration
  · intro elaboration
    cases elaboration with
    | application calleeElaboration argumentElaboration =>
      simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?,
        elaborateRecursiveLocalComputation?_iff.mpr calleeElaboration,
        (elaborateExpectedComputationLambda?_iff
          (@elaborateRecursiveLocalComputation?_iff)).mpr argumentElaboration]

/-- Rejection is precisely absence of exact two-level adapter evidence. -/
theorem elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type, TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- Removing both source groups preserves the inferred result type in Core. -/
theorem TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application calleeElaboration argumentElaboration =>
      exact .apply calleeElaboration.core_hasType
        (argumentElaboration.core_hasType
          (@RecursiveLocalComputationElaborates.core_hasType))

/-- Inversion exposes every original span, both children and the exact Core apply. -/
theorem TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan outerGroupSpan innerGroupSpan callee argument
        functionCore argumentCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan,
        [⟨outerGroupSpan, .group ⟨innerGroupSpan, .group argument⟩⟩]⟩⟩ ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
        types owner inputs argument argumentCore parameterType ∧
      core = .apply functionCore argumentCore := by
  cases elaboration with
  | application calleeElaboration argumentElaboration =>
      exact ⟨_, _, _, _, _, _, _, _, _, rfl, calleeElaboration,
        argumentElaboration, rfl⟩

end Solcore.Frontend
