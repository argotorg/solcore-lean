import Solcore.Frontend.Expected

/-!
This standalone singleton-call adapter accepts an immediate conditional
argument containing at least one direct computation lambda.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Classify only an immediate, ungrouped computation lambda. -/
def isImmediateExpectedComputationLambda : Syntax.Expr → Bool
  | ⟨_, .lambda _ _ _ _⟩ => true
  | _ => false

/-- Classify exactly the new singleton conditional application boundary. -/
def isConditionalExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .conditional _ _ thenBranch _ elseBranch⟩]⟩⟩ =>
      isImmediateExpectedComputationLambda thenBranch ||
        isImmediateExpectedComputationLambda elseBranch
  | _ => false

/-- Each branch is source-disjoint: an immediate lambda uses expected checking,
and every other source uses unchanged recursive inference at the exact type. -/
inductive ConditionalExpectedLambdaBranchElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (expected : Core.Ty) : Syntax.Expr → Core.Expr → Prop where
  | expected {source : Syntax.Expr} {core : Core.Expr}
      (boundary : isImmediateExpectedComputationLambda source = true)
      (elaboration : ExpectedComputationLambdaElaborates
        RecursiveLocalComputationElaborates types owner inputs source core expected) :
      ConditionalExpectedLambdaBranchElaborates types owner inputs expected source core
  | ordinary {source : Syntax.Expr} {core : Core.Expr}
      (boundary : isImmediateExpectedComputationLambda source = false)
      (elaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context source core expected) :
      ConditionalExpectedLambdaBranchElaborates types owner inputs expected source core

/-- Check one branch without falling across its source-classification boundary. -/
def elaborateConditionalExpectedLambdaBranch?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) (expected : Core.Ty) : Option Core.Expr :=
  if isImmediateExpectedComputationLambda source then
    elaborateExpectedComputationLambda?
      elaborateRecursiveLocalComputation? types owner inputs source expected
  else do
    let (core, inferred) ←
      elaborateRecursiveLocalComputation? inputs.names inputs.context source
    if inferred = expected then some core else none

/-- Exact executable/declarative branch correspondence. -/
theorem elaborateConditionalExpectedLambdaBranch?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} {core : Core.Expr} :
    elaborateConditionalExpectedLambdaBranch? types owner inputs source expected = some core ↔
      ConditionalExpectedLambdaBranchElaborates
        types owner inputs expected source core := by
  constructor
  · intro accepted
    unfold elaborateConditionalExpectedLambdaBranch? at accepted
    split at accepted
    · rename_i boundary
      exact .expected boundary
        ((elaborateExpectedComputationLambda?_iff
          (@elaborateRecursiveLocalComputation?_iff)).mp accepted)
    · rename_i boundaryNot
      have boundary : isImmediateExpectedComputationLambda source = false := by
        cases equality : isImmediateExpectedComputationLambda source <;> simp_all
      cases checked : elaborateRecursiveLocalComputation?
          inputs.names inputs.context source with
      | none => simp [checked] at accepted
      | some result =>
        rcases result with ⟨branchCore, inferred⟩
        simp only [checked, bind, Option.bind_some] at accepted
        split at accepted
        · rename_i same
          subst inferred
          cases Option.some.inj accepted
          exact .ordinary boundary (elaborateRecursiveLocalComputation?_iff.mp checked)
        · cases accepted
  · intro elaboration
    cases elaboration with
    | expected boundary child =>
        simp [elaborateConditionalExpectedLambdaBranch?, boundary,
          (elaborateExpectedComputationLambda?_iff
            (@elaborateRecursiveLocalComputation?_iff)).mpr child]
    | ordinary boundary child =>
        simp [elaborateConditionalExpectedLambdaBranch?, boundary,
          elaborateRecursiveLocalComputation?_iff.mpr child]

/-- Exact original conditional evidence and the inferred callee signature. -/
inductive ConditionalExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan conditionalSpan question colon : Syntax.SourceSpan}
      {callee condition thenBranch elseBranch : Syntax.Expr}
      {functionCore conditionCore thenCore elseCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (boundary : (isImmediateExpectedComputationLambda thenBranch ||
          isImmediateExpectedComputationLambda elseBranch) = true)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (conditionElaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context condition conditionCore .bool)
      (thenElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType thenBranch thenCore)
      (elseElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType elseBranch elseCore) :
      ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs
        ⟨span, .call callee ⟨argumentsSpan,
          [⟨conditionalSpan, .conditional condition question thenBranch colon elseBranch⟩]⟩⟩
        (.apply functionCore (.ifE conditionCore thenCore elseCore)) resultType

/-- Infer the callee, require a Bool condition, and check both branches at the
literal parameter type. A selected candidate never falls back. -/
def elaborateConditionalExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_,
      [⟨_, .conditional condition _ thenBranch _ elseBranch⟩]⟩⟩ =>
    if isImmediateExpectedComputationLambda thenBranch ||
        isImmediateExpectedComputationLambda elseBranch then do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let (conditionCore, conditionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context condition
          if conditionType = .bool then
            let thenCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs thenBranch parameterType
            let elseCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs elseBranch parameterType
            some (.apply functionCore (.ifE conditionCore thenCore elseCore), resultType)
          else none
      | _ => none
    else none
  | _ => none

/-- Exact executable/declarative correspondence for the conditional adapter. -/
theorem elaborateConditionalExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      ConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;>
        try { simp [elaborateConditionalExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateConditionalExpectedLambdaArgumentApplication?] at accepted
          | cons argument tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateConditionalExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases argument with
              | mk conditionalSpan argumentKind =>
                cases argumentKind <;>
                  try { simp [elaborateConditionalExpectedLambdaArgumentApplication?] at accepted }
                case conditional condition question thenBranch colon elseBranch =>
                  simp only [elaborateConditionalExpectedLambdaArgumentApplication?] at accepted
                  split at accepted
                  · rename_i boundary
                    cases calleeChecked : elaborateRecursiveLocalComputation?
                        inputs.names inputs.context callee with
                    | none => simp [calleeChecked] at accepted
                    | some calleeResult =>
                      rcases calleeResult with ⟨functionCore, functionType⟩
                      simp only [calleeChecked, bind, Option.bind_some] at accepted
                      have calleeElaboration :=
                        elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                      cases functionType <;> try { simp at accepted }
                      case function parameterType resultType =>
                        cases conditionChecked : elaborateRecursiveLocalComputation?
                            inputs.names inputs.context condition with
                        | none => simp [conditionChecked] at accepted
                        | some conditionResult =>
                          rcases conditionResult with ⟨conditionCore, conditionType⟩
                          simp only [conditionChecked, Option.bind_some] at accepted
                          split at accepted
                          · rename_i conditionSame
                            subst conditionType
                            have conditionElaboration :=
                              elaborateRecursiveLocalComputation?_iff.mp conditionChecked
                            cases thenChecked : elaborateConditionalExpectedLambdaBranch?
                                types owner inputs thenBranch parameterType with
                            | none => simp [thenChecked] at accepted
                            | some thenCore =>
                              cases elseChecked : elaborateConditionalExpectedLambdaBranch?
                                  types owner inputs elseBranch parameterType with
                              | none => simp [thenChecked, elseChecked] at accepted
                              | some elseCore =>
                                simp [thenChecked, elseChecked] at accepted
                                rcases accepted with ⟨rfl, rfl⟩
                                exact .application boundary calleeElaboration conditionElaboration
                                  (elaborateConditionalExpectedLambdaBranch?_iff.mp thenChecked)
                                  (elaborateConditionalExpectedLambdaBranch?_iff.mp elseChecked)
                          · simp_all
                  · simp at accepted
  · intro elaboration
    cases elaboration with
    | application boundary callee condition thenBranch elseBranch =>
      simp [elaborateConditionalExpectedLambdaArgumentApplication?, boundary,
        elaborateRecursiveLocalComputation?_iff.mpr callee,
        elaborateRecursiveLocalComputation?_iff.mpr condition,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr thenBranch,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr elseBranch]

/-- Rejection is exactly absence of the standalone evidence. -/
theorem elaborateConditionalExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type, ConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateConditionalExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateConditionalExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateConditionalExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- Branch checking preserves the literal expected Core type. -/
theorem ConditionalExpectedLambdaBranchElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {expected : Core.Ty} {source : Syntax.Expr} {core : Core.Expr}
    (elaboration : ConditionalExpectedLambdaBranchElaborates
      types owner inputs expected source core) :
    Core.HasType inputs.context.values core expected := by
  cases elaboration with
  | expected boundary child =>
      exact child.core_hasType (@RecursiveLocalComputationElaborates.core_hasType)
  | ordinary boundary child => exact child.core_hasType

/-- The constructed conditional application has the inferred result type. -/
theorem ConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application boundary callee condition thenBranch elseBranch =>
      exact .apply callee.core_hasType
        (.ifE condition.core_hasType thenBranch.core_hasType elseBranch.core_hasType)

/-- Every evidence term lies on the exact public source boundary. -/
theorem ConditionalExpectedLambdaArgumentApplicationElaborates.classified
    {types owner inputs source core type}
    (elaboration : ConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isConditionalExpectedLambdaArgumentApplication source = true := by
  cases elaboration with | application boundary _ _ _ _ => simpa [isConditionalExpectedLambdaArgumentApplication] using boundary

/-- Inversion retains all source spans, children, branch choices and exact Core. -/
theorem ConditionalExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan conditionalSpan question colon callee condition
        thenBranch elseBranch functionCore conditionCore thenCore elseCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan,
        [⟨conditionalSpan, .conditional condition question thenBranch colon elseBranch⟩]⟩⟩ ∧
      (isImmediateExpectedComputationLambda thenBranch ||
        isImmediateExpectedComputationLambda elseBranch) = true ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType thenBranch thenCore ∧
      ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType elseBranch elseCore ∧
      core = .apply functionCore (.ifE conditionCore thenCore elseCore) := by
  cases elaboration with
  | application boundary callee condition thenBranch elseBranch =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, boundary,
        callee, condition, thenBranch, elseBranch, rfl⟩

end Solcore.Frontend
