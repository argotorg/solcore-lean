import Solcore.Frontend.Fragments.Internal.Expected
import Solcore.Syntax.Term

/-!
# Grouped expected lambdas

One family of expected lambda arguments, through any depth of source groups and conditionals.
-/

section
-- leanmerge: from Solcore.Frontend.ConditionalExpectedLambdaArgumentApplication
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
end

section
-- leanmerge: from Solcore.Frontend.ConditionalGroupSpine
set_option autoImplicit false

namespace Solcore.Frontend

/-- A maximal finite group spine ending at the original immediate conditional. -/
inductive ConditionalGroupSpine :
    Syntax.Expr → List Syntax.SourceSpan → Syntax.Expr → Prop where
  | conditional {span question colon : Syntax.SourceSpan}
      {condition yes no : Syntax.Expr} :
      ConditionalGroupSpine
        ⟨span, .conditional condition question yes colon no⟩ []
        ⟨span, .conditional condition question yes colon no⟩
  | group {span : Syntax.SourceSpan} {inner terminal : Syntax.Expr}
      {spans : List Syntax.SourceSpan}
      (child : ConditionalGroupSpine inner spans terminal) :
      ConditionalGroupSpine ⟨span, .group inner⟩ (span :: spans) terminal

/-- Collect all original group spans and return the original terminal conditional. -/
def peelConditionalGroupSpine?
    : (source : Syntax.Expr) → Option (List Syntax.SourceSpan × Syntax.Expr) :=
  WellFounded.fix (measure sizeOf).wf fun source recurse =>
    match source with
    | terminal@⟨_, .conditional _ _ _ _ _⟩ => some ([], terminal)
    | ⟨span, .group inner⟩ => do
        let (spans, terminal) ← recurse inner (by decreasing_tactic)
        some (span :: spans, terminal)
    | _ => none

@[simp] theorem peelConditionalGroupSpine?_conditional
    (span question colon : Syntax.SourceSpan) (condition yes no : Syntax.Expr) :
    peelConditionalGroupSpine?
      ⟨span, .conditional condition question yes colon no⟩ =
        some ([], ⟨span, .conditional condition question yes colon no⟩) := by
  rw [peelConditionalGroupSpine?, WellFounded.fix_eq]

@[simp] theorem peelConditionalGroupSpine?_group
    (span : Syntax.SourceSpan) (inner : Syntax.Expr) :
    peelConditionalGroupSpine? ⟨span, .group inner⟩ = (do
      let (spans, terminal) ← peelConditionalGroupSpine? inner
      some (span :: spans, terminal)) := by
  rw [peelConditionalGroupSpine?, WellFounded.fix_eq]

private theorem peelConditionalGroupSpine?_sound
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan}
    (accepted : peelConditionalGroupSpine? source = some (spans, terminal)) :
    ConditionalGroupSpine source spans terminal := by
  revert spans terminal
  apply (measure sizeOf).wf.induction source
  intro source ih spans terminal accepted
  cases source with
  | mk span kind =>
    cases kind <;>
      try { rw [peelConditionalGroupSpine?, WellFounded.fix_eq] at accepted; cases accepted }
    case conditional condition question yes colon no =>
      simp only [peelConditionalGroupSpine?_conditional, Option.some.injEq,
        Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact .conditional
    case group inner =>
      cases checked : peelConditionalGroupSpine? inner with
      | none => simp [peelConditionalGroupSpine?_group, checked] at accepted
      | some result =>
        rcases result with ⟨innerSpans, argument⟩
        simp [peelConditionalGroupSpine?_group, checked] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact .group (ih inner (by simp_wf; omega) checked)

private theorem peelConditionalGroupSpine?_complete
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan}
    (spine : ConditionalGroupSpine source spans terminal) :
    peelConditionalGroupSpine? source = some (spans, terminal) := by
  induction spine with
  | conditional => simp only [peelConditionalGroupSpine?_conditional]
  | group child ih => simp [peelConditionalGroupSpine?_group, ih]

/-- Exact executable/declarative correspondence for the maximal spine. -/
theorem peelConditionalGroupSpine?_iff
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan} :
    peelConditionalGroupSpine? source = some (spans, terminal) ↔
      ConditionalGroupSpine source spans terminal :=
  ⟨peelConditionalGroupSpine?_sound, peelConditionalGroupSpine?_complete⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.EightOrMoreGroupedConditionalExpectedLambdaArgumentApplication
set_option autoImplicit false

namespace Solcore.Frontend


/-- Recognize every new depth-eight-or-more grouped conditional boundary. -/
def isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication :
    Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [grouped]⟩⟩ =>
      match peelConditionalGroupSpine? grouped with
      | some (spans, ⟨_, .conditional _ _ yes _ no⟩) =>
          if 8 ≤ spans.length then
            isImmediateExpectedComputationLambda yes ||
              isImmediateExpectedComputationLambda no
          else false
      | _ => false
  | _ => false

/-- Classification is exactly an ordered finite spine of length at least eight
ending at an immediate conditional with an expected-lambda branch. -/
theorem isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication_iff
    {span argumentsSpan : Syntax.SourceSpan} {callee grouped : Syntax.Expr} :
    isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication
        ⟨span, .call callee ⟨argumentsSpan, [grouped]⟩⟩ = true ↔
      ∃ spans conditionalSpan question colon condition yes no,
        ConditionalGroupSpine grouped spans
          ⟨conditionalSpan, .conditional condition question yes colon no⟩ ∧
        8 ≤ spans.length ∧
        (isImmediateExpectedComputationLambda yes ||
          isImmediateExpectedComputationLambda no) = true := by
  constructor
  · intro selected
    cases checked : peelConditionalGroupSpine? grouped with
    | none =>
        simp [isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication,
          checked] at selected
    | some result =>
      rcases result with ⟨spans, terminal⟩
      cases terminal with
      | mk conditionalSpan kind =>
        cases kind <;>
          try { simp [isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication,
            checked] at selected }
        case conditional condition question yes colon no =>
          simp only [isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication,
            checked] at selected
          split at selected
          · rename_i minimum
            exact ⟨spans, conditionalSpan, question, colon, condition, yes, no,
              peelConditionalGroupSpine?_iff.mp checked, minimum, selected⟩
          · simp at selected
  · rintro ⟨spans, conditionalSpan, question, colon, condition, yes, no,
      spine, minimum, boundary⟩
    simp [isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication,
      peelConditionalGroupSpine?_iff.mpr spine, minimum, boundary]

/-- Exact source evidence for all newly covered finite grouped conditionals. -/
inductive EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan conditionalSpan question colon : Syntax.SourceSpan}
      {spans : List Syntax.SourceSpan} {callee grouped condition yes no : Syntax.Expr}
      {functionCore conditionCore yesCore noCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (spine : ConditionalGroupSpine grouped spans
        ⟨conditionalSpan, .conditional condition question yes colon no⟩)
      (minimum : 8 ≤ spans.length)
      (boundary : (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (conditionElaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context condition conditionCore .bool)
      (yesElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType yes yesCore)
      (noElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType no noCore) :
      EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs ⟨span, .call callee ⟨argumentsSpan, [grouped]⟩⟩
        (.apply functionCore (.ifE conditionCore yesCore noCore)) resultType

/-- Elaborate the original terminal conditional for every finite depth at least eight. -/
def elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [grouped]⟩⟩ => do
      let (spans, terminal) ← peelConditionalGroupSpine? grouped
      match terminal with
      | ⟨_, .conditional condition _ yes _ no⟩ =>
        if 8 ≤ spans.length then
          if isImmediateExpectedComputationLambda yes ||
              isImmediateExpectedComputationLambda no then do
            let (functionCore, functionType) ←
              elaborateRecursiveLocalComputation? inputs.names inputs.context callee
            match functionType with
            | .function parameterType resultType => do
                let (conditionCore, conditionType) ←
                  elaborateRecursiveLocalComputation? inputs.names inputs.context condition
                if conditionType = .bool then
                  let yesCore ← elaborateConditionalExpectedLambdaBranch?
                    types owner inputs yes parameterType
                  let noCore ← elaborateConditionalExpectedLambdaBranch?
                    types owner inputs no parameterType
                  some (.apply functionCore (.ifE conditionCore yesCore noCore), resultType)
                else none
            | _ => none
          else none
        else none
      | _ => none
  | _ => none

/-- Exact executable/declarative correspondence. -/
theorem elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;>
        try { simp [elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?]
          at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil =>
              simp [elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?]
                at accepted
          | cons grouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?]
                  at accepted
            | nil =>
              cases spineChecked : peelConditionalGroupSpine? grouped with
              | none =>
                  simp [elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?,
                    spineChecked] at accepted
              | some result =>
                rcases result with ⟨spans, terminal⟩
                cases terminal with
                | mk conditionalSpan terminalKind =>
                  cases terminalKind <;>
                    try { simp [elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?,
                      spineChecked] at accepted }
                  case conditional condition question yes colon no =>
                    simp only [elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?,
                      spineChecked, bind, Option.bind_some] at accepted
                    split at accepted
                    · rename_i minimum
                      split at accepted
                      · rename_i boundary
                        cases calleeChecked : elaborateRecursiveLocalComputation?
                            inputs.names inputs.context callee with
                        | none => simp [calleeChecked] at accepted
                        | some calleeResult =>
                          rcases calleeResult with ⟨functionCore, functionType⟩
                          simp only [calleeChecked, Option.bind_some] at accepted
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
                              have conditionElaboration :=
                                elaborateRecursiveLocalComputation?_iff.mp conditionChecked
                              split at accepted
                              · rename_i same
                                subst conditionType
                                cases yesChecked : elaborateConditionalExpectedLambdaBranch?
                                    types owner inputs yes parameterType with
                                | none => simp [yesChecked] at accepted
                                | some yesCore =>
                                  cases noChecked : elaborateConditionalExpectedLambdaBranch?
                                      types owner inputs no parameterType with
                                  | none => simp [yesChecked, noChecked] at accepted
                                  | some noCore =>
                                    simp [yesChecked, noChecked] at accepted
                                    rcases accepted with ⟨rfl, rfl⟩
                                    exact .application
                                      (peelConditionalGroupSpine?_iff.mp spineChecked)
                                      minimum boundary calleeElaboration conditionElaboration
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp yesChecked)
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp noChecked)
                              · simp_all
                      · simp at accepted
                    · simp at accepted
  · intro elaboration
    cases elaboration with
    | application spine minimum boundary calleeElaboration conditionElaboration
        yesElaboration noElaboration =>
      rename_i span argumentsSpan conditionalSpan question colon spans callee grouped
        conditionSource yesSource noSource functionCore conditionCore yesCore noCore parameterType
      cases yesBoundary : isImmediateExpectedComputationLambda yesSource <;>
        cases noBoundary : isImmediateExpectedComputationLambda noSource <;>
        simp_all [elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?,
          peelConditionalGroupSpine?_iff.mpr spine,
          elaborateRecursiveLocalComputation?_iff.mpr calleeElaboration,
          elaborateRecursiveLocalComputation?_iff.mpr conditionElaboration,
          elaborateConditionalExpectedLambdaBranch?_iff.mpr yesElaboration,
          elaborateConditionalExpectedLambdaBranch?_iff.mpr noElaboration]

/-- Failure is exact absence of generic-spine evidence. -/
theorem elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type,
        EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
          types owner inputs source core type := by
  constructor
  · rintro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr
        elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp
          accepted⟩)

/-- Every successful generic-spine elaboration retains its inferred Core type. -/
theorem EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application _ _ _ callee condition yes no =>
      exact .apply callee.core_hasType
        (.ifE condition.core_hasType yes.core_hasType no.core_hasType)

/-- Provenance retains the ordered spine, original conditional and all children. -/
theorem EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan spans conditionalSpan question colon callee grouped condition yes no
        functionCore conditionCore yesCore noCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [grouped]⟩⟩ ∧
      ConditionalGroupSpine grouped spans
        ⟨conditionalSpan, .conditional condition question yes colon no⟩ ∧
      8 ≤ spans.length ∧
      (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧
      core = .apply functionCore (.ifE conditionCore yesCore noCore) := by
  cases elaboration with
  | application spine minimum boundary callee condition yes no =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, spine, minimum,
        boundary, callee, condition, yes, no, rfl⟩

/-- Every successful elaboration is selected by the generic classifier. -/
theorem EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified
    {types owner inputs source core type}
    (elaboration : EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application spine minimum boundary _ _ _ _ =>
      simp [isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication,
        peelConditionalGroupSpine?_iff.mpr spine, minimum, boundary]

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.FiveLevelGroupedConditionalExpectedLambdaArgumentApplication
/-!
Checks an immediate conditional through exactly five transparent source groups
in an exact singleton application argument.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly five groups around an immediate conditional whose branch
boundary is already settled by ADR-0324. -/
def isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .group ⟨_, .conditional _ _ yes _ no⟩⟩⟩⟩⟩⟩]⟩⟩ =>
      isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no
  | _ => false

/-- The source groups are retained while the unchanged ADR-0324 branch relations
check the two original immediate branches at the callee parameter type. -/
inductive FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan
        deepestGroupSpan innermostGroupSpan conditionalSpan question colon :
        Syntax.SourceSpan}
      {callee condition yes no : Syntax.Expr}
      {functionCore conditionCore yesCore noCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (boundary : (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (conditionElaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context condition conditionCore .bool)
      (yesElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType yes yesCore)
      (noElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType no noCore) :
      FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
          ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
            ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group
              ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩]⟩⟩
        (.apply functionCore (.ifE conditionCore yesCore noCore)) resultType

/-- Inspect the original grouped source and return the selected complete result. -/
def elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .group ⟨_, .conditional condition _ yes _ no⟩⟩⟩⟩⟩⟩]⟩⟩ =>
    if isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no then do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let (conditionCore, conditionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context condition
          if conditionType = .bool then
            let yesCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs yes parameterType
            let noCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs no parameterType
            some (.apply functionCore (.ifE conditionCore yesCore noCore), resultType)
          else none
      | _ => none
    else none
  | _ => none

/-- Exact executable/declarative correspondence. -/
theorem elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases grouped with
              | mk outerGroupSpan groupedKind =>
                cases groupedKind <;> try { simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                case group middle =>
                  cases middle with
                  | mk middleGroupSpan middleKind =>
                    cases middleKind <;> try { simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                    case group inner =>
                      cases inner with
                      | mk innerGroupSpan innerKind =>
                        cases innerKind <;> try { simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                        case group deepest =>
                          cases deepest with
                          | mk deepestGroupSpan deepestKind =>
                            cases deepestKind <;> try { simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                            case group innermost =>
                              cases innermost with
                              | mk innermostGroupSpan innermostKind =>
                                cases innermostKind <;> try { simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                case group conditional =>
                                  cases conditional with
                                  | mk conditionalSpan conditionalKind =>
                                    cases conditionalKind <;> try { simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                    case conditional condition question yes colon no =>
                      simp only [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
                      split at accepted
                      · rename_i boundary
                        cases calleeChecked : elaborateRecursiveLocalComputation?
                            inputs.names inputs.context callee with
                        | none => simp [calleeChecked] at accepted
                        | some calleeResult =>
                          rcases calleeResult with ⟨functionCore, functionType⟩
                          simp only [calleeChecked, bind, Option.bind_some] at accepted
                          have calleeElaboration := elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                          cases functionType <;> try { simp at accepted }
                          case function parameterType resultType =>
                            cases conditionChecked : elaborateRecursiveLocalComputation?
                                inputs.names inputs.context condition with
                            | none => simp [conditionChecked] at accepted
                            | some conditionResult =>
                              rcases conditionResult with ⟨conditionCore, conditionType⟩
                              simp only [conditionChecked, Option.bind_some] at accepted
                              have conditionElaboration :=
                                elaborateRecursiveLocalComputation?_iff.mp conditionChecked
                              split at accepted
                              · rename_i same
                                subst conditionType
                                cases yesChecked : elaborateConditionalExpectedLambdaBranch?
                                    types owner inputs yes parameterType with
                                | none => simp [yesChecked] at accepted
                                | some yesCore =>
                                  cases noChecked : elaborateConditionalExpectedLambdaBranch?
                                      types owner inputs no parameterType with
                                  | none => simp [yesChecked, noChecked] at accepted
                                  | some noCore =>
                                    simp [yesChecked, noChecked] at accepted
                                    rcases accepted with ⟨rfl, rfl⟩
                                    exact .application boundary calleeElaboration conditionElaboration
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp yesChecked)
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp noChecked)
                              · simp_all
                      · simp at accepted
  · intro elaboration
    cases elaboration with
    | application boundary callee condition yes no =>
      simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, boundary,
        elaborateRecursiveLocalComputation?_iff.mpr callee,
        elaborateRecursiveLocalComputation?_iff.mpr condition,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr yes,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr no]

/-- Failure is exact absence of evidence. -/
theorem elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type, FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · rintro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- The exact inferred Core result type is preserved. -/
theorem FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) : Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application _ callee condition yes no =>
      exact .apply callee.core_hasType
        (.ifE condition.core_hasType yes.core_hasType no.core_hasType)

/-- Every evidence term is on the exact source boundary. -/
theorem FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified
    {types owner inputs source core type}
    (elaboration : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application boundary _ _ _ _ =>
      simpa [isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication] using boundary

/-- Provenance retains all original groups, conditional children and Core. -/
theorem FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan
        innermostGroupSpan conditionalSpan question colon
        callee condition yes no
        functionCore conditionCore yesCore noCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
        ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
          ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group
            ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩]⟩⟩ ∧
      (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧
      core = .apply functionCore (.ifE conditionCore yesCore noCore) := by
  cases elaboration with
  | application boundary callee condition yes no =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, boundary,
        callee, condition, yes, no, rfl⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.FourLevelGroupedConditionalExpectedLambdaArgumentApplication
/-!
Checks an immediate conditional through exactly four transparent source groups
in an exact singleton application argument.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly four groups around an immediate conditional whose branch
boundary is already settled by ADR-0324. -/
def isFourLevelGroupedConditionalExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .conditional _ _ yes _ no⟩⟩⟩⟩⟩]⟩⟩ =>
      isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no
  | _ => false

/-- The source groups are retained while the unchanged ADR-0324 branch relations
check the two original immediate branches at the callee parameter type. -/
inductive FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan
        deepestGroupSpan conditionalSpan question colon :
        Syntax.SourceSpan}
      {callee condition yes no : Syntax.Expr}
      {functionCore conditionCore yesCore noCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (boundary : (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (conditionElaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context condition conditionCore .bool)
      (yesElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType yes yesCore)
      (noElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType no noCore) :
      FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
          ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
            ⟨deepestGroupSpan, .group
              ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩]⟩⟩
        (.apply functionCore (.ifE conditionCore yesCore noCore)) resultType

/-- Inspect the original grouped source and return the selected complete result. -/
def elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .conditional condition _ yes _ no⟩⟩⟩⟩⟩]⟩⟩ =>
    if isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no then do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let (conditionCore, conditionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context condition
          if conditionType = .bool then
            let yesCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs yes parameterType
            let noCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs no parameterType
            some (.apply functionCore (.ifE conditionCore yesCore noCore), resultType)
          else none
      | _ => none
    else none
  | _ => none

/-- Exact executable/declarative correspondence. -/
theorem elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases grouped with
              | mk outerGroupSpan groupedKind =>
                cases groupedKind <;> try { simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                case group middle =>
                  cases middle with
                  | mk middleGroupSpan middleKind =>
                    cases middleKind <;> try { simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                    case group inner =>
                      cases inner with
                      | mk innerGroupSpan innerKind =>
                        cases innerKind <;> try { simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                        case group deepest =>
                          cases deepest with
                          | mk deepestGroupSpan deepestKind =>
                            cases deepestKind <;> try { simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                            case group conditional =>
                              cases conditional with
                              | mk conditionalSpan conditionalKind =>
                                cases conditionalKind <;> try { simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                case conditional condition question yes colon no =>
                      simp only [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
                      split at accepted
                      · rename_i boundary
                        cases calleeChecked : elaborateRecursiveLocalComputation?
                            inputs.names inputs.context callee with
                        | none => simp [calleeChecked] at accepted
                        | some calleeResult =>
                          rcases calleeResult with ⟨functionCore, functionType⟩
                          simp only [calleeChecked, bind, Option.bind_some] at accepted
                          have calleeElaboration := elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                          cases functionType <;> try { simp at accepted }
                          case function parameterType resultType =>
                            cases conditionChecked : elaborateRecursiveLocalComputation?
                                inputs.names inputs.context condition with
                            | none => simp [conditionChecked] at accepted
                            | some conditionResult =>
                              rcases conditionResult with ⟨conditionCore, conditionType⟩
                              simp only [conditionChecked, Option.bind_some] at accepted
                              have conditionElaboration :=
                                elaborateRecursiveLocalComputation?_iff.mp conditionChecked
                              split at accepted
                              · rename_i same
                                subst conditionType
                                cases yesChecked : elaborateConditionalExpectedLambdaBranch?
                                    types owner inputs yes parameterType with
                                | none => simp [yesChecked] at accepted
                                | some yesCore =>
                                  cases noChecked : elaborateConditionalExpectedLambdaBranch?
                                      types owner inputs no parameterType with
                                  | none => simp [yesChecked, noChecked] at accepted
                                  | some noCore =>
                                    simp [yesChecked, noChecked] at accepted
                                    rcases accepted with ⟨rfl, rfl⟩
                                    exact .application boundary calleeElaboration conditionElaboration
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp yesChecked)
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp noChecked)
                              · simp_all
                      · simp at accepted
  · intro elaboration
    cases elaboration with
    | application boundary callee condition yes no =>
      simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, boundary,
        elaborateRecursiveLocalComputation?_iff.mpr callee,
        elaborateRecursiveLocalComputation?_iff.mpr condition,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr yes,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr no]

/-- Failure is exact absence of evidence. -/
theorem elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type, FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · rintro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- The exact inferred Core result type is preserved. -/
theorem FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) : Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application _ callee condition yes no =>
      exact .apply callee.core_hasType
        (.ifE condition.core_hasType yes.core_hasType no.core_hasType)

/-- Every evidence term is on the exact source boundary. -/
theorem FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified
    {types owner inputs source core type}
    (elaboration : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application boundary _ _ _ _ =>
      simpa [isFourLevelGroupedConditionalExpectedLambdaArgumentApplication] using boundary

/-- Provenance retains all original groups, conditional children and Core. -/
theorem FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan
        conditionalSpan question colon
        callee condition yes no
        functionCore conditionCore yesCore noCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
        ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
          ⟨deepestGroupSpan, .group
            ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩]⟩⟩ ∧
      (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧
      core = .apply functionCore (.ifE conditionCore yesCore noCore) := by
  cases elaboration with
  | application boundary callee condition yes no =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, boundary,
        callee, condition, yes, no, rfl⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.GroupedExpectedLambdaArgumentApplication
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
end

section
-- leanmerge: from Solcore.Frontend.OneLevelGroupedConditionalExpectedLambdaArgumentApplication
/-!
This standalone singleton-call adapter checks an immediate conditional through
exactly one transparent source group.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly one group around an immediate conditional whose branch
boundary is already settled by ADR-0324. -/
def isOneLevelGroupedConditionalExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .conditional _ _ yes _ no⟩⟩]⟩⟩ =>
      isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no
  | _ => false

/-- The source group is retained while the unchanged ADR-0324 branch relations
check the two original immediate branches at the callee parameter type. -/
inductive OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan groupSpan conditionalSpan question colon : Syntax.SourceSpan}
      {callee condition yes no : Syntax.Expr}
      {functionCore conditionCore yesCore noCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (boundary : (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (conditionElaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context condition conditionCore .bool)
      (yesElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType yes yesCore)
      (noElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType no noCore) :
      OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [⟨groupSpan, .group
          ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩]⟩⟩
        (.apply functionCore (.ifE conditionCore yesCore noCore)) resultType

/-- Inspect the original grouped source and return the selected complete result. -/
def elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [⟨_, .group
      ⟨_, .conditional condition _ yes _ no⟩⟩]⟩⟩ =>
    if isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no then do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let (conditionCore, conditionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context condition
          if conditionType = .bool then
            let yesCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs yes parameterType
            let noCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs no parameterType
            some (.apply functionCore (.ifE conditionCore yesCore noCore), resultType)
          else none
      | _ => none
    else none
  | _ => none

/-- Exact executable/declarative correspondence. -/
theorem elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases grouped with
              | mk groupSpan groupedKind =>
                cases groupedKind <;> try { simp [elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                case group inner =>
                  cases inner with
                  | mk conditionalSpan innerKind =>
                    cases innerKind <;> try { simp [elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                    case conditional condition question yes colon no =>
                      simp only [elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
                      split at accepted
                      · rename_i boundary
                        cases calleeChecked : elaborateRecursiveLocalComputation?
                            inputs.names inputs.context callee with
                        | none => simp [calleeChecked] at accepted
                        | some calleeResult =>
                          rcases calleeResult with ⟨functionCore, functionType⟩
                          simp only [calleeChecked, bind, Option.bind_some] at accepted
                          have calleeElaboration := elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                          cases functionType <;> try { simp at accepted }
                          case function parameterType resultType =>
                            cases conditionChecked : elaborateRecursiveLocalComputation?
                                inputs.names inputs.context condition with
                            | none => simp [conditionChecked] at accepted
                            | some conditionResult =>
                              rcases conditionResult with ⟨conditionCore, conditionType⟩
                              simp only [conditionChecked, Option.bind_some] at accepted
                              have conditionElaboration :=
                                elaborateRecursiveLocalComputation?_iff.mp conditionChecked
                              split at accepted
                              · rename_i same
                                subst conditionType
                                cases yesChecked : elaborateConditionalExpectedLambdaBranch?
                                    types owner inputs yes parameterType with
                                | none => simp [yesChecked] at accepted
                                | some yesCore =>
                                  cases noChecked : elaborateConditionalExpectedLambdaBranch?
                                      types owner inputs no parameterType with
                                  | none => simp [yesChecked, noChecked] at accepted
                                  | some noCore =>
                                    simp [yesChecked, noChecked] at accepted
                                    rcases accepted with ⟨rfl, rfl⟩
                                    exact .application boundary calleeElaboration conditionElaboration
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp yesChecked)
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp noChecked)
                              · simp_all
                      · simp at accepted
  · intro elaboration
    cases elaboration with
    | application boundary callee condition yes no =>
      simp [elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, boundary,
        elaborateRecursiveLocalComputation?_iff.mpr callee,
        elaborateRecursiveLocalComputation?_iff.mpr condition,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr yes,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr no]

/-- Failure is exact absence of evidence. -/
theorem elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type, OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · rintro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- The exact inferred Core result type is preserved. -/
theorem OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) : Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application _ callee condition yes no =>
      exact .apply callee.core_hasType
        (.ifE condition.core_hasType yes.core_hasType no.core_hasType)

/-- Every evidence term is on the exact source boundary. -/
theorem OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified
    {types owner inputs source core type}
    (elaboration : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application boundary _ _ _ _ =>
      simpa [isOneLevelGroupedConditionalExpectedLambdaArgumentApplication] using boundary

/-- Provenance retains the original group, conditional, children and Core. -/
theorem OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan groupSpan conditionalSpan question colon callee condition yes no
        functionCore conditionCore yesCore noCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [⟨groupSpan, .group
        ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩]⟩⟩ ∧
      (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧
      core = .apply functionCore (.ifE conditionCore yesCore noCore) := by
  cases elaboration with
  | application boundary callee condition yes no =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, boundary,
        callee, condition, yes, no, rfl⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.SevenLevelGroupedConditionalExpectedLambdaArgumentApplication
/-!
Checks an immediate conditional through exactly seven transparent source groups
in an exact singleton application argument.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly seven groups around an immediate conditional whose branch
boundary is already settled by ADR-0324. -/
def isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .group ⟨_, .group ⟨_, .group
        ⟨_, .conditional _ _ yes _ no⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩ =>
      isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no
  | _ => false

/-- The source groups are retained while the unchanged ADR-0324 branch relations
check the two original immediate branches at the callee parameter type. -/
inductive SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan
        deepestGroupSpan innermostGroupSpan terminalGroupSpan seventhGroupSpan
        conditionalSpan question colon :
        Syntax.SourceSpan}
      {callee condition yes no : Syntax.Expr}
      {functionCore conditionCore yesCore noCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (boundary : (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (conditionElaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context condition conditionCore .bool)
      (yesElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType yes yesCore)
      (noElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType no noCore) :
      SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
          ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
            ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group
              ⟨terminalGroupSpan, .group ⟨seventhGroupSpan, .group
                ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩
        (.apply functionCore (.ifE conditionCore yesCore noCore)) resultType

/-- Inspect the original grouped source and return the selected complete result. -/
def elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .group ⟨_, .group ⟨_, .group
        ⟨_, .conditional condition _ yes _ no⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩ =>
    if isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no then do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let (conditionCore, conditionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context condition
          if conditionType = .bool then
            let yesCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs yes parameterType
            let noCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs no parameterType
            some (.apply functionCore (.ifE conditionCore yesCore noCore), resultType)
          else none
      | _ => none
    else none
  | _ => none

/-- Exact executable/declarative correspondence. -/
theorem elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases grouped with
              | mk outerGroupSpan groupedKind =>
                cases groupedKind <;> try { simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                case group middle =>
                  cases middle with
                  | mk middleGroupSpan middleKind =>
                    cases middleKind <;> try { simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                    case group inner =>
                      cases inner with
                      | mk innerGroupSpan innerKind =>
                        cases innerKind <;> try { simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                        case group deepest =>
                          cases deepest with
                          | mk deepestGroupSpan deepestKind =>
                            cases deepestKind <;> try { simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                            case group innermost =>
                              cases innermost with
                              | mk innermostGroupSpan innermostKind =>
                                cases innermostKind <;> try { simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                case group terminal =>
                                  cases terminal with
                                  | mk terminalGroupSpan terminalKind =>
                                    cases terminalKind <;> try { simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                    case group seventh =>
                                      cases seventh with
                                      | mk seventhGroupSpan seventhKind =>
                                        cases seventhKind <;> try { simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                        case group conditional =>
                                          cases conditional with
                                          | mk conditionalSpan conditionalKind =>
                                            cases conditionalKind <;> try { simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                            case conditional condition question yes colon no =>
                      simp only [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
                      split at accepted
                      · rename_i boundary
                        cases calleeChecked : elaborateRecursiveLocalComputation?
                            inputs.names inputs.context callee with
                        | none => simp [calleeChecked] at accepted
                        | some calleeResult =>
                          rcases calleeResult with ⟨functionCore, functionType⟩
                          simp only [calleeChecked, bind, Option.bind_some] at accepted
                          have calleeElaboration := elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                          cases functionType <;> try { simp at accepted }
                          case function parameterType resultType =>
                            cases conditionChecked : elaborateRecursiveLocalComputation?
                                inputs.names inputs.context condition with
                            | none => simp [conditionChecked] at accepted
                            | some conditionResult =>
                              rcases conditionResult with ⟨conditionCore, conditionType⟩
                              simp only [conditionChecked, Option.bind_some] at accepted
                              have conditionElaboration :=
                                elaborateRecursiveLocalComputation?_iff.mp conditionChecked
                              split at accepted
                              · rename_i same
                                subst conditionType
                                cases yesChecked : elaborateConditionalExpectedLambdaBranch?
                                    types owner inputs yes parameterType with
                                | none => simp [yesChecked] at accepted
                                | some yesCore =>
                                  cases noChecked : elaborateConditionalExpectedLambdaBranch?
                                      types owner inputs no parameterType with
                                  | none => simp [yesChecked, noChecked] at accepted
                                  | some noCore =>
                                    simp [yesChecked, noChecked] at accepted
                                    rcases accepted with ⟨rfl, rfl⟩
                                    exact .application boundary calleeElaboration conditionElaboration
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp yesChecked)
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp noChecked)
                              · simp_all
                      · simp at accepted
  · intro elaboration
    cases elaboration with
    | application boundary callee condition yes no =>
      simp [elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, boundary,
        elaborateRecursiveLocalComputation?_iff.mpr callee,
        elaborateRecursiveLocalComputation?_iff.mpr condition,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr yes,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr no]

/-- Failure is exact absence of evidence. -/
theorem elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type, SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · rintro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- The exact inferred Core result type is preserved. -/
theorem SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) : Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application _ callee condition yes no =>
      exact .apply callee.core_hasType
        (.ifE condition.core_hasType yes.core_hasType no.core_hasType)

/-- Every evidence term is on the exact source boundary. -/
theorem SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified
    {types owner inputs source core type}
    (elaboration : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application boundary _ _ _ _ =>
      simpa [isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication] using boundary

/-- Provenance retains all original groups, conditional children and Core. -/
theorem SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan
        innermostGroupSpan terminalGroupSpan seventhGroupSpan conditionalSpan question colon
        callee condition yes no
        functionCore conditionCore yesCore noCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
        ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
          ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group
            ⟨terminalGroupSpan, .group ⟨seventhGroupSpan, .group
              ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩ ∧
      (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧
      core = .apply functionCore (.ifE conditionCore yesCore noCore) := by
  cases elaboration with
  | application boundary callee condition yes no =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, boundary,
        callee, condition, yes, no, rfl⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.SixLevelGroupedConditionalExpectedLambdaArgumentApplication
/-!
Checks an immediate conditional through exactly six transparent source groups
in an exact singleton application argument.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly six groups around an immediate conditional whose branch
boundary is already settled by ADR-0324. -/
def isSixLevelGroupedConditionalExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .group ⟨_, .group ⟨_, .conditional _ _ yes _ no⟩⟩⟩⟩⟩⟩⟩]⟩⟩ =>
      isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no
  | _ => false

/-- The source groups are retained while the unchanged ADR-0324 branch relations
check the two original immediate branches at the callee parameter type. -/
inductive SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan
        deepestGroupSpan innermostGroupSpan terminalGroupSpan conditionalSpan question colon :
        Syntax.SourceSpan}
      {callee condition yes no : Syntax.Expr}
      {functionCore conditionCore yesCore noCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (boundary : (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (conditionElaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context condition conditionCore .bool)
      (yesElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType yes yesCore)
      (noElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType no noCore) :
      SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
          ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
            ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group
              ⟨terminalGroupSpan, .group
                ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩⟩]⟩⟩
        (.apply functionCore (.ifE conditionCore yesCore noCore)) resultType

/-- Inspect the original grouped source and return the selected complete result. -/
def elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .group ⟨_, .group
        ⟨_, .conditional condition _ yes _ no⟩⟩⟩⟩⟩⟩⟩]⟩⟩ =>
    if isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no then do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let (conditionCore, conditionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context condition
          if conditionType = .bool then
            let yesCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs yes parameterType
            let noCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs no parameterType
            some (.apply functionCore (.ifE conditionCore yesCore noCore), resultType)
          else none
      | _ => none
    else none
  | _ => none

/-- Exact executable/declarative correspondence. -/
theorem elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases grouped with
              | mk outerGroupSpan groupedKind =>
                cases groupedKind <;> try { simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                case group middle =>
                  cases middle with
                  | mk middleGroupSpan middleKind =>
                    cases middleKind <;> try { simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                    case group inner =>
                      cases inner with
                      | mk innerGroupSpan innerKind =>
                        cases innerKind <;> try { simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                        case group deepest =>
                          cases deepest with
                          | mk deepestGroupSpan deepestKind =>
                            cases deepestKind <;> try { simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                            case group innermost =>
                              cases innermost with
                              | mk innermostGroupSpan innermostKind =>
                                cases innermostKind <;> try { simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                case group terminal =>
                                  cases terminal with
                                  | mk terminalGroupSpan terminalKind =>
                                    cases terminalKind <;> try { simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                    case group conditional =>
                                      cases conditional with
                                      | mk conditionalSpan conditionalKind =>
                                        cases conditionalKind <;> try { simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                                        case conditional condition question yes colon no =>
                      simp only [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
                      split at accepted
                      · rename_i boundary
                        cases calleeChecked : elaborateRecursiveLocalComputation?
                            inputs.names inputs.context callee with
                        | none => simp [calleeChecked] at accepted
                        | some calleeResult =>
                          rcases calleeResult with ⟨functionCore, functionType⟩
                          simp only [calleeChecked, bind, Option.bind_some] at accepted
                          have calleeElaboration := elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                          cases functionType <;> try { simp at accepted }
                          case function parameterType resultType =>
                            cases conditionChecked : elaborateRecursiveLocalComputation?
                                inputs.names inputs.context condition with
                            | none => simp [conditionChecked] at accepted
                            | some conditionResult =>
                              rcases conditionResult with ⟨conditionCore, conditionType⟩
                              simp only [conditionChecked, Option.bind_some] at accepted
                              have conditionElaboration :=
                                elaborateRecursiveLocalComputation?_iff.mp conditionChecked
                              split at accepted
                              · rename_i same
                                subst conditionType
                                cases yesChecked : elaborateConditionalExpectedLambdaBranch?
                                    types owner inputs yes parameterType with
                                | none => simp [yesChecked] at accepted
                                | some yesCore =>
                                  cases noChecked : elaborateConditionalExpectedLambdaBranch?
                                      types owner inputs no parameterType with
                                  | none => simp [yesChecked, noChecked] at accepted
                                  | some noCore =>
                                    simp [yesChecked, noChecked] at accepted
                                    rcases accepted with ⟨rfl, rfl⟩
                                    exact .application boundary calleeElaboration conditionElaboration
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp yesChecked)
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp noChecked)
                              · simp_all
                      · simp at accepted
  · intro elaboration
    cases elaboration with
    | application boundary callee condition yes no =>
      simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, boundary,
        elaborateRecursiveLocalComputation?_iff.mpr callee,
        elaborateRecursiveLocalComputation?_iff.mpr condition,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr yes,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr no]

/-- Failure is exact absence of evidence. -/
theorem elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type, SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · rintro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- The exact inferred Core result type is preserved. -/
theorem SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) : Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application _ callee condition yes no =>
      exact .apply callee.core_hasType
        (.ifE condition.core_hasType yes.core_hasType no.core_hasType)

/-- Every evidence term is on the exact source boundary. -/
theorem SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified
    {types owner inputs source core type}
    (elaboration : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application boundary _ _ _ _ =>
      simpa [isSixLevelGroupedConditionalExpectedLambdaArgumentApplication] using boundary

/-- Provenance retains all original groups, conditional children and Core. -/
theorem SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan
        innermostGroupSpan terminalGroupSpan conditionalSpan question colon
        callee condition yes no
        functionCore conditionCore yesCore noCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
        ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
          ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group
            ⟨terminalGroupSpan, .group
              ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩⟩]⟩⟩ ∧
      (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧
      core = .apply functionCore (.ifE conditionCore yesCore noCore) := by
  cases elaboration with
  | application boundary callee condition yes no =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, boundary,
        callee, condition, yes, no, rfl⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.ThreeLevelGroupedConditionalExpectedLambdaArgumentApplication
/-!
Checks an immediate conditional through exactly three transparent source groups
in an exact singleton application argument.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly three groups around an immediate conditional whose branch
boundary is already settled by ADR-0324. -/
def isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .conditional _ _ yes _ no⟩⟩⟩⟩]⟩⟩ =>
      isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no
  | _ => false

/-- The source groups are retained while the unchanged ADR-0324 branch relations
check the two original immediate branches at the callee parameter type. -/
inductive ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan
        conditionalSpan question colon :
        Syntax.SourceSpan}
      {callee condition yes no : Syntax.Expr}
      {functionCore conditionCore yesCore noCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (boundary : (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (conditionElaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context condition conditionCore .bool)
      (yesElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType yes yesCore)
      (noElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType no noCore) :
      ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
          ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
            ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩]⟩⟩
        (.apply functionCore (.ifE conditionCore yesCore noCore)) resultType

/-- Inspect the original grouped source and return the selected complete result. -/
def elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [⟨_, .group ⟨_, .group ⟨_, .group
      ⟨_, .conditional condition _ yes _ no⟩⟩⟩⟩]⟩⟩ =>
    if isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no then do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let (conditionCore, conditionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context condition
          if conditionType = .bool then
            let yesCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs yes parameterType
            let noCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs no parameterType
            some (.apply functionCore (.ifE conditionCore yesCore noCore), resultType)
          else none
      | _ => none
    else none
  | _ => none

/-- Exact executable/declarative correspondence. -/
theorem elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases grouped with
              | mk outerGroupSpan groupedKind =>
                cases groupedKind <;> try { simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                case group middle =>
                  cases middle with
                  | mk middleGroupSpan middleKind =>
                    cases middleKind <;> try { simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                    case group inner =>
                      cases inner with
                      | mk innerGroupSpan innerKind =>
                        cases innerKind <;> try { simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                        case group conditional =>
                          cases conditional with
                          | mk conditionalSpan conditionalKind =>
                            cases conditionalKind <;> try { simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                            case conditional condition question yes colon no =>
                      simp only [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
                      split at accepted
                      · rename_i boundary
                        cases calleeChecked : elaborateRecursiveLocalComputation?
                            inputs.names inputs.context callee with
                        | none => simp [calleeChecked] at accepted
                        | some calleeResult =>
                          rcases calleeResult with ⟨functionCore, functionType⟩
                          simp only [calleeChecked, bind, Option.bind_some] at accepted
                          have calleeElaboration := elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                          cases functionType <;> try { simp at accepted }
                          case function parameterType resultType =>
                            cases conditionChecked : elaborateRecursiveLocalComputation?
                                inputs.names inputs.context condition with
                            | none => simp [conditionChecked] at accepted
                            | some conditionResult =>
                              rcases conditionResult with ⟨conditionCore, conditionType⟩
                              simp only [conditionChecked, Option.bind_some] at accepted
                              have conditionElaboration :=
                                elaborateRecursiveLocalComputation?_iff.mp conditionChecked
                              split at accepted
                              · rename_i same
                                subst conditionType
                                cases yesChecked : elaborateConditionalExpectedLambdaBranch?
                                    types owner inputs yes parameterType with
                                | none => simp [yesChecked] at accepted
                                | some yesCore =>
                                  cases noChecked : elaborateConditionalExpectedLambdaBranch?
                                      types owner inputs no parameterType with
                                  | none => simp [yesChecked, noChecked] at accepted
                                  | some noCore =>
                                    simp [yesChecked, noChecked] at accepted
                                    rcases accepted with ⟨rfl, rfl⟩
                                    exact .application boundary calleeElaboration conditionElaboration
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp yesChecked)
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp noChecked)
                              · simp_all
                      · simp at accepted
  · intro elaboration
    cases elaboration with
    | application boundary callee condition yes no =>
      simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, boundary,
        elaborateRecursiveLocalComputation?_iff.mpr callee,
        elaborateRecursiveLocalComputation?_iff.mpr condition,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr yes,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr no]

/-- Failure is exact absence of evidence. -/
theorem elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type, ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · rintro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- The exact inferred Core result type is preserved. -/
theorem ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) : Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application _ callee condition yes no =>
      exact .apply callee.core_hasType
        (.ifE condition.core_hasType yes.core_hasType no.core_hasType)

/-- Every evidence term is on the exact source boundary. -/
theorem ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified
    {types owner inputs source core type}
    (elaboration : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application boundary _ _ _ _ =>
      simpa [isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication] using boundary

/-- Provenance retains all original groups, conditional children and Core. -/
theorem ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan conditionalSpan
        question colon
        callee condition yes no
        functionCore conditionCore yesCore noCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
        ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group
          ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩]⟩⟩ ∧
      (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧
      core = .apply functionCore (.ifE conditionCore yesCore noCore) := by
  cases elaboration with
  | application boundary callee condition yes no =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, boundary,
        callee, condition, yes, no, rfl⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.ThreeOrMoreGroupedExpectedLambdaArgumentApplication
/-!
This module recognizes a finite source-group spine around a direct computation
lambda.  The executable returns original subtrees and never constructs a
replacement source expression.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A maximal group spine ending at the original direct lambda.  The span list
is ordered from the outermost group to the innermost group. -/
inductive DirectLambdaGroupSpine :
    Syntax.Expr → List Syntax.SourceSpan → Syntax.Expr → Prop where
  | lambda {span keyword : Syntax.SourceSpan}
      {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
      {returnType : Option Syntax.TypeExpr} {body : Syntax.Block} :
      DirectLambdaGroupSpine
        ⟨span, .lambda keyword parameters returnType body⟩ []
        ⟨span, .lambda keyword parameters returnType body⟩
  | group {span : Syntax.SourceSpan} {inner terminal : Syntax.Expr}
      {spans : List Syntax.SourceSpan}
      (child : DirectLambdaGroupSpine inner spans terminal) :
      DirectLambdaGroupSpine ⟨span, .group inner⟩ (span :: spans) terminal
/-- Collect every original group span and return the original terminal lambda. -/
private def peelDirectLambdaGroupSpine?
    : (source : Syntax.Expr) → Option (List Syntax.SourceSpan × Syntax.Expr) :=
  WellFounded.fix (measure sizeOf).wf fun source recurse =>
    match source with
    | terminal@⟨_, .lambda _ _ _ _⟩ => some ([], terminal)
    | ⟨span, .group inner⟩ => do
        let (spans, terminal) ← recurse inner (by decreasing_tactic)
        some (span :: spans, terminal)
    | _ => none
@[simp] private theorem peelDirectLambdaGroupSpine?_lambda
    (span keyword : Syntax.SourceSpan)
    (parameters : Syntax.DelimitedList Syntax.LambdaParameter)
    (returnType : Option Syntax.TypeExpr) (body : Syntax.Block) :
    peelDirectLambdaGroupSpine?
      ⟨span, .lambda keyword parameters returnType body⟩ =
        some ([], ⟨span, .lambda keyword parameters returnType body⟩) := by
  rw [peelDirectLambdaGroupSpine?, WellFounded.fix_eq]
@[simp] private theorem peelDirectLambdaGroupSpine?_group
    (span : Syntax.SourceSpan) (inner : Syntax.Expr) :
    peelDirectLambdaGroupSpine? ⟨span, .group inner⟩ = (do
      let (spans, terminal) ← peelDirectLambdaGroupSpine? inner
      some (span :: spans, terminal)) := by
  rw [peelDirectLambdaGroupSpine?, WellFounded.fix_eq]
private theorem peelDirectLambdaGroupSpine?_sound
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan}
    (accepted : peelDirectLambdaGroupSpine? source = some (spans, terminal)) :
    DirectLambdaGroupSpine source spans terminal := by
  revert spans terminal
  apply (measure sizeOf).wf.induction source
  intro source ih spans terminal accepted
  cases source with
  | mk span kind =>
    cases kind <;>
      try { rw [peelDirectLambdaGroupSpine?, WellFounded.fix_eq] at accepted; cases accepted }
    case lambda keyword parameters returnType body =>
      simp only [peelDirectLambdaGroupSpine?_lambda, Option.some.injEq,
        Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact .lambda
    case group inner =>
      cases checked : peelDirectLambdaGroupSpine? inner with
      | none => simp [peelDirectLambdaGroupSpine?_group, checked] at accepted
      | some result =>
        rcases result with ⟨innerSpans, argument⟩
        simp [peelDirectLambdaGroupSpine?_group, checked] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact .group (ih inner (by simp_wf; omega) checked)
private theorem peelDirectLambdaGroupSpine?_complete
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan}
    (spine : DirectLambdaGroupSpine source spans terminal) :
    peelDirectLambdaGroupSpine? source = some (spans, terminal) := by
  induction spine with
  | lambda => simp only [peelDirectLambdaGroupSpine?_lambda]
  | group child ih => simp [peelDirectLambdaGroupSpine?_group, ih]
private theorem peelDirectLambdaGroupSpine?_iff
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan} :
    peelDirectLambdaGroupSpine? source = some (spans, terminal) ↔
      DirectLambdaGroupSpine source spans terminal :=
  ⟨peelDirectLambdaGroupSpine?_sound, peelDirectLambdaGroupSpine?_complete⟩
/-- Recognize a singleton call whose argument has at least three groups and ends
at a direct lambda.  Header and body validity are deliberately not inspected. -/
def isThreeOrMoreGroupedExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [grouped]⟩⟩ =>
      match peelDirectLambdaGroupSpine? grouped with
      | some (_ :: _ :: _ :: _, _) => true
      | _ => false
  | _ => false
/-- Selection is exactly a qualifying spine, independently of child validity. -/
theorem isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff
    {span argumentsSpan : Syntax.SourceSpan} {callee grouped : Syntax.Expr} :
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication
        ⟨span, .call callee ⟨argumentsSpan, [grouped]⟩⟩ = true ↔
      ∃ first second third rest terminal, DirectLambdaGroupSpine grouped
        (first :: second :: third :: rest) terminal := by
  constructor
  · intro selected
    cases checked : peelDirectLambdaGroupSpine? grouped with
    | none => simp [isThreeOrMoreGroupedExpectedLambdaArgumentApplication, checked] at selected
    | some result =>
      rcases result with ⟨spans, terminal⟩
      rcases spans with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
      <;> try { simp [isThreeOrMoreGroupedExpectedLambdaArgumentApplication, checked] at selected }
      exact ⟨first, second, third, rest, terminal, peelDirectLambdaGroupSpine?_iff.mp checked⟩
  · rintro ⟨first, second, third, rest, terminal, spine⟩
    simp [isThreeOrMoreGroupedExpectedLambdaArgumentApplication,
      peelDirectLambdaGroupSpine?_complete spine]
/-- Exact source evidence for three-or-more transparent groups around the expected
lambda.  All group spans remain in the spine evidence. -/
inductive ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan first second third : Syntax.SourceSpan}
      {rest : List Syntax.SourceSpan} {callee grouped argument : Syntax.Expr}
      {functionCore argumentCore : Core.Expr} {parameterType resultType : Core.Ty}
      (spine : DirectLambdaGroupSpine grouped (first :: second :: third :: rest) argument)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (argumentElaboration : ExpectedComputationLambdaElaborates
        RecursiveLocalComputationElaborates types owner inputs argument argumentCore parameterType) :
      ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [grouped]⟩⟩
        (.apply functionCore argumentCore) resultType
/-- Unwrap the finite spine, require at least three groups, infer the original
callee, and check the original terminal lambda at its parameter type. -/
def elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [grouped]⟩⟩ => do
      let (spans, argument) ← peelDirectLambdaGroupSpine? grouped
      match spans with
      | _ :: _ :: _ :: _ =>
          let (functionCore, functionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context callee
          match functionType with
          | .function parameterType resultType => do
              let argumentCore ← elaborateExpectedComputationLambda?
                elaborateRecursiveLocalComputation? types owner inputs argument parameterType
              some (.apply functionCore argumentCore, resultType)
          | _ => none
      | _ => none
  | _ => none

/-- The executable accepts exactly the independent finite-spine evidence. -/
theorem elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs source =
        some (core, type) ↔
      ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;>
        try { simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons secondArgument restArguments =>
                simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases spineChecked : peelDirectLambdaGroupSpine? grouped with
              | none =>
                  simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?, spineChecked]
                    at accepted
              | some result =>
                rcases result with ⟨spans, argument⟩
                cases spans with
                | nil =>
                    simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?, spineChecked]
                      at accepted
                | cons first tailSpans =>
                  cases tailSpans with
                  | nil =>
                      simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?, spineChecked]
                        at accepted
                  | cons second rest =>
                    cases rest with
                    | nil =>
                        simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?, spineChecked]
                          at accepted
                    | cons third tail =>
                      have spine := peelDirectLambdaGroupSpine?_iff.mp spineChecked
                      cases calleeChecked : elaborateRecursiveLocalComputation?
                          inputs.names inputs.context callee with
                      | none =>
                          simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
                            spineChecked, calleeChecked] at accepted
                      | some calleeResult =>
                        rcases calleeResult with ⟨functionCore, functionType⟩
                        have calleeElaboration :=
                          elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                        cases functionType <;>
                          try { simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
                            spineChecked, calleeChecked] at accepted }
                        case function parameterType resultType =>
                          cases argumentChecked : elaborateExpectedComputationLambda?
                              elaborateRecursiveLocalComputation? types owner inputs argument
                                parameterType with
                          | none =>
                              simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
                                spineChecked, calleeChecked, argumentChecked] at accepted
                          | some argumentCore =>
                            have argumentElaboration :=
                              (elaborateExpectedComputationLambda?_iff
                                (@elaborateRecursiveLocalComputation?_iff)).mp argumentChecked
                            simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
                              spineChecked, calleeChecked, argumentChecked] at accepted
                            rcases accepted with ⟨rfl, rfl⟩
                            exact .application spine calleeElaboration argumentElaboration
  · intro elaboration
    cases elaboration with
    | application spine calleeElaboration argumentElaboration =>
      simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
        peelDirectLambdaGroupSpine?_iff.mpr spine,
        elaborateRecursiveLocalComputation?_iff.mpr calleeElaboration,
        (elaborateExpectedComputationLambda?_iff
          (@elaborateRecursiveLocalComputation?_iff)).mpr argumentElaboration]

/-- Executable failure is exactly absence of finite-spine application evidence. -/
theorem elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs source = none ↔
      ¬ ∃ core type, ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted :
        elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- Every finite-spine elaboration has the inferred Core result type. -/
theorem ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application spine calleeElaboration argumentElaboration =>
      exact .apply calleeElaboration.core_hasType
        (argumentElaboration.core_hasType
          (@RecursiveLocalComputationElaborates.core_hasType))

/-- Successful evidence retains every source span and both child derivations. -/
theorem ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan first second third rest callee grouped argument
        functionCore argumentCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [grouped]⟩⟩ ∧
      DirectLambdaGroupSpine grouped (first :: second :: third :: rest) argument ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
        types owner inputs argument argumentCore parameterType ∧
      core = .apply functionCore argumentCore := by
  cases elaboration with
  | application spine calleeElaboration argumentElaboration =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, spine,
        calleeElaboration, argumentElaboration, rfl⟩

/-- Every successful finite-spine elaboration is selected by the classifier. -/
theorem ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates.classified
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application spine calleeElaboration argumentElaboration =>
      simp [isThreeOrMoreGroupedExpectedLambdaArgumentApplication,
        peelDirectLambdaGroupSpine?_complete spine]

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.TwoLevelGroupedConditionalExpectedLambdaArgumentApplication
/-!
Checks an immediate conditional through exactly two transparent source groups
in an exact singleton application argument.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly two groups around an immediate conditional whose branch
boundary is already settled by ADR-0324. -/
def isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .group
      ⟨_, .conditional _ _ yes _ no⟩⟩⟩]⟩⟩ =>
      isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no
  | _ => false

/-- The source group is retained while the unchanged ADR-0324 branch relations
check the two original immediate branches at the callee parameter type. -/
inductive TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan outerGroupSpan innerGroupSpan conditionalSpan question colon :
        Syntax.SourceSpan}
      {callee condition yes no : Syntax.Expr}
      {functionCore conditionCore yesCore noCore : Core.Expr}
      {parameterType resultType : Core.Ty}
      (boundary : (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (conditionElaboration : RecursiveLocalComputationElaborates
        inputs.names inputs.context condition conditionCore .bool)
      (yesElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType yes yesCore)
      (noElaboration : ConditionalExpectedLambdaBranchElaborates
        types owner inputs parameterType no noCore) :
      TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
          ⟨innerGroupSpan, .group
            ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩]⟩⟩
        (.apply functionCore (.ifE conditionCore yesCore noCore)) resultType

/-- Inspect the original grouped source and return the selected complete result. -/
def elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [⟨_, .group ⟨_, .group
      ⟨_, .conditional condition _ yes _ no⟩⟩⟩]⟩⟩ =>
    if isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no then do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let (conditionCore, conditionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context condition
          if conditionType = .bool then
            let yesCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs yes parameterType
            let noCore ← elaborateConditionalExpectedLambdaBranch?
              types owner inputs no parameterType
            some (.apply functionCore (.ifE conditionCore yesCore noCore), resultType)
          else none
      | _ => none
    else none
  | _ => none

/-- Exact executable/declarative correspondence. -/
theorem elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = some (core, type) ↔
      TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons second rest =>
                simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases grouped with
              | mk groupSpan groupedKind =>
                cases groupedKind <;> try { simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                case group inner =>
                  cases inner with
                  | mk innerGroupSpan innerKind =>
                    cases innerKind <;> try { simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                    case group conditional =>
                      cases conditional with
                      | mk conditionalSpan conditionalKind =>
                        cases conditionalKind <;> try { simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted }
                        case conditional condition question yes colon no =>
                      simp only [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?] at accepted
                      split at accepted
                      · rename_i boundary
                        cases calleeChecked : elaborateRecursiveLocalComputation?
                            inputs.names inputs.context callee with
                        | none => simp [calleeChecked] at accepted
                        | some calleeResult =>
                          rcases calleeResult with ⟨functionCore, functionType⟩
                          simp only [calleeChecked, bind, Option.bind_some] at accepted
                          have calleeElaboration := elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                          cases functionType <;> try { simp at accepted }
                          case function parameterType resultType =>
                            cases conditionChecked : elaborateRecursiveLocalComputation?
                                inputs.names inputs.context condition with
                            | none => simp [conditionChecked] at accepted
                            | some conditionResult =>
                              rcases conditionResult with ⟨conditionCore, conditionType⟩
                              simp only [conditionChecked, Option.bind_some] at accepted
                              have conditionElaboration :=
                                elaborateRecursiveLocalComputation?_iff.mp conditionChecked
                              split at accepted
                              · rename_i same
                                subst conditionType
                                cases yesChecked : elaborateConditionalExpectedLambdaBranch?
                                    types owner inputs yes parameterType with
                                | none => simp [yesChecked] at accepted
                                | some yesCore =>
                                  cases noChecked : elaborateConditionalExpectedLambdaBranch?
                                      types owner inputs no parameterType with
                                  | none => simp [yesChecked, noChecked] at accepted
                                  | some noCore =>
                                    simp [yesChecked, noChecked] at accepted
                                    rcases accepted with ⟨rfl, rfl⟩
                                    exact .application boundary calleeElaboration conditionElaboration
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp yesChecked)
                                      (elaborateConditionalExpectedLambdaBranch?_iff.mp noChecked)
                              · simp_all
                      · simp at accepted
  · intro elaboration
    cases elaboration with
    | application boundary callee condition yes no =>
      simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, boundary,
        elaborateRecursiveLocalComputation?_iff.mpr callee,
        elaborateRecursiveLocalComputation?_iff.mpr condition,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr yes,
        elaborateConditionalExpectedLambdaBranch?_iff.mpr no]

/-- Failure is exact absence of evidence. -/
theorem elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none ↔
      ¬ ∃ core type, TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · rintro rejected ⟨core, type, elaboration⟩
    have accepted :=
      elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source with
    | none => rfl
    | some result =>
      rcases result with ⟨core, type⟩
      exact False.elim (absent ⟨core, type,
        elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- The exact inferred Core result type is preserved. -/
theorem TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) : Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application _ callee condition yes no =>
      exact .apply callee.core_hasType
        (.ifE condition.core_hasType yes.core_hasType no.core_hasType)

/-- Every evidence term is on the exact source boundary. -/
theorem TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified
    {types owner inputs source core type}
    (elaboration : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application boundary _ _ _ _ =>
      simpa [isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication] using boundary

/-- Provenance retains the original group, conditional, children and Core. -/
theorem TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan outerGroupSpan innerGroupSpan conditionalSpan question colon
        callee condition yes no
        functionCore conditionCore yesCore noCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group
        ⟨innerGroupSpan, .group
          ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩]⟩⟩ ∧
      (isImmediateExpectedComputationLambda yes ||
        isImmediateExpectedComputationLambda no) = true ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧
      core = .apply functionCore (.ifE conditionCore yesCore noCore) := by
  cases elaboration with
  | application boundary callee condition yes no =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, boundary,
        callee, condition, yes, no, rfl⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.TwoLevelGroupedExpectedLambdaArgumentApplication
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
end
