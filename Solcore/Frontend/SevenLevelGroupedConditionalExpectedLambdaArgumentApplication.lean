import Solcore.Frontend.ConditionalExpectedLambdaArgumentApplication

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
