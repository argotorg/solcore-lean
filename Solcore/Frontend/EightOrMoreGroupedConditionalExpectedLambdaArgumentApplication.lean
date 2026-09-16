import Solcore.Frontend.ConditionalGroupSpine
import Solcore.Frontend.ConditionalExpectedLambdaArgumentApplication

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
