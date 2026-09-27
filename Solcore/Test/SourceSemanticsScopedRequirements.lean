import Solcore.SourceSemantics.SourceInferenceSoundness

/-!
Boundary examples for the whole-body scoped requirement ledger.

Qualified local-scheme assumptions are admitted only when a source-owned
initialized binder names the exact retained row and that row has a primary
use in the binder's initializer subtree.  Ordinary declaration assumptions
continue to use the declaration-wide evidence judgment.
-/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsScopedRequirements

open Frontend
open Frontend.SourceInference
open SourceSemantics
open TypeSystem

private def testModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"scoped_requirements", by decide⟩], by decide⟩⟩

private def testOwner : Resolved.DeclarationId := ⟨testModule, 0⟩

private def testSourceId : Syntax.SourceId := {
  origin := .main
  path := "scoped_requirements.sol"
}

private def testSpan : Syntax.SourceSpan := {
  source := testSourceId
  startByte := 0
  endByte := 0
}

private def emptySignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
}

private def templateVariable : TypeVarId := ⟨400⟩

private def templateId : RequirementId := ⟨0⟩

private def ordinaryId : RequirementId := ⟨401⟩

private def templatePredicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable templateVariable)

private def ordinaryPredicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate .word

private def templateRequirement : LocalSchemeRequirement := {
  templateRequirement := templateId
  predicate := templatePredicate
}

private def templateRow : SolvedRequirement := {
  id := templateId
  predicate := templatePredicate
  evidence := .assumption templatePredicate
}

private def ordinaryRow : SolvedRequirement := {
  id := ordinaryId
  predicate := ordinaryPredicate
  evidence := .assumption ordinaryPredicate
}

private def templateBinder (index : Nat) : TypedBinder := {
  id := ⟨testOwner, index⟩
  name := s!"template{index}"
  scheme := {
    quantified := [templateVariable]
    body := .variable templateVariable
  }
  schemeRequirements := [templateRequirement]
  span := some testSpan
}

private def expressionId (index : Nat) : ExpressionId :=
  ⟨⟨testOwner, index⟩⟩

private def statementId (index : Nat) : StatementId :=
  ⟨⟨testOwner, index⟩⟩

private def expressionNode (index : Nat)
    (requirements : List RequirementId) : ExpressionNode := {
  id := expressionId index
  span := testSpan
  type := .variable templateVariable
  form := .proxy (.variable templateVariable)
  requirements
}

private def letNode (index binderIndex initializerIndex : Nat) :
    StatementNode := {
  id := statementId index
  span := testSpan
  type := .unit
  form := .letDecl (templateBinder binderIndex)
    (some (expressionId initializerIndex))
}

private def scopedTemplateSource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [.statement (statementId 1)]
  nodes := [
    .expression (expressionNode 0 [templateId]),
    .statement (letNode 1 0 0)
  ]
}

private def scopedTemplateOwner : LocalSchemeTemplateOwner := {
  binder := templateBinder 0
  initializer := .expression (expressionId 0)
  requirement := templateRequirement
}

private def orphanSource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [.expression (expressionId 0)]
  nodes := [.expression (expressionNode 0 [templateId])]
}

private def duplicateOwnerSource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [.statement (statementId 1), .statement (statementId 3)]
  nodes := [
    .expression (expressionNode 0 [templateId]),
    .statement (letNode 1 0 0),
    .expression (expressionNode 2 []),
    .statement (letNode 3 1 2)
  ]
}

private def wrongScopeSource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [
    .statement (statementId 1),
    .expression (expressionId 2)
  ]
  nodes := [
    .expression (expressionNode 0 []),
    .statement (letNode 1 0 0),
    .expression (expressionNode 2 [templateId])
  ]
}

private def ordinarySource : TypedSource := {
  owner := testOwner
  inputs := []
  roots := [.expression (expressionId 0)]
  nodes := [.expression (expressionNode 0 [ordinaryId])]
}

private def templateContext : SourceSemantics.Context :=
  (Context.ofSignatures emptySignatures).withSolvedRequirements [templateRow]

private def orphanContext : SourceSemantics.Context := templateContext

private def ordinaryContextWithoutAssumption : SourceSemantics.Context :=
  (Context.ofSignatures emptySignatures).withSolvedRequirements [ordinaryRow]

private def ordinaryContextWithAssumption : SourceSemantics.Context :=
  ((Context.ofSignatures emptySignatures).withAssumptions [ordinaryPredicate])
    |>.withSolvedRequirements [ordinaryRow]

private def templateInferenceContext : SourceInference.Context := {
  environment := { modules := [], declarations := [] }
  signatures := emptySignatures
  scope := {
    currentModule := testModule
    genericOwner := testOwner
    genericParameters := []
  }
}

private def templateInputRequirement : Requirement := {
  id := templateId
  predicate := templatePredicate
}

private def templateSolverState : SourceInference.State := {
  SourceInference.State.initial testOwner with
  nextRequirement := 1
  requirements := [templateInputRequirement]
  localSchemeAssumptions := [templateId]
}

private def templateTrackingBaseState : SourceInference.State := {
  SourceInference.State.initial testOwner with
  nextRequirement := 1
  requirements := [templateInputRequirement]
}

private def templateTrackingAllocatedState : SourceInference.State :=
  (templateTrackingBaseState.allocateBinder "template0"
    (templateBinder 0).scheme (some testSpan) false
    [templateRequirement]).2

private def templateTrackingForNode : StatementNode := {
  id := statementId 2
  span := testSpan
  type := .unit
  form := .forLoop
    [.letDecl (templateBinder 0) (some (expressionId 0))]
    (expressionId 1) [] []
}

private theorem templateTrackingBase :
    SourceInferenceSoundness.TemplateTracking templateTrackingBaseState [] := by
  constructor <;>
    simp [templateTrackingBaseState, SourceInference.State.initial,
      SourceInference.State.toTypedSource, sourceLocalSchemeTemplateIds,
      localSchemeTemplateOwners, initializedLetBindings]

private def templateGeneralizationState : SourceInference.State := {
  templateTrackingBaseState with
  directCallRequirements := [templateId]
}

private theorem templateGeneralizationTracking :
    SourceInferenceSoundness.TemplateTracking templateGeneralizationState [] := by
  constructor <;>
    simp [templateGeneralizationState, templateTrackingBaseState,
      SourceInference.State.initial, SourceInference.State.toTypedSource,
      sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings]

/-- The real generalizer supplies allocation's uniqueness, freshness, and
ledger-coverage premises in one step, including a nonempty template set. -/
example :
    let generalized := SourceInference.Detail.generalizeValue
      templateGeneralizationState [] 0 (.variable templateVariable)
    SourceInferenceSoundness.TemplateTracking
      (({ templateGeneralizationState with locals := [] }).allocateBinder
        "template0" generalized.scheme (some testSpan) false
        generalized.requirements).2
      (generalized.requirements.map fun requirement =>
        requirement.templateRequirement) := by
  exact templateGeneralizationTracking.allocateGeneralizedValue (by rfl)
    [] 0 (.variable templateVariable) "template0" (some testSpan)

/-- The locals-only update used by both ordinary lets and for-loop items does
not disturb pending template ownership. -/
example : SourceInferenceSoundness.TemplateTracking
    { templateTrackingBaseState with
      locals := [("replacement", .mono .word)] } [] := by
  exact templateTrackingBase.replaceLocals [("replacement", .mono .word)]

private theorem templateTrackingAllocated :
    SourceInferenceSoundness.TemplateTracking templateTrackingAllocatedState
      [templateId] := by
  apply SourceInferenceSoundness.TemplateTracking.allocateBinder
      templateTrackingBase "template0" (templateBinder 0).scheme
      (some testSpan) false [templateRequirement]
  · simp [templateRequirement]
  · intro id member
    have id_eq : id = templateId := by
      simpa [templateRequirement] using member
    subst id
    change templateId ∉ []
    simp
  · simp [templateRequirement, templateTrackingBaseState,
      templateInputRequirement]

/-- A regular initialized let discharges the binder's pending template ID
when its owner node is recorded. -/
example : SourceInferenceSoundness.TemplateTracking
    (templateTrackingAllocatedState.recordNode
      (.statement (letNode 1 0 0))) [] := by
  apply SourceInferenceSoundness.TemplateTracking.recordNode
  simpa [SourceInferenceSoundness.nodeLocalSchemeTemplateIds,
    statementInitializedLetBindings, InitializedLetBinding.templateOwners,
    letNode, templateBinder, templateRequirement] using
    templateTrackingAllocated

/-- A for-loop node discharges the initialized header item's pending template
ID by the same node-local collector used for ordinary lets. -/
example : SourceInferenceSoundness.TemplateTracking
    (templateTrackingAllocatedState.recordNode
      (.statement templateTrackingForNode)) [] := by
  apply SourceInferenceSoundness.TemplateTracking.recordNode
  simpa [SourceInferenceSoundness.nodeLocalSchemeTemplateIds,
    templateTrackingForNode, statementInitializedLetBindings,
    forItemInitializedLetBindings, InitializedLetBinding.templateOwners,
    templateBinder, templateRequirement] using templateTrackingAllocated

private def templateFinalizeState : SourceInference.State := {
  templateSolverState with
  nodes := scopedTemplateSource.nodes
}

private def templateFinalizedResult : SourceInference.Result := {
  type := .variable templateVariable
  substitution := templateFinalizeState.inference.substitution
  solvedRequirements := [templateRow]
  typedSource := scopedTemplateSource.applySubstitution
    templateFinalizeState.inference.substitution
}

private theorem templateFinalizeStateAligned :
    SourceInferenceSoundness.TemplateIdsAligned templateFinalizeState
      scopedTemplateSource.roots := by
  intro id
  change id ∈ sourceLocalSchemeTemplateIds scopedTemplateSource ↔
    id ∈ [templateId]
  simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings, statementInitializedLetBindings,
    InitializedLetBinding.templateOwners, scopedTemplateSource, letNode,
    templateBinder, templateRequirement]

private theorem templateFinalizeSuccess :
    SourceInference.Detail.finalize templateInferenceContext
      (.variable templateVariable) templateFinalizeState
      scopedTemplateSource.roots = .ok templateFinalizedResult := by
  rfl

/-- Finalization preserves the exact source/state template-ID alignment of a
nonempty qualified-local fixture. -/
example : ∀ id,
    id ∈ sourceLocalSchemeTemplateIds templateFinalizedResult.typedSource ↔
      id ∈ templateFinalizeState.localSchemeAssumptions := by
  exact SourceInferenceSoundness.finalize_templateIdsAligned
    templateFinalizeStateAligned templateFinalizeSuccess

/-- A source-classified template emitted by finalization retains canonical
assumption evidence for its normalized predicate. -/
example : ∀ row, row ∈ templateFinalizedResult.solvedRequirements →
    row.id ∈ sourceLocalSchemeTemplateIds templateFinalizedResult.typedSource →
    row.evidence = .assumption row.predicate := by
  exact SourceInferenceSoundness.finalize_template_evidence
    templateFinalizeStateAligned templateFinalizeSuccess

private theorem templateOwnerContained :
    ContainsLocalSchemeTemplate scopedTemplateSource scopedTemplateOwner := by
  simp [ContainsLocalSchemeTemplate, localSchemeTemplateOwners,
    initializedLetBindings, statementInitializedLetBindings,
    InitializedLetBinding.templateOwners,
    scopedTemplateSource, scopedTemplateOwner, letNode, templateBinder,
    templateRequirement]

private theorem templateOccursAtInitializer :
    PrimaryRequirementOccursAt scopedTemplateSource
      (.expression (expressionId 0)) templateId := by
  simp [PrimaryRequirementOccursAt, primaryRequirementOccurrences,
    nodePrimaryRequirementOccurrences,
    expressionPrimaryRequirementOccurrences,
    statementPrimaryRequirementOccurrences, scopedTemplateSource,
    expressionNode, letNode]

/-- Executable template solving is accepted through scoped source ownership,
not through declaration-wide retained-evidence validity. -/
theorem templateSolverProducesScopedEntry :
    ScopedRequirementEntryValid templateContext scopedTemplateSource
      templateRow := by
  apply
    SourceInferenceSoundness.solveRequirements_scoped_entries_sound
      (inferenceContext := templateInferenceContext)
      (state := templateSolverState)
      (requirements := [templateInputRequirement])
      (solved := [templateRow])
  · rfl
  · rfl
  · intro requirement member
    have requirement_eq : requirement = templateInputRequirement := by
      simpa using member
    subst requirement
    constructor
    · intro _
      exact sourceLocalSchemeTemplateIds_mem_iff.mpr
        ⟨scopedTemplateOwner, templateOwnerContained, rfl⟩
    · intro _
      simp [templateInputRequirement, templateSolverState]
  · intro requirement member template
    have requirement_eq : requirement = templateInputRequirement := by
      simpa using member
    subst requirement
    simpa [templateInputRequirement, templateSolverState,
      SourceInference.Detail.applyPredicate, SourceInference.State.initial,
      TypedTraitResolution.applySubstitution] using
      (LocalSchemeTemplateRowScoped.intro scopedTemplateOwner
        templateOwnerContained rfl rfl rfl (.expression (expressionId 0))
        templateOccursAtInitializer
        (scopedTemplateOwner.scopes_initializer templateOwnerContained))
  · rfl
  · simp

/-- A nonempty canonical inference ledger containing a qualified-local
template becomes a complete scoped semantic ledger after solving. -/
theorem templateSolverProducesScopedLedger :
    ScopedRequirementLedgerWellFormed templateContext
      scopedTemplateSource := by
  apply
    SourceInferenceSoundness.solveRequirements_scoped_ledger_sound
      (inferenceContext := templateInferenceContext)
      (state := templateSolverState)
      (solved := [templateRow])
      (baseContext := Context.ofSignatures emptySignatures)
  · rfl
  · rfl
  · rfl
  · constructor
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners, scopedTemplateSource, letNode,
      templateBinder, templateRequirement]
  · intro requirement member
    have requirement_eq : requirement = templateInputRequirement := by
      simpa [templateSolverState] using member
    subst requirement
    constructor
    · intro _
      exact sourceLocalSchemeTemplateIds_mem_iff.mpr
        ⟨scopedTemplateOwner, templateOwnerContained, rfl⟩
    · intro _
      simp [templateInputRequirement, templateSolverState]
  · intro id member
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners, scopedTemplateSource, letNode,
      templateBinder, templateRequirement, templateSolverState] at member ⊢
    exact member
  · intro requirement member template
    have requirement_eq : requirement = templateInputRequirement := by
      simpa [templateSolverState] using member
    subst requirement
    simpa [templateInputRequirement, templateSolverState,
      SourceInference.Detail.applyPredicate, SourceInference.State.initial,
      TypedTraitResolution.applySubstitution] using
      (LocalSchemeTemplateRowScoped.intro scopedTemplateOwner
        templateOwnerContained rfl rfl rfl (.expression (expressionId 0))
        templateOccursAtInitializer
        (scopedTemplateOwner.scopes_initializer templateOwnerContained))
  · rfl

/-- A template assumption attached at the root of its exact initializer is a
valid scoped ledger entry even though it is not a declaration assumption. -/
theorem initializerRootTemplateAccepted :
    ScopedRequirementLedgerWellFormed templateContext
      scopedTemplateSource := by
  refine {
    idsUnique := ?_
    templateOwnership := ?_
    entriesValid := ?_
    templatesComplete := ?_
  }
  · simp [RequirementIdsUnique, templateContext, templateRow,
      Context.withSolvedRequirements, Context.ofSignatures]
  · constructor
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners,
      scopedTemplateSource, letNode, templateBinder, templateRequirement]
  · intro row member
    have rowEq : row = templateRow := by
      simpa [templateContext, Context.withSolvedRequirements,
        Context.ofSignatures] using member
    subst row
    apply ScopedRequirementEntryValid.template
    exact .intro scopedTemplateOwner templateOwnerContained rfl rfl rfl
      (.expression (expressionId 0)) templateOccursAtInitializer
      (scopedTemplateOwner.scopes_initializer templateOwnerContained)
  · intro owner contains
    have ownerEq : owner = scopedTemplateOwner := by
      simpa [ContainsLocalSchemeTemplate, localSchemeTemplateOwners,
        initializedLetBindings, statementInitializedLetBindings,
        InitializedLetBinding.templateOwners,
        scopedTemplateSource, scopedTemplateOwner, letNode, templateBinder,
        templateRequirement] using contains
    subst owner
    exact ⟨templateRow, by
      simp [templateContext, Context.withSolvedRequirements,
        Context.ofSignatures], rfl⟩

private theorem assumptionRowInvalid
    (context : SourceSemantics.Context) (row : SolvedRequirement)
    (evidenceEq : row.evidence = .assumption row.predicate)
    (absent : row.predicate ∉ context.assumptions) :
    ¬ SolvedRequirementValid context row := by
  intro valid
  cases valid with
  | intro retainedValid =>
      cases retainedValid with
      | intro represents semanticValid =>
          rw [evidenceEq] at represents
          cases represents with
          | assumption =>
              cases semanticValid with
              | assumption member => exact absent member

/-- An assumption row without a source local-scheme owner cannot acquire
initializer scope merely by being attached to an expression. -/
theorem orphanTemplateAssumptionRejected :
    ¬ ScopedRequirementLedgerWellFormed orphanContext orphanSource := by
  intro wellFormed
  have member : templateRow ∈ orphanContext.solvedRequirements := by
    simp [orphanContext, templateContext, Context.withSolvedRequirements,
      Context.ofSignatures]
  have notTemplate : templateRow.id ∉
      sourceLocalSchemeTemplateIds orphanSource := by
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, orphanSource]
  have valid := wellFormed.ordinary_valid member notTemplate
  exact assumptionRowInvalid orphanContext templateRow rfl (by
    simp [orphanContext, templateContext, Context.withSolvedRequirements,
      Context.ofSignatures]) valid

/-- Two initialized local schemes cannot claim the same template identity,
even when the flat solved ledger itself contains only one row. -/
theorem duplicateTemplateOwnersRejected :
    ¬ ScopedRequirementLedgerWellFormed templateContext
      duplicateOwnerSource := by
  intro wellFormed
  have unique := wellFormed.templateOwnership.ids_unique
  simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings, statementInitializedLetBindings,
    InitializedLetBinding.templateOwners,
    duplicateOwnerSource, letNode, templateBinder, templateRequirement]
    at unique

private theorem initializerHasNoChildren
    (child : NodeId) :
    ¬ DirectChild wrongScopeSource (.expression (expressionId 0)) child := by
  rintro ⟨node, contains, childMem⟩
  rcases contains with ⟨nodeMem, nodeId⟩
  simp [wrongScopeSource, expressionNode, letNode] at nodeMem
  rcases nodeMem with rfl | rfl | rfl
  · simp [nodeChildIds, expressionChildIds] at childMem
  · simp [Node.id, statementId, expressionId] at nodeId
  · simp [Node.id, expressionId] at nodeId

private theorem outsideNotInInitializer :
    ¬ InReflexiveSubtree wrongScopeSource
      (.expression (expressionId 0)) (.expression (expressionId 2)) := by
  rintro (same | descends)
  · simp [expressionId] at same
  · cases descends with
    | direct edge => exact initializerHasNoChildren _ edge
    | step edge _ => exact initializerHasNoChildren _ edge

/-- A source-owned template row is rejected when its sole primary attachment
is outside the owning initializer subtree. -/
theorem templateUseOutsideInitializerRejected :
    ¬ ScopedRequirementLedgerWellFormed templateContext wrongScopeSource := by
  intro wellFormed
  have member : templateRow ∈ templateContext.solvedRequirements := by
    simp [templateContext, Context.withSolvedRequirements,
      Context.ofSignatures]
  have templateMem : templateRow.id ∈
      sourceLocalSchemeTemplateIds wrongScopeSource := by
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners,
      wrongScopeSource, letNode, templateBinder, templateRequirement,
      templateRow]
  have rowScoped := wellFormed.template_scoped member templateMem
  rcases rowScoped.exact_owner with
    ⟨owner, occurrence, contains, _, _, _, occurs, inScope⟩
  have ownerEq : owner = {
      binder := templateBinder 0
      initializer := .expression (expressionId 0)
      requirement := templateRequirement
    } := by
    simpa [ContainsLocalSchemeTemplate, localSchemeTemplateOwners,
      initializedLetBindings, statementInitializedLetBindings,
      InitializedLetBinding.templateOwners,
      wrongScopeSource, letNode, templateBinder, templateRequirement] using
      contains
  subst owner
  have occurrenceEq : occurrence = .expression (expressionId 2) := by
    simpa [PrimaryRequirementOccursAt, primaryRequirementOccurrences,
      nodePrimaryRequirementOccurrences,
      expressionPrimaryRequirementOccurrences,
      statementPrimaryRequirementOccurrences, statementPrimaryRequirementIds,
      wrongScopeSource,
      expressionNode, letNode, templateRow] using occurs
  subst occurrence
  exact outsideNotInInitializer inScope.2

/-- A non-template assumption row remains invalid when its predicate is absent
from the declaration assumption context. -/
theorem ordinaryAssumptionWithoutDeclarationRejected :
    ¬ ScopedRequirementLedgerWellFormed ordinaryContextWithoutAssumption
      ordinarySource := by
  intro wellFormed
  have member : ordinaryRow ∈
      ordinaryContextWithoutAssumption.solvedRequirements := by
    simp [ordinaryContextWithoutAssumption, Context.withSolvedRequirements,
      Context.ofSignatures]
  have notTemplate : ordinaryRow.id ∉
      sourceLocalSchemeTemplateIds ordinarySource := by
    simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, ordinarySource]
  have valid := wellFormed.ordinary_valid member notTemplate
  exact assumptionRowInvalid ordinaryContextWithoutAssumption ordinaryRow rfl
    (by simp [ordinaryContextWithoutAssumption,
      Context.withSolvedRequirements, Context.ofSignatures]) valid

/-- Declaration-wide assumption evidence is still accepted through the
ordinary branch when its predicate is explicitly present. -/
theorem ordinaryDeclarationAssumptionAccepted :
    ScopedRequirementLedgerWellFormed ordinaryContextWithAssumption
      ordinarySource := by
  apply ScopedRequirementLedgerWellFormed.ofRequirementLedger
  · constructor
    · simp [RequirementIdsUnique, ordinaryContextWithAssumption,
        Context.withSolvedRequirements, Context.withAssumptions,
        Context.ofSignatures]
    · intro row member
      have rowEq : row = ordinaryRow := by
        simpa [ordinaryContextWithAssumption, Context.withSolvedRequirements,
          Context.withAssumptions, Context.ofSignatures] using member
      subst row
      unfold ordinaryRow
      apply SolvedRequirementValid.intro
      apply RetainedEvidenceValid.intro (.assumption ordinaryPredicate)
      exact .assumption (by
        simp [ordinaryContextWithAssumption, Context.withSolvedRequirements,
          Context.withAssumptions, Context.ofSignatures])
  · simp [sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings, ordinarySource]

end Solcore.Test.SourceSemanticsScopedRequirements
