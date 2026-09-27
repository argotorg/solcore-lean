import Solcore.SourceSemantics.SourceInferenceSoundness

/-! Focused parsed-source regressions for the source inference slice. -/

set_option autoImplicit false

namespace Tests.SourceInference

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def check (content : String) :
    IO (List SourceInference.CheckedFunction) := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"source inference failed: {reprStr errors}")

private def load (content : String) : IO LoadedProgram := do
  match loadProgram (workspace content) with
  | .ok loaded => pure loaded
  | .error errors =>
      throw (IO.userError s!"source inference loading failed: {reprStr errors}")

private def checkedNamed (environment : ProgramEnvironment)
    (checked : List SourceInference.CheckedFunction) (name : String) :
    IO SourceInference.CheckedFunction :=
  match checked.find? fun function =>
      (environment.declaration? function.declaration).any fun declaration =>
        declaration.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def traitNameOf (environment : ProgramEnvironment)
    (predicate : ProgramPredicate) : Option String := do
  let trait ← predicate.trait.declaration?
  let declaration ← environment.declaration? trait
  declaration.name

private def hasBuiltinIntWordEvidence
    (solved : SourceInference.SolvedRequirement) : Bool :=
  solved.predicate == ProgramSignatures.builtinIntPredicate .word &&
    match solved.evidence with
    | .implementation (.byImpl goal (.builtin .intWord) premises) =>
        goal == solved.predicate && premises.isEmpty
    | _ => false

private def solverRegressionModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_inference_solver", by decide⟩], by decide⟩⟩

private def solverRegressionOwner : Resolved.DeclarationId :=
  ⟨solverRegressionModule, 0⟩

private def solverRegressionFirst : TypeSystem.TypeVarId := ⟨0⟩
private def solverRegressionSecond : TypeSystem.TypeVarId := ⟨1⟩

private def solverRegressionSource : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable solverRegressionFirst)

private def solverRegressionNormalized : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable solverRegressionSecond)

private def solverRegressionContext : SourceInference.Context := {
  environment := { modules := [], declarations := [] }
  signatures := {
    functions := []
    implRules := []
    traits := []
    implementations := []
  }
  scope := {
    currentModule := solverRegressionModule
    genericOwner := solverRegressionOwner
    genericParameters := []
  }
  assumptions := [solverRegressionSource]
}

private def solverRegressionSpan : Syntax.SourceSpan :=
  ⟨⟨.main, "source_inference_solver.sol"⟩, 0, 0⟩

private def solverRegressionRecoveryType : Syntax.TypeExpr := {
  span := solverRegressionSpan
  value := .error
}

/-- Formation validation rejects the recovery sentinel independently of how
the resolved type was produced. -/
example : validateResolvedTypeFormation solverRegressionContext.signatures
    solverRegressionOwner [] .error =
    .error (.recoveryType solverRegressionOwner) := by
  rfl

/-- Formation validation also rejects constructor application syntax whose
head is not a cataloged nominal declaration. -/
example : validateResolvedTypeFormation solverRegressionContext.signatures
    solverRegressionOwner [] (.application .word .bool) =
    .error (.invalidApplication solverRegressionOwner
      (.application .word .bool)) := by
  rfl

private def solverRegressionState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  inference := {
    next := 2
    substitution := [
      (solverRegressionFirst, .variable solverRegressionSecond),
      (solverRegressionSecond, .bool)
    ]
  }
}

private def solverRegressionRequirement : SourceInference.Requirement := {
  id := ⟨0⟩
  predicate := solverRegressionSource
}

private def solverRegressionExpressionId : SourceInference.ExpressionId :=
  ⟨⟨solverRegressionOwner, 0⟩⟩

private def solverRegressionRequirementNode :
    SourceInference.ExpressionNode := {
  id := solverRegressionExpressionId
  span := solverRegressionSpan
  type := .word
  form := .literal (.decimal "0")
  requirements := [solverRegressionRequirement.id]
}

private def solverRegressionRoots : List SourceInference.NodeId :=
  [.expression solverRegressionExpressionId]

private def solverRegressionSemanticContext :
    Solcore.SourceSemantics.Context :=
  (Solcore.SourceSemantics.Context.ofSignatures
    solverRegressionContext.signatures).withAssumptions
      [solverRegressionNormalized]

private def solverRegressionTemplateState : SourceInference.State := {
  solverRegressionState with
  localSchemeAssumptions := [solverRegressionRequirement.id]
}

private def solverRegressionFinalizeState : SourceInference.State := {
  solverRegressionState with
  nextOccurrence := 1
  nodes := [.expression solverRegressionRequirementNode]
  requirements := [solverRegressionRequirement]
}

private def generalizationSideConditionState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  nextRequirement := 1
  requirements := [solverRegressionRequirement]
  directCallRequirements := [solverRegressionRequirement.id]
}

private theorem generalizationSideConditionState_requirementsWellFormed :
    generalizationSideConditionState.RequirementsWellFormed := by
  rfl

/-- Canonical ledger formation synchronizes its length and bounds every
retained stable identity by the next fresh identity. -/
example :
    generalizationSideConditionState.requirements.length =
        generalizationSideConditionState.nextRequirement ∧
      solverRegressionRequirement.id.index <
        generalizationSideConditionState.nextRequirement := by
  have member : solverRegressionRequirement ∈
      generalizationSideConditionState.requirements := by
    simp [generalizationSideConditionState]
  exact ⟨
    SourceInference.State.requirements_length_eq_nextRequirement
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed,
    SourceInference.State.requirement_id_lt_nextRequirement
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed member⟩

/-- Canonical identity order makes take/drop cutoffs coincide exactly with
the numerical boundary on stable requirement identities. -/
example :
    solverRegressionRequirement ∈
        generalizationSideConditionState.requirements.take 1 ∧
      solverRegressionRequirement ∉
        generalizationSideConditionState.requirements.take 0 ∧
      solverRegressionRequirement ∈
        generalizationSideConditionState.requirements.drop 0 ∧
      solverRegressionRequirement ∉
        generalizationSideConditionState.requirements.drop 1 := by
  constructor
  · rw [SourceInference.State.mem_take_requirements_iff
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed]
    simp [generalizationSideConditionState, solverRegressionRequirement]
  constructor
  · rw [SourceInference.State.mem_take_requirements_iff
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed]
    simp [solverRegressionRequirement]
  constructor
  · rw [SourceInference.State.mem_drop_requirements_iff
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed]
    simp [generalizationSideConditionState, solverRegressionRequirement]
  · rw [SourceInference.State.mem_drop_requirements_iff
      generalizationSideConditionState
      generalizationSideConditionState_requirementsWellFormed]
    simp [solverRegressionRequirement]

private def stableGeneralizationVariable : TypeSystem.TypeVarId := ⟨0⟩

private def stableGeneralizationState : SourceInference.State :=
  SourceInference.State.initial solverRegressionOwner [
    ("captured", .mono (.variable stableGeneralizationVariable))
  ]

/-- The executable blocker characterization exposes the exact lexical scheme
that prevents a captured variable from being generalized. -/
example : stableGeneralizationVariable ∈
    SourceInference.Detail.generalizeValueBlockedVariables
      stableGeneralizationState
      [("captured", .mono (.variable stableGeneralizationVariable))] 0 := by
  rw [SourceInference.Detail.mem_generalizeValueBlockedVariables_iff]
  left
  refine ⟨("captured", .mono (.variable stableGeneralizationVariable)),
    by simp, ?_⟩
  simp [TypeSystem.Scheme.mono, TypeSystem.Scheme.freeVariables,
    TypeSystem.Ty.freeVariables]

/-- A requirement predating the initializer contributes an exact blocker
witness even when its identity is otherwise classified as a direct call. -/
example :
    solverRegressionRequirement ∈
        SourceInference.Detail.generalizeValueBlockingRequirements
          generalizationSideConditionState 1 ∧
      solverRegressionRequirement ∉
        SourceInference.Detail.generalizeValueBlockingRequirements
          generalizationSideConditionState 0 := by
  constructor
  · rw [SourceInference.Detail.mem_generalizeValueBlockingRequirements_iff]
    exact Or.inl (by simp [generalizationSideConditionState])
  · rw [SourceInference.Detail.mem_generalizeValueBlockingRequirements_iff]
    simp [generalizationSideConditionState]

/-- A requirement-witness blocker exposes the variable carried by its
normalized predicate. -/
example : solverRegressionFirst ∈
    SourceInference.Detail.generalizeValueBlockedVariables
      generalizationSideConditionState [] 1 := by
  rw [SourceInference.Detail.mem_generalizeValueBlockedVariables_iff]
  right
  refine ⟨solverRegressionRequirement, ?_, ?_⟩
  · rw [SourceInference.Detail.mem_generalizeValueBlockingRequirements_iff]
    exact Or.inl (by simp [generalizationSideConditionState])
  · change solverRegressionFirst ∈
      (TypeSystem.Substitution.apply []
        (.variable solverRegressionFirst)).freeVariables
    rw [show ([] : TypeSystem.Substitution) =
      TypeSystem.Substitution.empty by rfl]
    rw [TypeSystem.Substitution.empty_apply]
    simp [TypeSystem.Ty.freeVariables]

/-- Exact quantified-variable projection excludes the requirement-blocked
variable and retains the other free variable in stable type order. -/
example :
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      1 (.product (.variable solverRegressionFirst)
        (.variable solverRegressionSecond))).scheme.quantified =
      [solverRegressionSecond] := by
  decide

/-- Generalization derives its lexical barrier from stable binders.  Replacing
the legacy environment cache with a stale closed scheme therefore cannot make
the captured variable polymorphic; using that stale cache directly would. -/
example :
    let stale : SourceInference.State := {
      stableGeneralizationState with locals := [("captured", .mono .word)]
    }
    (SourceInference.Detail.generalizeValue stale
      (stale.binderEnvironment.apply stale.inference.substitution) 0
      (.variable stableGeneralizationVariable)).scheme.quantified = [] ∧
    (SourceInference.Detail.generalizeValue stale
      (stale.locals.apply stale.inference.substitution) 0
      (.variable stableGeneralizationVariable)).scheme.quantified =
        [stableGeneralizationVariable] := by
  decide

private theorem generalizationSideConditionIds :
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).requirements.map
        (fun requirement => requirement.templateRequirement) =
      [solverRegressionRequirement.id] := by
  rfl

/-- The generalization projections supply exactly the uniqueness, coverage,
and freshness side conditions needed by template-tracking allocation. -/
example :
    ((SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).requirements.map
        (fun requirement => requirement.templateRequirement)).Nodup ∧
    ((SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).requirements.map
        (fun requirement => requirement.templateRequirement)).Sublist
      (generalizationSideConditionState.requirements.map
        (fun requirement => requirement.id)) ∧
    solverRegressionRequirement.id ∉
      generalizationSideConditionState.localSchemeAssumptions := by
  have ledgerUnique := SourceInference.State.requirementIds_nodup
    generalizationSideConditionState (by rfl)
  have covered := SourceInference.Detail.generalizeValue_templateIds_sublist
    generalizationSideConditionState [] 0 (.variable solverRegressionFirst)
  have fresh := SourceInference.Detail.generalizeValue_templateIds_fresh
    generalizationSideConditionState [] 0 (.variable solverRegressionFirst)
      solverRegressionRequirement.id (by
        rw [generalizationSideConditionIds]
        simp)
  exact ⟨covered.nodup ledgerUnique, covered, fresh⟩

/-- Canonical generalization exposes the exact scheme and predicate facts
needed by declarative generalized-let formation. -/
example :
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).scheme.body =
        .variable solverRegressionFirst ∧
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 (.variable solverRegressionFirst)).scheme.quantified.Nodup ∧
    ∃ requirement,
      requirement ∈
        (SourceInference.Detail.generalizeValue
          generalizationSideConditionState [] 0
            (.variable solverRegressionFirst)).requirements ∧
      (∃ metavariable,
        metavariable ∈
          (SourceInference.Detail.generalizeValue
            generalizationSideConditionState [] 0
              (.variable solverRegressionFirst)).scheme.quantified ∧
        metavariable ∈ TypedTraitResolution.predicateVariables
          requirement.predicate) ∧
      ∃ rawRequirement,
        rawRequirement ∈ generalizationSideConditionState.requirements ∧
        rawRequirement.id = requirement.templateRequirement ∧
        requirement.predicate =
          SourceInference.Detail.applyPredicate generalizationSideConditionState
            rawRequirement.predicate := by
  have idMember : solverRegressionRequirement.id ∈
      (SourceInference.Detail.generalizeValue generalizationSideConditionState []
        0 (.variable solverRegressionFirst)).requirements.map
          (fun requirement => requirement.templateRequirement) := by
    rw [generalizationSideConditionIds]
    simp
  rcases List.mem_map.mp idMember with
    ⟨requirement, requirementMember, _⟩
  refine ⟨SourceInference.Detail.generalizeValue_scheme_body _ _ _ _,
    SourceInference.Detail.generalizeValue_scheme_quantified_nodup _ _ _ _,
    requirement, requirementMember, ?_, ?_⟩
  · exact
      SourceInference.Detail.generalizeValue_requirement_depends_on_quantified
        generalizationSideConditionState [] 0 (.variable solverRegressionFirst)
        requirement requirementMember
  · exact SourceInference.Detail.generalizeValue_requirement_source
      generalizationSideConditionState [] 0 (.variable solverRegressionFirst)
      requirement requirementMember

/-- A result with no quantified variables cannot retain qualified scheme
requirements. -/
example :
    (SourceInference.Detail.generalizeValue generalizationSideConditionState []
      0 .word).requirements = [] := by
  apply SourceInference.Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
  rfl

private def solverRegressionSolvedRow : SourceInference.SolvedRequirement := {
  id := solverRegressionRequirement.id
  predicate := solverRegressionNormalized
  evidence := .assumption solverRegressionNormalized
}

private def solverRegressionFinalizedResult : SourceInference.Result := {
  type := .word
  substitution := solverRegressionFinalizeState.inference.substitution
  solvedRequirements := [solverRegressionSolvedRow]
  typedSource :=
    (solverRegressionFinalizeState.toTypedSource
      solverRegressionRoots).applySubstitution
      solverRegressionFinalizeState.inference.substitution
}

/-- This equation fails if the already-normalized head is passed through
`solvePredicate` and receives the inference substitution a second time. -/
example : SourceInference.Detail.solvePredicates solverRegressionContext
    solverRegressionState [solverRegressionSource] =
    .ok ([solverRegressionNormalized],
      [.assumption solverRegressionNormalized]) := by
  rfl

example : Solcore.SourceSemantics.RetainedEvidenceValid
    [solverRegressionNormalized]
    solverRegressionContext.signatures.resolutionRules
    solverRegressionNormalized
    (.assumption solverRegressionNormalized) := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.solvePredicate_sound
      (context := solverRegressionContext)
      (state := solverRegressionState)
      (source := solverRegressionSource)
      (by rfl)

example : Solcore.SourceSemantics.RetainedEvidenceValid
    [solverRegressionNormalized]
    solverRegressionContext.signatures.resolutionRules
    (ProgramSignatures.builtinIntPredicate .word)
    (.implementation (.byImpl
      (ProgramSignatures.builtinIntPredicate .word)
      (.builtin .intWord) [])) := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.solveNormalizedPredicate_sound
      (context := solverRegressionContext)
      (state := solverRegressionState)
      (goal := ProgramSignatures.builtinIntPredicate .word)
      (by rfl)

example : Solcore.SourceSemantics.SolvedRequirementValid
    solverRegressionSemanticContext {
      id := solverRegressionRequirement.id
      predicate := solverRegressionNormalized
      evidence := .assumption solverRegressionNormalized
    } := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirementEvidence_ordinary_sound
        (inferenceContext := solverRegressionContext)
        (state := solverRegressionState)
        (requirement := solverRegressionRequirement)
        (retained := .assumption solverRegressionNormalized)
        (semanticContext := solverRegressionSemanticContext)
        (by
          change solverRegressionRequirement.id ∉ []
          simp) rfl rfl (by rfl)

example {retained : SourceInference.PredicateEvidence}
    (success : SourceInference.Detail.solveRequirementEvidence
      solverRegressionContext solverRegressionTemplateState
      solverRegressionRequirement = .ok retained) :
    retained = .assumption solverRegressionNormalized := by
  exact
    Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirementEvidence_template_eq
        (context := solverRegressionContext)
        (state := solverRegressionTemplateState)
        (requirement := solverRegressionRequirement)
        (by simp [solverRegressionTemplateState]) success

/-- Whole-ledger solving preserves the ordinary row and validates it after
normalizing the declaration assumptions exactly once. -/
example : Solcore.SourceSemantics.SolvedRequirementsValid
    solverRegressionSemanticContext [{
      id := solverRegressionRequirement.id
      predicate := solverRegressionNormalized
      evidence := .assumption solverRegressionNormalized
    }] := by
  apply
    Solcore.SourceSemantics.SourceInferenceSoundness.solveRequirements_ordinary_sound
      (inferenceContext := solverRegressionContext)
      (state := solverRegressionState)
      (requirements := [solverRegressionRequirement])
  · intro requirement member
    have requirement_eq : requirement = solverRegressionRequirement := by
      simpa using member
    subst requirement
    change solverRegressionRequirement.id ∉ []
    simp
  · rfl
  · rfl
  · rfl

/-- Finalizing a nonempty ordinary ledger exposes a declarative context in
which every emitted solved row has valid retained evidence. -/
example : Solcore.SourceSemantics.SolvedRequirementsValid
    (Solcore.SourceSemantics.SourceInferenceSoundness.finalizedRequirementContext
      solverRegressionContext solverRegressionFinalizedResult)
    solverRegressionFinalizedResult.solvedRequirements := by
  apply
    Solcore.SourceSemantics.SourceInferenceSoundness.finalize_solvedRequirementsValid
      (inferenceContext := solverRegressionContext)
      (type := .word)
      (state := solverRegressionFinalizeState)
      (roots := solverRegressionRoots)
  · rfl
  · rfl

private def integerLiteralRows
    (function : SourceInference.CheckedFunction) :
    List (SourceInference.ExpressionNode ×
      SourceInference.IntegerLiteralResolution) :=
  function.typedBody.nodes.filterMap fun
    | .expression node =>
        match node.form with
        | .integerLiteral _ resolution => some (node, resolution)
        | _ => none
    | .statement _ => none

private def hasExactDefaultedWordEvidence
    (function : SourceInference.CheckedFunction)
    (row : SourceInference.ExpressionNode ×
      SourceInference.IntegerLiteralResolution) : Bool :=
  let node := row.1
  let resolution := row.2
  node.type == TypeSystem.Ty.word &&
    resolution.targetType == TypeSystem.Ty.word &&
    node.requirements == [resolution.requirement] &&
    node.coercions.isEmpty &&
    function.solvedRequirements.any fun solved =>
      solved.id == resolution.requirement && hasBuiltinIntWordEvidence solved

private def testLambdaLetTupleConditional : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function polymorphic(flag: Bool) returns (Word, Bool) {",
    "  let id = lam(value) { return value; };",
    "  return (id(((1))), id(flag ? flag : !flag));",
    "}",
    "function expected(flag: Bool) returns (function(Word) returns (Word)) {",
    "  return lam(value) { return flag ? value + 1 : value; };",
    "}",
    "function empty() { return (); }"
  ])
  assertTrue (decide (checked.length = 3))
    "lambda/let/tuple fixture lost a checked function"
  match checked with
  | first :: second :: third :: [] =>
      assertTrue (decide (first.inferredBodyType =
          TypeSystem.Ty.product .word .bool))
        "let-polymorphic tuple did not infer Word × Bool"
      let idBinders := first.typedBody.nodes.filterMap fun
        | .statement { form := .letDecl binder (some _), .. } =>
            if binder.name == "id" then some binder else none
        | _ => none
      match idBinders with
      | [binder] =>
          let schemeShape := match binder.scheme.quantified,
              binder.scheme.body with
            | [quantified], .function (.variable parameter) (.variable result) =>
                quantified == parameter && parameter == result
            | _, _ => false
          assertTrue schemeShape
            "local id did not retain its generalized α → α scheme"
          let referenceTypes := first.typedBody.nodes.filterMap fun
            | .expression node => match node.form with
                | .reference _ (.local candidate) =>
                    if candidate == binder.id then some node.rawType else none
                | _ => none
            | .statement _ => none
          assertTrue (referenceTypes.length == 2 &&
              referenceTypes.any (· == .function .word .word) &&
              referenceTypes.any (· == .function .bool .bool))
            "local id was not independently instantiated at Word and Bool"
      | _ => throw (IO.userError
          "let-polymorphic fixture did not retain exactly one local id binder")
      assertTrue (decide (second.inferredBodyType =
          TypeSystem.Ty.function .word .word))
        "expected function type did not guide an inferred lambda"
      assertTrue (decide (third.inferredBodyType = .unit))
        "empty tuple did not check as Unit"
  | _ => throw (IO.userError "checked function order changed")

/-- A discarded use of a polymorphic local has no expected type.  The
frontend therefore retains a fresh occurrence metavariable after independently
generalizing the binder; the declarative source semantics must admit it as a
body-wide residual variable. -/
private def testDiscardedPolymorphicReferenceResidual : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function discard() {",
    "  let id = lam(value) { return value; };",
    "  id;",
    "  return ();",
    "}"
  ])
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"discarded polymorphic fixture produced {functions.length} functions")
  let binders := function.typedBody.nodes.filterMap fun
    | .statement { form := .letDecl binder (some _), .. } =>
        if binder.name == "id" then some binder else none
    | _ => none
  let binder ← match binders with
    | [binder] => pure binder
    | _ => throw (IO.userError
        "discarded polymorphic fixture lost its unique id binder")
  let referenceTypes := function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
        | .reference _ (.local candidate) =>
            if candidate == binder.id then some node.rawType else none
        | _ => none
    | .statement _ => none
  let retainedResidual := match binder.scheme.quantified, referenceTypes with
    | [quantified], [.function (.variable parameter) (.variable result)] =>
        parameter == result && parameter != quantified
    | _, _ => false
  assertTrue retainedResidual
    "discarded polymorphic reference did not retain an independent residual type"

private def testAmbiguousOverload : IO Unit := do
  let source := String.intercalate "\n" [
    "function choose(value: Word) returns (Word) { return value; }",
    "function choose(other: Word) returns (Word) { return other + 1; }",
    "function run() returns (Word) { return choose(1); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOverload "choose" candidates, .. } =>
            candidates.length == 2
        | _ => false) "ambiguous overload was not reported explicitly"
  | .ok _ => throw (IO.userError "ambiguous overload was selected")

private def testIntegerLiteralExpectedType : IO Unit := do
  let source := "function bad() returns (Bool) { return 1; }"
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .unsupportedIntegerLiteralTarget _ type, .. } =>
            type == TypeSystem.Ty.bool
        | _ => false) "an integer literal silently checked as Bool"
  | .ok _ => throw (IO.userError "an integer literal checked as Bool")

private def testClosedUnsupportedIntegerLiteralTarget : IO Unit := do
  let metavariable : TypeSystem.TypeVarId := ⟨0⟩
  let expression : SourceInference.ExpressionId :=
    ⟨⟨solverRegressionOwner, 0⟩⟩
  let origin : SourceInference.IntegerLiteralOrigin := {
    metavariable
    expression
    requirement := ⟨0⟩
  }
  let initial := SourceInference.State.initial solverRegressionOwner
  let state : SourceInference.State := {
    initial with
    inference := {
      next := 1
      substitution := [(metavariable, .bool)]
    }
  }
  match SourceInference.Detail.validateIntegerLiteralTarget origin state with
  | .error (.unsupportedIntegerLiteralTarget rejected type) =>
      assertTrue (rejected == expression && type == TypeSystem.Ty.bool)
        "unsupported closed integer-literal target lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"unsupported closed integer-literal target produced {reprStr error}")
  | .ok _ => throw (IO.userError
      "unsupported closed integer-literal target passed final validation")

private def literalLedgerMetavariable : TypeSystem.TypeVarId := ⟨0⟩

private def literalLedgerExpression : SourceInference.ExpressionId :=
  ⟨⟨solverRegressionOwner, 0⟩⟩

private def literalLedgerRequirement : SourceInference.RequirementId := ⟨0⟩

private def literalLedgerResolution :
    SourceInference.IntegerLiteralResolution := {
  rawValue := 7
  targetType := .variable literalLedgerMetavariable
  requirement := literalLedgerRequirement
}

private def literalLedgerNode : SourceInference.ExpressionNode := {
  id := literalLedgerExpression
  span := solverRegressionSpan
  type := .variable literalLedgerMetavariable
  form := .integerLiteral (.decimal "7") literalLedgerResolution
  requirements := [literalLedgerRequirement]
}

private def literalLedgerState : SourceInference.State := {
  SourceInference.State.initial solverRegressionOwner with
  inference := { next := 1 }
  nextOccurrence := 1
  nodes := [.expression literalLedgerNode]
  integerLiterals := [{
    metavariable := literalLedgerMetavariable
    expression := literalLedgerExpression
    requirement := literalLedgerRequirement
  }]
  nextRequirement := 1
  requirements := [{
    id := literalLedgerRequirement
    predicate := literalLedgerResolution.predicate
  }]
}

private def testIntegerLiteralLedgerValidation : IO Unit := do
  match SourceInference.Detail.validateIntegerLiteralLedger literalLedgerState with
  | .ok () => pure ()
  | .error error => throw (IO.userError
      s!"a consistent integer-literal ledger produced {reprStr error}")

  let missingOrigin := { literalLedgerState with integerLiterals := [] }
  match SourceInference.Detail.validateIntegerLiteralLedger missingOrigin with
  | .error (.missingIntegerLiteralRequirement expression requirement) =>
      assertTrue (expression == literalLedgerExpression &&
          requirement == literalLedgerRequirement)
        "missing integer-literal origin lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"missing integer-literal origin produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an integer-literal node without origin metadata passed validation")

  let missingRequirement := { literalLedgerState with requirements := [] }
  match SourceInference.Detail.validateIntegerLiteralLedger missingRequirement with
  | .error (.missingIntegerLiteralRequirement expression requirement) =>
      assertTrue (expression == literalLedgerExpression &&
          requirement == literalLedgerRequirement)
        "missing integer-literal requirement row lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"missing integer-literal requirement row produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an integer-literal node without its requirement row passed validation")

  let wrongPredicate := ProgramSignatures.builtinIntPredicate .bool
  let mismatchedPredicate := {
    literalLedgerState with
    requirements := [{
      id := literalLedgerRequirement
      predicate := wrongPredicate
    }]
  }
  match SourceInference.Detail.validateIntegerLiteralLedger mismatchedPredicate with
  | .error (.integerLiteralRequirementPredicateMismatch expression requirement
      expected actual) =>
      assertTrue (expression == literalLedgerExpression &&
          requirement == literalLedgerRequirement &&
          expected == literalLedgerResolution.predicate &&
          actual == wrongPredicate)
        "mismatched integer-literal predicate lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"mismatched integer-literal predicate produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an integer-literal node with a mismatched predicate passed validation")

  let inconsistentResolution : SourceInference.IntegerLiteralResolution := {
    literalLedgerResolution with rawValue := 8
  }
  let inconsistentNode : SourceInference.ExpressionNode := {
    literalLedgerNode with
    form := .integerLiteral (.decimal "7") inconsistentResolution
  }
  let inconsistentValue := {
    literalLedgerState with nodes := [.expression inconsistentNode]
  }
  match SourceInference.Detail.validateIntegerLiteralLedger inconsistentValue with
  | .error (.unsupportedLiteral kind) =>
      assertTrue (kind == "inconsistent integer literal metadata")
        "inconsistent integer-literal value lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"inconsistent integer-literal value produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an integer-literal node with an inconsistent value passed validation")

private def graphValidationOccurrence (index : Nat) :
    SourceInference.OccurrenceId :=
  ⟨solverRegressionOwner, index⟩

private def graphValidationExpression (index : Nat) :
    SourceInference.ExpressionId :=
  ⟨graphValidationOccurrence index⟩

private def graphValidationStatement (index : Nat) :
    SourceInference.StatementId :=
  ⟨graphValidationOccurrence index⟩

private def graphValidationExpressionNode (index : Nat)
    (form : SourceInference.ExpressionForm) :
    SourceInference.ExpressionNode := {
  id := graphValidationExpression index
  span := solverRegressionSpan
  type := .word
  form
}

private def graphValidationStatementNode (index : Nat)
    (form : SourceInference.StatementForm) :
    SourceInference.StatementNode := {
  id := graphValidationStatement index
  span := solverRegressionSpan
  type := .word
  form
}

private def validSourceGraph : SourceInference.TypedSource := {
  owner := solverRegressionOwner
  inputs := []
  roots := [.expression (graphValidationExpression 1)]
  nodes := [
    .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
    .expression (graphValidationExpressionNode 1
      (.group (graphValidationExpression 0)))
  ]
}

/-- Require the forest validator to retain the exact repeated incoming ID. -/
private def expectDuplicateIncomingNode (label : String)
    (source : SourceInference.TypedSource)
    (expected : SourceInference.NodeId) : IO Unit := do
  match SourceInference.Detail.validateSourceGraph source with
  | .error (.duplicateIncomingNode id) =>
      assertTrue (id == expected)
        s!"{label} lost its exact duplicate-incoming diagnostic"
  | .error error => throw (IO.userError
      s!"{label} produced {reprStr error}")
  | .ok () => throw (IO.userError
      s!"{label} passed graph validation")

/-- Require root-driven coverage to identify the first unreachable table ID. -/
private def expectUnreachableNode (label : String)
    (source : SourceInference.TypedSource)
    (expected : SourceInference.NodeId) : IO Unit := do
  match SourceInference.Detail.validateSourceGraph source with
  | .error (.unreachableNode id) =>
      assertTrue (id == expected)
        s!"{label} lost its exact unreachable-node diagnostic"
  | .error error => throw (IO.userError
      s!"{label} produced {reprStr error}")
  | .ok () => throw (IO.userError
      s!"{label} passed graph validation")

/-- The finalization boundary rejects malformed occurrence graphs before
exposing them to semantic consumers.  Node-table duplicate detection erases
category, while lookup and forest validation preserve it. -/
private def testSourceGraphValidation : IO Unit := do
  match SourceInference.Detail.validateSourceGraph validSourceGraph with
  | .ok () => pure ()
  | .error error => throw (IO.userError
      s!"a valid typed-source graph produced {reprStr error}")

  let foreignOwner : Resolved.DeclarationId :=
    { solverRegressionOwner with declarationIndex := 1 }
  let foreignOccurrence : SourceInference.OccurrenceId := ⟨foreignOwner, 0⟩
  let foreignExpression : SourceInference.ExpressionId := ⟨foreignOccurrence⟩
  let foreignNode : SourceInference.ExpressionNode := {
    graphValidationExpressionNode 0 (.literal (.decimal "0")) with
    id := foreignExpression
  }
  let ownerMismatch := {
    validSourceGraph with
    roots := []
    nodes := [.expression foreignNode]
  }
  match SourceInference.Detail.validateSourceGraph ownerMismatch with
  | .error (.nodeOwnerMismatch expected actual) =>
      assertTrue (expected == solverRegressionOwner &&
          actual == foreignOccurrence)
        "node-owner mismatch lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"node-owner mismatch produced {reprStr error}")
  | .ok () => throw (IO.userError
      "a foreign-owner source node passed graph validation")

  let duplicateOccurrence := graphValidationOccurrence 0
  let crossCategoryDuplicate := {
    validSourceGraph with
    roots := []
    nodes := [
      .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
      .statement (graphValidationStatementNode 0 .continueStmt)
    ]
  }
  match SourceInference.Detail.validateSourceGraph crossCategoryDuplicate with
  | .error (.duplicateOccurrence occurrence) =>
      assertTrue (occurrence == duplicateOccurrence)
        "cross-category duplicate occurrence lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"cross-category duplicate occurrence produced {reprStr error}")
  | .ok () => throw (IO.userError
      "expression and statement nodes shared one occurrence")

  let wrongCategoryRoot : SourceInference.NodeId :=
    .statement (graphValidationStatement 1)
  let missingRoot := { validSourceGraph with roots := [wrongCategoryRoot] }
  match SourceInference.Detail.validateSourceGraph missingRoot with
  | .error (.missingRoot root) =>
      assertTrue (root == wrongCategoryRoot)
        "wrong-category root lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"wrong-category root produced {reprStr error}")
  | .ok () => throw (IO.userError
      "a statement root resolved to an expression at the same occurrence")

  let parentId : SourceInference.NodeId :=
    .expression (graphValidationExpression 1)
  let missingChildId : SourceInference.NodeId :=
    .expression (graphValidationExpression 0)
  let wrongCategoryChild := {
    validSourceGraph with
    nodes := [
      .statement (graphValidationStatementNode 0 .continueStmt),
      .expression (graphValidationExpressionNode 1
        (.group (graphValidationExpression 0)))
    ]
  }
  match SourceInference.Detail.validateSourceGraph wrongCategoryChild with
  | .error (.missingChild parent child) =>
      assertTrue (parent == parentId && child == missingChildId)
        "wrong-category child edge lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"wrong-category child edge produced {reprStr error}")
  | .ok () => throw (IO.userError
      "an expression edge resolved to a statement at the same occurrence")

  let rootOne : SourceInference.NodeId :=
    .expression (graphValidationExpression 1)
  let rootZero : SourceInference.NodeId :=
    .expression (graphValidationExpression 0)
  let rootTwo : SourceInference.NodeId :=
    .expression (graphValidationExpression 2)

  let duplicateRoot := {
    validSourceGraph with
    roots := [rootOne, rootOne]
  }
  expectDuplicateIncomingNode "a duplicate source root" duplicateRoot rootOne

  let duplicateChildSlot := {
    validSourceGraph with
    nodes := [
      .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
      .expression (graphValidationExpressionNode 1
        (.tuple [graphValidationExpression 0, graphValidationExpression 0]))
    ]
  }
  expectDuplicateIncomingNode "a duplicate child slot"
    duplicateChildSlot rootZero

  let sharedChild := {
    validSourceGraph with
    roots := [rootOne, rootTwo]
    nodes := [
      .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
      .expression (graphValidationExpressionNode 1
        (.group (graphValidationExpression 0))),
      .expression (graphValidationExpressionNode 2
        (.group (graphValidationExpression 0)))
    ]
  }
  expectDuplicateIncomingNode "a child shared by two parents"
    sharedChild rootZero

  let rootAsChild := {
    validSourceGraph with
    roots := [rootZero, rootOne]
  }
  expectDuplicateIncomingNode "a root retained as a child"
    rootAsChild rootZero

  let orphanCycle := {
    validSourceGraph with
    roots := [rootZero]
    nodes := [
      .expression (graphValidationExpressionNode 0 (.literal (.decimal "0"))),
      .expression (graphValidationExpressionNode 1
        (.group (graphValidationExpression 2))),
      .expression (graphValidationExpressionNode 2
        (.group (graphValidationExpression 1)))
    ]
  }
  expectUnreachableNode "an orphan cycle" orphanCycle rootOne

  let simpleCycle := {
    validSourceGraph with
    roots := [rootZero]
    nodes := [
      .expression (graphValidationExpressionNode 0
        (.group (graphValidationExpression 1))),
      .expression (graphValidationExpressionNode 1
        (.group (graphValidationExpression 0)))
    ]
  }
  expectDuplicateIncomingNode "a reachable cycle" simpleCycle rootZero

  let finalizationState : SourceInference.State := {
    SourceInference.State.initial solverRegressionOwner with
    nextOccurrence := 2
    nodes := validSourceGraph.nodes
  }
  match SourceInference.Detail.finalize solverRegressionContext .word
      finalizationState [wrongCategoryRoot] with
  | .error (.missingRoot root) =>
      assertTrue (root == wrongCategoryRoot)
        "finalization lost its graph-validation diagnostic"
  | .error error => throw (IO.userError
      s!"finalization returned the wrong graph error: {reprStr error}")
  | .ok _ => throw (IO.userError
      "finalization accepted a wrong-category root")

private def testClosedUnsupportedIntegerPatternTarget : IO Unit := do
  let metavariable : TypeSystem.TypeVarId := ⟨0⟩
  let origin : SourceInference.IntegerPatternOrigin := {
    metavariable
    span := solverRegressionSpan
    requirement := ⟨0⟩
  }
  let initial := SourceInference.State.initial solverRegressionOwner
  let state : SourceInference.State := {
    initial with
    inference := {
      next := 1
      substitution := [(metavariable, .bool)]
    }
  }
  match SourceInference.Detail.validateIntegerPatternTarget origin state with
  | .error (.nonNumericPatternType span type) =>
      assertTrue (span == solverRegressionSpan && type == TypeSystem.Ty.bool)
        "unsupported closed integer-pattern target lost its exact diagnostic"
  | .error error => throw (IO.userError
      s!"unsupported closed integer-pattern target produced {reprStr error}")
  | .ok _ => throw (IO.userError
      "unsupported closed integer-pattern target passed final validation")

private def testSourceNamedLiteralTraitsDoNotAuthorize : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Int<T> {}",
    "trait FromLiteral<T> {}",
    "trait Numeric<T> {}",
    "enum Box { Only }",
    "impl Int<Box> {}",
    "impl FromLiteral<Box> {}",
    "impl Numeric<Box> {}",
    "function literal() returns (Box) { return 1; }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .unsupportedIntegerLiteralTarget _ type, .. } =>
            type != TypeSystem.Ty.word && type != TypeSystem.Ty.integer
        | _ => false)
        "source traits named Int/FromLiteral/Numeric authorized a nominal literal"
  | .ok _ => throw (IO.userError
      "source traits named Int/FromLiteral/Numeric authorized a nominal literal")

private def testUnconstrainedIntegerLiteralDefaultsToWord : IO Unit := do
  let checked ← check "function defaulted() { 1; return; }"
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"unconstrained literal fixture checked {functions.length} functions")
  let literals := integerLiteralRows function
  assertTrue (decide (function.inferredBodyType = TypeSystem.Ty.unit) &&
      literals.length == 1 && literals.all (hasExactDefaultedWordEvidence function) &&
      function.solvedRequirements.length == 1 &&
      function.solvedRequirements.all hasBuiltinIntWordEvidence)
    "an unconstrained integer literal did not default exactly to builtin Int<Word>"

private def testLetBoundIntegerLiteralClosesLater : IO Unit := do
  let checked ← check
    "function closeLater() returns (Word) { let value = 1; return value; }"
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"let-bound literal fixture checked {functions.length} functions")
  assertTrue (function.solvedRequirements.length == 1 &&
      function.solvedRequirements.all fun solved =>
        solved.predicate == ProgramSignatures.builtinIntPredicate .word)
    "a later return context did not close the let-bound literal as Word"

private def testUnusedLetIntegerLiteralDefaultsIndependently : IO Unit := do
  let checked ← check
    "function unused() returns (Word) { let value = 1; return 9; }"
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"unused literal fixture checked {functions.length} functions")
  let binder ← match function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "value" then some binder else none
      | _ => none with
    | [binder] => pure binder
    | binders => throw (IO.userError
        s!"unused literal fixture retained {binders.length} value binders")
  let literals := integerLiteralRows function
  assertTrue (decide (binder.scheme = .mono .word) &&
      literals.map (fun row => row.2.rawValue) == [1, 9] &&
      literals.all (hasExactDefaultedWordEvidence function) &&
      function.solvedRequirements.length == 2 &&
      function.solvedRequirements.all hasBuiltinIntWordEvidence)
    "an unused let literal and returned literal did not retain independent Int<Word> evidence"

private def testLiteralRequirementPreservesIndependentPolymorphism : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function run(flag: Bool) returns ((Word, Word), (Word, Bool)) {",
    "  let f = lam(value) { return (1, value); };",
    "  return (f(2), f(flag));",
    "}"
  ])
  let function ← match checked with
    | [function] => pure function
    | functions => throw (IO.userError
        s!"mixed literal-polymorphism fixture checked {functions.length} functions")
  assertTrue (decide (function.inferredBodyType =
      TypeSystem.Ty.product (.product .word .word) (.product .word .bool)) &&
      function.solvedRequirements.length == 2 &&
      function.solvedRequirements.all fun solved =>
        solved.predicate == ProgramSignatures.builtinIntPredicate .word)
    "an integer literal monomorphized an independent let-bound type variable"

private def testContextualIntegerLiteralOperators : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function addLiterals() returns (Word) { return 1 + 1; }",
    "function complementLiteral() returns (Word) { return ~1; }"
  ])
  let intWordRequirements (function : SourceInference.CheckedFunction) :=
    function.solvedRequirements.filter fun solved =>
      solved.predicate == ProgramSignatures.builtinIntPredicate .word
  match checked with
  | [addition, complement] =>
      assertTrue (decide (addition.inferredBodyType = TypeSystem.Ty.word ∧
          (intWordRequirements addition).length = 2))
        "Word context did not close both addition literals through builtin Int"
      assertTrue (decide (complement.inferredBodyType = TypeSystem.Ty.word ∧
          (intWordRequirements complement).length = 1))
        "Word context did not close the complemented literal through builtin Int"
  | functions => throw (IO.userError
      s!"contextual operator fixture checked {functions.length} functions")

private def testNestedIntegerLiteralOperatorsCloseLater : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function accept(value: Word) returns (Word) { return value; }",
    "function nestedAdd() returns (Word) { return accept(1 + 1); }",
    "function nestedNot() returns (Word) { return accept(~1); }",
    "function letAdd() returns (Word) {",
    "  let value = 1 + 1;",
    "  return accept(value);",
    "}",
    "function letNot() returns (Word) {",
    "  let value = ~1;",
    "  return accept(value);",
    "}"
  ])
  let validate (label : String) (literalCount : Nat)
      (acceptsOperator : SourceInference.ExpressionForm → Bool)
      (function : SourceInference.CheckedFunction) : IO Unit := do
    let literals := function.typedBody.nodes.filterMap fun
      | .expression { form := .integerLiteral _ resolution, .. } =>
          some resolution
      | _ => none
    let hasWordOperator := function.typedBody.nodes.any fun
      | .expression node =>
          node.type == TypeSystem.Ty.word && acceptsOperator node.form
      | .statement _ => false
    assertTrue (decide (function.inferredBodyType = TypeSystem.Ty.word) &&
        literals.length == literalCount &&
        (literals.all fun resolution =>
          resolution.targetType == TypeSystem.Ty.word) &&
        function.solvedRequirements.length == literalCount &&
        (function.solvedRequirements.all fun solved =>
          solved.predicate == ProgramSignatures.builtinIntPredicate .word) &&
        hasWordOperator)
      s!"{label} did not close its deferred operator and literal carriers as Word"
  match checked with
  | _ :: nestedAdd :: nestedNot :: letAdd :: letNot :: [] =>
      validate "nested addition" 2
        (fun form => form matches .binary _ .add _) nestedAdd
      validate "nested complement" 1
        (fun form => form matches .unary .bitNot _) nestedNot
      validate "let-bound addition" 2
        (fun form => form matches .binary _ .add _) letAdd
      validate "let-bound complement" 1
        (fun form => form matches .unary .bitNot _) letNot
  | functions => throw (IO.userError
      s!"nested operator fixture checked {functions.length} functions")

private def testUnconstrainedIntegerLiteralOperatorsDefaultToWord : IO Unit := do
  let unconstrained := String.intercalate "\n" [
    "function add() { 1 + 1; return; }",
    "function invert() { ~1; return; }",
    "function compare() returns (Bool) { return 1 == 1; }"
  ]
  let checked ← check unconstrained
  let validate (label : String) (expectedBody expectedOperator : TypeSystem.Ty)
      (literalCount : Nat)
      (acceptsOperator : SourceInference.ExpressionForm → Bool)
      (function : SourceInference.CheckedFunction) : IO Unit := do
    let literals := integerLiteralRows function
    let hasOperator := function.typedBody.nodes.any fun
      | .expression node =>
          node.type == expectedOperator && node.requirements.isEmpty &&
            node.coercions.isEmpty && acceptsOperator node.form
      | .statement _ => false
    assertTrue (function.inferredBodyType == expectedBody &&
        literals.length == literalCount &&
        literals.all (hasExactDefaultedWordEvidence function) &&
        function.solvedRequirements.length == literalCount &&
        function.solvedRequirements.all hasBuiltinIntWordEvidence && hasOperator)
      s!"{label} did not default its operands to the builtin Word operator"
  match checked with
  | [addition, complement, comparison] =>
      validate "unconstrained addition" .unit .word 2
        (fun form => form matches .binary _ .add _) addition
      validate "unconstrained complement" .unit .word 1
        (fun form => form matches .unary .bitNot _) complement
      validate "unconstrained equality" .bool .bool 2
        (fun form => form matches .binary _ .equal _) comparison
  | functions => throw (IO.userError
      s!"unconstrained operator fixture checked {functions.length} functions")

private def testDeferredIntegerLiteralOperatorRejections : IO Unit := do
  let unsupported := String.intercalate "\n" [
    "enum Box { Only }",
    "function acceptBox(value: Box) returns (Box) { return value; }",
    "function acceptBool(value: Bool) returns (Bool) { return value; }",
    "function box() returns (Box) { return acceptBox(1 + 1); }",
    "function boolean() returns (Bool) { return acceptBool(~1); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace unsupported) with
  | .error errors =>
      let rejected := errors.filter fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.trait == ProgramTraitId.builtin .int &&
              predicate.subject != TypeSystem.Ty.word &&
              predicate.subject != TypeSystem.Ty.integer
        | _ => false
      assertTrue (rejected.length == 2)
        "a deferred operator authorized a nominal or Bool literal target"
  | .ok _ => throw (IO.userError
      "a deferred operator accepted a nominal or Bool literal target")
  let traitOwned := String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "function accept(value: Word) returns (Word) { return value; }",
    "function rejected() returns (Word) { return accept(1 + 1); }"
  ]
  let loaded ← load traitOwned
  let add ← match loaded.environment.traitsNamed "Add" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Add trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = add) &&
              predicate.subject == TypeSystem.Ty.word &&
              predicate.arguments.isEmpty
        | _ => false)
        "a defaulted Word operator bypassed its source Add<Word> obligation"
  | .ok _ => throw (IO.userError
      "an available Add catalog was bypassed by direct builtin deferral")
  let logical := String.intercalate "\n" [
    "function accept(value: Word) returns (Word) { return value; }",
    "function badAnd() returns (Word) {",
    "  let value = 1;",
    "  value && value;",
    "  return accept(value);",
    "}",
    "function badOr() returns (Word) {",
    "  let value = 1;",
    "  value || value;",
    "  return accept(value);",
    "}",
    "function badNot() returns (Word) {",
    "  let value = 1;",
    "  !value;",
    "  return accept(value);",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace logical) with
  | .error errors =>
      let hasUnknown (name : String) := errors.any fun error => match error with
        | .body { error := .unknownVariable actual, .. } => actual == name
        | _ => false
      assertTrue (hasUnknown "and" && hasUnknown "or" && hasUnknown "not")
        "a Bool-domain logical operator was deferred over a Word literal target"
  | .ok _ => throw (IO.userError
      "Bool-domain logical operators were accepted over Word literal targets")
  let unrelatedStaged := String.intercalate "\n" [
    "function take(value: integer, ignored: integer) returns (integer) {",
    "  return value;",
    "}",
    "function bad(value: integer) returns (integer) {",
    "  return take(value, 1) + value;",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace unrelatedStaged) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .operatorNotSupported "Add" .integer, .. } => true
        | _ => false)
        "an unrelated ground integer literal authorized a staged operator"
  | .ok _ => throw (IO.userError
      "an unrelated literal authorized an integer operator on nonliteral inputs")

private def testDefaultedIntegerLiteralOperatorsRespectSourceTraits : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {",
    "  function eq(left: T, right: T) returns (Bool);",
    "}",
    "trait BitNot<T> {",
    "  function bnot(value: T) returns (T);",
    "}",
    "function compare() returns (Bool) { return 1 == 1; }",
    "function invert() { ~1; return; }"
  ]
  let loaded ← load source
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  let bitNot ← match loaded.environment.traitsNamed "BitNot" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one BitNot trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      let misses (trait : Resolved.DeclarationId) := errors.any fun error =>
        match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = trait) &&
              predicate.subject == TypeSystem.Ty.word &&
              predicate.arguments.isEmpty
        | _ => false
      assertTrue (errors.length == 2 && misses eq && misses bitNot)
        "defaulted literal operators lost their exact Eq<Word> or BitNot<Word> obligation"
  | .ok _ => throw (IO.userError
      "source Eq/BitNot catalogs without Word implementations were bypassed")

private def testGroundOperatorResultKeepsCoercion : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Add<Box> {",
    "  function add(left: Box, right: Box) returns (Box) { return left; }",
    "}",
    "impl Coerce<Box, Word> {}",
    "function convert(left: Box, right: Box) returns (Word) {",
    "  return left + right;",
    "}"
  ])
  let function ← match checked.getLast? with
    | some function => pure function
    | none => throw (IO.userError "ground operator fixture checked no function")
  assertTrue (decide (function.inferredBodyType = TypeSystem.Ty.word ∧
      function.solvedRequirements.length = 2) &&
      (function.solvedRequirements.any fun solved =>
        solved.predicate.arguments == []) &&
      (function.solvedRequirements.any fun solved =>
        solved.predicate.arguments == [TypeSystem.Ty.word]))
    "a ground operator result lost its Add evidence or result coercion"

private def testUnsupportedStatement : IO Unit := do
  let source :=
    "function loop(flag: Bool) { while (flag) { return; } }"
  let checked ← check source
  assertTrue (checked.any fun function =>
      function.typedBody.nodes.any fun
        | .statement { form := .whileLoop .., .. } => true
        | _ => false)
    "while inference did not retain its typed control-flow node"

private def testTraitBackedCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function convert(value: Word) returns (Box) { return accept(value); }"
  ]
  let checked ← check source
  match checked.find? fun function =>
      function.evidence.any fun evidence => match evidence with
        | .implementation _ => true
        | .assumption _ => false with
  | some function =>
      assertTrue (decide (function.predicates.length = 1))
        "coercion evidence lost its Coerce predicate"
  | none => throw (IO.userError "trait-backed coercion produced no evidence")

private def testMissingCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "function accept(value: Box) returns (Box) { return value; }",
    "function reject(value: Word) returns (Box) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.arguments.length == 1
        | _ => false) "missing coercion implementation was accepted"
  | .ok _ => throw (IO.userError "missing coercion implementation was accepted")

private def testInconclusiveCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "impl Coerce<Word, Box> {}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function reject(value: Word) returns (Box) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .inconclusiveTrait (.ambiguous _ _ _), .. } => true
        | _ => false) "overlapping coercion implementations lost ambiguity"
  | .ok _ => throw (IO.userError "ambiguous coercion implementation was selected")

private def testUnsolvedCoercionMethodPredicate : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Coerce<From, To> {",
    "  function coerce(value: From) returns (To) where From: Eq;",
    "}",
    "function acceptWord(value: Word) returns (Word) { return value; }",
    "function reject<T>(value: T) returns (Word) where T: Coerce<Word> {",
    "  return acceptWord(value);",
    "}"
  ]
  let loaded ← load source
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = eq) && predicate.arguments.isEmpty
        | _ => false)
        "a coercion method predicate was accepted without Eq<T>"
  | .ok _ => throw (IO.userError
      "a coercion method predicate was accepted without Eq<T>")

private def testConstrainedLetDoesNotGeneralizeAwayEvidence : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "impl Eq<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
    "function reject() returns (Bool) {",
    "  let f = lam(value) { return keep(value); };",
    "  return f(true);",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.subject == TypeSystem.Ty.bool
        | _ => false)
        "a constrained let detached its predicate from the instantiated type"
  | .ok _ => throw (IO.userError "Eq<Word> evidence was reused for Bool")

private def testQualifiedLocalSchemeRequirements : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "impl Eq<Word> {}",
    "impl Eq<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "  let f = lam(value) { return keep(value); };",
    "  return (f(1), f(flag));",
    "}"
  ]
  let loaded ← load source
  let checked ← match SourceInference.checkLoadedProgram loaded with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"qualified local inference failed: {reprStr errors}")
  let function ← checkedNamed loaded.environment checked "run"
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  let binder ← match function.typedBody.nodes.filterMap fun
      | .statement { form := .letDecl binder (some _), .. } =>
          if binder.name == "f" then some binder else none
      | _ => none with
    | [binder] => pure binder
    | binders => throw (IO.userError
        s!"qualified local fixture retained {binders.length} f binders")
  let (quantified, template) ←
    match binder.scheme.quantified, binder.scheme.body,
        binder.schemeRequirements with
    | [quantified], .function (.variable parameter) (.variable result),
        [requirement] =>
        if quantified == parameter && parameter == result &&
            requirement.predicate.trait == .declaration eq &&
            requirement.predicate.subject == .variable quantified &&
            requirement.predicate.arguments.isEmpty then
          pure (quantified, requirement)
        else
          throw (IO.userError
            "qualified local scheme did not retain Eq<α> with its shared binder")
    | _, _, _ => throw (IO.userError
        "qualified local scheme did not retain one quantified requirement")
  let templateSolved ← match function.solvedRequirements.find? fun solved =>
      solved.id == template.templateRequirement with
    | some solved => pure solved
    | none => throw (IO.userError
        "qualified local template requirement was removed from the ledger")
  assertTrue (match templateSolved.evidence with
    | .assumption predicate =>
        predicate == templateSolved.predicate &&
          predicate.trait == .declaration eq &&
          predicate.subject == .variable quantified
    | _ => false)
    "qualified local template requirement was resolved instead of retained as an assumption"
  let references := function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
        | .reference _ (.local candidate) =>
            if candidate == binder.id then some node else none
        | _ => none
    | .statement _ => none
  let validatesReference (expected : TypeSystem.Ty)
      (node : SourceInference.ExpressionNode) : Bool :=
    node.rawType == .function expected expected &&
      match node.requirements with
      | [requirement] =>
          requirement != template.templateRequirement &&
            match function.solvedRequirements.find? fun solved =>
                solved.id == requirement with
            | some solved =>
                solved.predicate.trait == .declaration eq &&
                  solved.predicate.subject == expected &&
                  solved.predicate.arguments.isEmpty &&
                  match solved.evidence with
                  | .implementation (.byImpl goal _ _) =>
                      goal == solved.predicate
                  | _ => false
            | none => false
      | _ => false
  assertTrue (references.length == 2 &&
      references.any (validatesReference .word) &&
      references.any (validatesReference .bool))
    "qualified local references did not freshen type and Eq evidence together"

private def testNestedQualifiedRequirementOwnership : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "  let outer = lam(value) {",
    "    let inner = lam(item) { return keep(item); };",
    "    return value;",
    "  };",
    "  return (outer(1), outer(flag));",
    "}"
  ]
  let loaded ← load source
  let checked ← match SourceInference.checkLoadedProgram loaded with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"nested qualified ownership failed: {reprStr errors}")
  let function ← checkedNamed loaded.environment checked "run"
  let binders := function.typedBody.nodes.filterMap fun
    | .statement { form := .letDecl binder (some _), .. } => some binder
    | _ => none
  let outer ← match binders.find? fun binder => binder.name == "outer" with
    | some binder => pure binder
    | none => throw (IO.userError "nested qualified fixture lost outer")
  let inner ← match binders.find? fun binder => binder.name == "inner" with
    | some binder => pure binder
    | none => throw (IO.userError "nested qualified fixture lost inner")
  let template ← match inner.schemeRequirements with
    | [requirement] => pure requirement
    | requirements => throw (IO.userError
        s!"inner retained {requirements.length} qualified requirements")
  let owners := binders.filter fun binder =>
    binder.schemeRequirements.any fun requirement =>
      requirement.templateRequirement == template.templateRequirement
  assertTrue (decide (outer.schemeRequirements = [] ∧ owners = [inner]))
    "an outer local scheme recaptured its nested binder's template requirement"

private def testOperatorMethodPredicates : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Noise<T> {}",
    "trait Add<T> {",
    "  function tag(value: T) returns (T) where T: Noise;",
    "  function add(left: T, right: T) returns (T) where T: Eq;",
    "}",
    "trait BitNot<T> {",
    "  function bnot(value: T) returns (T) where T: Eq;",
    "}",
    "function addWithMethodEvidence<T>(left: T, right: T) returns (T)",
    "    where T: Add, T: Eq {",
    "  return left + right;",
    "}",
    "function bitNotWithMethodEvidence<T>(value: T) returns (T)",
    "    where T: BitNot, T: Eq {",
    "  return ~value;",
    "}"
  ]
  let loaded ← load source
  let checked ← match SourceInference.checkLoadedProgram loaded with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"operator method predicates were rejected: {reprStr errors}")
  let addition ← checkedNamed loaded.environment checked
    "addWithMethodEvidence"
  let bitNot ← checkedNamed loaded.environment checked
    "bitNotWithMethodEvidence"
  let names (function : SourceInference.CheckedFunction) :=
    function.solvedRequirements.map fun solved =>
      traitNameOf loaded.environment solved.predicate
  let assumptionEvidence (function : SourceInference.CheckedFunction) :=
    function.solvedRequirements.all fun solved =>
      match solved.evidence with
      | .assumption predicate => predicate == solved.predicate
      | .implementation _ => false
  assertTrue (decide (names addition = [some "Add", some "Eq"]) &&
      assumptionEvidence addition)
    "binary inference did not retain Add<T>, Eq<T> in declaration order"
  assertTrue (decide (names bitNot = [some "BitNot", some "Eq"]) &&
      assumptionEvidence bitNot)
    "unary inference did not retain BitNot<T>, Eq<T> in declaration order"

private def testUnsolvedOperatorMethodPredicates : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T) where T: Eq;",
    "}",
    "trait BitNot<T> {",
    "  function bnot(value: T) returns (T) where T: Eq;",
    "}",
    "function rejectAdd<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}",
    "function rejectBitNot<T>(value: T) returns (T) where T: BitNot {",
    "  return ~value;",
    "}"
  ]
  let loaded ← load source
  let eq ← match loaded.environment.traitsNamed "Eq" with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one Eq trait, found {declarations.length}")
  match SourceInference.checkLoadedProgram loaded with
  | .error errors =>
      let unsolved := errors.filter fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            decide (predicate.trait = eq)
        | _ => false
      assertTrue (unsolved.length == 2)
        "a binary or unary method predicate was accepted without Eq<T>"
  | .ok _ => throw (IO.userError
      "operator method predicates were accepted without Eq<T>")

private def testOperatorMethodCatalogDiagnostics : IO Unit := do
  let missingSource := String.intercalate "\n" [
    "trait Add<T> {",
    "  function tag(value: T) returns (T);",
    "}",
    "function reject<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace missingSource) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .missingOperatorTraitMethod _ "add", .. } => true
        | _ => false)
        "a trait catalog without the named add method lost its diagnostic"
  | .ok _ => throw (IO.userError
      "a trait catalog without the named add method was accepted")

  let malformedSource := String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(value: T) returns (Bool);",
    "}",
    "function reject<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace malformedSource) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := (.operatorTraitMethodSignatureMismatch _ "add"
            expectedParameters actualParameters expectedReturns actualReturns),
            .. } => decide (expectedParameters.length = 2 ∧
              actualParameters.length = 1 ∧ expectedReturns.length = 1 ∧
              actualReturns = [.bool])
        | _ => false)
        "a malformed add method lost its operator-signature diagnostic"
  | .ok _ => throw (IO.userError
      "a malformed add method was accepted as binary operator semantics")

  let duplicateSource := String.intercalate "\n" [
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T);",
    "}",
    "function reject<T>(left: T, right: T) returns (T) where T: Add {",
    "  return left + right;",
    "}"
  ]
  let loaded ← load duplicateSource
  let signatures ← match buildProgramSignatures loaded.environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"operator catalog fixture failed: {reprStr errors}")
  let add ← match signatures.traits.filter fun trait => trait.name == "Add" with
    | [trait] => pure trait
    | traits => throw (IO.userError
        s!"expected one Add catalog, found {traits.length}")
  let method ← match add.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"expected one Add method, found {methods.length}")
  let duplicate := {
    method with id := { method.id with methodIndex := method.id.methodIndex + 1 }
  }
  let tampered := {
    signatures with
    traits := signatures.traits.map fun trait =>
      if trait.id = add.id then { trait with methods := trait.methods ++ [duplicate] }
      else trait
  }
  match SourceInference.checkFunctionBodies loaded.environment tampered with
  | .error errors =>
      assertTrue (errors.any fun error => match error.error with
        | .duplicateOperatorTraitMethod trait "add" 2 => trait == add.id
        | _ => false)
        "a duplicate named operator method lost its defensive diagnostic"
  | .ok _ => throw (IO.userError
      "a duplicate named operator method was selected silently")

private def testAmbiguousCoercionTrait : IO Unit := do
  let raw : Workspace.RawWorkspace := {
    entry := "main.solc"
    mainSources := [
      { path := "left.solc", content :=
          "export {Coerce}; trait Coerce<From, To> {}" },
      { path := "right.solc", content :=
          "export {Coerce}; trait Coerce<From, To> {}" },
      {
        path := "main.solc"
        content := String.intercalate "\n" [
          "import * from left;",
          "import * from right;",
          "function accept(value: Bool) returns (Bool) { return value; }",
          "function reject(value: Word) returns (Bool) { return accept(value); }"
        ]
      }
    ]
    externalLibraries := []
  }
  match SourceInference.loadAndCheckProgram raw with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOperatorTrait "Coerce" candidates, .. } =>
            candidates.length == 2
        | _ => false) "ambiguous Coerce declarations lost their diagnostic"
  | .ok _ => throw (IO.userError "ambiguous Coerce declaration was selected")

private def testGenericBodyAnnotationFormation : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function keep<T>(value: T) returns (T) {",
    "  let local: T = value;",
    "  return local;",
    "}"
  ])
  assertTrue (checked.length == 1)
    "a declaration-owned generic body annotation failed formation validation"

private def testRecoveryBodyAnnotationFormation : IO Unit := do
  match SourceInference.Detail.resolveSourceType solverRegressionContext
      solverRegressionRecoveryType with
  | .error (.typeFormation (.recoveryType owner)) =>
      assertTrue (owner == solverRegressionOwner)
        "a recovery body annotation lost its declaration owner"
  | .error error => throw (IO.userError
      s!"a recovery body annotation produced the wrong error: {reprStr error}")
  | .ok type => throw (IO.userError
      s!"a recovery body annotation was accepted as {reprStr type}")

/-- Exercise parsed lambdas, local schemes, tuples, grouping, conditionals,
operators, contextual integer literals, and explicit deferrals. -/
def testSourceInference : IO Unit := do
  testGenericBodyAnnotationFormation
  testRecoveryBodyAnnotationFormation
  testLambdaLetTupleConditional
  testDiscardedPolymorphicReferenceResidual
  testAmbiguousOverload
  testIntegerLiteralExpectedType
  testClosedUnsupportedIntegerLiteralTarget
  testIntegerLiteralLedgerValidation
  testSourceGraphValidation
  testClosedUnsupportedIntegerPatternTarget
  testSourceNamedLiteralTraitsDoNotAuthorize
  testUnconstrainedIntegerLiteralDefaultsToWord
  testLetBoundIntegerLiteralClosesLater
  testUnusedLetIntegerLiteralDefaultsIndependently
  testLiteralRequirementPreservesIndependentPolymorphism
  testContextualIntegerLiteralOperators
  testNestedIntegerLiteralOperatorsCloseLater
  testUnconstrainedIntegerLiteralOperatorsDefaultToWord
  testDeferredIntegerLiteralOperatorRejections
  testDefaultedIntegerLiteralOperatorsRespectSourceTraits
  testGroundOperatorResultKeepsCoercion
  testUnsupportedStatement
  testTraitBackedCoercion
  testMissingCoercion
  testInconclusiveCoercion
  testUnsolvedCoercionMethodPredicate
  testConstrainedLetDoesNotGeneralizeAwayEvidence
  testQualifiedLocalSchemeRequirements
  testNestedQualifiedRequirementOwnership
  testOperatorMethodPredicates
  testUnsolvedOperatorMethodPredicates
  testOperatorMethodCatalogDiagnostics
  testAmbiguousCoercionTrait

end Tests.SourceInference
