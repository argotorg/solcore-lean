import Solcore.Frontend.SourceInference.Resolution
import Solcore.Frontend.WordLiteral

/-! Fuel-bounded inference for canonical expressions and simple bodies. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

structure StatementResult where
  id : StatementId
  type : Ty
  hasValue : Bool
  sawReturn : Bool
  state : State

structure BlockResult where
  statements : List StatementId
  type : Ty
  sawReturn : Bool
  state : State

def bindLambdaParameters (context : Context) :
    List Syntax.LambdaParameter → Nat → List String → State →
      Except Error (List TypedBinder × List Ty × State)
  | [], _, _, state => .ok ([], [], state)
  | parameter :: rest, index, seen, state => do
      let (name, type, comptime, state) ← match parameter.value with
        | .error => throw (.malformedLambdaParameter index)
        | .inferred name =>
            let (type, state) := state.fresh
            pure (name.value, type, false, state)
        | .typed marker name sourceType =>
            pure (name.value, (← resolveSourceType context sourceType),
              marker.isSome, state)
      if seen.contains name then
        throw (.duplicateLambdaParameter name)
      else
        let (binder, state) :=
          state.allocateBinder name (.mono type) (some parameter.span)
            (comptime := comptime)
        let (binders, types, state) ← bindLambdaParameters context rest
          (index + 1) (name :: seen) state
        pure (binder :: binders, type :: types, state)

/-- Keep every literal created in the current argument subtree, plus an older
literal whose still-flexible target flows through an argument type.  The
second case covers monomorphic let-bound literals without making unrelated
earlier literals affect overload ranking. -/
def relevantIntegerLiterals (state : State) (start : Nat)
    (arguments : List InferredExpression) : List IntegerLiteralOrigin :=
  let introduced := state.integerLiterals.drop start
  state.integerLiterals.filter fun origin =>
    introduced.contains origin ||
      (state.resolve (.variable origin.metavariable)).freeVariables.any
        fun metavariable => arguments.any fun argument =>
          (state.resolve argument.type).freeVariables.contains metavariable

structure GeneralizedValue where
  scheme : Scheme
  requirements : List LocalSchemeRequirement

private def requirementVariables (state : State)
    (requirements : List Requirement) : List TypeVarId :=
  requirements.flatMap fun requirement =>
    TypedTraitResolution.predicateVariables
      (applyPredicate state requirement.predicate)

/-- Generalize one local value together with the proof-only declaration-call
requirements introduced while inferring its initializer.  Every older
requirement, and every new operational requirement, continues to block its
variables exactly as before. -/
def generalizeValue (state : State) (locals : TypeSystem.Environment)
    (requirementStart : Nat) (type : Ty) : GeneralizedValue :=
  let priorRequirements := state.requirements.take requirementStart
  let introducedRequirements := state.requirements.drop requirementStart
  let eligibleRequirements := introducedRequirements.filter fun requirement =>
    state.directCallRequirements.contains requirement.id &&
      !state.localSchemeAssumptions.contains requirement.id
  let operationalRequirements := introducedRequirements.filter fun requirement =>
    !state.directCallRequirements.contains requirement.id
  let blockedVariables := locals.freeVariables ++
    requirementVariables state (priorRequirements ++ operationalRequirements)
  let quantified := type.freeVariables.filter fun metavariable =>
    !(blockedVariables.contains metavariable)
  let requirements := eligibleRequirements.filterMap fun requirement =>
    let predicate := applyPredicate state requirement.predicate
    let dependsOnQuantified :=
      (TypedTraitResolution.predicateVariables predicate).any fun metavariable =>
        quantified.contains metavariable
    if dependsOnQuantified then
      some {
        templateRequirement := requirement.id
        predicate
      }
    else
      none
  {
    scheme := {
      quantified
      body := type
    }
    requirements
  }

/-- Local generalization retains the inferred value type as the scheme body. -/
@[simp] theorem generalizeValue_scheme_body (state : State)
    (locals : TypeSystem.Environment) (requirementStart : Nat) (type : Ty) :
    (generalizeValue state locals requirementStart type).scheme.body = type := by
  rfl

/-- Local generalization quantifies each flexible metavariable at most once. -/
theorem generalizeValue_scheme_quantified_nodup (state : State)
    (locals : TypeSystem.Environment) (requirementStart : Nat) (type : Ty) :
    (generalizeValue state locals requirementStart type).scheme.quantified.Nodup := by
  simp only [generalizeValue]
  exact (Ty.freeVariables_nodup type).filter _

private theorem generalizeValue_requirement_witness
    (state : State) (locals : TypeSystem.Environment)
    (requirementStart : Nat) (type : Ty) (template : LocalSchemeRequirement)
    (member : template ∈
      (generalizeValue state locals requirementStart type).requirements) :
    ∃ rawRequirement, rawRequirement ∈ state.requirements ∧
      rawRequirement.id = template.templateRequirement ∧
      template.predicate = applyPredicate state rawRequirement.predicate ∧
      ∃ metavariable,
        metavariable ∈
          (generalizeValue state locals requirementStart type).scheme.quantified ∧
        metavariable ∈
          TypedTraitResolution.predicateVariables template.predicate := by
  let introducedRequirements := state.requirements.drop requirementStart
  let eligibleRequirements := introducedRequirements.filter fun requirement =>
    state.directCallRequirements.contains requirement.id &&
      !state.localSchemeAssumptions.contains requirement.id
  let blockedVariables := locals.freeVariables ++
    requirementVariables state
      (state.requirements.take requirementStart ++
        introducedRequirements.filter fun requirement =>
          !state.directCallRequirements.contains requirement.id)
  let quantified := type.freeVariables.filter fun metavariable =>
    !(blockedVariables.contains metavariable)
  let select : Requirement → Option LocalSchemeRequirement := fun requirement =>
    let predicate := applyPredicate state requirement.predicate
    let dependsOnQuantified :=
      (TypedTraitResolution.predicateVariables predicate).any fun metavariable =>
        quantified.contains metavariable
    if dependsOnQuantified then
      some { templateRequirement := requirement.id, predicate }
    else
      none
  change template ∈ eligibleRequirements.filterMap select at member
  rw [List.mem_filterMap] at member
  obtain ⟨rawRequirement, rawMember, produced⟩ := member
  simp only [select] at produced
  split at produced
  · rename_i dependsOnQuantified
    injection produced with templateEq
    subst template
    obtain ⟨metavariable, predicateMember, quantifiedMember⟩ :=
      List.any_eq_true.mp dependsOnQuantified
    have eligibleSublist : eligibleRequirements.Sublist state.requirements :=
      List.filter_sublist.trans (List.drop_sublist _ _)
    refine ⟨rawRequirement, eligibleSublist.subset rawMember, rfl, rfl,
      metavariable, ?_, predicateMember⟩
    simpa [generalizeValue, introducedRequirements, eligibleRequirements,
      blockedVariables, quantified]
      using quantifiedMember
  · contradiction

/-- Every retained local-scheme row depends on a metavariable quantified by
the generalized scheme. -/
theorem generalizeValue_requirement_depends_on_quantified
    (state : State) (locals : TypeSystem.Environment)
    (requirementStart : Nat) (type : Ty) (requirement : LocalSchemeRequirement)
    (member : requirement ∈
      (generalizeValue state locals requirementStart type).requirements) :
    ∃ metavariable,
      metavariable ∈
        (generalizeValue state locals requirementStart type).scheme.quantified ∧
      metavariable ∈
        TypedTraitResolution.predicateVariables requirement.predicate := by
  obtain ⟨_, _, _, _, witness⟩ :=
    generalizeValue_requirement_witness state locals requirementStart type
      requirement member
  exact witness

/-- A monomorphic generalization cannot retain qualified requirements: every
retained row must mention at least one variable quantified by the scheme. -/
theorem generalizeValue_requirements_empty_of_quantified_eq_nil
    (state : State) (locals : TypeSystem.Environment)
    (requirementStart : Nat) (type : Ty)
    (quantifiedEmpty :
      (generalizeValue state locals requirementStart type).scheme.quantified =
        []) :
    (generalizeValue state locals requirementStart type).requirements = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro requirement member
  obtain ⟨metavariable, quantifiedMember, _⟩ :=
    generalizeValue_requirement_depends_on_quantified state locals
      requirementStart type requirement member
  rw [quantifiedEmpty] at quantifiedMember
  simp at quantifiedMember

/-- Every retained local-scheme row comes from a raw inference-ledger row
with the same identity and its predicate under the final substitution. -/
theorem generalizeValue_requirement_source
    (state : State) (locals : TypeSystem.Environment)
    (requirementStart : Nat) (type : Ty) (requirement : LocalSchemeRequirement)
    (member : requirement ∈
      (generalizeValue state locals requirementStart type).requirements) :
    ∃ rawRequirement, rawRequirement ∈ state.requirements ∧
      rawRequirement.id = requirement.templateRequirement ∧
      requirement.predicate = applyPredicate state rawRequirement.predicate := by
  obtain ⟨rawRequirement, rawMember, idEq, predicateEq, _⟩ :=
    generalizeValue_requirement_witness state locals requirementStart type
      requirement member
  exact ⟨rawRequirement, rawMember, idEq, predicateEq⟩

private theorem filterMap_templateRequirementIds_sublist
    (requirements : List Requirement)
    (select : Requirement → Option LocalSchemeRequirement)
    (selectedId : ∀ requirement template,
      select requirement = some template →
      template.templateRequirement = requirement.id) :
    ((requirements.filterMap select).map
      (fun requirement => requirement.templateRequirement)).Sublist
      (requirements.map (fun requirement => requirement.id)) := by
  induction requirements with
  | nil => exact .slnil
  | cons requirement rest induction =>
      cases selected : select requirement with
      | none =>
          simp only [List.filterMap_cons, selected, List.map_cons]
          exact .cons _ induction
      | some template =>
          simp only [List.filterMap_cons, selected, List.map_cons]
          rw [selectedId requirement template selected]
          exact .cons_cons _ induction

/-- Every template identity retained by local generalization comes from the
input state's requirement ledger. -/
theorem generalizeValue_templateIds_sublist (state : State)
    (locals : TypeSystem.Environment) (requirementStart : Nat) (type : Ty) :
    ((generalizeValue state locals requirementStart type).requirements.map
      (fun requirement => requirement.templateRequirement)).Sublist
      (state.requirements.map (fun requirement => requirement.id)) := by
  let introducedRequirements := state.requirements.drop requirementStart
  let eligibleRequirements := introducedRequirements.filter fun requirement =>
    state.directCallRequirements.contains requirement.id &&
      !state.localSchemeAssumptions.contains requirement.id
  let blockedVariables := locals.freeVariables ++
    requirementVariables state
      (state.requirements.take requirementStart ++
        introducedRequirements.filter fun requirement =>
          !state.directCallRequirements.contains requirement.id)
  let quantified := type.freeVariables.filter fun metavariable =>
    !(blockedVariables.contains metavariable)
  let select : Requirement → Option LocalSchemeRequirement := fun requirement =>
    let predicate := applyPredicate state requirement.predicate
    let dependsOnQuantified :=
      (TypedTraitResolution.predicateVariables predicate).any fun metavariable =>
        quantified.contains metavariable
    if dependsOnQuantified then
      some { templateRequirement := requirement.id, predicate }
    else
      none
  have selected :
      ((eligibleRequirements.filterMap select).map
        (fun requirement => requirement.templateRequirement)).Sublist
        (eligibleRequirements.map (fun requirement => requirement.id)) := by
    apply filterMap_templateRequirementIds_sublist
    intro requirement template produced
    simp only [select] at produced
    split at produced
    · cases produced
      rfl
    · contradiction
  have eligible : eligibleRequirements.Sublist state.requirements := by
    exact List.filter_sublist.trans (List.drop_sublist _ _)
  change ((eligibleRequirements.filterMap select).map
      (fun requirement => requirement.templateRequirement)).Sublist
    (state.requirements.map (fun requirement => requirement.id))
  exact selected.trans (eligible.map _)

private theorem requirementId_beq_iff_eq
    (left right : RequirementId) : (left == right) = true ↔ left = right := by
  rw [show (left == right) = (left.index == right.index) by rfl]
  rw [beq_iff_eq]
  constructor
  · intro indicesEq
    cases left
    cases right
    cases indicesEq
    rfl
  · intro same
    exact congrArg RequirementId.index same

private theorem requirementId_contains_iff_mem
    (ids : List RequirementId) (id : RequirementId) :
    ids.contains id = true ↔ id ∈ ids := by
  induction ids with
  | nil => simp
  | cons head tail induction =>
      simp only [List.contains_cons, List.mem_cons]
      rw [Bool.or_eq_true, requirementId_beq_iff_eq, induction]

/-- Canonical local generalization never reclassifies an identity that was
already owned by an enclosing local scheme. -/
theorem generalizeValue_templateIds_fresh (state : State)
    (locals : TypeSystem.Environment) (requirementStart : Nat) (type : Ty)
    (id : RequirementId)
    (member : id ∈
      (generalizeValue state locals requirementStart type).requirements.map
        (fun requirement => requirement.templateRequirement)) :
    id ∉ state.localSchemeAssumptions := by
  let introducedRequirements := state.requirements.drop requirementStart
  let eligibleRequirements := introducedRequirements.filter fun requirement =>
    state.directCallRequirements.contains requirement.id &&
      !state.localSchemeAssumptions.contains requirement.id
  let blockedVariables := locals.freeVariables ++
    requirementVariables state
      (state.requirements.take requirementStart ++
        introducedRequirements.filter fun requirement =>
          !state.directCallRequirements.contains requirement.id)
  let quantified := type.freeVariables.filter fun metavariable =>
    !(blockedVariables.contains metavariable)
  let select : Requirement → Option LocalSchemeRequirement := fun requirement =>
    let predicate := applyPredicate state requirement.predicate
    let dependsOnQuantified :=
      (TypedTraitResolution.predicateVariables predicate).any fun metavariable =>
        quantified.contains metavariable
    if dependsOnQuantified then
      some { templateRequirement := requirement.id, predicate }
    else
      none
  change id ∈ (eligibleRequirements.filterMap select).map
      (fun requirement => requirement.templateRequirement) at member
  rw [List.mem_map] at member
  obtain ⟨template, templateMember, idEq⟩ := member
  rw [List.mem_filterMap] at templateMember
  obtain ⟨requirement, requirementMember, produced⟩ := templateMember
  simp only [select] at produced
  split at produced
  · injection produced with templateEq
    subst template
    subst id
    have selected := (List.mem_filter.mp requirementMember).2
    have absent := (Bool.and_eq_true_iff.mp selected).2
    intro oldMember
    have present : state.localSchemeAssumptions.contains requirement.id = true :=
      (requirementId_contains_iff_mem _ _).mpr oldMember
    simp [present] at absent
  · contradiction

def coercionRequirements (coercions : List CoercionStep) :
    List RequirementId :=
  coercions.flatMap (·.requirements)

private def nominalTypeParts? (type : Ty) :
    Option (Resolved.DeclarationId × List Ty) :=
  let rec loop (type : Ty) (arguments : List Ty) :=
    match type with
    | .application function argument => loop function (argument :: arguments)
    | .constructor (.declaration declaration) => some (declaration, arguments)
    | _ => none
  loop type []

private structure AccessibleDataType where
  signature : ProgramDataSignature
  constructors : ProgramConstructorVisibility

private def fullyAccessibleDataType
    (signature : ProgramDataSignature) : AccessibleDataType := {
  signature
  constructors := .ofVisible (signature.constructors.map (·.name))
}

private def dataSignaturesForImportedTypes (context : Context)
    (types : List ProgramImportedType) : List AccessibleDataType :=
  types.filterMap fun imported => do
    let signature ← context.signatures.dataType? imported.declaration.id
    pure { signature, constructors := imported.constructors }

private def dataSignaturesForPublicEntities (context : Context)
    (entities : List ProgramPublicEntity) : List AccessibleDataType :=
  entities.filterMap fun entity => do
    let signature ← context.signatures.dataType? entity.declaration.id
    pure { signature, constructors := entity.constructors }

private def visibleDataTypesNamed (context : Context) (name : String) :
    Except Error (List AccessibleDataType) :=
  let localDataTypes := context.signatures.dataTypes.filter fun dataType =>
    dataType.name == name &&
      decide (dataType.id.moduleId = context.scope.currentModule)
  if !localDataTypes.isEmpty then
    pure (localDataTypes.map fullyAccessibleDataType)
  else
    match buildProgramImports context.environment context.scope.currentModule with
    | .error errors => throw (.importVisibility errors)
    | .ok visibility =>
        pure (dataSignaturesForImportedTypes context
          (visibility.typeBindingsNamed name))

private def qualifiedDataTypesNamed (context : Context)
    (qualifiers : List String) : Except Error (List AccessibleDataType) := do
  let typeName ← match qualifiers.getLast? with
    | some name => pure name
    | none => pure ""
  let modulePath := qualifiers.dropLast
  if modulePath.isEmpty then
    visibleDataTypesNamed context typeName
  else
    match buildProgramImports context.environment context.scope.currentModule with
    | .error errors => throw (.importVisibility errors)
    | .ok visibility =>
        if visibility.hasNamespaceRoot modulePath then
          pure (dataSignaturesForPublicEntities context
            (visibility.typeEntitiesInNamespacePathNamed modulePath typeName))
        else
          pure []

private def constructorsInDataTypes (dataTypes : List AccessibleDataType)
    (name : String) :
    List (ProgramDataSignature × ProgramDataConstructorSignature) :=
  dataTypes.flatMap fun dataType =>
    dataType.signature.constructors.filterMap fun constructor =>
      if constructor.name == name && dataType.constructors.contains name then
        some (dataType.signature, constructor)
      else none

private def exactConstructorCandidate (qualifiers : List String) (name : String) :
    List (ProgramDataSignature × ProgramDataConstructorSignature) →
      Except Error (ProgramDataSignature × ProgramDataConstructorSignature)
  | [] => throw (.unknownConstructor qualifiers name)
  | [candidate] => pure candidate
  | candidates => throw (.ambiguousConstructor qualifiers name
      (candidates.map fun candidate => candidate.2.id))

private def explicitConstructorCandidate (context : Context)
    (qualifiers : List String) (name : String) :
    Except Error (ProgramDataSignature × ProgramDataConstructorSignature) := do
  exactConstructorCandidate qualifiers name
    (constructorsInDataTypes (← qualifiedDataTypesNamed context qualifiers) name)

private def contextualConstructorCandidate (context : Context) (state : State)
    (expected : Option Ty) (name : String) :
    Except Error (ProgramDataSignature × ProgramDataConstructorSignature × List Ty) := do
  let expected ← match expected with
    | some expected => pure (state.resolve expected)
    | none => throw (.constructorNeedsExpectedType name)
  let (declaration, arguments) ← match nominalTypeParts? expected with
    | some parts => pure parts
    | none => throw (.constructorNeedsExpectedType name)
  let dataType ← match context.signatures.dataType? declaration with
    | some dataType => pure dataType
    | none => throw (.unknownConstructor [] name)
  let constructorVisibility ←
    if decide (dataType.id.moduleId = context.scope.currentModule) then
      pure (fullyAccessibleDataType dataType).constructors
    else
      match buildProgramImports context.environment context.scope.currentModule with
      | .error errors => throw (.importVisibility errors)
      | .ok visibility =>
          pure <| (visibility.constructorVisibilityForDeclaration? dataType.id).getD
            .opaqueData
  let constructor ← exactConstructorCandidate [] name
    (constructorsInDataTypes [{
      signature := dataType
      constructors := constructorVisibility
    }] name)
  pure (constructor.1, constructor.2, arguments)

private def instantiateDataConstructor
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature)
    (arguments : List Ty) : DataConstructorInstantiation :=
  let parameterSubstitution := dataType.parameters.zip arguments
  {
    constructor := constructor.id
    parameterSubstitution
    payloadTypes := constructor.payloadTypes.map fun type =>
      TypeSystem.ParameterSubstitution.apply parameterSubstitution type
    resultType := Ty.nominal dataType.id arguments
  }

def freshDataConstructorInstantiation
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature)
    (state : State) : DataConstructorInstantiation × State :=
  let (arguments, state) := dataType.parameters.foldl
    (fun (result : List Ty × State) _ =>
      let (type, state) := result.2.fresh
      (result.1 ++ [type], state)) ([], state)
  (instantiateDataConstructor dataType constructor arguments, state)

private def constructorCalleeCandidates (context : Context) (state : State)
    (callee : Syntax.Expr) :
    Except Error
      (List (ProgramDataSignature × ProgramDataConstructorSignature)) := do
  match calleeQualifiedIdentifier? callee with
  | some (qualifiers, name) =>
      match qualifiers with
      | root :: _ =>
          if (state.lookupBinder? root).isSome then pure []
          else
            pure (constructorsInDataTypes
              (← qualifiedDataTypesNamed context qualifiers) name)
      | [] => pure []
  | none =>
      match calleeIdentifier? callee with
      | none => pure []
      | some name =>
          if (state.lookupBinder? name).isSome then pure []
          else
            pure (constructorsInDataTypes
              ((← visibleDataTypesNamed context name).filter fun dataType =>
                dataType.signature.name == name) name)

/-- Distinguish an existing data namespace with a missing constructor from an
ordinary qualified function/member expression.  Local roots continue to shadow
type namespaces. -/
private def missingExplicitConstructor? (context : Context) (state : State)
    (callee : Syntax.Expr) : Except Error (Option (List String × String)) := do
  match calleeQualifiedIdentifier? callee with
  | some (qualifiers, name) =>
      match qualifiers with
      | root :: _ =>
          if (state.lookupBinder? root).isSome then pure none
          else
            let dataTypes ← qualifiedDataTypesNamed context qualifiers
            if dataTypes.isEmpty then pure none
            else if (constructorsInDataTypes dataTypes name).isEmpty then
              pure (some (qualifiers, name))
            else pure none
      | [] => pure none
  | none => pure none

def attachExpressionCoercions (state : State)
    (entries : List ExpressionCoercions) : State :=
  entries.foldl (fun state entry =>
    state.modifyExpressionNode entry.expression fun node => {
      node with
      type := entry.coercions.foldl (fun _ step => step.target) node.type
      requirements := node.requirements ++ coercionRequirements entry.coercions
      coercions := node.coercions ++ entry.coercions
    }) state

def recordExpression (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State) :
    InferredExpression × State :=
  let node : ExpressionNode := {
    id := expression.id
    span := source.span
    type := expression.type
    form
    requirements
    coercions
  }
  (expression, state.recordNode (.expression node))

def recordExpressionWithExpected (context : Context) (source : Syntax.Expr)
    (id : ExpressionId) (type : Ty) (form : ExpressionForm)
    (requirements : List RequirementId) (expected : Option Ty) (state : State) :
    Except Error (InferredExpression × State) := do
  let fitted ← withExpected context state { id, type } expected
  pure <| recordExpression source fitted.expression form
    (requirements ++ coercionRequirements fitted.coercions)
    fitted.coercions fitted.state

def recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    InferredExpression × State :=
  let state := attachExpressionCoercions state attempt.argumentCoercions
  let (calleeId, state) := state.allocateExpressionId
  let calleeExpression : InferredExpression := {
    id := calleeId
    type := state.resolve attempt.instantiation.type
  }
  let (_, state) := recordExpression callee calleeExpression
    (.reference name (.declaration attempt.instantiation)) [] [] state
  recordExpression source result
    (.call calleeId (arguments.map (·.id))
      (.declaration attempt.instantiation))
    (coercionRequirements attempt.callCoercions ++
      attempt.signatureRequirements ++
      coercionRequirements trailingCoercions)
    (attempt.callCoercions ++ trailingCoercions) state

def recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    InferredExpression × State :=
  recordSelectedCallResult source callee name arguments attempt
    attempt.result [] attempt.state

def recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    InferredExpression × State :=
  let argumentType := Ty.productMany (arguments.map (·.type))
  let coercedArgumentType := result.argumentCoercions.foldl
    (fun _ step => step.target) argumentType
  recordExpression source result.result
    (.call callee.id (arguments.map (·.id)) (.indirect {
      argumentCount := arguments.length
      argumentTypeBeforeCoercion := argumentType
      argumentTypeAfterCoercion := coercedArgumentType
      argumentCoercions := result.argumentCoercions
    }))
    (coercionRequirements result.argumentCoercions ++
      coercionRequirements result.callCoercions)
    result.callCoercions result.state

def unifyBuiltinFunctionArgumentsEqual :
    List InferredExpression → List Ty → State → Except Error State
  | [], _, state => .ok state
  | _, [], state => .ok state
  | argument :: arguments, parameter :: parameters, state => do
      let state ← unify state argument.type parameter
      unifyBuiltinFunctionArgumentsEqual arguments parameters state

/-- Check one fixed compiler-function signature without overload, coercion, or
source-declaration metadata.  The caller has already established that no
source-visible function shadows this lowest-priority fallback. -/
def recordBuiltinFunctionCall (source callee : Syntax.Expr) (name : String)
    (function : BuiltinFunctionId) (arguments : List InferredExpression)
    (call : ExpressionId) (expected : Option Ty) (state : State) :
    Except Error (InferredExpression × State) := do
  let parameters := function.parameterTypes
  unless arguments.length = parameters.length do
    throw (.builtinFunctionArityMismatch function parameters.length
      arguments.length)
  let state ← unifyBuiltinFunctionArgumentsEqual arguments parameters state
  let state ← match expected with
    | none => pure state
    | some expected => unify state function.returnType expected
  let (calleeId, state) := state.allocateExpressionId
  let calleeExpression : InferredExpression := {
    id := calleeId
    type := function.type
  }
  let (_, state) := recordExpression callee calleeExpression
    (.reference name (.builtinFunction function)) [] [] state
  let result : InferredExpression := {
    id := call
    type := state.resolve function.returnType
  }
  pure <| recordExpression source result
    (.call calleeId (arguments.map (·.id)) (.builtinFunction function))
    [] [] state

/-- Result of checking every explicit case in source order. -/
structure MatchCasesResult where
  cases : List TypedMatchCase
  hasWildcard : Bool
  allReturn : Bool
  state : State

structure InferredForItems where
  items : List ForItemForm
  state : State

/-- Internal result of recursively checking one source pattern.  The prefix
instruction stream is self-delimiting because constructor and tuple nodes
retain their child counts. -/
structure InferredPattern where
  source : MatchPatternSource
  resolution : MatchPatternResolution
  instructions : List MatchPatternInstruction
  requirements : List RequirementId
  names : List String
  state : State

structure InferredPatterns where
  instructions : List MatchPatternInstruction
  requirements : List RequirementId
  names : List String
  state : State

def freshTypes : Nat → State → List Ty × State
  | 0, state => ([], state)
  | count + 1, state =>
      let (type, state) := state.fresh
      let (types, state) := freshTypes count state
      (type :: types, state)

mutual

  def inferMatchPatternFlatFuel (fuel : Nat) (context : Context)
      (pattern : Syntax.Pattern) (expected : Ty) (seen : List String)
      (state : State) : Except Error InferredPattern :=
    match fuel with
    | 0 => .error .nestingLimit
    | fuel + 1 => match pattern.value with
      | .wildcard marker =>
          pure {
            source := .wildcard pattern.span marker
            resolution := .wildcard
            instructions := [.wildcard]
            requirements := []
            names := seen
            state
          }
      | .literal literal =>
          match literal.value with
          | value@(.decimal _) | value@(.hexadecimal _) => do
              let rawValue ← match numericLiteralValue? value with
                | some rawValue => pure rawValue
                | none => throw (.unsupportedPattern pattern.span
                    "malformed integer literal")
              let (target, state) := state.fresh
              let .variable metavariable := target
                | throw (.unsupportedPattern pattern.span
                    "integer target allocation")
              let (requirement, state) := state.addRequirementWithId
                (ProgramSignatures.builtinIntPredicate target)
              let origin : IntegerPatternOrigin := {
                metavariable
                span := pattern.span
                requirement
              }
              let state := {
                state with integerPatterns := state.integerPatterns ++ [origin]
              }
              let normalizedExpected := state.resolve expected
              let state ← match normalizedExpected with
                | .variable _ | .constructor (.builtin .word)
                | .constructor (.builtin .integer) =>
                    unify state target normalizedExpected
                | _ => throw (Error.nonNumericPatternType pattern.span
                    normalizedExpected)
              let resolution : IntegerLiteralResolution := {
                rawValue
                targetType := target
                requirement
              }
              pure {
                source := .integerLiteral pattern.span literal
                resolution := .integerLiteral value resolution
                instructions := [.integerLiteral value resolution]
                requirements := [requirement]
                names := seen
                state
              }
          | .string _ =>
              .error (.unsupportedPattern pattern.span "string literal")
      | .binder name => do
          if seen.contains name.value then
            throw (.duplicatePatternBinder name.value)
          let (binder, state) := state.allocateBinder name.value
            (.mono (state.resolve expected)) (some name.span)
          pure {
            source := .binder pattern.span name.value
            resolution := .binder binder
            instructions := [.binder binder]
            requirements := []
            names := seen ++ [name.value]
            state
          }
      | .constructor leadingDot qualifiers name arguments => do
          let qualifierNames := qualifiers.map (·.value)
          let sourceArguments := arguments.map (·.elements.toList) |>.getD []
          let (constructor, instantiation, state) ←
            if leadingDot.isSome || qualifierNames.isEmpty then
              let (dataType, constructor, typeArguments) ←
                contextualConstructorCandidate context state (some expected)
                  name.value
              pure (constructor,
                instantiateDataConstructor dataType constructor typeArguments,
                state)
            else
              let (dataType, constructor) ←
                explicitConstructorCandidate context qualifierNames name.value
              let (instantiation, state) :=
                freshDataConstructorInstantiation dataType constructor state
              pure (constructor, instantiation, state)
          unless sourceArguments.length = instantiation.payloadTypes.length do
            throw (.constructorArityMismatch constructor.id
              instantiation.payloadTypes.length sourceArguments.length)
          let state ← unify state instantiation.resultType expected
          let children ← inferMatchPatternsFlatFuel fuel context sourceArguments
            instantiation.payloadTypes seen state
          let instantiation := {
            instantiation with
            payloadTypes := instantiation.payloadTypes.map children.state.resolve
            resultType := children.state.resolve instantiation.resultType
          }
          pure {
            source := .constructor pattern.span leadingDot qualifierNames
              name.value sourceArguments.length
            resolution := .constructor instantiation children.instructions
            instructions := .constructor instantiation sourceArguments.length ::
              children.instructions
            requirements := children.requirements
            names := children.names
            state := children.state
          }
      | .group inner => do
          let result ← inferMatchPatternFlatFuel fuel context inner expected seen
            state
          pure { result with source := .group pattern.span result.source }
      | .tuple elements => do
          let sources := elements.elements
          let (elementTypes, state) := freshTypes sources.length state
          let state ← unify state expected (Ty.productMany elementTypes)
          let children ← inferMatchPatternsFlatFuel fuel context sources
            elementTypes seen state
          pure {
            source := .tuple pattern.span sources.length
            resolution := .tuple children.instructions
            instructions := .tuple sources.length :: children.instructions
            requirements := children.requirements
            names := children.names
            state := children.state
          }
      | .comptime .. =>
          .error (.unsupportedPattern pattern.span "comptime")
      | .error => .error (.unsupportedPattern pattern.span "parser recovery")

  def inferMatchPatternsFlatFuel (fuel : Nat) (context : Context) :
      List Syntax.Pattern → List Ty → List String → State →
        Except Error InferredPatterns
    | [], [], seen, state => pure {
        instructions := []
        requirements := []
        names := seen
        state
      }
    | pattern :: patterns, expected :: expectedTypes, seen, state => do
        let head ← inferMatchPatternFlatFuel fuel context pattern expected seen
          state
        let tail ← inferMatchPatternsFlatFuel fuel context patterns expectedTypes
          head.names head.state
        pure {
          instructions := head.instructions ++ tail.instructions
          requirements := head.requirements ++ tail.requirements
          names := tail.names
          state := tail.state
        }
    | _, _, _, _ => throw .nestingLimit

end

/-- Check an arbitrary nested source pattern, retaining a first-order prefix
program for execution while entering every binder into the arm scope. -/
def inferMatchPatternFuel (fuel : Nat) (context : Context)
    (pattern : Syntax.Pattern) (expected : Ty) (state : State) :
    Except Error (TypedMatchPattern × State) := do
  let result ← inferMatchPatternFlatFuel fuel context pattern expected [] state
  pure ({
    source := result.source
    type := result.state.resolve expected
    resolution := result.resolution
    requirements := result.requirements
  }, result.state)

mutual

  private def consumeIrrefutableInstruction (fuel : Nat) :
      List MatchPatternInstruction → Option (Bool × List MatchPatternInstruction)
    | [] => none
    | instruction :: rest =>
        match fuel with
        | 0 => none
        | fuel + 1 =>
            match instruction with
            | .wildcard | .binder _ => some (true, rest)
            | .integerLiteral .. => some (false, rest)
            | .constructor _ count => do
                let (_, rest) ← consumeIrrefutableInstructions fuel count rest
                pure (false, rest)
            | .tuple count => consumeIrrefutableInstructions fuel count rest

  private def consumeIrrefutableInstructions (fuel : Nat) :
      Nat → List MatchPatternInstruction →
        Option (Bool × List MatchPatternInstruction)
    | 0, instructions => some (true, instructions)
    | count + 1, instructions => do
        let (head, instructions) ←
          consumeIrrefutableInstruction fuel instructions
        let (tail, instructions) ←
          consumeIrrefutableInstructions fuel count instructions
        pure (head && tail, instructions)

end

private def constructorArgumentsIrrefutable
    (instantiation : DataConstructorInstantiation)
    (instructions : List MatchPatternInstruction) : Bool :=
  match consumeIrrefutableInstructions (instructions.length + 1)
      instantiation.payloadTypes.length instructions with
  | some (true, []) => true
  | _ => false

private def typedPatternIsCatchall (pattern : TypedMatchPattern) : Bool :=
  match pattern.resolution with
  | .wildcard | .binder _ => true
  | .tuple instructions =>
      match pattern.source with
      | .tuple _ count =>
          match consumeIrrefutableInstructions (instructions.length + 1) count
              instructions with
          | some (true, []) => true
          | _ => false
      | _ => false
  | .integerLiteral .. | .constructor .. => false

private def exhaustsNominalConstructors (context : Context) (state : State)
    (scrutineeType : Ty) (cases : List TypedMatchCase) : Bool :=
  match nominalTypeParts? (state.resolve scrutineeType) with
  | none => false
  | some (declaration, _) =>
      match context.signatures.dataType? declaration with
      | none => false
      | some dataType =>
          let covered := cases.filterMap fun arm =>
            match arm.pattern.resolution with
            | .constructor instantiation arguments =>
                if constructorArgumentsIrrefutable instantiation arguments then
                  some instantiation.constructor
                else none
            | _ => none
          dataType.constructors.all fun constructor =>
            covered.contains constructor.id

private def statementIsMatch (statement : Syntax.Statement) : Bool :=
  match statement.value with
  | .matchWith .. => true
  | _ => false

mutual

  def inferExprFuel (fuel : Nat) (context : Context)
      (expression : Syntax.Expr) (expected : Option Ty) (state : State) :
      Except Error (InferredExpression × State) :=
    match fuel with
    | 0 => .error .nestingLimit
    | fuel + 1 =>
      let (id, state) := state.allocateExpressionId
      match expression.value with
      | .literal literal =>
          match literal.value with
          | value@(.decimal _) | value@(.hexadecimal _) => do
              let rawValue ← match numericLiteralValue? value with
                | some rawValue => pure rawValue
                | none => throw (.unsupportedLiteral "malformed integer")
              let (type, state) := state.fresh
              let .variable metavariable := type
                | throw (.unsupportedLiteral "integer target allocation")
              let (requirement, state) := state.addRequirementWithId
                (ProgramSignatures.builtinIntPredicate type)
              let state := {
                state with integerLiterals := state.integerLiterals ++ [{
                  metavariable
                  expression := id
                  requirement
                }]
              }
              recordExpressionWithExpected context expression id type
                (.integerLiteral value {
                  rawValue
                  targetType := type
                  requirement
                }) [requirement] expected state
          | .string _ => .error (.unsupportedLiteral "string")
      | .identifier name =>
          match state.lookupBinder? name.value with
          | some binder =>
              let instantiated :=
                binder.scheme.instantiateWithSubstitution state.inference.next
              let inference := {
                state.inference with next := instantiated.next
              }
              let state := { state with inference }
              let type := state.resolve instantiated.body
              let predicates := binder.schemeRequirements.map fun requirement =>
                applyPredicate state
                  (TypedTraitResolution.applySubstitution
                    instantiated.substitution requirement.predicate)
              let (requirements, state) :=
                state.addRequirementsWithIds predicates
              recordExpressionWithExpected context expression id type
                (.reference name.value (.local binder.id)) requirements expected
                state
          | none =>
              if name.value == "true" || name.value == "false" then
                recordExpressionWithExpected context expression id .bool
                  (.reference name.value
                    (.builtinBoolean (name.value == "true"))) [] expected state
              else do
                match ← functionsNamed context name.value with
                | [] =>
                    match builtinFunctionNamed? name.value with
                    | some function =>
                        recordExpressionWithExpected context expression id
                          function.type
                          (.reference name.value (.builtinFunction function))
                          [] expected state
                    | none => .error (.unknownVariable name.value)
                | [signature] =>
                    let instantiated :=
                      signature.scheme.instantiate state.inference.next
                    let inference := {
                      state.inference with next := instantiated.next
                    }
                    let (requirements, state) :=
                      ({ state with inference }).addRequirementsWithIds
                        instantiated.predicates
                    recordExpressionWithExpected context expression id
                      instantiated.body
                      (.reference name.value (.declaration
                        (DeclarationInstantiation.ofInstantiated
                          signature instantiated)))
                      requirements expected state
                | candidates =>
                    .error (.ambiguousOverload name.value (candidates.map (·.id)))
      | .group inner => do
          let (inner, state) ← inferExprFuel fuel context inner expected state
          recordExpressionWithExpected context expression id inner.type
            (.group inner.id) [] expected state
      | .tuple elements => do
          let (elements, state) ← inferExprsFuel fuel context
            elements.elements state
          recordExpressionWithExpected context expression id
            (Ty.productMany (elements.map (·.type)))
            (.tuple (elements.map (·.id))) [] expected state
      | .unary operator operand => do
          let integerLiteralStart := state.integerLiterals.length
          let (operand, state) ← inferExprFuel fuel context operand none state
          let integerLiterals :=
            relevantIntegerLiterals state integerLiteralStart [operand]
          match unaryOperatorDispatch operator.value with
          | .function name =>
              match ← functionsNamed context name with
              | [] =>
                  let inferred ← inferUnaryOperator context operator.value
                    operand.type expected integerLiterals state
                  recordExpressionWithExpected context expression id
                    inferred.type (.unary operator.value operand.id)
                    inferred.requirements expected inferred.state
              | candidates =>
                  let attempt ← selectFunctionCandidateFrom context name
                    candidates [operand] integerLiterals id expected state
                  let callee : Syntax.Expr := {
                    span := operator.span
                    value := .identifier { span := operator.span, value := name }
                  }
                  pure <| recordSelectedCall expression callee name
                    [operand] attempt
          | .traitMethod _ _ =>
              let inferred ← inferUnaryOperator context operator.value
                operand.type expected integerLiterals state
              recordExpressionWithExpected context expression id inferred.type
                (.unary operator.value operand.id) inferred.requirements expected
                inferred.state
      | .binary left operator right => do
          let integerLiteralStart := state.integerLiterals.length
          let (left, state) ← inferExprFuel fuel context left none state
          let (right, state) ← inferExprFuel fuel context right none state
          let integerLiterals :=
            relevantIntegerLiterals state integerLiteralStart [left, right]
          match binaryOperatorDispatch operator.value with
          | .function name =>
              match ← functionsNamed context name with
              | [] =>
                  let inferred ← inferBinaryOperator context operator.value
                    left.type right.type expected integerLiterals state
                  recordExpressionWithExpected context expression id inferred.type
                    (.binary left.id operator.value right.id)
                    inferred.requirements expected inferred.state
              | candidates =>
                  let attempt ← selectFunctionCandidateFrom context name
                    candidates [left, right] integerLiterals id (some .bool)
                      state
                  let fitted ← withExpected context attempt.state
                    attempt.result expected
                  let callee : Syntax.Expr := {
                    span := operator.span
                    value := .identifier { span := operator.span, value := name }
                  }
                  pure <| recordSelectedCallResult expression callee name
                    [left, right] attempt fitted.expression fitted.coercions
                    fitted.state
          | .traitMethod _ _ =>
              let inferred ← inferBinaryOperator context operator.value
                left.type right.type expected integerLiterals state
              recordExpressionWithExpected context expression id inferred.type
                (.binary left.id operator.value right.id) inferred.requirements
                expected inferred.state
      | .conditional condition _ thenBranch _ elseBranch => do
          let (condition, state) ← inferExprFuel fuel context condition
            (some .bool) state
          let (thenBranch, state) ← inferExprFuel fuel context thenBranch
            expected state
          let (elseBranch, state) ← inferExprFuel fuel context elseBranch
            expected state
          let state ← unify state thenBranch.type elseBranch.type
          recordExpressionWithExpected context expression id
            (state.resolve thenBranch.type)
            (.conditional condition.id thenBranch.id elseBranch.id) []
            expected state
      | .lambda _ parameters returnType body => do
          let outerScope := state.lexicalScope
          let (parameters, parameterTypes, state) ← bindLambdaParameters context
            parameters.elements 0 [] state
          let parameterType := Ty.productMany parameterTypes
          let expectedParts := expected.bind fun type =>
            functionParts? (state.resolve type)
          let state ← match expectedParts with
            | some (expectedParameter, _) =>
                unify state parameterType expectedParameter
            | none => pure state
          let (resultType, state) ← match returnType with
            | some sourceType =>
                pure ((← resolveSourceType context sourceType), state)
            | none =>
                match expectedParts with
                | some (_, result) => pure (result, state)
                | none => pure state.fresh
          let lambdaContext := { context with loopDepth := 0 }
          let bodyResult ← inferStatementsFuel fuel lambdaContext body.value
            resultType state
          let state ← unify bodyResult.state bodyResult.type resultType
          let state := state.restoreLexicalScope outerScope
          recordExpressionWithExpected context expression id
            (.function (state.resolve parameterType) (state.resolve resultType))
            (.lambda parameters (state.resolve resultType)
              bodyResult.statements) [] expected state
      | .call callee arguments => do
          let constructorCandidates ←
            constructorCalleeCandidates context state callee
          match constructorCandidates with
          | [(dataType, constructor)] =>
              let (instantiation, state) :=
                freshDataConstructorInstantiation dataType constructor state
              inferConstructorApplicationFuel fuel context expression id
                instantiation arguments.elements expected state
          | _ :: _ :: _ =>
              let name := (calleeNameComponents? callee).bind (·.getLast?)
                |>.getD "<constructor>"
              throw (.ambiguousConstructor [] name
                (constructorCandidates.map fun candidate => candidate.2.id))
          | [] =>
              match ← missingExplicitConstructor? context state callee with
              | some (qualifiers, name) =>
                  throw (.unknownConstructor qualifiers name)
              | none => pure ()
              let integerLiteralStart := state.integerLiterals.length
              let (arguments, state) ← inferExprsFuel fuel context
                arguments.elements state
              let integerLiterals :=
                relevantIntegerLiterals state integerLiteralStart arguments
              match calleeQualifiedIdentifier? callee with
              | some (namespacePath, name) =>
                  let namespaceName := namespacePath.head!
                  match state.lookupBinder? namespaceName with
                  | some _ =>
                      let (calleeResult, state) ←
                        inferExprFuel fuel context callee none state
                      let result ← applyFunctionType context id calleeResult.type
                        arguments expected state
                      pure <| recordIndirectCall expression calleeResult
                        arguments result
                  | none =>
                      match ← qualifiedFunctionsNamed context namespacePath name with
                      | some candidates =>
                          let displayName :=
                            String.intercalate "." (namespacePath ++ [name])
                          let attempt ← selectFunctionCandidateFrom context
                            displayName candidates arguments integerLiterals id
                            expected state
                          pure <| recordSelectedCall expression callee displayName
                            arguments attempt
                      | none =>
                          let (calleeResult, state) ←
                            inferExprFuel fuel context callee none state
                          let result ← applyFunctionType context id calleeResult.type
                            arguments expected state
                          pure <| recordIndirectCall expression calleeResult
                            arguments result
              | none =>
                  match calleeIdentifier? callee with
                  | some name =>
                      match state.lookupBinder? name with
                      | none => do
                          let candidates ← functionsNamed context name
                          match candidates with
                          | [] =>
                              match builtinFunctionNamed? name with
                              | some function =>
                                  recordBuiltinFunctionCall expression callee name
                                    function arguments id expected state
                              | none => throw (.noMatchingOverload name [])
                          | candidates =>
                              let attempt ← selectFunctionCandidateFrom context name
                                candidates arguments integerLiterals id expected state
                              pure <| recordSelectedCall expression callee name arguments
                                attempt
                      | some _ =>
                          let (calleeResult, state) ←
                            inferExprFuel fuel context callee none state
                          let result ← applyFunctionType context id calleeResult.type
                            arguments expected state
                          pure <| recordIndirectCall expression calleeResult
                            arguments result
                  | none =>
                      let (calleeResult, state) ←
                        inferExprFuel fuel context callee none state
                      let result ← applyFunctionType context id calleeResult.type
                        arguments expected state
                      pure <| recordIndirectCall expression calleeResult arguments result
      | .dotConstructor _ name arguments => do
          let (dataType, constructor, typeArguments) ←
            contextualConstructorCandidate context state expected name.value
          let instantiation := instantiateDataConstructor dataType constructor
            typeArguments
          inferConstructorApplicationFuel fuel context expression id instantiation
            (arguments.map (·.elements) |>.getD []) expected state
      | .proxy _ sourceType => do
          let inner ← resolveSourceType context sourceType
          recordExpressionWithExpected context expression id (.proxy inner)
            (.proxy inner) [] expected state
      | .index base _ index => do
          let (base, state) ← inferExprFuel fuel context base none state
          let (keyType, state) := state.fresh
          let (valueType, state) := state.fresh
          let state ← unify state base.type (.mapping keyType valueType)
          let (index, state) ← inferExprFuel fuel context index
            (some (state.resolve keyType)) state
          recordExpressionWithExpected context expression id
            (state.resolve valueType) (.index base.id index.id) [] expected state
      | .field _ _ name => do
          let candidates ← constructorCalleeCandidates context state expression
          match candidates with
          | [(dataType, constructor)] =>
              let (instantiation, state) :=
                freshDataConstructorInstantiation dataType constructor state
              inferConstructorApplicationFuel fuel context expression id
                instantiation [] expected state
          | [] =>
              match ← missingExplicitConstructor? context state expression with
              | some (qualifiers, missing) =>
                  throw (.unknownConstructor qualifiers missing)
              | none => .error (.unsupportedExpression "field")
          | _ => throw (.ambiguousConstructor [] name.value
              (candidates.map fun candidate => candidate.2.id))
      | .array .. => .error (.unsupportedExpression "array")
      | .error => .error (.unsupportedExpression "parser recovery")

  def inferExprsFuel (fuel : Nat) (context : Context) :
      List Syntax.Expr → State →
        Except Error (List InferredExpression × State)
    | expressions, state =>
      match fuel with
      | 0 => .error .nestingLimit
      | fuel + 1 =>
        match expressions with
        | [] => .ok ([], state)
        | expression :: rest => do
            let (expression, state) ←
              inferExprFuel fuel context expression none state
            let (expressions, state) ←
              inferExprsFuel fuel context rest state
            pure (expression :: expressions, state)

  def inferConstructorArgumentsFuel (fuel : Nat) (context : Context) :
      List Syntax.Expr → List Ty → State →
        Except Error (List InferredExpression × State)
    | [], [], state => pure ([], state)
    | source :: sources, expected :: expectedTypes, state => do
        let (expression, state) ← inferExprFuel fuel context source
          (some (state.resolve expected)) state
        let (expressions, state) ← inferConstructorArgumentsFuel fuel context
          sources expectedTypes state
        pure (expression :: expressions, state)
    | _, _, _ => throw .nestingLimit

  def inferConstructorApplicationFuel (fuel : Nat) (context : Context)
      (source : Syntax.Expr) (id : ExpressionId)
      (instantiation : DataConstructorInstantiation)
      (arguments : List Syntax.Expr) (expected : Option Ty) (state : State) :
      Except Error (InferredExpression × State) := do
    unless arguments.length = instantiation.payloadTypes.length do
      throw (.constructorArityMismatch instantiation.constructor
        instantiation.payloadTypes.length arguments.length)
    let state ← match expected with
      | none => pure state
      | some expected => unify state instantiation.resultType expected
    let (arguments, state) ← inferConstructorArgumentsFuel fuel context
      arguments instantiation.payloadTypes state
    recordExpressionWithExpected context source id
      (state.resolve instantiation.resultType)
      (.constructor instantiation (arguments.map (·.id))) [] expected state

  /-- Resolve the deliberately narrow assignable-place grammar.  A place is
  rooted at a monomorphic local and may traverse mapping indexes; every index
  expression is inferred exactly once and retained by occurrence identity. -/
  def inferPlaceFuel (fuel : Nat) (context : Context)
      (target : Syntax.Expr) (state : State) :
      Except Error (PlaceResolution × State) :=
    match fuel with
    | 0 => throw .nestingLimit
    | fuel + 1 =>
        match target.value with
        | .identifier name =>
            match state.lookupBinder? name.value with
            | some binder =>
                if binder.scheme.quantified.isEmpty then
                  pure ({
                    root := binder.id
                    projections := []
                    type := state.resolve binder.scheme.body
                  }, state)
                else
                  throw (.invalidAssignmentTarget target.span)
            | none => throw (.invalidAssignmentTarget target.span)
        | .group inner => inferPlaceFuel fuel context inner state
        | .index base _ key => do
            let (base, state) ← inferPlaceFuel fuel context base state
            let (keyType, state) := state.fresh
            let (valueType, state) := state.fresh
            let state ← unify state base.type (.mapping keyType valueType)
            let (key, state) ← inferExprFuel fuel context key
              (some (state.resolve keyType)) state
            pure ({
              base with
              projections := base.projections ++ [.index key.id]
              type := state.resolve valueType
            }, state)
        | _ => throw (.invalidAssignmentTarget target.span)

  def inferAssignedValueFuel (fuel : Nat) (context : Context)
      (target : Syntax.Expr) (operator : Syntax.ValueAssignOp)
      (value : Syntax.Expr) (state : State) :
      Except Error (AssignmentResolution × InferredExpression × State) := do
    let (target, state) ← inferPlaceFuel fuel context target state
    let state ← match operator with
      | .equal => pure state
      | _ => unify state target.type .word
    let expected := match operator with
      | .equal => state.resolve target.type
      | _ => Ty.word
    let (value, state) ← inferExprFuel fuel context value (some expected) state
    pure ({ target := { target with type := state.resolve target.type } }, value,
      state)

  def inferForItemFuel (fuel : Nat) (context : Context)
      (item : Syntax.ForItem) (state : State) :
      Except Error (ForItemForm × State) :=
    match fuel with
    | 0 => throw .nestingLimit
    | fuel + 1 =>
        match item.value with
        | .letDecl name sourceType initializer => do
            let requirementStart := state.nextRequirement
            let (valueType, initializerId, state) ←
              match sourceType, initializer with
              | none, none => throw (.missingInitializer name.value)
              | some sourceType, none =>
                  pure ((← resolveSourceType context sourceType), none, state)
              | none, some initializer => do
                  let (initializer, state) ←
                    inferExprFuel fuel context initializer none state
                  pure (initializer.type, some initializer.id, state)
              | some sourceType, some initializer => do
                  let type ← resolveSourceType context sourceType
                  let (initializer, state) ← inferExprFuel fuel context
                    initializer (some type) state
                  pure (initializer.type, some initializer.id, state)
            let locals := state.locals.apply state.inference.substitution
            let valueType := state.resolve valueType
            let generalized :=
              generalizeValue state locals requirementStart valueType
            let (binder, state) := ({ state with locals }).allocateBinder
              name.value generalized.scheme (some name.span)
              (schemeRequirements := generalized.requirements)
            pure (.letDecl binder initializerId, state)
        | .expression expression => do
            let (expression, state) ←
              inferExprFuel fuel context expression none state
            pure (.expression expression.id, state)
        | .assignValue target operator value => do
            let (assignment, value, state) ← inferAssignedValueFuel fuel context
              target operator.value value state
            pure (.assignValue assignment operator.value value.id, state)
        | .assignBitNot target _ => do
            let (target, state) ← inferPlaceFuel fuel context target state
            let state ← unify state target.type .word
            pure (.assignBitNot {
              target := { target with type := state.resolve target.type }
            }, state)

  def inferForItemsFuel (fuel : Nat) (context : Context) :
      List Syntax.ForItem → State → Except Error InferredForItems
    | [], state => pure { items := [], state }
    | item :: items, state => do
        let (item, state) ← inferForItemFuel fuel context item state
        let tail ← inferForItemsFuel fuel context items state
        pure { items := item :: tail.items, state := tail.state }

  def inferMatchCasesFuel (fuel : Nat) (context : Context)
      (scrutineeType expectedReturn : Ty) (outerScope : LexicalScope) :
      List Syntax.MatchCase → State → Except Error MatchCasesResult
    | cases, state =>
      match fuel with
      | 0 => .error .nestingLimit
      | fuel + 1 =>
        match cases with
        | [] => .ok {
            cases := []
            hasWildcard := false
            allReturn := true
            state
          }
        | arm :: rest => do
            let (pattern, state) ← inferMatchPatternFuel fuel context
              arm.value.pattern scrutineeType state
            let body ← inferStatementsFuel fuel context arm.value.body.value
              expectedReturn state
            let state := body.state.restoreLexicalScope outerScope
            let tail ← inferMatchCasesFuel fuel context scrutineeType
              expectedReturn outerScope rest state
            pure {
              cases := {
                span := arm.span
                pattern
                body := body.statements
              } :: tail.cases
              hasWildcard := typedPatternIsCatchall pattern ||
                tail.hasWildcard
              allReturn := body.sawReturn && tail.allReturn
              state := tail.state
            }

  def inferStatementFuel (fuel : Nat) (context : Context)
      (statement : Syntax.Statement) (expectedReturn : Ty) (state : State) :
      Except Error StatementResult :=
    match fuel with
    | 0 => .error .nestingLimit
    | fuel + 1 =>
      let (id, state) := state.allocateStatementId
      match statement.value with
      | .letDecl name sourceType initializer => do
          let requirementStart := state.nextRequirement
          let (valueType, initializerId, state) ←
            match sourceType, initializer with
            | none, none => throw (.missingInitializer name.value)
            | some sourceType, none =>
                pure ((← resolveSourceType context sourceType), none, state)
            | none, some initializer => do
                let (initializer, state) ←
                  inferExprFuel fuel context initializer none state
                pure (initializer.type, some initializer.id, state)
            | some sourceType, some initializer => do
                let type ← resolveSourceType context sourceType
                let (initializer, state) ← inferExprFuel fuel context initializer
                  (some type) state
                pure (initializer.type, some initializer.id, state)
          let locals := state.locals.apply state.inference.substitution
          let valueType := state.resolve valueType
          let generalized :=
            generalizeValue state locals requirementStart valueType
          let (binder, state) := ({ state with locals }).allocateBinder
            name.value generalized.scheme (some name.span)
            (schemeRequirements := generalized.requirements)
          let state := state.recordNode (.statement {
            id
            span := statement.span
            type := .unit
            form := .letDecl binder initializerId
          })
          pure {
            id
            type := .unit
            hasValue := false
            sawReturn := false
            state
          }
      | .returnStmt value => do
          let (valueId, state) ← match value with
            | none => pure (none, ← unify state .unit expectedReturn)
            | some value => do
                let (value, state) ← inferExprFuel fuel context value
                  (some expectedReturn) state
                pure (some value.id, state)
          let type := state.resolve expectedReturn
          let state := state.recordNode (.statement {
            id
            span := statement.span
            type
            form := .returnStmt valueId
          })
          pure {
            id
            type
            hasValue := true
            sawReturn := true
            state
          }
      | .expression expression trailingSemicolon => do
          let (expression, state) ←
            inferExprFuel fuel context expression none state
          let type := if trailingSemicolon then .unit else expression.type
          let state := state.recordNode (.statement {
            id
            span := statement.span
            type
            form := .expression expression.id trailingSemicolon
          })
          pure {
            id
            type
            hasValue := !trailingSemicolon
            sawReturn := false
            state
          }
      | .ifThen condition thenBody elseBody => do
          let (condition, state) ← inferExprFuel fuel context condition
            (some .bool) state
          let outerScope := state.lexicalScope
          let thenResult ← inferStatementsFuel fuel context thenBody.value
            expectedReturn state
          let afterThen := thenResult.state.restoreLexicalScope outerScope
          match elseBody with
          | none =>
              let type := Ty.unit
              let state := afterThen.recordNode (.statement {
                id
                span := statement.span
                type
                form := .ifThen condition.id thenResult.statements none
              })
              pure {
                id
                type
                hasValue := false
                sawReturn := false
                state
              }
          | some elseBody => do
              let elseResult ← inferStatementsFuel fuel context elseBody.value
                expectedReturn afterThen
              let type := if thenResult.sawReturn && elseResult.sawReturn then
                  elseResult.state.resolve expectedReturn
                else
                  .unit
              let hasValue := thenResult.sawReturn && elseResult.sawReturn
              let state := elseResult.state.restoreLexicalScope outerScope
                |>.recordNode (.statement {
                  id
                  span := statement.span
                  type
                  form := .ifThen condition.id thenResult.statements
                    (some elseResult.statements)
                })
              pure {
                id
                type
                hasValue
                sawReturn := hasValue
                state
              }
      | .block body => do
          let outerScope := state.lexicalScope
          let result ← inferStatementsFuel fuel context body expectedReturn state
          let state := result.state.restoreLexicalScope outerScope
            |>.recordNode (.statement {
              id
              span := statement.span
              type := result.type
              form := .block result.statements
            })
          pure {
            id
            type := result.type
            hasValue := result.sawReturn
            sawReturn := result.sawReturn
            state
          }
      | .assignValue target operator value => do
          let (assignment, value, state) ← inferAssignedValueFuel fuel context
            target operator.value value state
          let state := state.recordNode (.statement {
            id
            span := statement.span
            type := .unit
            form := .assignValue assignment operator.value value.id
          })
          pure {
            id
            type := .unit
            hasValue := false
            sawReturn := false
            state
          }
      | .assignBitNot target _ => do
          let (target, state) ← inferPlaceFuel fuel context target state
          let state ← unify state target.type .word
          let state := state.recordNode (.statement {
            id
            span := statement.span
            type := .unit
            form := .assignBitNot {
              target := { target with type := state.resolve target.type }
            }
          })
          pure {
            id
            type := .unit
            hasValue := false
            sawReturn := false
            state
          }
      | .matchWith scrutinees arms => do
          let sources := scrutinees.elements.toList
          let (scrutinee, state) ← match sources with
            | [source] => inferExprFuel fuel context source none state
            | sources => do
                let (elements, state) ← inferExprsFuel fuel context sources state
                let (tupleId, state) := state.allocateExpressionId
                let type := Ty.productMany (elements.map (·.type))
                let state := state.recordNode (.expression {
                  id := tupleId
                  span := statement.span
                  type
                  form := .tuple (elements.map (·.id))
                })
                pure ({ id := tupleId, type }, state)
          let (hiddenScrutinee, state) := state.allocateHiddenLocal
          let outerScope := state.lexicalScope
          let checked ← inferMatchCasesFuel fuel context scrutinee.type
            expectedReturn outerScope arms.value.cases state
          let (defaultBody, state) ← match arms.value.defaultBody with
            | none => pure (none, checked.state)
            | some body => do
                let inferred ← inferStatementsFuel fuel context body.value
                  expectedReturn checked.state
                pure (some (inferred.statements, inferred.sawReturn),
                  inferred.state.restoreLexicalScope outerScope)
          let exhaustive := checked.hasWildcard || defaultBody.isSome ||
            exhaustsNominalConstructors context state scrutinee.type checked.cases
          if !exhaustive then
            throw (.nonExhaustiveMatch statement.span)
          else
            let requirements := checked.cases.flatMap fun arm =>
              arm.pattern.requirements
            let defaultStatements := defaultBody.map (·.1)
            let defaultReturns := defaultBody.map (·.2) |>.getD true
            let sawReturn := checked.allReturn && defaultReturns
            let type := if sawReturn then state.resolve expectedReturn else .unit
            let state := state.recordNode (.statement {
              id
              span := statement.span
              type
              form := .matchWith {
                scrutinee := scrutinee.id
                hiddenScrutinee
                cases := checked.cases
                defaultBody := defaultStatements
                requirements
              }
            })
            pure {
              id
              type
              hasValue := sawReturn
              sawReturn
              state
            }
      | .forLoop _ initializer condition post body => do
          let outerScope := state.lexicalScope
          let initializer ← inferForItemsFuel fuel context initializer state
          let loopScope := initializer.state.lexicalScope
          let (condition, state) ← inferExprFuel fuel context condition
            (some .bool) initializer.state
          let loopContext := {
            context with loopDepth := context.loopDepth + 1
          }
          let bodyResult ← inferStatementsFuel fuel loopContext body.value
            expectedReturn state
          let afterBody := bodyResult.state.restoreLexicalScope loopScope
          let postResult ← inferForItemsFuel fuel loopContext post afterBody
          let state := postResult.state.restoreLexicalScope outerScope
            |>.recordNode (.statement {
              id
              span := statement.span
              type := .unit
              form := .forLoop initializer.items condition.id postResult.items
                bodyResult.statements
            })
          pure {
            id
            type := .unit
            hasValue := false
            sawReturn := false
            state
          }
      | .whileLoop condition body => do
          let (condition, state) ← inferExprFuel fuel context condition
            (some .bool) state
          let outerScope := state.lexicalScope
          let loopContext := {
            context with loopDepth := context.loopDepth + 1
          }
          let bodyResult ← inferStatementsFuel fuel loopContext body.value
            expectedReturn state
          let state := bodyResult.state.restoreLexicalScope outerScope
            |>.recordNode (.statement {
              id
              span := statement.span
              type := .unit
              form := .whileLoop condition.id bodyResult.statements
            })
          pure {
            id
            type := .unit
            hasValue := false
            sawReturn := false
            state
          }
      | .assembly .. => .error (.unsupportedStatement "assembly")
      | .breakStmt =>
          if context.loopDepth = 0 then
            throw (.controlOutsideLoop "break")
          else
            let state := state.recordNode (.statement {
              id
              span := statement.span
              type := .unit
              form := .breakStmt
            })
            pure {
              id
              type := .unit
              hasValue := false
              sawReturn := false
              state
            }
      | .continueStmt =>
          if context.loopDepth = 0 then
            throw (.controlOutsideLoop "continue")
          else
            let state := state.recordNode (.statement {
              id
              span := statement.span
              type := .unit
              form := .continueStmt
            })
            pure {
              id
              type := .unit
              hasValue := false
              sawReturn := false
              state
            }
      | .error => .error (.unsupportedStatement "parser recovery")

  def inferStatementsFuel (fuel : Nat) (context : Context) :
      List Syntax.Statement → Ty → State → Except Error BlockResult
    | statements, expectedReturn, state =>
      match fuel with
      | 0 => .error .nestingLimit
      | fuel + 1 =>
        match statements with
        | [] => .ok {
            statements := []
            type := .unit
            sawReturn := false
            state
          }
        | statement :: rest => do
            let head ← inferStatementFuel fuel context statement
              expectedReturn state
            match rest with
            | [] => pure {
                statements := [head.id]
                type := if head.sawReturn || head.hasValue then head.type
                  else .unit
                sawReturn := head.sawReturn
                state := head.state
              }
            | _ => do
                let tail ← inferStatementsFuel fuel context rest
                  expectedReturn head.state
                pure {
                  statements := head.id :: tail.statements
                  type := if tail.sawReturn then tail.type
                    else if head.sawReturn then head.type
                    else tail.type
                  sawReturn := head.sawReturn || tail.sawReturn
                  state := tail.state
                }

end

end Solcore.Frontend.SourceInference.Detail
