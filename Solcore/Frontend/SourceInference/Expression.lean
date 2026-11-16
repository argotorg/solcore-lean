import Solcore.Frontend.SourceInference.Resolution
import Solcore.Frontend.WordLiteral

/-!
# Expression and body inference

Fuel-bounded inference of expressions, statements and simple bodies, with the shift and unchecked
operator branches. Main declarations: `SourceInference.Detail.inferExprFuel`,
`SourceInference.Detail.inferStatementFuel`, `SourceInference.Detail.inferStatementsFuel`.
-/

section
-- leanmerge: from Solcore.Frontend.SourceInference.Expression
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

/-- Requirements whose variables prevent local generalization.  Requirements
that predate the initializer remain visible, while newly introduced direct
declaration-call requirements are candidates for qualified generalization
rather than blockers. -/
def generalizeValueBlockingRequirements (state : State)
    (requirementStart : Nat) : List Requirement :=
  state.requirements.take requirementStart ++
    (state.requirements.drop requirementStart).filter fun requirement =>
      !state.directCallRequirements.contains requirement.id

/-- A blocking row either predates the initializer or is a row introduced by
the initializer whose identity is not classified as a direct declaration
call. -/
@[simp] theorem mem_generalizeValueBlockingRequirements_iff
    (state : State) (requirementStart : Nat) (requirement : Requirement) :
    requirement ∈
        generalizeValueBlockingRequirements state requirementStart ↔
      requirement ∈ state.requirements.take requirementStart ∨
      (requirement ∈ state.requirements.drop requirementStart ∧
        requirement.id ∉ state.directCallRequirements) := by
  unfold generalizeValueBlockingRequirements
  rw [List.mem_append]
  constructor
  · rintro (prior | operational)
    · exact Or.inl prior
    · rcases List.mem_filter.mp operational with ⟨introduced, selected⟩
      refine Or.inr ⟨introduced, ?_⟩
      intro direct
      have present :
          state.directCallRequirements.contains requirement.id = true :=
        (requirementId_contains_iff_mem _ _).mpr direct
      simp [present] at selected
  · rintro (prior | ⟨introduced, notDirect⟩)
    · exact Or.inl prior
    · apply Or.inr
      apply List.mem_filter.mpr
      refine ⟨introduced, ?_⟩
      have absent :
          state.directCallRequirements.contains requirement.id = false := by
        apply Bool.eq_false_iff.mpr
        intro present
        exact notDirect ((requirementId_contains_iff_mem _ _).mp present)
      simp [absent]

/-- Flexible variables that the executable local-value generalizer must not
quantify: variables free in the lexical environment together with variables
mentioned by every blocking requirement after applying the current inference
substitution. -/
def generalizeValueBlockedVariables (state : State)
    (locals : TypeSystem.Environment) (requirementStart : Nat) :
    List TypeVarId :=
  locals.freeVariables ++
    requirementVariables state
      (generalizeValueBlockingRequirements state requirementStart)

/-- Membership in the executable generalization barrier has either an exact
lexical-scheme witness or an exact blocking-requirement witness. -/
@[simp] theorem mem_generalizeValueBlockedVariables_iff
    (state : State) (locals : TypeSystem.Environment)
    (requirementStart : Nat) (metavariable : TypeVarId) :
    metavariable ∈
        generalizeValueBlockedVariables state locals requirementStart ↔
      (∃ entry ∈ locals, metavariable ∈ entry.2.freeVariables) ∨
      ∃ requirement ∈
          generalizeValueBlockingRequirements state requirementStart,
        metavariable ∈ TypedTraitResolution.predicateVariables
          (applyPredicate state requirement.predicate) := by
  simp [generalizeValueBlockedVariables, requirementVariables,
    TypeSystem.Environment.mem_freeVariables_iff]

/-- Generalize one local value together with the proof-only declaration-call
requirements introduced while inferring its initializer.  Every older
requirement, and every new operational requirement, continues to block its
variables exactly as before. -/
def generalizeValue (state : State) (locals : TypeSystem.Environment)
    (requirementStart : Nat) (type : Ty) : GeneralizedValue :=
  let introducedRequirements := state.requirements.drop requirementStart
  let eligibleRequirements := introducedRequirements.filter fun requirement =>
    state.directCallRequirements.contains requirement.id &&
      !state.localSchemeAssumptions.contains requirement.id
  let blockedVariables :=
    generalizeValueBlockedVariables state locals requirementStart
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

/-- Local generalization quantifies exactly the inferred type variables that
are absent from the executable lexical-and-requirement barrier. -/
@[simp] theorem generalizeValue_scheme_quantified (state : State)
    (locals : TypeSystem.Environment) (requirementStart : Nat) (type : Ty) :
    (generalizeValue state locals requirementStart type).scheme.quantified =
      type.freeVariables.filter fun metavariable =>
        !(generalizeValueBlockedVariables state locals requirementStart).contains
          metavariable := by
  rfl

/-- Local generalization quantifies each flexible metavariable at most once. -/
theorem generalizeValue_scheme_quantified_nodup (state : State)
    (locals : TypeSystem.Environment) (requirementStart : Nat) (type : Ty) :
    (generalizeValue state locals requirementStart type).scheme.quantified.Nodup := by
  rw [generalizeValue_scheme_quantified]
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
  let blockedVariables :=
    generalizeValueBlockedVariables state locals requirementStart
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
  let blockedVariables :=
    generalizeValueBlockedVariables state locals requirementStart
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
  let blockedVariables :=
    generalizeValueBlockedVariables state locals requirementStart
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

private def nominalTypePartsAux? (type : Ty) (arguments : List Ty) :
    Option (Resolved.DeclarationId × List Ty) :=
  match type with
  | .application function argument =>
      nominalTypePartsAux? function (argument :: arguments)
  | .constructor (.declaration declaration) => some (declaration, arguments)
  | _ => none

def nominalTypeParts? (type : Ty) :
    Option (Resolved.DeclarationId × List Ty) :=
  nominalTypePartsAux? type []

private theorem nominalTypePartsAux?_success_reconstruct
    {type : Ty} {arguments : List Ty}
    {declaration : Resolved.DeclarationId} {resultArguments : List Ty}
    (success : nominalTypePartsAux? type arguments =
      some (declaration, resultArguments)) :
    Ty.applyMany type arguments = Ty.nominal declaration resultArguments := by
  induction type generalizing arguments with
  | application function argument induction =>
      exact induction success
  | constructor constructor =>
      cases constructor with
      | builtin builtin => simp [nominalTypePartsAux?] at success
      | declaration candidate =>
          simp only [nominalTypePartsAux?, Option.some.injEq,
            Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          rfl
  | «variable» | parameter | function | product | mapping | proxy | comptime
  | error =>
      simp [nominalTypePartsAux?] at success

theorem nominalTypeParts?_success_reconstruct
    {type : Ty} {declaration : Resolved.DeclarationId}
    {arguments : List Ty}
    (success : nominalTypeParts? type = some (declaration, arguments)) :
    type = Ty.nominal declaration arguments := by
  simpa only [nominalTypeParts?, Ty.applyMany, List.foldl_nil] using
    nominalTypePartsAux?_success_reconstruct success

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

private theorem dataType?_success_member
    {signatures : ProgramSignatures} {id : Resolved.DeclarationId}
    {dataType : ProgramDataSignature}
    (success : signatures.dataType? id = some dataType) :
    dataType ∈ signatures.dataTypes := by
  apply List.mem_of_find?_eq_some
  simpa [ProgramSignatures.dataType?] using success

private theorem dataType?_success_id
    {signatures : ProgramSignatures} {id : Resolved.DeclarationId}
    {dataType : ProgramDataSignature}
    (success : signatures.dataType? id = some dataType) :
    dataType.id = id := by
  have rawFound : signatures.dataTypes.find?
      (fun candidate => decide (candidate.id = id)) = some dataType := by
    simpa [ProgramSignatures.dataType?] using success
  have accepted : decide (dataType.id = id) = true :=
    List.find?_some
      (p := fun candidate : ProgramDataSignature =>
        decide (candidate.id = id)) rawFound
  exact of_decide_eq_true accepted

private theorem dataSignaturesForImportedTypes_members
    (context : Context) (types : List ProgramImportedType) :
    ∀ accessible ∈ dataSignaturesForImportedTypes context types,
      accessible.signature ∈ context.signatures.dataTypes := by
  intro accessible member
  simp only [dataSignaturesForImportedTypes, List.mem_filterMap] at member
  obtain ⟨imported, _, produced⟩ := member
  cases found : context.signatures.dataType? imported.declaration.id with
  | none => simp [found, pure, Pure.pure] at produced
  | some signature =>
      simp [found, pure, Pure.pure] at produced
      subst accessible
      exact dataType?_success_member found

private theorem dataSignaturesForPublicEntities_members
    (context : Context) (entities : List ProgramPublicEntity) :
    ∀ accessible ∈ dataSignaturesForPublicEntities context entities,
      accessible.signature ∈ context.signatures.dataTypes := by
  intro accessible member
  simp only [dataSignaturesForPublicEntities, List.mem_filterMap] at member
  obtain ⟨entity, _, produced⟩ := member
  cases found : context.signatures.dataType? entity.declaration.id with
  | none => simp [found, pure, Pure.pure] at produced
  | some signature =>
      simp [found, pure, Pure.pure] at produced
      subst accessible
      exact dataType?_success_member found

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

private theorem visibleDataTypesNamed_success_members
    {context : Context} {name : String} {dataTypes : List AccessibleDataType}
    (success : visibleDataTypesNamed context name = .ok dataTypes) :
    ∀ accessible ∈ dataTypes,
      accessible.signature ∈ context.signatures.dataTypes := by
  let localDataTypes := context.signatures.dataTypes.filter fun dataType =>
    dataType.name == name &&
      decide (dataType.id.moduleId = context.scope.currentModule)
  by_cases localEmpty : localDataTypes = []
  · cases imported : buildProgramImports context.environment
      context.scope.currentModule with
    | error errors =>
        simp [visibleDataTypesNamed, localDataTypes, localEmpty, imported]
          at success
    | ok visibility =>
        simp [visibleDataTypesNamed, localDataTypes, localEmpty, imported,
          pure, Pure.pure, Except.pure] at success
        subst dataTypes
        exact dataSignaturesForImportedTypes_members context
          (visibility.typeBindingsNamed name)
  · simp [visibleDataTypesNamed, localDataTypes, localEmpty, pure,
      Pure.pure, Except.pure] at success
    subst dataTypes
    intro accessible member
    rcases List.mem_map.mp member with ⟨dataType, dataTypeMember, rfl⟩
    exact (List.mem_filter.mp dataTypeMember).1

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

private theorem qualifiedDataTypesNamed_success_members
    {context : Context} {qualifiers : List String}
    {dataTypes : List AccessibleDataType}
    (success : qualifiedDataTypesNamed context qualifiers = .ok dataTypes) :
    ∀ accessible ∈ dataTypes,
      accessible.signature ∈ context.signatures.dataTypes := by
  have afterTypeName : ∀ typeName,
      (if qualifiers.dropLast.isEmpty then
        visibleDataTypesNamed context typeName
      else
        match buildProgramImports context.environment
            context.scope.currentModule with
        | .error errors => throw (.importVisibility errors)
        | .ok visibility =>
            if visibility.hasNamespaceRoot qualifiers.dropLast then
              pure (dataSignaturesForPublicEntities context
                (visibility.typeEntitiesInNamespacePathNamed
                  qualifiers.dropLast typeName))
            else
              pure []) = .ok dataTypes →
        ∀ accessible ∈ dataTypes,
          accessible.signature ∈ context.signatures.dataTypes := by
    intro typeName reduced
    cases pathEmpty : qualifiers.dropLast.isEmpty with
    | true =>
        apply visibleDataTypesNamed_success_members
        simpa [pathEmpty] using reduced
    | false =>
        cases imported : buildProgramImports context.environment
            context.scope.currentModule with
        | error errors =>
            simp [pathEmpty, imported] at reduced
        | ok visibility =>
            cases namespaceRoot : visibility.hasNamespaceRoot
                qualifiers.dropLast with
            | false =>
                simp [pathEmpty, imported, namespaceRoot, pure, Pure.pure,
                  Except.pure] at reduced
                subst dataTypes
                simp
            | true =>
                simp [pathEmpty, imported, namespaceRoot, pure, Pure.pure,
                  Except.pure] at reduced
                subst dataTypes
                exact dataSignaturesForPublicEntities_members context
                  (visibility.typeEntitiesInNamespacePathNamed
                    qualifiers.dropLast typeName)
  cases last : qualifiers.getLast? with
  | none =>
      apply afterTypeName ""
      simpa [qualifiedDataTypesNamed, last, bind, Except.bind, pure, Pure.pure,
        Except.pure] using success
  | some typeName =>
      apply afterTypeName typeName
      simpa [qualifiedDataTypesNamed, last, bind, Except.bind, pure, Pure.pure,
        Except.pure] using success

private def constructorsInDataTypes (dataTypes : List AccessibleDataType)
    (name : String) :
    List (ProgramDataSignature × ProgramDataConstructorSignature) :=
  dataTypes.flatMap fun dataType =>
    dataType.signature.constructors.filterMap fun constructor =>
      if constructor.name == name && dataType.constructors.contains name then
        some (dataType.signature, constructor)
      else none

private theorem constructorsInDataTypes_member_origin
    {dataTypes : List AccessibleDataType} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    (member : (dataType, constructor) ∈
      constructorsInDataTypes dataTypes name) :
    ∃ accessible ∈ dataTypes,
      dataType = accessible.signature ∧
        constructor ∈ accessible.signature.constructors ∧
        constructor.name = name := by
  unfold constructorsInDataTypes at member
  rcases List.mem_flatMap.mp member with
    ⟨accessible, accessibleMember, constructorMember⟩
  simp only [List.mem_filterMap] at constructorMember
  obtain ⟨candidate, candidateMember, produced⟩ := constructorMember
  split at produced <;> rename_i accepted
  · simp only [Option.some.injEq, Prod.mk.injEq] at produced
    rcases produced with ⟨dataTypeEq, rfl⟩
    exact ⟨accessible, accessibleMember, dataTypeEq.symm, candidateMember,
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp accepted).1⟩
  · contradiction

private theorem constructorsInDataTypes_member_facts
    {context : Context} {dataTypes : List AccessibleDataType} {name : String}
    (cataloged : ∀ accessible ∈ dataTypes,
      accessible.signature ∈ context.signatures.dataTypes)
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    (member : (dataType, constructor) ∈
      constructorsInDataTypes dataTypes name) :
    dataType ∈ context.signatures.dataTypes ∧
      constructor ∈ dataType.constructors := by
  rcases constructorsInDataTypes_member_origin member with
    ⟨accessible, accessibleMember, rfl, constructorMember, _⟩
  exact ⟨cataloged accessible accessibleMember, constructorMember⟩

private theorem constructorsInDataTypes_member_name
    {dataTypes : List AccessibleDataType} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    (member : (dataType, constructor) ∈
      constructorsInDataTypes dataTypes name) :
    constructor.name = name := by
  rcases constructorsInDataTypes_member_origin member with
    ⟨_, _, _, _, nameEqual⟩
  exact nameEqual

private def exactConstructorCandidate (qualifiers : List String) (name : String) :
    List (ProgramDataSignature × ProgramDataConstructorSignature) →
      Except Error (ProgramDataSignature × ProgramDataConstructorSignature)
  | [] => throw (.unknownConstructor qualifiers name)
  | [candidate] => pure candidate
  | candidates => throw (.ambiguousConstructor qualifiers name
      (candidates.map fun candidate => candidate.2.id))

private theorem exactConstructorCandidate_success_member
    {qualifiers : List String} {name : String}
    {candidates : List
      (ProgramDataSignature × ProgramDataConstructorSignature)}
    {candidate : ProgramDataSignature × ProgramDataConstructorSignature}
    (success : exactConstructorCandidate qualifiers name candidates =
      .ok candidate) :
    candidate ∈ candidates := by
  cases candidates with
  | nil =>
      simp [exactConstructorCandidate] at success
  | cons head tail =>
      cases tail with
      | nil =>
          simp [exactConstructorCandidate, pure, Pure.pure, Except.pure]
            at success
          subst candidate
          simp
      | cons second rest =>
          simp [exactConstructorCandidate] at success

def explicitConstructorCandidate (context : Context)
    (qualifiers : List String) (name : String) :
    Except Error (ProgramDataSignature × ProgramDataConstructorSignature) := do
  exactConstructorCandidate qualifiers name
    (constructorsInDataTypes (← qualifiedDataTypesNamed context qualifiers) name)

/-- An explicitly selected constructor comes from the whole-program data
catalog and from the constructor list of its selected data declaration. -/
theorem explicitConstructorCandidate_success_members
    {context : Context} {qualifiers : List String} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    (success : explicitConstructorCandidate context qualifiers name =
      .ok (dataType, constructor)) :
    dataType ∈ context.signatures.dataTypes ∧
      constructor ∈ dataType.constructors := by
  cases found : qualifiedDataTypesNamed context qualifiers with
  | error errors =>
      simp [explicitConstructorCandidate, found, bind, Except.bind] at success
  | ok dataTypes =>
      have selected : (dataType, constructor) ∈
          constructorsInDataTypes dataTypes name := by
        apply exactConstructorCandidate_success_member
        simpa [explicitConstructorCandidate, found, bind, Except.bind, pure,
          Pure.pure, Except.pure] using success
      exact constructorsInDataTypes_member_facts
        (qualifiedDataTypesNamed_success_members found) selected

/-- An explicitly selected constructor has the name requested by the source
path. -/
theorem explicitConstructorCandidate_success_name
    {context : Context} {qualifiers : List String} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    (success : explicitConstructorCandidate context qualifiers name =
      .ok (dataType, constructor)) :
    constructor.name = name := by
  cases found : qualifiedDataTypesNamed context qualifiers with
  | error errors =>
      simp [explicitConstructorCandidate, found, bind, Except.bind] at success
  | ok dataTypes =>
      apply constructorsInDataTypes_member_name
      apply exactConstructorCandidate_success_member
      simpa [explicitConstructorCandidate, found, bind, Except.bind, pure,
        Pure.pure, Except.pure] using success

/-- The complete stable provenance boundary for explicit constructor
selection. -/
theorem explicitConstructorCandidate_success_facts
    {context : Context} {qualifiers : List String} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    (success : explicitConstructorCandidate context qualifiers name =
      .ok (dataType, constructor)) :
    dataType ∈ context.signatures.dataTypes ∧
      constructor ∈ dataType.constructors ∧
      constructor.name = name := by
  exact ⟨(explicitConstructorCandidate_success_members success).1,
    (explicitConstructorCandidate_success_members success).2,
    explicitConstructorCandidate_success_name success⟩

def contextualConstructorCandidate (context : Context) (state : State)
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

/-- Contextual constructor selection preserves catalog provenance, the
queried constructor name, and the nominal expected type that supplied its
type arguments. -/
theorem contextualConstructorCandidate_success_facts_with_name
    {context : Context} {state : State} {expected : Option Ty} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (success : contextualConstructorCandidate context state expected name =
      .ok (dataType, constructor, arguments)) :
    dataType ∈ context.signatures.dataTypes ∧
      constructor ∈ dataType.constructors ∧
      constructor.name = name ∧
      ∃ expectedType,
          expected = some expectedType ∧
            state.resolve expectedType = Ty.nominal dataType.id arguments := by
  cases expected with
  | none =>
      simp [contextualConstructorCandidate, bind, Except.bind, pure,
        Pure.pure, Except.pure] at success
  | some expectedType =>
      cases parts : nominalTypeParts? (state.resolve expectedType) with
      | none =>
          simp [contextualConstructorCandidate, parts, bind, Except.bind, pure,
            Pure.pure, Except.pure] at success
      | some result =>
          rcases result with ⟨declaration, sourceArguments⟩
          have nominal := nominalTypeParts?_success_reconstruct parts
          cases found : context.signatures.dataType? declaration with
          | none =>
              simp [contextualConstructorCandidate, parts, found, bind,
                Except.bind, pure, Pure.pure, Except.pure] at success
          | some sourceDataType =>
              have sourceDataTypeMember :
                  sourceDataType ∈ context.signatures.dataTypes :=
                dataType?_success_member found
              have nominalSource : state.resolve expectedType =
                  Ty.nominal sourceDataType.id sourceArguments := by
                rw [dataType?_success_id found]
                exact nominal
              have selectedFacts : ∀ visibility selectedDataType
                  selectedConstructor,
                  exactConstructorCandidate [] name
                    (constructorsInDataTypes [{
                      signature := sourceDataType
                      constructors := visibility
                    }] name) = .ok (selectedDataType, selectedConstructor) →
                  selectedDataType = sourceDataType ∧
                    selectedDataType ∈ context.signatures.dataTypes ∧
                    selectedConstructor ∈ selectedDataType.constructors ∧
                    selectedConstructor.name = name := by
                intro visibility selectedDataType selectedConstructor selected
                rcases constructorsInDataTypes_member_origin
                    (exactConstructorCandidate_success_member selected) with
                  ⟨accessible, accessibleMember, selectedOwner,
                    constructorMember, constructorName⟩
                simp only [List.mem_singleton] at accessibleMember
                subst accessible
                subst selectedDataType
                exact ⟨rfl, sourceDataTypeMember, constructorMember,
                  constructorName⟩
              cases isLocal : decide
                  (sourceDataType.id.moduleId = context.scope.currentModule) with
              | true =>
                  cases selected : exactConstructorCandidate [] name
                      (constructorsInDataTypes [{
                        signature := sourceDataType
                        constructors :=
                          (fullyAccessibleDataType sourceDataType).constructors
                      }] name) with
                  | error error =>
                      simp [contextualConstructorCandidate, parts, found,
                        isLocal, selected, bind, Except.bind, pure, Pure.pure,
                        Except.pure] at success
                  | ok selectedConstructor =>
                      rcases selectedConstructor with
                        ⟨selectedDataType, selectedConstructor⟩
                      have provenance := selectedFacts
                        (fullyAccessibleDataType sourceDataType).constructors
                        selectedDataType selectedConstructor selected
                      simp [contextualConstructorCandidate, parts, found,
                        isLocal, selected, bind, Except.bind, pure, Pure.pure,
                        Except.pure] at success
                      rcases success with ⟨rfl, rfl, rfl⟩
                      have nominalSelected : state.resolve expectedType =
                          Ty.nominal selectedDataType.id sourceArguments := by
                        rw [provenance.1]
                        exact nominalSource
                      exact ⟨provenance.2.1, provenance.2.2.1,
                        provenance.2.2.2, expectedType, rfl, nominalSelected⟩
              | false =>
                  cases imported : buildProgramImports context.environment
                      context.scope.currentModule with
                  | error errors =>
                      simp [contextualConstructorCandidate, parts, found,
                        isLocal, imported, bind, Except.bind, pure, Pure.pure,
                        Except.pure] at success
                  | ok visibility =>
                      let constructorVisibility :=
                        (visibility.constructorVisibilityForDeclaration?
                          sourceDataType.id).getD .opaqueData
                      cases selected : exactConstructorCandidate [] name
                          (constructorsInDataTypes [{
                            signature := sourceDataType
                            constructors := constructorVisibility
                          }] name) with
                      | error error =>
                          simp [contextualConstructorCandidate, parts, found,
                            isLocal, imported, constructorVisibility, selected,
                            bind, Except.bind, pure, Pure.pure, Except.pure]
                            at success
                      | ok selectedConstructor =>
                          rcases selectedConstructor with
                            ⟨selectedDataType, selectedConstructor⟩
                          have provenance := selectedFacts
                            constructorVisibility selectedDataType
                            selectedConstructor selected
                          simp [contextualConstructorCandidate, parts, found,
                            isLocal, imported, constructorVisibility, selected,
                            bind, Except.bind, pure, Pure.pure, Except.pure]
                            at success
                          rcases success with ⟨rfl, rfl, rfl⟩
                          have nominalSelected : state.resolve expectedType =
                              Ty.nominal selectedDataType.id sourceArguments := by
                            rw [provenance.1]
                            exact nominalSource
                          exact ⟨provenance.2.1, provenance.2.2.1,
                            provenance.2.2.2, expectedType, rfl,
                            nominalSelected⟩

/-- Contextual constructor selection preserves both catalog provenance and
the nominal expected type that supplied its type arguments. -/
theorem contextualConstructorCandidate_success_facts
    {context : Context} {state : State} {expected : Option Ty} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (success : contextualConstructorCandidate context state expected name =
      .ok (dataType, constructor, arguments)) :
    dataType ∈ context.signatures.dataTypes ∧
      constructor ∈ dataType.constructors ∧
      ∃ expectedType,
        expected = some expectedType ∧
          state.resolve expectedType = Ty.nominal dataType.id arguments := by
  rcases contextualConstructorCandidate_success_facts_with_name success with
    ⟨dataTypeMember, constructorMember, _, expectedFacts⟩
  exact ⟨dataTypeMember, constructorMember, expectedFacts⟩

/-- A contextually selected constructor has the name requested by the source
pattern. -/
theorem contextualConstructorCandidate_success_name
    {context : Context} {state : State} {expected : Option Ty} {name : String}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (success : contextualConstructorCandidate context state expected name =
      .ok (dataType, constructor, arguments)) :
    constructor.name = name :=
  (contextualConstructorCandidate_success_facts_with_name success).2.2.1

def instantiateDataConstructor
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

/-- Applying constructor parameters cannot introduce an out-of-range flexible
variable when both the actual arguments and source payload types are bounded. -/
theorem instantiateDataConstructor_types_variablesBelow
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    {next : Nat}
    (argumentsBelow : ∀ argument ∈ arguments,
      argument.VariablesBelow next)
    (payloadTypesBelow : ∀ payload ∈ constructor.payloadTypes,
      payload.VariablesBelow next) :
    (∀ payload ∈
        (instantiateDataConstructor dataType constructor arguments).payloadTypes,
      payload.VariablesBelow next) ∧
      Ty.VariablesBelow next
        (instantiateDataConstructor dataType constructor arguments).resultType := by
  constructor
  · intro payload member
    change payload ∈ constructor.payloadTypes.map
      (TypeSystem.ParameterSubstitution.apply
        (dataType.parameters.zip arguments)) at member
    rcases List.mem_map.mp member with
      ⟨sourcePayload, sourceMember, rfl⟩
    apply TypeSystem.ParameterSubstitution.apply_variables_below
    · intro parameter replacement entryMember
      exact argumentsBelow replacement (List.of_mem_zip entryMember).2
    · exact payloadTypesBelow sourcePayload sourceMember
  · exact Ty.variablesBelow_nominal argumentsBelow

def freshDataConstructorInstantiation
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature)
    (state : State) : DataConstructorInstantiation × State :=
  let (arguments, state) := dataType.parameters.foldl
    (fun (result : List Ty × State) _ =>
      let (type, state) := result.2.fresh
      (result.1 ++ [type], state)) ([], state)
  (instantiateDataConstructor dataType constructor arguments, state)

def constructorCalleeCandidates (context : Context) (state : State)
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

/-- Constructor-callee discovery only returns constructors paired with their
owning declarations from the whole-program data catalog. -/
theorem constructorCalleeCandidates_success_members
    {context : Context} {state : State} {callee : Syntax.Expr}
    {candidates : List
      (ProgramDataSignature × ProgramDataConstructorSignature)}
    (success : constructorCalleeCandidates context state callee =
      .ok candidates) :
    ∀ dataType constructor, (dataType, constructor) ∈ candidates →
      dataType ∈ context.signatures.dataTypes ∧
        constructor ∈ dataType.constructors := by
  intro dataType constructor member
  cases qualified : calleeQualifiedIdentifier? callee with
  | some qualifiedName =>
      rcases qualifiedName with ⟨qualifiers, name⟩
      cases qualifiers with
      | nil =>
          simp [constructorCalleeCandidates, qualified, pure, Pure.pure,
            Except.pure] at success
          subst candidates
          simp at member
      | cons root rest =>
          cases binder : state.lookupBinder? root with
          | some binding =>
              simp [constructorCalleeCandidates, qualified, binder, pure,
                Pure.pure, Except.pure] at success
              subst candidates
              simp at member
          | none =>
              cases found : qualifiedDataTypesNamed context (root :: rest) with
              | error errors =>
                  simp [constructorCalleeCandidates, qualified, binder, found,
                    bind, Except.bind] at success
              | ok dataTypes =>
                  simp [constructorCalleeCandidates, qualified, binder, found,
                    bind, Except.bind, pure, Pure.pure, Except.pure] at success
                  subst candidates
                  exact constructorsInDataTypes_member_facts
                    (qualifiedDataTypesNamed_success_members found) member
  | none =>
      cases identifier : calleeIdentifier? callee with
      | none =>
          simp [constructorCalleeCandidates, qualified, identifier, pure,
            Pure.pure, Except.pure] at success
          subst candidates
          simp at member
      | some name =>
          cases binder : state.lookupBinder? name with
          | some binding =>
              simp [constructorCalleeCandidates, qualified, identifier, binder,
                pure, Pure.pure, Except.pure] at success
              subst candidates
              simp at member
          | none =>
              cases found : visibleDataTypesNamed context name with
              | error errors =>
                  simp [constructorCalleeCandidates, qualified, identifier,
                    binder, found, bind, Except.bind] at success
              | ok dataTypes =>
                  simp [constructorCalleeCandidates, qualified, identifier,
                    binder, found, bind, Except.bind, pure, Pure.pure,
                    Except.pure] at success
                  subst candidates
                  apply constructorsInDataTypes_member_facts _ member
                  intro accessible accessibleMember
                  exact visibleDataTypesNamed_success_members found accessible
                    (List.mem_filter.mp accessibleMember).1

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

/-- Append an already allocated coercion path to one expression node.  The
node's authoritative type advances to the final coercion target while its
requirements and retained path preserve source order. -/
def appendExpressionCoercions (node : ExpressionNode)
    (coercions : List CoercionStep) : ExpressionNode := {
  node with
  type := coercions.foldl (fun _ step => step.target) node.type
  requirements := node.requirements ++ coercionRequirements coercions
  coercions := node.coercions ++ coercions
}

def attachExpressionCoercions (state : State)
    (entries : List ExpressionCoercions) : State :=
  entries.foldl (fun state entry =>
    state.modifyExpressionNode entry.expression fun node =>
      appendExpressionCoercions node entry.coercions) state

def recordExpression (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    (localSchemeInstantiationStart : Option Nat := none) :
    InferredExpression × State :=
  let node : ExpressionNode := {
    id := expression.id
    span := source.span
    type := expression.type
    form
    requirements
    coercions
    localSchemeInstantiationStart
  }
  (expression, state.recordNode (.expression node))

def recordExpressionWithExpected (context : Context) (source : Syntax.Expr)
    (id : ExpressionId) (type : Ty) (form : ExpressionForm)
    (requirements : List RequirementId) (expected : Option Ty) (state : State)
    (localSchemeInstantiationStart : Option Nat := none) :
    Except Error (InferredExpression × State) := do
  let fitted ← withExpected context state { id, type } expected
  pure <| recordExpression source fitted.expression form
    (requirements ++ coercionRequirements fitted.coercions)
    fitted.coercions fitted.state localSchemeInstantiationStart

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

/-- The two functions of upstream's `Typedef` trait, which Lean has as
compiler functions rather than a trait. -/
inductive TypedefCall where
  | abs
  | rep
  deriving Repr, DecidableEq

/-- `Typedef.abs` and `Typedef.rep`: the qualified names of compiler
functions, found only when no source namespace or local is named `Typedef`. -/
def typedefCall? : List String → String → Option TypedefCall
  | ["Typedef"], "abs" => some .abs
  | ["Typedef"], "rep" => some .rep
  | _, _ => none

/-- The compiler function of a `Typedef` call, chosen by the type already
known at the call once its arguments are inferred: the expected type for
`abs` and the argument's type for `rep`. `word` gives the identity and one of
the twelve fixed-width types its conversion. Any other type, including one
still open, is rejected: the choice is made here and does not wait for later
uses, as upstream's instance resolution would. -/
def typedefFunction (call : TypedefCall) (arguments : List InferredExpression)
    (expected : Option Ty) (state : State) : Except Error BuiltinFunctionId :=
  let known : Option Ty := match call with
    | .abs => expected.map state.resolve
    | .rep => arguments.head?.map fun (argument : InferredExpression) =>
        state.resolve argument.type
  match known with
  | some .word => .ok .wordIdentity
  | some (.fixed type) =>
      .ok (match call with
        | .abs => .fixedFromWord type
        | .rep => .fixedToWord type)
  | some other => .error (.operatorNotSupported "Typedef" other)
  | none => .error (.operatorNotSupported "Typedef" state.fresh.1)

/-- `Length.length`, the function of upstream's `Length` trait, which Lean has
as a memory array's length rather than a trait: the qualified name of a
compiler form, found only when no source namespace or local is named `Length`,
as `Typedef`'s are. -/
def lengthCall : List String → String → Bool
  | ["Length"], "length" => true
  | _, _ => false

/-- Whether inference has made `array`'s type a memory array or a slice, as a
length needs, as `typedefFunction` reads `Typedef.rep`'s argument. A type still
open is rejected: the choice is made here and does not wait for later uses. -/
def arrayLengthOf (array : InferredExpression) (state : State) : Except Error Unit :=
  match (state.resolve array.type).viewElement? with
  | some _ => .ok ()
  | none => .error (.operatorNotSupported "Length" (state.resolve array.type))

/-- The array of `Length.length(a)`: its one argument, once inference has made
its type a memory array (`arrayLengthOf`). Another row of arguments is
rejected. -/
def arrayLengthArgument (arguments : List InferredExpression) (state : State) :
    Except Error InferredExpression :=
  match arguments with
  | [array] => do
      arrayLengthOf array state
      pure array
  | arguments => .error (.operatorNotSupported "Length"
      (state.resolve (Ty.productMany (arguments.map (·.type)))))

/-- `a.length()`: a call of a field named `length` with no arguments, which is
the field itself, as upstream's method call of `Length.length` is. -/
def lengthMethodCall (callee : Syntax.Expr) (arguments : List InferredExpression) : Bool :=
  match callee.value, arguments with
  | .field _ _ name, [] => name.value == "length"
  | _, _ => false

/-- An array whose length is taken has a memory array or slice type once
resolved. -/
theorem arrayLengthOf_ok {array : InferredExpression} {state : State} {checked : Unit}
    (success : arrayLengthOf array state = .ok checked) :
    ∃ element, (state.resolve array.type).viewElement? = some element := by
  unfold arrayLengthOf at success
  cases found : (state.resolve array.type).viewElement? with
  | none => simp [found] at success
  | some element => exact ⟨element, rfl⟩

/-- `Length.length(a)`'s argument row is its one array, whose type is a memory
array once resolved. -/
theorem arrayLengthArgument_ok {arguments : List InferredExpression} {state : State}
    {array : InferredExpression}
    (success : arrayLengthArgument arguments state = .ok array) :
    arguments = [array] ∧ ∃ element, (state.resolve array.type).viewElement? = some element := by
  match arguments with
  | [only] =>
      unfold arrayLengthArgument at success
      cases checked : arrayLengthOf only state with
      | error error => simp [checked, bind, Except.bind] at success
      | ok _ =>
          simp only [checked, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at success
          subst success
          exact ⟨rfl, arrayLengthOf_ok checked⟩
  | [] => simp [arrayLengthArgument] at success
  | _ :: _ :: _ => simp [arrayLengthArgument] at success

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

/-- The one pattern of `case uint256(p)`, which a `uint256` value's word is
matched with: spelled `uint256` with no qualifier and no leading dot, at a type
that is `uint256` or still open. Upstream rejects a constructor pattern at the
other eleven types (`SC0107`), and `uint256` at any other type. -/
def uint256PatternArgument? (leadingDot : Option Syntax.SourceSpan)
    (qualifiers : List Syntax.Identifier) (name : String) (arguments : List Syntax.Pattern)
    (expected : Ty) : Option Syntax.Pattern :=
  match leadingDot, qualifiers, arguments, expected with
  | none, [], [argument], .variable _ => if name = "uint256" then some argument else none
  | none, [], [argument], .constructor (.builtin (.fixed ⟨false, .w256⟩)) =>
      if name = "uint256" then some argument else none
  | _, _, _, _ => none

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
                rawValue
              }
              let state := {
                state with integerPatterns := state.integerPatterns ++ [origin]
              }
              let normalizedExpected := state.resolve expected
              let state ← match normalizedExpected with
                | .variable _ | .constructor (.builtin .word)
                | .constructor (.builtin .integer)
                | .constructor (.builtin (.fixed ⟨false, .w256⟩)) =>
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
          match uint256PatternArgument? leadingDot qualifiers name.value
              (arguments.map (·.elements.toList) |>.getD []) (state.resolve expected) with
          | none =>
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
          | some argument =>
              let state ← unify state expected (.fixed .uint256)
              let children ← inferMatchPatternsFlatFuel fuel context [argument] [.word] seen
                state
              pure {
                source := .constructor pattern.span leadingDot qualifierNames name.value 1
                resolution := .uint256Word children.instructions
                instructions := .uint256Word :: children.instructions
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

  def consumeIrrefutableInstruction (fuel : Nat) :
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
            | .uint256Word => consumeIrrefutableInstructions fuel 1 rest

  def consumeIrrefutableInstructions (fuel : Nat) :
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

def constructorArgumentsIrrefutable
    (instantiation : DataConstructorInstantiation)
    (instructions : List MatchPatternInstruction) : Bool :=
  match consumeIrrefutableInstructions (instructions.length + 1)
      instantiation.payloadTypes.length instructions with
  | some (true, []) => true
  | _ => false

def typedPatternIsCatchall (pattern : TypedMatchPattern) : Bool :=
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
  | .uint256Word instructions =>
      match consumeIrrefutableInstructions (instructions.length + 1) 1 instructions with
      | some (true, []) => true
      | _ => false
  | .integerLiteral .. | .constructor .. => false

def exhaustsNominalConstructors (context : Context) (state : State)
    (scrutineeType : Ty) (cases : List TypedMatchCase) : Bool :=
  if cases.isEmpty then false else
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

/-- The equation an index of an assignable place unifies: on a memory array, its
value type is the array's element, as a read's type is; otherwise the base is a
mapping from the key type to it. -/
def placeIndexEquation (state : State) (base keyType valueType : Ty) : Ty × Ty :=
  match (state.resolve base).arrayElement? with
  | some element => (valueType, element)
  | none => (base, .mapping keyType valueType)

/-- The expected type of an assignable place's index: none on a memory array,
whose index waits for its type until finalization checks it, as a read's does;
otherwise the key type, resolved at the later state. -/
def placeIndexExpected (state later : State) (base keyType : Ty) : Option Ty :=
  match (state.resolve base).arrayElement? with
  | some _ => none
  | none => some (later.resolve keyType)

/-- An assignable place's index projection: an element of a memory array, or a
mapping index. -/
def placeIndexProjection (state : State) (base : Ty) (key : ExpressionId) : PlaceProjection :=
  match (state.resolve base).arrayElement? with
  | some _ => .element key
  | none => .index key

/-- Either projection of an index names its index expression. -/
@[simp high] theorem placeIndexProjection_references (state : State) (base : Ty)
    (key : ExpressionId) :
    (placeIndexProjection state base key).references = [.expression key] := by
  unfold placeIndexProjection
  split <;> rfl

/-- On a base that is not a memory array, an index unifies the base with a
mapping, takes the key type and is a mapping index, as before memory arrays. -/
theorem placeIndex_of_notArray {state : State} {base : Ty}
    (notArray : (state.resolve base).arrayElement? = none) (later : State)
    (keyType valueType : Ty) (key : ExpressionId) :
    placeIndexEquation state base keyType valueType = (base, .mapping keyType valueType) ∧
      placeIndexExpected state later base keyType = some (later.resolve keyType) ∧
      placeIndexProjection state base key = .index key := by
  simp [placeIndexEquation, placeIndexExpected, placeIndexProjection, notArray]

/-- On a memory array, an index's value type is the element type, the index has no
expected type and is an element. -/
theorem placeIndex_of_array {state : State} {base element : Ty}
    (array : (state.resolve base).arrayElement? = some element) (later : State)
    (keyType valueType : Ty) (key : ExpressionId) :
    placeIndexEquation state base keyType valueType = (valueType, element) ∧
      placeIndexExpected state later base keyType = none ∧
      placeIndexProjection state base key = .element key := by
  simp [placeIndexEquation, placeIndexExpected, placeIndexProjection, array]

/-- Every expected type of an assignable place's index has a property that its
resolved key type has. -/
theorem placeIndexExpected_forall {state later : State} {base keyType : Ty}
    {property : Ty → Prop} (holds : property (later.resolve keyType)) :
    ∀ expectedType ∈ placeIndexExpected state later base keyType, property expectedType := by
  intro expectedType member
  unfold placeIndexExpected at member
  cases found : (state.resolve base).arrayElement? with
  | some _ => simp [found] at member
  | none =>
      simp only [found, Option.mem_def, Option.some.injEq] at member
      subst expectedType
      exact holds

/-- The element type of `new T[](n)`'s resolved array type `T[]`, which a memory
array admits once type resolution has checked it. -/
def newArrayElement (type : Ty) : Except Error Ty :=
  match type.arrayElement? with
  | some element =>
      if element.arrayElementAllowed then pure element
      else .error (.unsupportedExpression "new")
  | none => .error (.unsupportedExpression "new")

/-- A slice's start and stop in its typed form, from its present bounds' inferred
results in order, the start first. -/
def sliceBoundIds (start stop : Option Syntax.Expr) (bounds : List InferredExpression) :
    Option ExpressionId × Option ExpressionId :=
  match start, stop, bounds with
  | some _, some _, first :: last :: _ => (some first.id, some last.id)
  | some _, none, first :: _ => (some first.id, none)
  | none, some _, last :: _ => (none, some last.id)
  | _, _, _ => (none, none)

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
              -- A negative literal (`-128`, folded by `Syntax.Unchecked.mark`)
              -- keeps its sign in the spelling and its magnitude here.
              let rawValue ← match literalMagnitude? value with
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
              let localSchemeInstantiationStart := state.inference.next
              let instantiated :=
                binder.scheme.instantiateWithSubstitution
                  localSchemeInstantiationStart
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
                state (localSchemeInstantiationStart :=
                  some localSchemeInstantiationStart)
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
                      if lengthMethodCall callee arguments then
                        recordExpressionWithExpected context expression id
                          calleeResult.type (.group calleeResult.id) [] expected state
                      else
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
                          match typedefCall? namespacePath name with
                          | some call =>
                              let function ← typedefFunction call arguments
                                expected state
                              recordBuiltinFunctionCall expression callee
                                function.spelling function arguments id expected
                                state
                          | none =>
                              if lengthCall namespacePath name then
                                let array ← arrayLengthArgument arguments state
                                recordExpressionWithExpected context expression id
                                  (.fixed .uint256) (.arrayLength array.id) []
                                  expected state
                              else
                                let (calleeResult, state) ←
                                  inferExprFuel fuel context callee none state
                                let result ← applyFunctionType context id
                                  calleeResult.type arguments expected state
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
                      if lengthMethodCall callee arguments then
                        recordExpressionWithExpected context expression id
                          calleeResult.type (.group calleeResult.id) [] expected state
                      else
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
          match (state.resolve base.type).viewElement? with
          | none =>
              let (keyType, state) := state.fresh
              let (valueType, state) := state.fresh
              let state ← unify state base.type (.mapping keyType valueType)
              let (index, state) ← inferExprFuel fuel context index
                (some (state.resolve keyType)) state
              recordExpressionWithExpected context expression id
                (state.resolve valueType) (.index base.id index.id) [] expected state
          -- A read of a memory array or of a slice infers its index on its own, which
          -- finalization checks (`validateArrayIndex`), and has the element type.
          | some element =>
              let (index, state) ← inferExprFuel fuel context index none state
              recordExpressionWithExpected context expression id element
                (.arrayIndex base.id index.id) [] expected state
      | .field base _ name => do
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
              | none =>
                  if name.value == "length" then
                    let (array, state) ← inferExprFuel fuel context base none state
                    arrayLengthOf array state
                    recordExpressionWithExpected context expression id
                      (.fixed .uint256) (.arrayLength array.id) [] expected state
                  else .error (.unsupportedExpression "field")
          | _ => throw (.ambiguousConstructor [] name.value
              (candidates.map fun candidate => candidate.2.id))
      -- A literal infers its elements with no expected type, as a tuple does, and
      -- unifies their types with one fresh element type, as upstream's
      -- `infer_array_expr` does. Finalization checks that type (`validateArrayLiteral`).
      | .array elements => do
          let (values, state) ← inferExprsFuel fuel context elements.elements state
          let (element, state) := state.fresh
          let state ← unify state (Ty.productMany (values.map (·.type)))
            (Ty.productMany (List.replicate values.length element))
          recordExpressionWithExpected context expression id (Ty.array element)
            (.arrayLiteral element (values.map (·.id))) [] expected state
      | .newArray _ sourceType length => do
          let element ← newArrayElement (← resolveSourceType context sourceType)
          let (length, state) ← inferExprFuel fuel context length
            (some (.fixed .uint256)) state
          recordExpressionWithExpected context expression id (Ty.array element)
            (.newArray element length.id) [] expected state
      -- A slice infers its base, then its present bounds, with no expected type, as
      -- a tuple's elements, takes its base only when the base's type is a memory array
      -- or a slice there, as a read decides on its base, and unifies the bounds' types
      -- with `uint256`s, as a literal's elements' with its element type.
      | .slice base _ start _ stop => do
          let (values, state) ← inferExprsFuel fuel context
            (base :: (start.toList ++ stop.toList)) state
          let some baseResult := values.head? | throw (.unsupportedExpression "slice")
          unless (state.resolve baseResult.type).arraySliceBaseAllowed do
            throw (.unsupportedExpression "slice")
          let state ← unify state (Ty.productMany (values.tail.map (·.type)))
            (Ty.productMany (List.replicate values.tail.length (.fixed .uint256)))
          recordExpressionWithExpected context expression id
            (Ty.arraySlice (state.resolve baseResult.type))
            (.arraySlice baseResult.id (sliceBoundIds start stop values.tail).1
              (sliceBoundIds start stop values.tail).2) [] expected state
      -- The parser's recovery nodes.
      | _ => .error (.unsupportedExpression "parser recovery")

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
        -- An element of a memory array infers its index on its own, as a read does;
        -- otherwise the base is a mapping (`placeIndexEquation`).
        | .index base _ key => do
            let (base, state) ← inferPlaceFuel fuel context base state
            let (keyType, state) := state.fresh
            let (valueType, valueState) := state.fresh
            let state ← unify valueState
              (placeIndexEquation valueState base.type keyType valueType).1
              (placeIndexEquation valueState base.type keyType valueType).2
            let (key, state) ← inferExprFuel fuel context key
              (placeIndexExpected valueState state base.type keyType) state
            pure ({
              base with
              projections := base.projections ++ [placeIndexProjection valueState base.type key.id]
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
      | _ => unify state target.type (compoundOperandType operator (state.resolve target.type))
    -- A shift's amount is typed on its own, as upstream's `x = x << n` types it.
    let (value, state) ← inferExprFuel fuel context value
      (match operator with
        | .equal => some (state.resolve target.type)
        | .shiftLeft | .shiftRight => none
        | .add | .subtract | .multiply | .divide | .modulo | .bitAnd | .bitXor | .bitOr
        | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply | .uncheckedDivide
        | .uncheckedModulo => some (compoundOperandType operator (state.resolve target.type))) state
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
            let locals :=
              state.binderEnvironment.apply state.inference.substitution
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
            let state ← unify state target.type (bitNotTargetType (state.resolve target.type))
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
          let locals :=
            state.binderEnvironment.apply state.inference.substitution
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
          let state ← unify state target.type (bitNotTargetType (state.resolve target.type))
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

/-- Invert successful `a.length` inference, a field that names no constructor:
the field is `length`, and the base, inferred with no expected type, is a
memory array once resolved, whose length is recorded at `uint256`. -/
theorem inferExprFuel_success_fieldLength_facts
    {fuel : Nat} {context : Context} {expression base : Syntax.Expr}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {expected : Option Ty} {initial allocated : State}
    {id : ExpressionId} {result : InferredExpression × State}
    (expressionEq : expression.value = .field base dot name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (nonconstructor : constructorCalleeCandidates context allocated expression = .ok [])
    (success : inferExprFuel (fuel + 1) context expression expected initial =
      .ok result) :
    ∃ arrayResult arrayState element,
      inferExprFuel fuel context base none allocated = .ok (arrayResult, arrayState) ∧
        (arrayState.resolve arrayResult.type).viewElement? = some element ∧
        recordExpressionWithExpected context expression id (.fixed .uint256)
          (.arrayLength arrayResult.id) [] expected arrayState = .ok result := by
  unfold inferExprFuel at success
  simp only [allocationEq, expressionEq, nonconstructor, bind, Except.bind] at success
  cases missing : missingExplicitConstructor? context allocated expression with
  | error error => simp [missing] at success
  | ok missingResult =>
      cases missingResult with
      | some pair =>
          rcases pair with ⟨qualifiers, missingName⟩
          simp [missing] at success
      | none =>
          simp only [missing] at success
          by_cases lengthName : (name.value == "length") = true
          · simp only [lengthName, ↓reduceIte] at success
            cases baseRun : inferExprFuel fuel context base none allocated with
            | error error => simp [baseRun] at success
            | ok basePair =>
                rcases basePair with ⟨arrayResult, arrayState⟩
                simp only [baseRun] at success
                cases checked : arrayLengthOf arrayResult arrayState with
                | error error => simp [checked] at success
                | ok _ =>
                    simp only [checked] at success
                    obtain ⟨element, resolved⟩ := arrayLengthOf_ok checked
                    exact ⟨arrayResult, arrayState, element, rfl, resolved, success⟩
          · simp [lengthName] at success

end Solcore.Frontend.SourceInference.Detail
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.ShiftOperatorInference
/-! The shift branch of binary-operator inference: a shift leaves the state as
it is, adds no requirement, and has its value's type; finalization checks the
value's and the amount's types. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

theorem inferBinaryOperator_shift_result {context : Context}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {result : OperatorInferenceResult}
    (shift : isShiftOperator operator = true)
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.requirements = [] ∧ result.type = state.resolve left ∧ result.state = state := by
  unfold inferBinaryOperator at success
  rw [if_pos shift] at success
  simp only [pure, Except.pure, Except.ok.injEq] at success
  subst success
  exact ⟨rfl, rfl, rfl⟩

/-- A shift preserves every projection of the inference state. -/
theorem inferBinaryOperator_shift_projection {α : Type} {context : Context}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {result : OperatorInferenceResult} (projection : State → α)
    (shift : isShiftOperator operator = true)
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    projection result.state = projection state := by
  rw [(inferBinaryOperator_shift_result shift success).2.2]

end Solcore.Frontend.SourceInference.Detail
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.UncheckedOperatorInference
/-! The unchecked branch of binary-operator inference: the operands' types
unify, an open literal operand then becomes a Word, and the operator's meaning
is selected as for a checked operator whose operands are not open literals. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

theorem isShiftOperator_of_unchecked {operator : Syntax.BinaryOp}
    (unchecked : isUncheckedOperator operator = true) : isShiftOperator operator = false := by
  cases operator <;> simp_all [isUncheckedOperator, isShiftOperator]

theorem inferBinaryOperator_unchecked_result {context : Context}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {result : OperatorInferenceResult}
    (unchecked : isUncheckedOperator operator = true)
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    ∃ unified prepared, unify state left right = .ok unified ∧
      (prepared = unified ∨ ∃ expectedType, expected = some expectedType ∧
        unify unified (unified.resolve left) expectedType = .ok prepared) ∧
      binaryOperatorTail context operator left
        (binaryDefers operator
          (isOpenIntegerLiteralTarget state integerLiterals left ||
            isOpenIntegerLiteralTarget state integerLiterals right)
          prepared (prepared.resolve left)) prepared = .ok result := by
  unfold inferBinaryOperator at success
  rw [if_neg (by simp [isShiftOperator_of_unchecked unchecked])] at success
  cases unifyResult : unify state left right with
  | error error => simp [unifyResult, bind, Except.bind] at success
  | ok unified =>
      simp only [unifyResult, bind, Except.bind] at success
      cases expected with
      | none =>
          exact ⟨unified, unified, rfl, .inl rfl, by simpa [pure, Except.pure] using success⟩
      | some expectedType =>
          simp only [pure, Except.pure] at success
          split at success
          · exact ⟨unified, unified, rfl, .inl rfl, success⟩
          · cases second : unify unified (unified.resolve left) expectedType with
            | error error => simp [second] at success
            | ok prepared =>
                exact ⟨unified, prepared, rfl, .inr ⟨expectedType, rfl, second⟩, by
                  simpa [second] using success⟩

/-- A projection of the inference state that unification and the operator
tail without open literals preserve is also preserved by an unchecked
operator. -/
theorem inferBinaryOperator_unchecked_projection {α : Type} {context : Context}
    {operator : Syntax.BinaryOp} {left right : Ty} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {result : OperatorInferenceResult} (projection : State → α)
    (unified : ∀ {before after : State} {first second : Ty},
      unify before first second = .ok after → projection after = projection before)
    (tail : ∀ {defers : Bool} {before : State} {finished : OperatorInferenceResult},
      binaryOperatorTail context operator left defers before = .ok finished →
        projection finished.state = projection before)
    (unchecked : isUncheckedOperator operator = true)
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    projection result.state = projection state := by
  obtain ⟨middle, prepared, unifyResult, prepare, tailResult⟩ :=
    inferBinaryOperator_unchecked_result unchecked success
  rw [tail tailResult]
  rcases prepare with rfl | ⟨_, _, expectedResult⟩
  · exact unified unifyResult
  · rw [unified expectedResult, unified unifyResult]

end Solcore.Frontend.SourceInference.Detail
end
