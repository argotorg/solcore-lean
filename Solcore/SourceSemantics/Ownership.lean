import Solcore.SourceSemantics.Requirements

/-!
Whole-source ownership of stable local and requirement identities.

The typed occurrence graph contains several mirrors of the same evidence
identity.  This module counts only primary owners: expression requirement
lists, pattern requirement lists, and assignment requirement lists.  Coercion
steps, literal metadata, and match-level concatenations are checked by their
local judgments rather than counted a second time.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend.SourceInference

/-- Binder identities introduced by a flat pattern instruction stream. -/
def patternInstructionBinderIds
    (instructions : List MatchPatternInstruction) : List Resolved.LocalId :=
  instructions.filterMap fun instruction =>
    match instruction with
    | .binder binder => some binder.id
    | .wildcard | .integerLiteral .. | .constructor .. | .tuple .. => none

/-- Binder identities introduced by a resolved pattern root and its children. -/
def patternBinderIds (pattern : TypedMatchPattern) : List Resolved.LocalId :=
  match pattern.resolution with
  | .wildcard | .integerLiteral .. => []
  | .binder binder => [binder.id]
  | .constructor _ arguments | .tuple arguments =>
      patternInstructionBinderIds arguments

/-- Local definitions retained directly by a `for` header item. -/
def forItemDefinedLocalIds : ForItemForm → List Resolved.LocalId
  | .letDecl binder _ => [binder.id]
  | .expression _ | .assignValue .. | .assignBitNot _ => []

/-- Primary assignment-owned evidence in one `for` header item. -/
def forItemPrimaryRequirementIds : ForItemForm → List RequirementId
  | .assignValue assignment _ _ | .assignBitNot assignment =>
      assignment.requirements
  | .letDecl .. | .expression _ => []

/-- Local definitions owned directly by one expression form. -/
def expressionDefinedLocalIds : ExpressionForm → List Resolved.LocalId
  | .lambda parameters _ _ => parameters.map (fun binder => binder.id)
  | _ => []

/-- Local definitions owned directly by one statement form. -/
def statementDefinedLocalIds : StatementForm → List Resolved.LocalId
  | .letDecl binder _ => [binder.id]
  | .matchWith resolution =>
      resolution.hiddenScrutinee ::
        resolution.cases.flatMap fun matchCase =>
          patternBinderIds matchCase.pattern
  | .forLoop initializer _ post _ =>
      initializer.flatMap forItemDefinedLocalIds ++
        post.flatMap forItemDefinedLocalIds
  | _ => []

/-- Stable locals defined anywhere in a typed source, with inputs first and
then node-table order. -/
def definedLocalIds (source : TypedSource) : List Resolved.LocalId :=
  source.inputs.map (fun binder => binder.id) ++ source.nodes.flatMap fun node =>
    match node with
    | .expression expression => expressionDefinedLocalIds expression.form
    | .statement statement => statementDefinedLocalIds statement.form

/-- The executable carrier and the declarative semantics use one exact local
definition inventory.  The source-semantics helper names remain public for
proof readability, while finalization consumes the canonical carrier view. -/
@[simp] theorem patternInstructionBinderIds_eq_carrier
    (instructions : List MatchPatternInstruction) :
    MatchPatternInstruction.binderIds instructions =
      patternInstructionBinderIds instructions := by
  rfl

@[simp] theorem patternBinderIds_eq_carrier (pattern : TypedMatchPattern) :
    pattern.binderIds = patternBinderIds pattern := by
  cases pattern with
  | mk source type resolution requirements =>
      cases resolution <;> rfl

@[simp] theorem forItemDefinedLocalIds_eq_carrier (item : ForItemForm) :
    item.definedLocalIds = forItemDefinedLocalIds item := by
  cases item <;> rfl

@[simp] theorem flatMapForItemDefinedLocalIds_eq_carrier
    (items : List ForItemForm) :
    items.flatMap ForItemForm.definedLocalIds =
      items.flatMap forItemDefinedLocalIds := by
  induction items with
  | nil => rfl
  | cons item rest induction => simp [induction]

@[simp] theorem expressionDefinedLocalIds_eq_carrier (form : ExpressionForm) :
    form.definedLocalIds = expressionDefinedLocalIds form := by
  cases form <;> rfl

@[simp] theorem statementDefinedLocalIds_eq_carrier (form : StatementForm) :
    form.definedLocalIds = statementDefinedLocalIds form := by
  cases form <;> simp [StatementForm.definedLocalIds,
    statementDefinedLocalIds]

@[simp] theorem nodeDefinedLocalIds_eq_carrier (node : Node) :
    node.definedLocalIds =
      match node with
      | .expression expression => expressionDefinedLocalIds expression.form
      | .statement statement => statementDefinedLocalIds statement.form := by
  cases node <;> simp [Node.definedLocalIds]

@[simp] theorem flatMapNodeDefinedLocalIds_eq_carrier (nodes : List Node) :
    nodes.flatMap Node.definedLocalIds =
      nodes.flatMap (fun node =>
        match node with
        | .expression expression => expressionDefinedLocalIds expression.form
        | .statement statement => statementDefinedLocalIds statement.form) := by
  induction nodes with
  | nil => rfl
  | cons node rest induction => simp [induction]

/-- The canonical executable inventory is definitionally aligned with the
declarative ownership inventory. -/
@[simp] theorem typedSourceDefinedLocalIds_eq_carrier (source : TypedSource) :
    source.definedLocalIds = definedLocalIds source := by
  simp [TypedSource.definedLocalIds, definedLocalIds]

/-- One initialized lexical `let`, retaining both the complete binder metadata
and the root of its initializer subtree.  Lambda parameters, declaration
inputs, patterns, and uninitialized lets deliberately do not inhabit this
inventory because none of them owns a generalized initializer. -/
structure InitializedLetBinding where
  binder : TypedBinder
  initializer : NodeId
  deriving Repr, BEq, DecidableEq

/-- Initialized lets retained by one `for` initializer or post item. -/
def forItemInitializedLetBindings : ForItemForm → List InitializedLetBinding
  | .letDecl binder (some initializer) =>
      [{ binder, initializer := .expression initializer }]
  | .letDecl _ none | .expression _ | .assignValue .. | .assignBitNot _ => []

/-- Initialized lets retained directly by one statement form.  For-loop header
items are included in source order; lets nested under child statement or
expression occurrences are enumerated when those table nodes are visited. -/
def statementInitializedLetBindings : StatementForm → List InitializedLetBinding
  | .letDecl binder (some initializer) =>
      [{ binder, initializer := .expression initializer }]
  | .forLoop initializer _ post _ =>
      initializer.flatMap forItemInitializedLetBindings ++
        post.flatMap forItemInitializedLetBindings
  | .letDecl _ none | .returnStmt _ | .expression .. | .assignValue .. |
      .assignBitNot _ | .ifThen .. | .block _ | .matchWith _ | .whileLoop .. |
      .breakStmt | .continueStmt => []

/-- Every initialized lexical let in node-table order. -/
def initializedLetBindings (source : TypedSource) : List InitializedLetBinding :=
  source.nodes.flatMap fun node =>
    match node with
    | .expression _ => []
    | .statement statement => statementInitializedLetBindings statement.form

/-- Proof-facing name for the canonical executable local-scheme template
site.  Both layers deliberately share the same carrier. -/
abbrev LocalSchemeTemplateOwner := LocalSchemeTemplateSite

namespace InitializedLetBinding

/-- Flatten the qualified requirements owned by this initialized binder while
retaining their common initializer root. -/
def templateOwners (binding : InitializedLetBinding) :
    List LocalSchemeTemplateOwner :=
  binding.binder.schemeRequirements.map fun requirement => {
    binder := binding.binder
    initializer := binding.initializer
    requirement
  }

end InitializedLetBinding

/-- Every qualified local-scheme template owner in source and predicate order. -/
def localSchemeTemplateOwners (source : TypedSource) :
    List LocalSchemeTemplateOwner :=
  (initializedLetBindings source).flatMap InitializedLetBinding.templateOwners

/-- The executable and proof-facing template-site inventories agree for one
`for` header item. -/
@[simp] theorem forItemLocalSchemeTemplateSites_eq_carrier
    (item : ForItemForm) :
    item.localSchemeTemplateSites =
      (forItemInitializedLetBindings item).flatMap
        InitializedLetBinding.templateOwners := by
  cases item with
  | letDecl binder initializer =>
      cases initializer <;> simp [ForItemForm.localSchemeTemplateSites,
        forItemInitializedLetBindings, InitializedLetBinding.templateOwners]
  | expression expression => rfl
  | assignValue assignment operator value => rfl
  | assignBitNot assignment => rfl

@[simp] theorem flatMapForItemLocalSchemeTemplateSites_eq_carrier
    (items : List ForItemForm) :
    items.flatMap ForItemForm.localSchemeTemplateSites =
      (items.flatMap forItemInitializedLetBindings).flatMap
        InitializedLetBinding.templateOwners := by
  induction items with
  | nil => rfl
  | cons item rest induction => simp [induction]

/-- The executable and proof-facing template-site inventories agree for one
statement form. -/
@[simp] theorem statementLocalSchemeTemplateSites_eq_carrier
    (form : StatementForm) :
    form.localSchemeTemplateSites =
      (statementInitializedLetBindings form).flatMap
        InitializedLetBinding.templateOwners := by
  cases form with
  | letDecl binder initializer =>
      cases initializer <;> simp [StatementForm.localSchemeTemplateSites,
        statementInitializedLetBindings, InitializedLetBinding.templateOwners]
  | returnStmt value => rfl
  | expression expression trailingSemicolon => rfl
  | assignValue assignment operator value => rfl
  | assignBitNot assignment => rfl
  | ifThen condition thenBody elseBody => rfl
  | block body => rfl
  | matchWith resolution => rfl
  | forLoop initializer condition post body =>
      simp [StatementForm.localSchemeTemplateSites,
        statementInitializedLetBindings]
  | whileLoop condition body => rfl
  | breakStmt => rfl
  | continueStmt => rfl

@[simp] theorem nodeLocalSchemeTemplateSites_eq_carrier (node : Node) :
    node.localSchemeTemplateSites =
      match node with
      | .expression _ => []
      | .statement statement =>
          (statementInitializedLetBindings statement.form).flatMap
            InitializedLetBinding.templateOwners := by
  cases node <;> simp [Node.localSchemeTemplateSites]

/-- The canonical executable template sites are exactly the declarative owner
inventory. -/
@[simp] theorem typedSourceLocalSchemeTemplateSites_eq_carrier
    (source : TypedSource) :
    source.localSchemeTemplateSites = localSchemeTemplateOwners source := by
  cases source with
  | mk owner inputs roots nodes =>
      simp only [TypedSource.localSchemeTemplateSites,
        localSchemeTemplateOwners, initializedLetBindings]
      induction nodes with
      | nil => rfl
      | cons node nodes induction =>
          cases node <;> simp [induction]

/-- Stable identities of every qualified local-scheme template in the source. -/
def sourceLocalSchemeTemplateIds (source : TypedSource) : List RequirementId :=
  (localSchemeTemplateOwners source).map fun owner =>
    owner.requirement.templateRequirement

/-- The canonical carrier and declarative ownership inventory agree for one
`for` initializer or post item. -/
@[simp] theorem forItemLocalSchemeTemplateIds_eq_carrier
    (item : ForItemForm) :
    item.localSchemeTemplateIds =
      (forItemInitializedLetBindings item).flatMap fun binding =>
        binding.binder.schemeRequirements.map fun requirement =>
          requirement.templateRequirement := by
  cases item with
  | letDecl binder initializer =>
      cases initializer <;> simp [ForItemForm.localSchemeTemplateIds,
        forItemInitializedLetBindings]
  | expression expression => rfl
  | assignValue assignment operator value => rfl
  | assignBitNot assignment => rfl

@[simp] theorem flatMapForItemLocalSchemeTemplateIds_eq_carrier
    (items : List ForItemForm) :
    items.flatMap ForItemForm.localSchemeTemplateIds =
      (items.flatMap forItemInitializedLetBindings).flatMap fun binding =>
        binding.binder.schemeRequirements.map fun requirement =>
          requirement.templateRequirement := by
  induction items with
  | nil => rfl
  | cons item rest induction => simp [induction]

/-- The canonical carrier and declarative ownership inventory agree for one
statement form. -/
@[simp] theorem statementLocalSchemeTemplateIds_eq_carrier
    (form : StatementForm) :
    form.localSchemeTemplateIds =
      (statementInitializedLetBindings form).flatMap fun binding =>
        binding.binder.schemeRequirements.map fun requirement =>
          requirement.templateRequirement := by
  cases form with
  | letDecl binder initializer =>
      cases initializer <;> simp [StatementForm.localSchemeTemplateIds,
        statementInitializedLetBindings]
  | returnStmt value => rfl
  | expression expression trailingSemicolon => rfl
  | assignValue assignment operator value => rfl
  | assignBitNot assignment => rfl
  | ifThen condition thenBody elseBody => rfl
  | block body => rfl
  | matchWith resolution => rfl
  | forLoop initializer condition post body =>
      simp [StatementForm.localSchemeTemplateIds,
        statementInitializedLetBindings]
  | whileLoop condition body => rfl
  | breakStmt => rfl
  | continueStmt => rfl

@[simp] theorem nodeLocalSchemeTemplateIds_eq_carrier (node : Node) :
    node.localSchemeTemplateIds =
      match node with
      | .expression _ => []
      | .statement statement =>
          (statementInitializedLetBindings statement.form).flatMap fun binding =>
            binding.binder.schemeRequirements.map fun requirement =>
              requirement.templateRequirement := by
  cases node <;> simp [Node.localSchemeTemplateIds]

@[simp] theorem flatMapNodeLocalSchemeTemplateIds_eq_carrier
    (nodes : List Node) :
    nodes.flatMap Node.localSchemeTemplateIds =
      nodes.flatMap fun node =>
        match node with
        | .expression _ => []
        | .statement statement =>
            (statementInitializedLetBindings statement.form).flatMap fun binding =>
              binding.binder.schemeRequirements.map fun requirement =>
                requirement.templateRequirement := by
  induction nodes with
  | nil => rfl
  | cons node rest induction => simp [induction]

/-- The canonical executable template inventory is exactly the declarative
source ownership inventory. -/
@[simp] theorem typedSourceLocalSchemeTemplateIds_eq_carrier
    (source : TypedSource) :
    source.localSchemeTemplateIds = sourceLocalSchemeTemplateIds source := by
  cases source with
  | mk owner inputs roots nodes =>
      simp only [TypedSource.localSchemeTemplateIds, sourceLocalSchemeTemplateIds,
        localSchemeTemplateOwners, initializedLetBindings, List.map_flatMap,
        InitializedLetBinding.templateOwners, List.map_map, Function.comp_def]
      induction nodes with
      | nil => rfl
      | cons node nodes induction =>
          cases node <;> simp [induction]

/-- Forgetting the owner metadata from canonical executable template sites
recovers the stable template-ID inventory exactly. -/
theorem typedSourceLocalSchemeTemplateIds_eq_sites (source : TypedSource) :
    source.localSchemeTemplateIds =
      source.localSchemeTemplateSites.map fun site =>
        site.requirement.templateRequirement := by
  rw [typedSourceLocalSchemeTemplateIds_eq_carrier,
    typedSourceLocalSchemeTemplateSites_eq_carrier]
  rfl

/-- Exact source ownership of one qualified local-scheme template. -/
def ContainsLocalSchemeTemplate (source : TypedSource)
    (owner : LocalSchemeTemplateOwner) : Prop :=
  owner ∈ localSchemeTemplateOwners source

theorem sourceLocalSchemeTemplateIds_mem_iff
    {source : TypedSource} {id : RequirementId} :
    id ∈ sourceLocalSchemeTemplateIds source ↔
      ∃ owner, ContainsLocalSchemeTemplate source owner ∧
        owner.requirement.templateRequirement = id := by
  simp [sourceLocalSchemeTemplateIds, ContainsLocalSchemeTemplate]

/-- One retained solved row is exactly the assumption-template row named by a
source-owned qualified local scheme.  Ledger membership remains a separate
whole-body condition, so this relation can be reused by that later layer. -/
inductive LocalSchemeTemplateRowOwned (source : TypedSource)
    (row : SolvedRequirement) : Prop where
  | intro
      (owner : LocalSchemeTemplateOwner)
      (contains : ContainsLocalSchemeTemplate source owner)
      (id_eq : row.id = owner.requirement.templateRequirement)
      (predicate_eq : row.predicate = owner.requirement.predicate)
      (evidence_eq : row.evidence = .assumption owner.requirement.predicate) :
      LocalSchemeTemplateRowOwned source row

/-- Template identities are globally unique across every initialized local
scheme in one typed source. -/
structure LocalSchemeTemplateOwnership (source : TypedSource) : Prop where
  ids_unique : (sourceLocalSchemeTemplateIds source).Nodup

namespace LocalSchemeTemplateOwner

theorem binding_mem
    {source : TypedSource} {owner : LocalSchemeTemplateOwner}
    (contains : ContainsLocalSchemeTemplate source owner) :
    { binder := owner.binder, initializer := owner.initializer } ∈
      initializedLetBindings source := by
  unfold ContainsLocalSchemeTemplate localSchemeTemplateOwners at contains
  rcases List.mem_flatMap.mp contains with ⟨binding, bindingMem, ownerMem⟩
  simp only [InitializedLetBinding.templateOwners, List.mem_map] at ownerMem
  rcases ownerMem with ⟨requirement, _, ownerEq⟩
  subst owner
  simpa using bindingMem

theorem requirement_mem
    {source : TypedSource} {owner : LocalSchemeTemplateOwner}
    (contains : ContainsLocalSchemeTemplate source owner) :
    owner.requirement ∈ owner.binder.schemeRequirements := by
  unfold ContainsLocalSchemeTemplate localSchemeTemplateOwners at contains
  rcases List.mem_flatMap.mp contains with ⟨binding, _, ownerMem⟩
  simp only [InitializedLetBinding.templateOwners, List.mem_map] at ownerMem
  rcases ownerMem with ⟨requirement, requirementMem, ownerEq⟩
  subst owner
  simpa using requirementMem

end LocalSchemeTemplateOwner

namespace LocalSchemeTemplateRowOwned

theorem template_id_mem
    {source : TypedSource} {row : SolvedRequirement}
    (owned : LocalSchemeTemplateRowOwned source row) :
    row.id ∈ sourceLocalSchemeTemplateIds source := by
  cases owned with
  | intro owner contains idEq _ _ =>
      exact sourceLocalSchemeTemplateIds_mem_iff.mpr
        ⟨owner, contains, idEq.symm⟩

theorem exact_owner
    {source : TypedSource} {row : SolvedRequirement}
    (owned : LocalSchemeTemplateRowOwned source row) :
    ∃ owner, ContainsLocalSchemeTemplate source owner ∧
      row.id = owner.requirement.templateRequirement ∧
      row.predicate = owner.requirement.predicate ∧
      row.evidence = .assumption owner.requirement.predicate := by
  cases owned with
  | intro owner contains idEq predicateEq evidenceEq =>
      exact ⟨owner, contains, idEq, predicateEq, evidenceEq⟩

end LocalSchemeTemplateRowOwned

namespace LocalSchemeTemplateOwnership

theorem owner_ids_unique
    {source : TypedSource} (ownership : LocalSchemeTemplateOwnership source) :
    ((localSchemeTemplateOwners source).map fun owner =>
      owner.requirement.templateRequirement).Nodup :=
  ownership.ids_unique

private theorem owner_eq_of_mem_of_ids_nodup
    {owners : List LocalSchemeTemplateOwner}
    (idsUnique : (owners.map fun owner =>
      owner.requirement.templateRequirement).Nodup)
    {left right : LocalSchemeTemplateOwner}
    (leftMem : left ∈ owners)
    (rightMem : right ∈ owners)
    (idEq : left.requirement.templateRequirement =
      right.requirement.templateRequirement) :
    left = right := by
  induction owners generalizing left right with
  | nil => simp at leftMem
  | cons first rest induction =>
      simp only [List.map_cons, List.nodup_cons] at idsUnique
      rcases idsUnique with ⟨firstFresh, restUnique⟩
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          apply firstFresh
          exact List.mem_map.mpr ⟨right, rightMem, idEq.symm⟩
      · rcases rightMem with rfl | rightMem
        · exfalso
          apply firstFresh
          exact List.mem_map.mpr ⟨left, leftMem, idEq⟩
        · exact induction restUnique leftMem rightMem idEq

/-- Source-wide template-identity uniqueness makes the owner of one retained
template identity unique as well. -/
theorem owner_unique
    {source : TypedSource} (ownership : LocalSchemeTemplateOwnership source)
    {left right : LocalSchemeTemplateOwner}
    (leftContains : ContainsLocalSchemeTemplate source left)
    (rightContains : ContainsLocalSchemeTemplate source right)
    (idEq : left.requirement.templateRequirement =
      right.requirement.templateRequirement) :
    left = right := by
  exact owner_eq_of_mem_of_ids_nodup ownership.owner_ids_unique
    leftContains rightContains idEq

end LocalSchemeTemplateOwnership

/-- Primary evidence owners retained directly by one statement form. -/
def statementPrimaryRequirementIds : StatementForm → List RequirementId
  | .assignValue assignment _ _ | .assignBitNot assignment =>
      assignment.requirements
  | .matchWith resolution =>
      resolution.cases.flatMap fun matchCase => matchCase.pattern.requirements
  | .forLoop initializer _ post _ =>
      initializer.flatMap forItemPrimaryRequirementIds ++
        post.flatMap forItemPrimaryRequirementIds
  | _ => []

/-- Proof-facing name for the canonical executable primary requirement site.
Both layers deliberately share the same carrier. -/
abbrev PrimaryRequirementOccurrence := PrimaryRequirementSite

/-- Primary requirement attachments owned by one expression occurrence. -/
def expressionPrimaryRequirementOccurrences
    (expression : ExpressionNode) : List PrimaryRequirementOccurrence :=
  expression.requirements.map fun requirement => {
    occurrence := .expression expression.id
    requirement
  }

/-- Primary requirement attachments owned directly by one statement
occurrence.  Mirrored match-level and coercion metadata remain excluded by
the same policy as `statementPrimaryRequirementIds`. -/
def statementPrimaryRequirementOccurrences
    (statement : StatementNode) : List PrimaryRequirementOccurrence :=
  (statementPrimaryRequirementIds statement.form).map fun requirement => {
    occurrence := .statement statement.id
    requirement
  }

/-- Primary requirement attachments retained by one heterogeneous source
node. -/
def nodePrimaryRequirementOccurrences : Node → List PrimaryRequirementOccurrence
  | .expression expression => expressionPrimaryRequirementOccurrences expression
  | .statement statement => statementPrimaryRequirementOccurrences statement

/-- Every primary requirement attachment in node-table and attachment order,
with its exact category-safe owning occurrence. -/
def primaryRequirementOccurrences
    (source : TypedSource) : List PrimaryRequirementOccurrence :=
  source.nodes.flatMap nodePrimaryRequirementOccurrences

/-- One stable requirement identity is primarily attached at one exact source
occurrence. -/
def PrimaryRequirementOccursAt (source : TypedSource) (occurrence : NodeId)
    (requirement : RequirementId) : Prop :=
  { occurrence, requirement } ∈ primaryRequirementOccurrences source

/-- Every primary evidence owner in node-table order. -/
def primaryRequirementIds (source : TypedSource) : List RequirementId :=
  source.nodes.flatMap fun node =>
    match node with
    | .expression expression => expression.requirements
    | .statement statement => statementPrimaryRequirementIds statement.form

/-- The executable carrier and declarative semantics agree on the primary
requirements owned by one `for` header item. -/
@[simp] theorem forItemPrimaryRequirementIds_eq_carrier
    (item : ForItemForm) :
    item.primaryRequirementIds = forItemPrimaryRequirementIds item := by
  cases item <;> rfl

@[simp] theorem flatMapForItemPrimaryRequirementIds_eq_carrier
    (items : List ForItemForm) :
    items.flatMap ForItemForm.primaryRequirementIds =
      items.flatMap forItemPrimaryRequirementIds := by
  induction items with
  | nil => rfl
  | cons item rest induction => simp [induction]

/-- The executable carrier and declarative semantics agree on the primary
requirements owned directly by one statement form. -/
@[simp] theorem statementPrimaryRequirementIds_eq_carrier
    (form : StatementForm) :
    form.primaryRequirementIds = statementPrimaryRequirementIds form := by
  cases form <;> simp [StatementForm.primaryRequirementIds,
    statementPrimaryRequirementIds]

@[simp] theorem nodePrimaryRequirementIds_eq_carrier (node : Node) :
    node.primaryRequirementIds =
      match node with
      | .expression expression => expression.requirements
      | .statement statement => statementPrimaryRequirementIds statement.form := by
  cases node <;> simp [Node.primaryRequirementIds]

@[simp] theorem flatMapNodePrimaryRequirementIds_eq_carrier
    (nodes : List Node) :
    nodes.flatMap Node.primaryRequirementIds =
      nodes.flatMap (fun node =>
        match node with
        | .expression expression => expression.requirements
        | .statement statement => statementPrimaryRequirementIds statement.form) := by
  induction nodes with
  | nil => rfl
  | cons node rest induction => simp [induction]

/-- The canonical executable primary-requirement inventory is exactly the
declarative ownership inventory. -/
@[simp] theorem typedSourcePrimaryRequirementIds_eq_carrier
    (source : TypedSource) :
    source.primaryRequirementIds = primaryRequirementIds source := by
  simp [TypedSource.primaryRequirementIds, primaryRequirementIds]

/-- The executable primary sites and proof-facing occurrences agree for one
heterogeneous source node. -/
@[simp] theorem nodePrimaryRequirementSites_eq_carrier (node : Node) :
    node.primaryRequirementSites = nodePrimaryRequirementOccurrences node := by
  cases node with
  | expression expression =>
      rfl
  | statement statement =>
      simp [Node.primaryRequirementSites, nodePrimaryRequirementOccurrences,
        statementPrimaryRequirementOccurrences]

/-- The executable primary-site inventory is exactly the proof-facing
occurrence inventory. -/
@[simp] theorem typedSourcePrimaryRequirementSites_eq_carrier
    (source : TypedSource) :
    source.primaryRequirementSites = primaryRequirementOccurrences source := by
  cases source with
  | mk owner inputs roots nodes =>
      simp only [TypedSource.primaryRequirementSites,
        primaryRequirementOccurrences]
      induction nodes with
      | nil => rfl
      | cons node nodes induction => simp [induction]

/-- Forgetting occurrence ownership from the detailed inventory recovers the
original flat primary-requirement identity inventory exactly. -/
@[simp] theorem primaryRequirementOccurrenceIds_eq
    (source : TypedSource) :
    (primaryRequirementOccurrences source).map
        (fun occurrence => occurrence.requirement) =
      primaryRequirementIds source := by
  cases source with
  | mk owner inputs roots nodes =>
      simp only [primaryRequirementOccurrences, primaryRequirementIds]
      induction nodes with
      | nil => rfl
      | cons node nodes induction =>
          cases node <;>
            simp [nodePrimaryRequirementOccurrences,
              expressionPrimaryRequirementOccurrences,
              statementPrimaryRequirementOccurrences, Function.comp_def,
              induction]

theorem primaryRequirementIds_mem_iff_occursAt
    {source : TypedSource} {requirement : RequirementId} :
    requirement ∈ primaryRequirementIds source ↔
      ∃ occurrence, PrimaryRequirementOccursAt source occurrence requirement := by
  rw [← primaryRequirementOccurrenceIds_eq]
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨owned, ownedMem, ownedId⟩
    rcases owned with ⟨occurrence, candidate⟩
    simp only at ownedId
    subst candidate
    exact ⟨occurrence, ownedMem⟩
  · rintro ⟨occurrence, occurs⟩
    exact List.mem_map.mpr
      ⟨{ occurrence, requirement }, occurs, rfl⟩

/-- Every local definition has a globally unique stable identity owned by the
declaration represented by this source. -/
structure LocalIdentityOwnership (source : TypedSource) : Prop where
  unique : (definedLocalIds source).Nodup
  owned : ∀ id, id ∈ definedLocalIds source → id.owner = source.owner

/-- Primary source occurrences own the solved ledger exactly once. -/
structure RequirementOwnership (context : Context) (source : TypedSource) : Prop where
  primary_unique : (primaryRequirementIds source).Nodup
  ledger_exact : (primaryRequirementIds source).Perm
    (context.solvedRequirements.map fun requirement => requirement.id)

namespace RequirementOwnership

theorem ledger_ids_unique
    {context : Context} {source : TypedSource}
    (ownership : RequirementOwnership context source) :
    RequirementIdsUnique context := by
  unfold RequirementIdsUnique
  exact ownership.ledger_exact.nodup_iff.mp ownership.primary_unique

theorem primary_mem_iff_ledger
    {context : Context} {source : TypedSource}
    (ownership : RequirementOwnership context source)
    (id : RequirementId) :
    id ∈ primaryRequirementIds source ↔
      id ∈ context.solvedRequirements.map (fun requirement => requirement.id) :=
  ownership.ledger_exact.mem_iff

end RequirementOwnership

end Solcore.SourceSemantics
