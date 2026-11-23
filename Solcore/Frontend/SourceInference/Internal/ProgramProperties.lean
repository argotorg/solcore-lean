import Solcore.Frontend.ProgramInterfaces
import Solcore.Frontend.Internal.CheckingProperties
import Solcore.Frontend.Internal.SignatureProperties
import Solcore.Frontend.SourceInference.Internal.ExpressionProperties
import Solcore.Frontend.SourceInference.Program
import Solcore.Frontend.SourceInference.Internal.TypedIRProperties

/-!
# Finalization projections

Success projections of source-inference finalization.
-/

/-! Success projections for source-inference finalization. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

/-- Exact category-preserving table membership recognized by the executable
source-node membership test. -/
theorem sourceContainsNodeId_eq_true_iff
    (source : TypedSource) (id : NodeId) :
    sourceContainsNodeId source id = true ↔
      ∃ node, node ∈ source.nodes ∧ node.id = id := by
  simp [sourceContainsNodeId]

private theorem occurrenceId_beq_iff_eq
    (left right : OccurrenceId) :
    (left == right) = true ↔ left = right := by
  constructor
  · intro accepted
    cases left
    cases right
    delta instBEqOccurrenceId instBEqOccurrenceId.beq at accepted
    obtain ⟨ownerEqual, indexEqual⟩ := Bool.and_eq_true_iff.mp accepted
    cases beq_iff_eq.mp ownerEqual
    cases beq_iff_eq.mp indexEqual
    rfl
  · rintro rfl
    cases left
    delta instBEqOccurrenceId instBEqOccurrenceId.beq
    simp

private theorem occurrenceId_contains_iff_mem
    (ids : List OccurrenceId) (id : OccurrenceId) :
    ids.contains id = true ↔ id ∈ ids := by
  induction ids with
  | nil => simp
  | cons head tail induction =>
      simp only [List.contains_cons, List.mem_cons]
      rw [Bool.or_eq_true, occurrenceId_beq_iff_eq, induction]

private theorem localIdMember_eq_true_iff
    (ids : List Resolved.LocalId) (id : Resolved.LocalId) :
    localIdMember ids id = true ↔ id ∈ ids := by
  simp [localIdMember]

private theorem requirementIdMember_eq_true_iff
    (ids : List RequirementId) (id : RequirementId) :
    requirementIdMember ids id = true ↔ id ∈ ids := by
  simp [requirementIdMember]

private theorem nodeIdMember_eq_true_iff
    (ids : List NodeId) (id : NodeId) :
    nodeIdMember ids id = true ↔ id ∈ ids := by
  simp [nodeIdMember]

private theorem validateOccurrenceTableFrom_success
    {owner : Resolved.DeclarationId} {seen : List OccurrenceId}
    {nodes : List Node}
    (success : validateOccurrenceTableFrom owner seen nodes = .ok ()) :
    (∀ node, node ∈ nodes → node.occurrenceId.owner = owner) ∧
      (nodes.map Node.occurrenceId).Nodup ∧
      ∀ occurrence, occurrence ∈ nodes.map Node.occurrenceId →
        occurrence ∉ seen := by
  induction nodes generalizing seen with
  | nil => simp
  | cons node rest induction =>
      cases ownerMismatch : node.occurrenceId.owner != owner with
      | true =>
          simp [validateOccurrenceTableFrom, ownerMismatch, bind, Except.bind]
            at success
      | false =>
        have ownerEq : node.occurrenceId.owner = owner := by
          simpa using ownerMismatch
        cases duplicate : seen.contains node.occurrenceId with
        | true =>
            simp [validateOccurrenceTableFrom, ownerMismatch, duplicate,
              bind, Except.bind] at success
        | false =>
          have seenFresh : node.occurrenceId ∉ seen := by
            intro member
            have contained : seen.contains node.occurrenceId = true :=
              (occurrenceId_contains_iff_mem seen node.occurrenceId).mpr member
            rw [duplicate] at contained
            simp at contained
          have tailSuccess :
              validateOccurrenceTableFrom owner
                (node.occurrenceId :: seen) rest = .ok () := by
            simpa [validateOccurrenceTableFrom, ownerMismatch, duplicate,
              bind, Except.bind] using success
          obtain ⟨tailOwned, tailUnique, tailFresh⟩ := induction tailSuccess
          refine ⟨?_, ?_, ?_⟩
          · intro candidate member
            rcases List.mem_cons.mp member with rfl | tailMember
            · exact ownerEq
            · exact tailOwned candidate tailMember
          · simp only [List.map_cons, List.nodup_cons]
            refine ⟨?_, tailUnique⟩
            intro tailMember
            exact tailFresh node.occurrenceId tailMember (by simp)
          · intro occurrence member occurrenceSeen
            simp only [List.map_cons, List.mem_cons] at member
            rcases member with headEq | tailMember
            · subst occurrence
              exact seenFresh occurrenceSeen
            · exact tailFresh occurrence tailMember (by simp [occurrenceSeen])

/-- Successful occurrence-table validation proves declaration ownership for
every node retained by the table. -/
theorem validateOccurrenceTable_success_nodesOwned
    {source : TypedSource}
    (success : validateOccurrenceTable source = .ok ()) :
    ∀ node, node ∈ source.nodes →
      node.occurrenceId.owner = source.owner := by
  exact (validateOccurrenceTableFrom_success success).1

/-- Successful occurrence-table validation proves global uniqueness after
erasing the expression/statement category. -/
theorem validateOccurrenceTable_success_nodeOccurrencesUnique
    {source : TypedSource}
    (success : validateOccurrenceTable source = .ok ()) :
    (source.nodes.map Node.occurrenceId).Nodup := by
  exact (validateOccurrenceTableFrom_success success).2.1

private theorem validateLocalIdentitiesFrom_success
    {owner : Resolved.DeclarationId} {seen ids : List Resolved.LocalId}
    (success : validateLocalIdentitiesFrom owner seen ids = .ok ()) :
    ids.Nodup ∧
      (∀ id, id ∈ ids → id.owner = owner) ∧
      ∀ id, id ∈ ids → id ∉ seen := by
  induction ids generalizing seen with
  | nil => simp
  | cons head tail induction =>
      by_cases ownerEq : head.owner = owner
      · have ownerMismatch : ¬ head.owner ≠ owner := by
          simp [ownerEq]
        cases duplicate : localIdMember seen head with
        | true =>
            simp [validateLocalIdentitiesFrom, ownerMismatch, duplicate,
              bind, Except.bind] at success
        | false =>
            have headFresh : head ∉ seen := by
              intro member
              have contained : localIdMember seen head = true :=
                (localIdMember_eq_true_iff seen head).mpr member
              rw [duplicate] at contained
              simp at contained
            have tailSuccess :
                validateLocalIdentitiesFrom owner (head :: seen) tail =
                  .ok () := by
              simpa [validateLocalIdentitiesFrom, ownerMismatch, duplicate,
                bind, Except.bind] using success
            obtain ⟨tailUnique, tailOwned, tailFresh⟩ := induction tailSuccess
            refine ⟨?_, ?_, ?_⟩
            · simp only [List.nodup_cons]
              refine ⟨?_, tailUnique⟩
              intro member
              exact tailFresh head member (by simp)
            · intro id member
              rcases List.mem_cons.mp member with rfl | tailMember
              · exact ownerEq
              · exact tailOwned id tailMember
            · intro id member seenMember
              rcases List.mem_cons.mp member with rfl | tailMember
              · exact headFresh seenMember
              · exact tailFresh id tailMember (by simp [seenMember])
      · have ownerMismatch : head.owner ≠ owner := ownerEq
        simp [validateLocalIdentitiesFrom, ownerMismatch, bind, Except.bind]
          at success

/-- Successful local-identity validation proves global binder uniqueness. -/
theorem validateSourceLocalIdentities_success_unique
    {source : TypedSource}
    (success : validateSourceLocalIdentities source = .ok ()) :
    source.definedLocalIds.Nodup :=
  (validateLocalIdentitiesFrom_success success).1

/-- Successful local-identity validation proves declaration ownership for
every retained binder. -/
theorem validateSourceLocalIdentities_success_owned
    {source : TypedSource}
    (success : validateSourceLocalIdentities source = .ok ()) :
    ∀ id, id ∈ source.definedLocalIds → id.owner = source.owner :=
  (validateLocalIdentitiesFrom_success success).2.1

private theorem validateRequirementIdsUniqueFrom_success
    {duplicateError : RequirementId → Error}
    {seen ids : List RequirementId}
    (success : validateRequirementIdsUniqueFrom duplicateError seen ids =
      .ok ()) :
    ids.Nodup ∧ ∀ id, id ∈ ids → id ∉ seen := by
  induction ids generalizing seen with
  | nil => simp
  | cons head tail induction =>
      cases duplicate : requirementIdMember seen head with
      | true =>
          simp [validateRequirementIdsUniqueFrom, duplicate, bind,
            Except.bind] at success
      | false =>
          have headFresh : head ∉ seen := by
            intro member
            have contained : requirementIdMember seen head = true :=
              (requirementIdMember_eq_true_iff seen head).mpr member
            rw [duplicate] at contained
            simp at contained
          have tailSuccess :
              validateRequirementIdsUniqueFrom duplicateError (head :: seen)
                tail = .ok () := by
            simpa [validateRequirementIdsUniqueFrom, duplicate, bind,
              Except.bind] using success
          obtain ⟨tailUnique, tailFresh⟩ := induction tailSuccess
          refine ⟨?_, ?_⟩
          · simp only [List.nodup_cons]
            refine ⟨?_, tailUnique⟩
            intro member
            exact tailFresh head member (by simp)
          · intro id member seenMember
            rcases List.mem_cons.mp member with rfl | tailMember
            · exact headFresh seenMember
            · exact tailFresh id tailMember (by simp [seenMember])

private theorem validateRequirementIdsContained_success
    {missingError : RequirementId → Error}
    {available requested : List RequirementId}
    (success : validateRequirementIdsContained missingError available requested =
      .ok ()) :
    requested ⊆ available := by
  induction requested with
  | nil => simp
  | cons head tail induction =>
      cases memberResult : requirementIdMember available head with
      | false =>
          simp [validateRequirementIdsContained, memberResult, bind,
            Except.bind] at success
      | true =>
          have headMember : head ∈ available :=
            (requirementIdMember_eq_true_iff available head).mp memberResult
          have tailSuccess :
              validateRequirementIdsContained missingError available tail =
                .ok () := by
            simpa [validateRequirementIdsContained, memberResult, bind,
              Except.bind] using success
          intro id member
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact headMember
          · exact induction tailSuccess tailMember

/-- Successful exact-ledger validation proves both side-specific uniqueness
facts and the order-insensitive primary-to-ledger bijection. -/
theorem validateSourceRequirementOwnership_success
    {source : TypedSource} {requirements : List Requirement}
    (success : validateSourceRequirementOwnership source requirements =
      .ok ()) :
    source.primaryRequirementIds.Nodup ∧
      (requirements.map (fun requirement => requirement.id)).Nodup ∧
      source.primaryRequirementIds.Perm
        (requirements.map (fun requirement => requirement.id)) := by
  let primary := source.primaryRequirementIds
  let ledger := requirements.map (fun requirement => requirement.id)
  have primarySuccess :
      validateRequirementIdsUniqueFrom Error.duplicatePrimaryRequirement []
        primary = .ok () := by
    cases primaryResult :
        validateRequirementIdsUniqueFrom Error.duplicatePrimaryRequirement []
          primary with
    | error error =>
        simp [validateSourceRequirementOwnership, primary,
          primaryResult, bind, Except.bind] at success
    | ok value =>
        exact congrArg Except.ok (Subsingleton.elim _ _)
  have ledgerSuccess :
      validateRequirementIdsUniqueFrom Error.duplicateRequirementLedgerRow []
        ledger = .ok () := by
    cases ledgerResult :
        validateRequirementIdsUniqueFrom Error.duplicateRequirementLedgerRow []
          ledger with
    | error error =>
        simp [validateSourceRequirementOwnership, primary, ledger,
          primarySuccess, ledgerResult, bind, Except.bind] at success
    | ok value =>
        exact congrArg Except.ok (Subsingleton.elim _ _)
  have primaryContained :
      validateRequirementIdsContained Error.missingRequirementLedgerRow ledger
        primary = .ok () := by
    cases containmentResult :
        validateRequirementIdsContained Error.missingRequirementLedgerRow ledger
          primary with
    | error error =>
        simp [validateSourceRequirementOwnership, primary, ledger,
          primarySuccess, ledgerSuccess, containmentResult, bind, Except.bind]
          at success
    | ok value =>
        exact congrArg Except.ok (Subsingleton.elim _ _)
  have ledgerContained :
      validateRequirementIdsContained Error.unattachedRequirementLedgerRow
        primary ledger = .ok () := by
    simpa [validateSourceRequirementOwnership, primary, ledger, primarySuccess,
      ledgerSuccess, primaryContained, bind, Except.bind] using success
  have primaryUnique : primary.Nodup :=
    (validateRequirementIdsUniqueFrom_success primarySuccess).1
  have ledgerUnique : ledger.Nodup :=
    (validateRequirementIdsUniqueFrom_success ledgerSuccess).1
  have primarySubset : primary ⊆ ledger :=
    validateRequirementIdsContained_success primaryContained
  have ledgerSubset : ledger ⊆ primary :=
    validateRequirementIdsContained_success ledgerContained
  have exactMembership : ∀ id, id ∈ primary ↔ id ∈ ledger :=
    fun _ => ⟨fun member => primarySubset member,
      fun member => ledgerSubset member⟩
  exact ⟨primaryUnique, ledgerUnique,
    (List.perm_ext_iff_of_nodup primaryUnique ledgerUnique).2 exactMembership⟩

/-- Successful qualified-template validation gives the exact classification
permutation and proves that every classified identity has a raw ledger row. -/
theorem validateSourceTemplateTracking_success
    {source : TypedSource} {state : State}
    (success : validateSourceTemplateTracking source state = .ok ()) :
    source.localSchemeTemplateIds.Nodup ∧
      state.localSchemeAssumptions.Nodup ∧
      state.localSchemeAssumptions.Perm source.localSchemeTemplateIds ∧
      state.localSchemeAssumptions ⊆
        state.requirements.map (fun requirement => requirement.id) := by
  let templates := source.localSchemeTemplateIds
  let classified := state.localSchemeAssumptions
  let ledger := state.requirements.map (fun requirement => requirement.id)
  have templatesSuccess :
      validateRequirementIdsUniqueFrom Error.duplicateLocalSchemeTemplate []
        templates = .ok () := by
    cases templatesResult :
        validateRequirementIdsUniqueFrom Error.duplicateLocalSchemeTemplate []
          templates with
    | error error =>
        simp [validateSourceTemplateTracking, templates, templatesResult,
          bind, Except.bind] at success
    | ok value =>
        exact congrArg Except.ok (Subsingleton.elim _ _)
  have classifiedSuccess :
      validateRequirementIdsUniqueFrom Error.duplicateLocalSchemeAssumption []
        classified = .ok () := by
    cases classifiedResult :
        validateRequirementIdsUniqueFrom Error.duplicateLocalSchemeAssumption []
          classified with
    | error error =>
        simp [validateSourceTemplateTracking, templates, classified,
          templatesSuccess, classifiedResult, bind, Except.bind] at success
    | ok value =>
        exact congrArg Except.ok (Subsingleton.elim _ _)
  have templatesContained :
      validateRequirementIdsContained Error.missingLocalSchemeAssumption
        classified templates = .ok () := by
    cases templatesContainedResult :
        validateRequirementIdsContained Error.missingLocalSchemeAssumption
          classified templates with
    | error error =>
        simp [validateSourceTemplateTracking, templates, classified,
          templatesSuccess, classifiedSuccess, templatesContainedResult,
          bind, Except.bind] at success
    | ok value =>
        exact congrArg Except.ok (Subsingleton.elim _ _)
  have classifiedContained :
      validateRequirementIdsContained Error.unownedLocalSchemeAssumption
        templates classified = .ok () := by
    cases classifiedContainedResult :
        validateRequirementIdsContained Error.unownedLocalSchemeAssumption
          templates classified with
    | error error =>
        simp [validateSourceTemplateTracking, templates, classified,
          templatesSuccess, classifiedSuccess, templatesContained,
          classifiedContainedResult, bind, Except.bind] at success
    | ok value =>
        exact congrArg Except.ok (Subsingleton.elim _ _)
  have ledgerContained :
      validateRequirementIdsContained Error.missingLocalSchemeRequirement
        ledger classified = .ok () := by
    simpa [validateSourceTemplateTracking, templates, classified, ledger,
      templatesSuccess, classifiedSuccess, templatesContained,
      classifiedContained, bind, Except.bind] using success
  have templatesUnique : templates.Nodup :=
    (validateRequirementIdsUniqueFrom_success templatesSuccess).1
  have classifiedUnique : classified.Nodup :=
    (validateRequirementIdsUniqueFrom_success classifiedSuccess).1
  have templatesSubset : templates ⊆ classified :=
    validateRequirementIdsContained_success templatesContained
  have classifiedSubset : classified ⊆ templates :=
    validateRequirementIdsContained_success classifiedContained
  have classifiedExact : classified.Perm templates :=
    (List.perm_ext_iff_of_nodup classifiedUnique templatesUnique).2
      (fun _ => ⟨fun member => classifiedSubset member,
        fun member => templatesSubset member⟩)
  exact ⟨templatesUnique, classifiedUnique, classifiedExact,
    validateRequirementIdsContained_success ledgerContained⟩

/-- Successful validation of one qualified template exposes its exact raw
ledger row, primary source attachment, predicate agreement, and executable
initializer-subtree membership. -/
theorem validateSourceTemplateScope_success
    {source : TypedSource} {state : State}
    {site : LocalSchemeTemplateSite}
    (success : validateSourceTemplateScope source state site = .ok ()) :
    ∃ requirement primary,
      requirement ∈ state.requirements ∧
      requirement.id = site.requirement.templateRequirement ∧
      applyPredicate state requirement.predicate = site.requirement.predicate ∧
      primary ∈ source.primaryRequirementSites ∧
      primary.requirement = site.requirement.templateRequirement ∧
      primary.occurrence ∈ sourceSubtreeNodeIds source site.initializer := by
  cases requirementResult : state.requirements.find? (fun requirement =>
      decide (requirement.id = site.requirement.templateRequirement)) with
  | none =>
      simp [validateSourceTemplateScope, requirementResult] at success
  | some requirement =>
      have requirementMember : requirement ∈ state.requirements :=
        List.mem_of_find?_eq_some requirementResult
      have requirementId :
          requirement.id = site.requirement.templateRequirement :=
        of_decide_eq_true (List.find?_some
          (p := fun candidate : Requirement =>
            decide (candidate.id = site.requirement.templateRequirement))
          requirementResult)
      by_cases predicateEq : site.requirement.predicate =
          applyPredicate state requirement.predicate
      · have predicateEq' :
            applyPredicate state requirement.predicate =
              site.requirement.predicate := predicateEq.symm
        cases primaryResult : source.primaryRequirementSites.find?
            (fun primary => decide (primary.requirement =
              site.requirement.templateRequirement)) with
        | none =>
            simp [validateSourceTemplateScope, requirementResult,
              predicateEq, primaryResult] at success
        | some primary =>
            have primaryMember : primary ∈ source.primaryRequirementSites :=
              List.mem_of_find?_eq_some primaryResult
            have primaryId :
                primary.requirement =
                  site.requirement.templateRequirement :=
              of_decide_eq_true (List.find?_some
                (p := fun candidate : PrimaryRequirementSite =>
                  decide (candidate.requirement =
                    site.requirement.templateRequirement)) primaryResult)
            cases contained : nodeIdMember
                (sourceSubtreeNodeIds source site.initializer)
                primary.occurrence with
            | false =>
                simp [validateSourceTemplateScope, requirementResult,
                  predicateEq, primaryResult, contained] at success
            | true =>
                have primaryScoped : primary.occurrence ∈
                    sourceSubtreeNodeIds source site.initializer :=
                  (nodeIdMember_eq_true_iff _ _).mp contained
                exact ⟨requirement, primary, requirementMember,
                  requirementId, predicateEq', primaryMember, primaryId,
                  primaryScoped⟩
      · simp [validateSourceTemplateScope, requirementResult, predicateEq]
          at success

private theorem validateSourceTemplateScopesFrom_success
    {source : TypedSource} {state : State}
    {sites : List LocalSchemeTemplateSite}
    (success : validateSourceTemplateScopesFrom source state sites = .ok ()) :
    ∀ site, site ∈ sites →
      ∃ requirement primary,
        requirement ∈ state.requirements ∧
        requirement.id = site.requirement.templateRequirement ∧
        applyPredicate state requirement.predicate =
          site.requirement.predicate ∧
        primary ∈ source.primaryRequirementSites ∧
        primary.requirement = site.requirement.templateRequirement ∧
        primary.occurrence ∈
          sourceSubtreeNodeIds source site.initializer := by
  induction sites with
  | nil => simp
  | cons head tail induction =>
      cases headResult : validateSourceTemplateScope source state head with
      | error error =>
          simp [validateSourceTemplateScopesFrom, headResult, bind,
            Except.bind] at success
      | ok value =>
          cases value
          have tailResult :
              validateSourceTemplateScopesFrom source state tail = .ok () := by
            simpa [validateSourceTemplateScopesFrom, headResult, bind,
              Except.bind] using success
          intro site member
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact validateSourceTemplateScope_success headResult
          · exact induction tailResult site tailMember

/-- Successful complete template-scope validation supplies the exact witness
for every canonical source template site. -/
theorem validateSourceTemplateScopes_success
    {source : TypedSource} {state : State}
    (success : validateSourceTemplateScopes source state = .ok ()) :
    ∀ site, site ∈ source.localSchemeTemplateSites →
      ∃ requirement primary,
        requirement ∈ state.requirements ∧
        requirement.id = site.requirement.templateRequirement ∧
        applyPredicate state requirement.predicate =
          site.requirement.predicate ∧
        primary ∈ source.primaryRequirementSites ∧
        primary.requirement = site.requirement.templateRequirement ∧
        primary.occurrence ∈
          sourceSubtreeNodeIds source site.initializer := by
  exact validateSourceTemplateScopesFrom_success success

private theorem validateSourceRootsFrom_success
    {source : TypedSource} {roots : List NodeId}
    (success : validateSourceRootsFrom source roots = .ok ()) :
    ∀ root, root ∈ roots → root ∈ source.nodes.map Node.id := by
  induction roots with
  | nil => simp
  | cons head tail induction =>
      cases contained : sourceContainsNodeId source head with
      | false =>
          simp [validateSourceRootsFrom, contained, bind, Except.bind] at success
      | true =>
          have tailSuccess : validateSourceRootsFrom source tail = .ok () := by
            simpa [validateSourceRootsFrom, contained, bind, Except.bind]
              using success
          intro root member
          rcases List.mem_cons.mp member with rfl | tailMember
          · obtain ⟨node, nodeMem, nodeId⟩ :=
              (sourceContainsNodeId_eq_true_iff source root).mp contained
            exact List.mem_map.mpr ⟨node, nodeMem, nodeId⟩
          · exact induction tailSuccess root tailMember

/-- Successful root validation proves exact category-preserving existence of
every retained root in the source table. -/
theorem validateSourceRoots_success_rootsExist
    {source : TypedSource}
    (success : validateSourceRoots source = .ok ()) :
    ∀ root, root ∈ source.roots → root ∈ source.nodes.map Node.id := by
  exact validateSourceRootsFrom_success success

private theorem validateSourceReferencesFrom_success
    {source : TypedSource} {parent : NodeId} {children : List NodeId}
    (success :
      validateSourceReferencesFrom source parent children = .ok ()) :
    ∀ child, child ∈ children → child ∈ source.nodes.map Node.id := by
  induction children with
  | nil => simp
  | cons head tail induction =>
      cases contained : sourceContainsNodeId source head with
      | false =>
          simp [validateSourceReferencesFrom, contained, bind, Except.bind]
            at success
      | true =>
          have tailSuccess :
              validateSourceReferencesFrom source parent tail = .ok () := by
            simpa [validateSourceReferencesFrom, contained, bind, Except.bind]
              using success
          intro child member
          rcases List.mem_cons.mp member with rfl | tailMember
          · obtain ⟨node, nodeMem, nodeId⟩ :=
              (sourceContainsNodeId_eq_true_iff source child).mp contained
            exact List.mem_map.mpr ⟨node, nodeMem, nodeId⟩
          · exact induction tailSuccess child tailMember

private theorem validateSourceNodeChildren_success
    {source : TypedSource} {node : Node}
    (success : validateSourceNodeChildren source node = .ok ()) :
    ∀ child, child ∈ node.references →
      child ∈ source.nodes.map Node.id := by
  exact validateSourceReferencesFrom_success success

private theorem validateSourceChildrenFrom_success
    {source : TypedSource} {nodes : List Node}
    (success : validateSourceChildrenFrom source nodes = .ok ()) :
    ∀ node, node ∈ nodes → ∀ child, child ∈ node.references →
      child ∈ source.nodes.map Node.id := by
  induction nodes with
  | nil => simp
  | cons head tail induction =>
      cases headResult : validateSourceNodeChildren source head with
      | error error =>
          simp [validateSourceChildrenFrom, headResult, bind, Except.bind]
            at success
      | ok value =>
          cases value
          have tailSuccess : validateSourceChildrenFrom source tail = .ok () := by
            simpa [validateSourceChildrenFrom, headResult, bind, Except.bind]
              using success
          intro node member child childMember
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact validateSourceNodeChildren_success headResult child childMember
          · exact induction tailSuccess node tailMember child childMember

/-- Successful child validation proves exact category-preserving existence of
every direct source edge. -/
theorem validateSourceChildren_success_childEdgesExist
    {source : TypedSource}
    (success : validateSourceChildren source = .ok ()) :
    ∀ node, node ∈ source.nodes →
      ∀ child, child ∈ node.references →
        child ∈ source.nodes.map Node.id := by
  exact validateSourceChildrenFrom_success success

private theorem validateIncomingNodeIdsFrom_success
    {seen ids : List NodeId}
    (success : validateIncomingNodeIdsFrom seen ids = .ok ()) :
    ids.Nodup ∧
      ∀ id, id ∈ ids → id ∉ seen := by
  induction ids generalizing seen with
  | nil => simp
  | cons head tail induction =>
      cases duplicate : nodeIdMember seen head with
      | true =>
          simp [validateIncomingNodeIdsFrom, duplicate, bind, Except.bind]
            at success
      | false =>
          have headFresh : head ∉ seen := by
            intro member
            have contained : nodeIdMember seen head = true :=
              (nodeIdMember_eq_true_iff seen head).mpr member
            rw [duplicate] at contained
            simp at contained
          have tailSuccess :
              validateIncomingNodeIdsFrom (head :: seen) tail = .ok () := by
            simpa [validateIncomingNodeIdsFrom, duplicate, bind, Except.bind]
              using success
          obtain ⟨tailUnique, tailFresh⟩ := induction tailSuccess
          refine ⟨?_, ?_⟩
          · simp only [List.nodup_cons]
            refine ⟨?_, tailUnique⟩
            intro member
            exact tailFresh head member (by simp)
          · intro id member seenMember
            rcases List.mem_cons.mp member with rfl | tailMember
            · exact headFresh seenMember
            · exact tailFresh id tailMember (by simp [seenMember])

/-- Successful incoming-position validation proves that every root and child
slot is globally unique after retaining the expression/statement category. -/
theorem validateIncomingNodeIds_success_nodup
    {source : TypedSource}
    (success :
      validateIncomingNodeIdsFrom [] source.incomingNodeIds = .ok ()) :
    source.incomingNodeIds.Nodup :=
  (validateIncomingNodeIdsFrom_success success).1

private theorem validateAllSourceNodesReachedFrom_success
    {reached : List NodeId} {nodes : List Node}
    (success : validateAllSourceNodesReachedFrom reached nodes = .ok ()) :
    ∀ node, node ∈ nodes → node.id ∈ reached := by
  induction nodes with
  | nil => simp
  | cons head tail induction =>
      cases contained : nodeIdMember reached head.id with
      | false =>
          simp [validateAllSourceNodesReachedFrom, contained] at success
      | true =>
          have tailSuccess :
              validateAllSourceNodesReachedFrom reached tail = .ok () := by
            simpa [validateAllSourceNodesReachedFrom, contained, bind,
              Except.bind] using success
          intro node member
          rcases List.mem_cons.mp member with nodeEq | tailMember
          · subst node
            exact (nodeIdMember_eq_true_iff reached head.id).mp contained
          · exact induction tailSuccess node tailMember

/-- Successful forest validation exposes both executable structural
certificates used by the declarative closure bridge. -/
structure SourceForestValidationWitness (source : TypedSource) : Prop where
  incoming :
    validateIncomingNodeIdsFrom [] source.incomingNodeIds = .ok ()
  reached :
    validateAllSourceNodesReachedFrom (sourceReachableNodeIds source)
      source.nodes = .ok ()

theorem validateSourceForest_success_witness
    {source : TypedSource}
    (success : validateSourceForest source = .ok ()) :
    SourceForestValidationWitness source := by
  unfold validateSourceForest at success
  cases incomingResult :
      validateIncomingNodeIdsFrom [] source.incomingNodeIds with
  | error error =>
      simp [incomingResult, bind, Except.bind] at success
  | ok incomingValue =>
      cases incomingValue
      cases reachedResult :
          validateAllSourceNodesReachedFrom (sourceReachableNodeIds source)
            source.nodes with
      | error error =>
          simp [incomingResult, reachedResult, bind, Except.bind] at success
      | ok reachedValue =>
          cases reachedValue
          exact { incoming := incomingResult, reached := reachedResult }

/-- Successful forest validation proves global uniqueness of all incoming
root and child positions. -/
theorem validateSourceForest_success_incomingNodeIds_nodup
    {source : TypedSource}
    (success : validateSourceForest source = .ok ()) :
    source.incomingNodeIds.Nodup :=
  validateIncomingNodeIds_success_nodup
    (validateSourceForest_success_witness success).incoming

/-- Successful forest validation proves that the root worklist collected the
exact identity of every retained table node. -/
theorem validateSourceForest_success_allNodesReached
    {source : TypedSource}
    (success : validateSourceForest source = .ok ()) :
    ∀ node, node ∈ source.nodes →
      node.id ∈ sourceReachableNodeIds source :=
  validateAllSourceNodesReachedFrom_success
    (validateSourceForest_success_witness success).reached

/-- Successful graph validation exposes the successful result of each
structural validation stage. -/
structure SourceGraphValidationWitness (source : TypedSource) : Prop where
  occurrenceTable : validateOccurrenceTable source = .ok ()
  roots : validateSourceRoots source = .ok ()
  children : validateSourceChildren source = .ok ()
  forest : validateSourceForest source = .ok ()

theorem validateSourceGraph_success_witness
    {source : TypedSource}
    (success : validateSourceGraph source = .ok ()) :
    SourceGraphValidationWitness source := by
  unfold validateSourceGraph at success
  cases occurrenceResult : validateOccurrenceTable source with
  | error error => simp [occurrenceResult, bind, Except.bind] at success
  | ok occurrenceValue =>
      cases occurrenceValue
      cases rootsResult : validateSourceRoots source with
      | error error =>
          simp [occurrenceResult, rootsResult, bind, Except.bind] at success
      | ok rootsValue =>
          cases rootsValue
          cases childrenResult : validateSourceChildren source with
          | error error =>
              simp [occurrenceResult, rootsResult, childrenResult, bind,
                Except.bind] at success
          | ok childrenValue =>
              cases childrenValue
              cases forestResult : validateSourceForest source with
              | error error =>
                  simp [occurrenceResult, rootsResult, childrenResult,
                    forestResult, bind, Except.bind] at success
              | ok forestValue =>
                  cases forestValue
                  exact {
                    occurrenceTable := occurrenceResult
                    roots := rootsResult
                    children := childrenResult
                    forest := forestResult
                  }

/-- Successful complete graph validation proves category-erased occurrence
uniqueness. -/
theorem validateSourceGraph_success_nodeOccurrencesUnique
    {source : TypedSource}
    (success : validateSourceGraph source = .ok ()) :
    (source.nodes.map Node.occurrenceId).Nodup := by
  exact validateOccurrenceTable_success_nodeOccurrencesUnique
    (validateSourceGraph_success_witness success).occurrenceTable

/-- Successful complete graph validation proves ownership of every node. -/
theorem validateSourceGraph_success_nodesOwned
    {source : TypedSource}
    (success : validateSourceGraph source = .ok ()) :
    ∀ node, node ∈ source.nodes →
      node.occurrenceId.owner = source.owner := by
  exact validateOccurrenceTable_success_nodesOwned
    (validateSourceGraph_success_witness success).occurrenceTable

/-- Successful complete graph validation proves exact root existence. -/
theorem validateSourceGraph_success_rootsExist
    {source : TypedSource}
    (success : validateSourceGraph source = .ok ()) :
    ∀ root, root ∈ source.roots → root ∈ source.nodes.map Node.id := by
  exact validateSourceRoots_success_rootsExist
    (validateSourceGraph_success_witness success).roots

/-- Successful complete graph validation proves exact direct-child
existence. -/
theorem validateSourceGraph_success_childEdgesExist
    {source : TypedSource}
    (success : validateSourceGraph source = .ok ()) :
    ∀ node, node ∈ source.nodes →
      ∀ child, child ∈ node.references →
        child ∈ source.nodes.map Node.id := by
  exact validateSourceChildren_success_childEdgesExist
    (validateSourceGraph_success_witness success).children

/-- Successful complete graph validation proves global uniqueness of roots
and direct child positions. -/
theorem validateSourceGraph_success_incomingNodeIds_nodup
    {source : TypedSource}
    (success : validateSourceGraph source = .ok ()) :
    source.incomingNodeIds.Nodup :=
  validateSourceForest_success_incomingNodeIds_nodup
    (validateSourceGraph_success_witness success).forest

/-- Successful complete graph validation proves worklist coverage of every
retained source node. -/
theorem validateSourceGraph_success_allNodesReached
    {source : TypedSource}
    (success : validateSourceGraph source = .ok ()) :
    ∀ node, node ∈ source.nodes →
      node.id ∈ sourceReachableNodeIds source :=
  validateSourceForest_success_allNodesReached
    (validateSourceGraph_success_witness success).forest

/-- The executable check for one expression node produces its open structural
formation witness. -/
theorem validateExpressionNodeTypeFormation_success
    {context : Context} {node : ExpressionNode}
    (success : validateExpressionNodeTypeFormation context node = .ok ()) :
    InferenceTypeFormationValidated context.signatures
      context.scope.genericOwner context.typeParameters node.type.freeVariables
      node.type := by
  unfold validateExpressionNodeTypeFormation at success
  cases validation : validateInferenceTypeFormation context.signatures
      context.scope.genericOwner context.typeParameters node.type.freeVariables
      node.type with
  | error error => simp [validation] at success
  | ok value =>
      cases value
      exact validateInferenceTypeFormation_success validation

/-- Successful suffix validation covers every expression node retained by
that suffix of the heterogeneous source table. -/
private theorem validateSourceExpressionTypeFormationFrom_success
    {context : Context} {nodes : List Node}
    (success : validateSourceExpressionTypeFormationFrom context nodes =
      .ok ()) :
    ∀ node, Node.expression node ∈ nodes →
      InferenceTypeFormationValidated context.signatures
        context.scope.genericOwner context.typeParameters
        node.type.freeVariables node.type := by
  induction nodes with
  | nil =>
      intro node member
      simp at member
  | cons head tail induction =>
      cases head with
      | expression headNode =>
          simp only [validateSourceExpressionTypeFormationFrom, bind,
            Except.bind] at success
          cases headResult :
              validateExpressionNodeTypeFormation context headNode with
          | error error => simp [headResult] at success
          | ok value =>
              cases value
              have tailSuccess :
                  validateSourceExpressionTypeFormationFrom context tail =
                    .ok () := by
                simpa [headResult] using success
              intro node member
              rcases List.mem_cons.mp member with headEq | tailMember
              · cases headEq
                exact validateExpressionNodeTypeFormation_success headResult
              · exact induction tailSuccess node tailMember
      | statement headNode =>
          have tailSuccess :
              validateSourceExpressionTypeFormationFrom context tail =
                .ok () := by
            simpa [validateSourceExpressionTypeFormationFrom] using success
          intro node member
          rcases List.mem_cons.mp member with headEq | tailMember
          · cases headEq
          · exact induction tailSuccess node tailMember

/-- Successful source validation certifies the retained type of every
expression-table member. -/
theorem validateSourceExpressionTypeFormation_success
    {context : Context} {source : TypedSource}
    (success : validateSourceExpressionTypeFormation context source = .ok ())
    {node : ExpressionNode}
    (member : Node.expression node ∈ source.nodes) :
    InferenceTypeFormationValidated context.signatures
      context.scope.genericOwner context.typeParameters node.type.freeVariables
      node.type := by
  exact validateSourceExpressionTypeFormationFrom_success success node member

/-- The proof-facing binder-local form of the executable capture check.  It
contains exactly the freshness and relevance-restricted range facts consumed
by canonical local-scheme instantiation; formation, admissibility, and
evidence remain separate semantic obligations. -/
structure LocalBinderInstantiationNoCapture
    (substitution : Substitution) (binder : TypedBinder) : Prop where
  quantified_fresh : ∀ metavariable,
    metavariable ∈ binder.scheme.quantified →
      metavariable ∉ substitution.domain
  body_range : substitution.RangeAvoidsVariablesOn
    binder.scheme.quantified binder.scheme.body
  requirement_ranges : ∀ requirement,
    requirement ∈ binder.schemeRequirements →
      substitution.RangeAvoidsVariablesOn binder.scheme.quantified
          requirement.predicate.subject ∧
        ∀ argument, argument ∈ requirement.predicate.arguments →
          substitution.RangeAvoidsVariablesOn binder.scheme.quantified argument

namespace LocalBinderInstantiationNoCapture

/-- A monomorphic binder cannot capture any scheme-local variable because it
protects no quantified variables.  This covers function inputs, lambda
parameters, and every other binder introduced with `Scheme.mono`, independently
of the closing inference substitution. -/
theorem of_quantified_eq_nil
    {substitution : Substitution} {binder : TypedBinder}
    (monomorphic : binder.scheme.quantified = []) :
    LocalBinderInstantiationNoCapture substitution binder := by
  constructor
  · simp [monomorphic]
  · simp [Substitution.RangeAvoidsVariablesOn, monomorphic]
  · intro requirement member
    constructor
    · simp [Substitution.RangeAvoidsVariablesOn, monomorphic]
    · intro argument argumentMember
      simp [Substitution.RangeAvoidsVariablesOn, monomorphic]

end LocalBinderInstantiationNoCapture

/-- The finite executable range check is equivalent to the first-match
relevance-restricted no-capture proposition. -/
theorem substitutionRangeAvoidsVariablesOn_eq_true_iff
    (substitution : Substitution) (protectedVariables : List TypeVarId)
    (type : Ty) :
    substitutionRangeAvoidsVariablesOn substitution protectedVariables type =
        true ↔
      substitution.RangeAvoidsVariablesOn protectedVariables type := by
  constructor
  · intro accepted sourceVariable sourceMember replacement found
      protectedVariable protectedMember
    have sourceAccepted :=
      List.all_eq_true.mp accepted sourceVariable sourceMember
    have rangeAccepted : replacement.freeVariables.all (fun rangeVariable =>
        !protectedVariables.contains rangeVariable) = true := by
      simpa only [found] using sourceAccepted
    have protectedAccepted :=
      List.all_eq_true.mp rangeAccepted protectedVariable protectedMember
    simpa using protectedAccepted
  · intro avoids
    apply List.all_eq_true.mpr
    intro sourceVariable sourceMember
    cases found : substitution.lookup? sourceVariable with
    | none => rfl
    | some replacement =>
        apply List.all_eq_true.mpr
        intro protectedVariable protectedMember
        have absent := avoids sourceVariable sourceMember replacement found
          protectedVariable protectedMember
        simpa using absent

/-- The aggregate executable binder check recognizes exactly
`LocalBinderInstantiationNoCapture`. -/
theorem localBinderInstantiationNoCapture_eq_true_iff
    (substitution : Substitution) (binder : TypedBinder) :
    localBinderInstantiationNoCapture substitution binder = true ↔
      LocalBinderInstantiationNoCapture substitution binder := by
  constructor
  · intro accepted
    rcases Bool.and_eq_true_iff.mp accepted with
      ⟨bodySideAccepted, requirementsAccepted⟩
    rcases Bool.and_eq_true_iff.mp bodySideAccepted with
      ⟨freshAccepted, bodyAccepted⟩
    constructor
    · intro metavariable member
      have absent := List.all_eq_true.mp freshAccepted metavariable member
      simpa using absent
    · exact (substitutionRangeAvoidsVariablesOn_eq_true_iff _ _ _).mp
        bodyAccepted
    · intro requirement member
      have requirementAccepted :=
        List.all_eq_true.mp requirementsAccepted requirement member
      rcases Bool.and_eq_true_iff.mp requirementAccepted with
        ⟨subjectAccepted, argumentsAccepted⟩
      constructor
      · exact (substitutionRangeAvoidsVariablesOn_eq_true_iff _ _ _).mp
          subjectAccepted
      · intro argument argumentMember
        exact (substitutionRangeAvoidsVariablesOn_eq_true_iff _ _ _).mp
          (List.all_eq_true.mp argumentsAccepted argument argumentMember)
  · intro certificate
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply Bool.and_eq_true_iff.mpr
      constructor
      · apply List.all_eq_true.mpr
        intro metavariable member
        simpa using certificate.quantified_fresh metavariable member
      · exact (substitutionRangeAvoidsVariablesOn_eq_true_iff _ _ _).mpr
          certificate.body_range
    · apply List.all_eq_true.mpr
      intro requirement member
      apply Bool.and_eq_true_iff.mpr
      constructor
      · exact (substitutionRangeAvoidsVariablesOn_eq_true_iff _ _ _).mpr
          (certificate.requirement_ranges requirement member).1
      · apply List.all_eq_true.mpr
        intro argument argumentMember
        exact (substitutionRangeAvoidsVariablesOn_eq_true_iff _ _ _).mpr
          ((certificate.requirement_ranges requirement member).2 argument
            argumentMember)

private theorem validateLocalSchemeBindersNoCapture_success
    {substitution : Substitution} {binders : List TypedBinder}
    (success : validateLocalSchemeBindersNoCapture substitution binders =
      .ok ()) :
    ∀ binder, binder ∈ binders →
      LocalBinderInstantiationNoCapture substitution binder := by
  induction binders with
  | nil => simp
  | cons head tail induction =>
      cases accepted : localBinderInstantiationNoCapture substitution head with
      | false =>
          simp [validateLocalSchemeBindersNoCapture, accepted] at success
      | true =>
          have tailSuccess :
              validateLocalSchemeBindersNoCapture substitution tail =
                .ok () := by
            simpa [validateLocalSchemeBindersNoCapture, accepted] using success
          intro binder member
          rcases List.mem_cons.mp member with rfl | member
          · exact (localBinderInstantiationNoCapture_eq_true_iff _ _).mp
              accepted
          · exact induction tailSuccess binder member

/-- Successful whole-source validation supplies the binder-local no-capture
certificate for every initialized let, including generic binders with no
qualified requirements. -/
theorem validateSourceLocalSchemeNoCapture_success
    {source : TypedSource} {substitution : Substitution}
    (success : validateSourceLocalSchemeNoCapture source substitution =
      .ok ()) :
    ∀ binder, binder ∈ source.initializedLetBinders →
      LocalBinderInstantiationNoCapture substitution binder := by
  exact validateLocalSchemeBindersNoCapture_success success

@[simp] theorem supportedIntegerTarget_eq_true_iff
    (type : Ty) :
    supportedIntegerTarget type = true ↔
      type = .word ∨ type = .integer := by
  constructor
  · intro supported
    cases type <;> simp [supportedIntegerTarget] at supported
    case constructor constructor =>
      cases constructor with
      | builtin builtin =>
        cases builtin <;>
          simp [Ty.word, Ty.integer] at supported ⊢
      | declaration declaration =>
          simp at supported
  · intro supported
    rcases supported with rfl | rfl <;> rfl

@[simp] theorem supportedIntegerPatternTarget_eq_true_iff
    (type : Ty) :
    supportedIntegerPatternTarget type = true ↔ type.IntegerPatternCarrier := by
  unfold Ty.IntegerPatternCarrier
  constructor
  · intro supported
    cases type with
    | constructor constructor =>
      cases constructor with
      | builtin builtin =>
        cases builtin with
        | fixed fixed =>
          rcases fixed with ⟨signed, width⟩
          cases signed <;> cases width <;>
            simp [supportedIntegerPatternTarget, supportedIntegerTarget, Ty.fixed,
              TypeSystem.FixedInteger.uint256] at supported ⊢
        | _ =>
          simp [supportedIntegerPatternTarget, supportedIntegerTarget, Ty.word,
            Ty.integer, Ty.fixed] at supported ⊢
      | declaration declaration =>
        simp [supportedIntegerPatternTarget, supportedIntegerTarget] at supported
    | _ => simp [supportedIntegerPatternTarget, supportedIntegerTarget] at supported
  · rintro (rfl | rfl | rfl) <;> rfl

/-- Successful pattern-target validation exposes exactly the carriers
implemented by source pattern matching: `word`, `integer` and `uint256`. -/
theorem validateIntegerPatternTarget_success_supported
    {state : State} {origin : IntegerPatternOrigin}
    (success : validateIntegerPatternTarget origin state = .ok ()) :
    (state.resolve (.variable origin.metavariable)).IntegerPatternCarrier := by
  simp only [validateIntegerPatternTarget] at success
  by_cases supported : supportedIntegerPatternTarget
      (state.resolve (.variable origin.metavariable)) = true
  · exact (supportedIntegerPatternTarget_eq_true_iff _).mp supported
  · simp [supported] at success

/-- Successful validation of the complete pattern-origin row supports every
retained integer-pattern target. -/
theorem validateIntegerPatternTargets_success_supported
    {state : State} {origins : List IntegerPatternOrigin}
    (success : validateIntegerPatternTargets state origins = .ok ()) :
    ∀ origin, origin ∈ origins →
      (state.resolve (.variable origin.metavariable)).IntegerPatternCarrier := by
  induction origins with
  | nil =>
      intro origin member
      simp at member
  | cons head tail induction =>
      simp only [validateIntegerPatternTargets, bind, Except.bind] at success
      cases headResult : validateIntegerPatternTarget head state with
      | error error => simp [headResult] at success
      | ok value =>
          cases value
          have tailResult :
              validateIntegerPatternTargets state tail = .ok () := by
            simpa [headResult] using success
          intro origin member
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact validateIntegerPatternTarget_success_supported headResult
          · exact induction tailResult origin tailMember

@[simp] theorem supportedIntegerLiteralTarget_eq_true_iff
    (type : Ty) :
    supportedIntegerLiteralTarget type = true ↔ type.IntegerLiteralCarrier := by
  unfold Ty.IntegerLiteralCarrier
  constructor
  · intro supported
    cases type with
    | constructor constructor =>
      cases constructor with
      | builtin builtin =>
        cases builtin with
        | fixed fixed => exact .inr (.inr ⟨fixed, rfl⟩)
        | _ =>
          simp [supportedIntegerLiteralTarget, supportedIntegerTarget, Ty.word,
            Ty.integer, Ty.fixed] at supported ⊢
      | declaration declaration =>
        simp [supportedIntegerLiteralTarget, supportedIntegerTarget] at supported
    | _ => simp [supportedIntegerLiteralTarget, supportedIntegerTarget] at supported
  · rintro (rfl | rfl | ⟨fixed, rfl⟩) <;> rfl

/-- Successful literal-target validation exposes a carrier implemented by
source literal materialization: `word`, `integer` or a fixed-width type. -/
theorem validateIntegerLiteralTarget_success_supported
    {state : State} {origin : IntegerLiteralOrigin}
    (success : validateIntegerLiteralTarget origin state = .ok ()) :
    (state.resolve (.variable origin.metavariable)).IntegerLiteralCarrier := by
  simp only [validateIntegerLiteralTarget] at success
  by_cases supported : supportedIntegerLiteralTarget
      (state.resolve (.variable origin.metavariable)) = true
  · exact (supportedIntegerLiteralTarget_eq_true_iff _).mp supported
  · simp [supported] at success

/-- Successful literal-target validation also checks that every literal node
at the origin's expression fits the carrier. -/
theorem validateIntegerLiteralTarget_success_fits
    {state : State} {origin : IntegerLiteralOrigin}
    (success : validateIntegerLiteralTarget origin state = .ok ()) :
    literalNodesFit state origin.expression
      (state.resolve (.variable origin.metavariable)) = true := by
  simp only [validateIntegerLiteralTarget] at success
  by_cases supported : supportedIntegerLiteralTarget
      (state.resolve (.variable origin.metavariable)) = true
  · by_cases fits : literalNodesFit state origin.expression
        (state.resolve (.variable origin.metavariable)) = true
    · exact fits
    · simp [supported, fits] at success
  · simp [supported] at success

/-- A fitting expression identity bounds each of its literal nodes. -/
theorem literalNodesFit_member {state : State} {expression : ExpressionId} {type : Ty}
    (fits : literalNodesFit state expression type = true)
    {node : ExpressionNode} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (member : Node.expression node ∈ state.nodes) (identity : node.id = expression)
    (form : node.form = .integerLiteral source resolution) :
    signedLiteralFitsTarget source type resolution.rawValue = true := by
  have each := List.all_eq_true.mp fits _ member
  simpa [form, identity] using each

/-- Successful validation of the complete origin row fits every literal node at
every retained integer-literal origin. -/
theorem validateIntegerLiteralTargets_success_fits
    {state : State} {origins : List IntegerLiteralOrigin}
    (success : validateIntegerLiteralTargets state origins = .ok ()) :
    ∀ origin, origin ∈ origins →
      literalNodesFit state origin.expression
        (state.resolve (.variable origin.metavariable)) = true := by
  induction origins with
  | nil =>
      intro origin member
      simp at member
  | cons head tail induction =>
      simp only [validateIntegerLiteralTargets, bind, Except.bind] at success
      cases headResult : validateIntegerLiteralTarget head state with
      | error error => simp [headResult] at success
      | ok value =>
          cases value
          have tailResult :
              validateIntegerLiteralTargets state tail = .ok () := by
            simpa [headResult] using success
          intro origin member
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact validateIntegerLiteralTarget_success_fits headResult
          · exact induction tailResult origin tailMember

/-- Successful validation of the complete origin row supports every retained
integer-literal target. -/
theorem validateIntegerLiteralTargets_success_supported
    {state : State} {origins : List IntegerLiteralOrigin}
    (success : validateIntegerLiteralTargets state origins = .ok ()) :
    ∀ origin, origin ∈ origins →
      (state.resolve (.variable origin.metavariable)).IntegerLiteralCarrier := by
  induction origins with
  | nil =>
      intro origin member
      simp at member
  | cons head tail induction =>
      simp only [validateIntegerLiteralTargets, bind, Except.bind] at success
      cases headResult : validateIntegerLiteralTarget head state with
      | error error => simp [headResult] at success
      | ok value =>
          cases value
          have tailResult :
              validateIntegerLiteralTargets state tail = .ok () := by
            simpa [headResult] using success
          intro origin member
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact validateIntegerLiteralTarget_success_supported headResult
          · exact induction tailResult origin tailMember

private theorem validateIntegerLiteralNode_success_correspondence
    {state : State} {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (form_eq : node.form = .integerLiteral source resolution)
    (success : validateIntegerLiteralNode state (.expression node) = .ok ()) :
    Frontend.literalMagnitude? source = some resolution.rawValue ∧
      ∃ origin, origin ∈ state.integerLiterals ∧
        origin.expression = node.id ∧
        resolution.targetType = .variable origin.metavariable ∧
        resolution.requirement = origin.requirement ∧
        ({ id := resolution.requirement, predicate := resolution.predicate } :
          Requirement) ∈ state.requirements := by
  simp only [validateIntegerLiteralNode, form_eq] at success
  split at success
  next decoded =>
    cases originResult : state.integerLiterals.find? (fun origin =>
        decide (origin.expression = node.id ∧
          resolution.targetType = .variable origin.metavariable ∧
          origin.requirement = resolution.requirement)) with
    | none =>
        simp only [originResult] at success
        cases success
    | some origin =>
        cases requirementResult : state.requirements.find? (fun requirement =>
            decide (requirement.id = resolution.requirement)) with
        | none =>
            simp only [originResult, requirementResult] at success
            cases success
        | some requirement =>
            simp only [originResult, requirementResult] at success
            split at success
            next predicateEq =>
              have originMatches :
                  origin.expression = node.id ∧
                    resolution.targetType = .variable origin.metavariable ∧
                    origin.requirement = resolution.requirement := by
                have accepted : decide (origin.expression = node.id ∧
                    resolution.targetType = .variable origin.metavariable ∧
                    origin.requirement = resolution.requirement) = true :=
                  List.find?_some (p := fun candidate : IntegerLiteralOrigin =>
                    decide (candidate.expression = node.id ∧
                      resolution.targetType = .variable candidate.metavariable ∧
                      candidate.requirement = resolution.requirement))
                    originResult
                exact of_decide_eq_true accepted
              rcases originMatches with
                ⟨expressionEq, targetEq, requirementEq⟩
              have originMem : origin ∈ state.integerLiterals :=
                List.mem_of_find?_eq_some originResult
              have requirementIdEq :
                  requirement.id = resolution.requirement :=
                of_decide_eq_true (List.find?_some
                  (p := fun candidate : Requirement =>
                    decide (candidate.id = resolution.requirement))
                  requirementResult)
              have requirementMem : requirement ∈ state.requirements :=
                List.mem_of_find?_eq_some requirementResult
              refine ⟨decoded, origin, originMem, expressionEq, targetEq,
                requirementEq.symm, ?_⟩
              cases requirement with
              | mk id predicate =>
                  simp only at requirementIdEq predicateEq
                  subst id
                  subst predicate
                  exact requirementMem
            next predicateNe =>
              cases success
  next decodedNe =>
    cases success

private theorem validateIntegerLiteralNodes_success_correspondence
    {state : State} {nodes : List Node}
    (success : validateIntegerLiteralNodes state nodes = .ok ()) :
    ∀ node source resolution,
      Node.expression node ∈ nodes →
      node.form = .integerLiteral source resolution →
      Frontend.literalMagnitude? source = some resolution.rawValue ∧
        ∃ origin, origin ∈ state.integerLiterals ∧
          origin.expression = node.id ∧
          resolution.targetType = .variable origin.metavariable ∧
          resolution.requirement = origin.requirement ∧
          ({ id := resolution.requirement, predicate := resolution.predicate } :
            Requirement) ∈ state.requirements := by
  induction nodes with
  | nil =>
      intro node source resolution member
      simp at member
  | cons head tail induction =>
      simp only [validateIntegerLiteralNodes, bind, Except.bind] at success
      cases headResult : validateIntegerLiteralNode state head with
      | error error =>
          simp [headResult] at success
      | ok value =>
          cases value
          have tailSuccess :
              validateIntegerLiteralNodes state tail = .ok () := by
            simpa [headResult] using success
          intro node source resolution member formEq
          rcases List.mem_cons.mp member with headEq | tailMember
          · subst head
            exact validateIntegerLiteralNode_success_correspondence
              formEq headResult
          · exact induction tailSuccess node source resolution tailMember
              formEq

/-- Successful executable ledger validation exposes the complete reusable
node-to-origin-to-requirement correspondence. -/
theorem validateIntegerLiteralLedger_success_correspondence
    {state : State}
    (success : validateIntegerLiteralLedger state = .ok ()) :
    state.IntegerLiteralLedgerCorrespondence := by
  exact validateIntegerLiteralNodes_success_correspondence success

theorem unify_localSchemeAssumptions
    {state next : State} {left right : Ty}
    (result : unify state left right = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
  unfold unify at result
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at result
  cases result
  rfl

theorem unify_integerLiterals
    {state next : State} {left right : Ty}
    (result : unify state left right = .ok next) :
    next.integerLiterals = state.integerLiterals := by
  unfold unify at result
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at result
  cases result
  rfl

theorem unify_integerPatterns
    {state next : State} {left right : Ty}
    (result : unify state left right = .ok next) :
    next.integerPatterns = state.integerPatterns := by
  unfold unify at result
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at result
  cases result
  rfl

theorem unify_requirements_eq
    {state next : State} {left right : Ty}
    (result : unify state left right = .ok next) :
    next.requirements = state.requirements := by
  unfold unify at result
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at result
  cases result
  rfl

theorem defaultIntegerPatternTarget_localSchemeAssumptions
    {state next : State} {origin : IntegerPatternOrigin}
    (result : defaultIntegerPatternTarget state origin = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerPatternTarget, resolved] at result
  · exact unify_localSchemeAssumptions result
  all_goals cases result <;> rfl

theorem defaultIntegerPatternTargets_localSchemeAssumptions
    {origins : List IntegerPatternOrigin} {state next : State}
    (result : defaultIntegerPatternTargets origins state = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerPatternTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerPatternTarget state origin with
      | error error =>
          simp [defaultIntegerPatternTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerPatternTargets rest middle = .ok next := by
            simpa [defaultIntegerPatternTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerPatternTarget_localSchemeAssumptions headResult)

theorem defaultIntegerPatternTarget_integerLiterals
    {state next : State} {origin : IntegerPatternOrigin}
    (result : defaultIntegerPatternTarget state origin = .ok next) :
    next.integerLiterals = state.integerLiterals := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerPatternTarget, resolved] at result
  · exact unify_integerLiterals result
  all_goals cases result <;> rfl

theorem defaultIntegerPatternTargets_integerLiterals
    {origins : List IntegerPatternOrigin} {state next : State}
    (result : defaultIntegerPatternTargets origins state = .ok next) :
    next.integerLiterals = state.integerLiterals := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerPatternTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerPatternTarget state origin with
      | error error =>
          simp [defaultIntegerPatternTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerPatternTargets rest middle = .ok next := by
            simpa [defaultIntegerPatternTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerPatternTarget_integerLiterals headResult)

theorem defaultIntegerPatternTarget_integerPatterns
    {state next : State} {origin : IntegerPatternOrigin}
    (result : defaultIntegerPatternTarget state origin = .ok next) :
    next.integerPatterns = state.integerPatterns := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerPatternTarget, resolved] at result
  · exact unify_integerPatterns result
  all_goals cases result <;> rfl

theorem defaultIntegerPatternTargets_integerPatterns
    {origins : List IntegerPatternOrigin} {state next : State}
    (result : defaultIntegerPatternTargets origins state = .ok next) :
    next.integerPatterns = state.integerPatterns := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerPatternTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerPatternTarget state origin with
      | error error =>
          simp [defaultIntegerPatternTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerPatternTargets rest middle = .ok next := by
            simpa [defaultIntegerPatternTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerPatternTarget_integerPatterns headResult)

theorem defaultIntegerPatternTarget_requirements
    {state next : State} {origin : IntegerPatternOrigin}
    (result : defaultIntegerPatternTarget state origin = .ok next) :
    next.requirements = state.requirements := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerPatternTarget, resolved] at result
  · exact unify_requirements_eq result
  all_goals cases result <;> rfl

theorem defaultIntegerPatternTargets_requirements
    {origins : List IntegerPatternOrigin} {state next : State}
    (result : defaultIntegerPatternTargets origins state = .ok next) :
    next.requirements = state.requirements := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerPatternTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerPatternTarget state origin with
      | error error =>
          simp [defaultIntegerPatternTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerPatternTargets rest middle = .ok next := by
            simpa [defaultIntegerPatternTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerPatternTarget_requirements headResult)

theorem defaultIntegerLiteralTarget_localSchemeAssumptions
    {state next : State} {origin : IntegerLiteralOrigin}
    (result : defaultIntegerLiteralTarget state origin = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerLiteralTarget, resolved] at result
  · split at result
    · exact unify_localSchemeAssumptions result
    · cases result
  all_goals cases result <;> rfl

theorem defaultIntegerLiteralTargets_localSchemeAssumptions
    {origins : List IntegerLiteralOrigin} {state next : State}
    (result : defaultIntegerLiteralTargets origins state = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerLiteralTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerLiteralTarget state origin with
      | error error =>
          simp [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerLiteralTargets rest middle = .ok next := by
            simpa [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerLiteralTarget_localSchemeAssumptions headResult)

theorem defaultIntegerLiteralTarget_integerLiterals
    {state next : State} {origin : IntegerLiteralOrigin}
    (result : defaultIntegerLiteralTarget state origin = .ok next) :
    next.integerLiterals = state.integerLiterals := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerLiteralTarget, resolved] at result
  · split at result
    · exact unify_integerLiterals result
    · cases result
  all_goals cases result <;> rfl

theorem defaultIntegerLiteralTargets_integerLiterals
    {origins : List IntegerLiteralOrigin} {state next : State}
    (result : defaultIntegerLiteralTargets origins state = .ok next) :
    next.integerLiterals = state.integerLiterals := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerLiteralTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerLiteralTarget state origin with
      | error error =>
          simp [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerLiteralTargets rest middle = .ok next := by
            simpa [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerLiteralTarget_integerLiterals headResult)

theorem defaultIntegerLiteralTarget_integerPatterns
    {state next : State} {origin : IntegerLiteralOrigin}
    (result : defaultIntegerLiteralTarget state origin = .ok next) :
    next.integerPatterns = state.integerPatterns := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerLiteralTarget, resolved] at result
  · split at result
    · exact unify_integerPatterns result
    · cases result
  all_goals cases result <;> rfl

theorem defaultIntegerLiteralTargets_integerPatterns
    {origins : List IntegerLiteralOrigin} {state next : State}
    (result : defaultIntegerLiteralTargets origins state = .ok next) :
    next.integerPatterns = state.integerPatterns := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerLiteralTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerLiteralTarget state origin with
      | error error =>
          simp [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerLiteralTargets rest middle = .ok next := by
            simpa [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerLiteralTarget_integerPatterns headResult)

theorem defaultIntegerLiteralTarget_requirements
    {state next : State} {origin : IntegerLiteralOrigin}
    (result : defaultIntegerLiteralTarget state origin = .ok next) :
    next.requirements = state.requirements := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerLiteralTarget, resolved] at result
  · split at result
    · exact unify_requirements_eq result
    · cases result
  all_goals cases result <;> rfl

theorem defaultIntegerLiteralTargets_requirements
    {origins : List IntegerLiteralOrigin} {state next : State}
    (result : defaultIntegerLiteralTargets origins state = .ok next) :
    next.requirements = state.requirements := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerLiteralTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerLiteralTarget state origin with
      | error error =>
          simp [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerLiteralTargets rest middle = .ok next := by
            simpa [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerLiteralTarget_requirements headResult)

/-- Defaulting one unresolved integer-pattern target is ordinary inference
progress and preserves readiness when the recorded metavariable lies below
the input allocator.  A target already fixed to a non-variable type leaves
the state unchanged. -/
theorem defaultIntegerPatternTarget_inferenceProperties
    {state next : State} {origin : IntegerPatternOrigin}
    (ready : state.InferenceReady)
    (originBelow : origin.metavariable.index < state.inference.next)
    (success : defaultIntegerPatternTarget state origin = .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerPatternTarget, resolved] at success
  · have targetBelow : (Ty.variable origin.metavariable).VariablesBelow
        state.inference.next :=
      (Ty.variablesBelow_variable_iff _ _).2 originBelow
    have wordBelow : (Ty.fixed .uint256).VariablesBelow state.inference.next :=
      Ty.variablesBelow_constructor _ _
    exact ⟨unify_inferenceProgress ready.solved targetBelow wordBelow success,
      unify_preserves_inferenceReady ready targetBelow wordBelow success⟩
  all_goals cases success
  all_goals exact ⟨State.InferenceProgress.refl ready.solved, ready⟩

/-- Defaulting a source-ordered list of integer-pattern targets composes the
single-origin inference certificates. -/
theorem defaultIntegerPatternTargets_inferenceProperties
    {origins : List IntegerPatternOrigin} {state next : State}
    (ready : state.InferenceReady)
    (originsBelow : ∀ origin ∈ origins,
      origin.metavariable.index < state.inference.next)
    (success : defaultIntegerPatternTargets origins state = .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerPatternTargets] at success
      cases success
      exact ⟨State.InferenceProgress.refl ready.solved, ready⟩
  | cons origin rest induction =>
      cases headResult : defaultIntegerPatternTarget state origin with
      | error error =>
          simp [defaultIntegerPatternTargets, headResult, bind, Except.bind]
            at success
      | ok middle =>
          have tailResult :
              defaultIntegerPatternTargets rest middle = .ok next := by
            simpa [defaultIntegerPatternTargets, headResult, bind, Except.bind]
              using success
          have headProperties := defaultIntegerPatternTarget_inferenceProperties
            ready (originsBelow origin (by simp)) headResult
          have restBelow : ∀ candidate ∈ rest,
              candidate.metavariable.index < middle.inference.next := by
            intro candidate member
            exact Nat.lt_of_lt_of_le
              (originsBelow candidate (by simp [member]))
              headProperties.1.next_le
          have tailProperties := induction headProperties.2 restBelow tailResult
          exact ⟨headProperties.1.trans tailProperties.1, tailProperties.2⟩

/-- Integer-literal defaulting has the same inference behavior as pattern
defaulting. -/
theorem defaultIntegerLiteralTarget_inferenceProperties
    {state next : State} {origin : IntegerLiteralOrigin}
    (ready : state.InferenceReady)
    (originBelow : origin.metavariable.index < state.inference.next)
    (success : defaultIntegerLiteralTarget state origin = .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerLiteralTarget, resolved] at success
  · split at success
    · have targetBelow : (Ty.variable origin.metavariable).VariablesBelow
          state.inference.next :=
        (Ty.variablesBelow_variable_iff _ _).2 originBelow
      have wordBelow : (Ty.fixed .uint256).VariablesBelow state.inference.next :=
        Ty.variablesBelow_constructor _ _
      exact ⟨unify_inferenceProgress ready.solved targetBelow wordBelow success,
        unify_preserves_inferenceReady ready targetBelow wordBelow success⟩
    · cases success
  all_goals cases success
  all_goals exact ⟨State.InferenceProgress.refl ready.solved, ready⟩

/-- Defaulting a source-ordered list of integer-literal targets composes the
single-origin inference certificates. -/
theorem defaultIntegerLiteralTargets_inferenceProperties
    {origins : List IntegerLiteralOrigin} {state next : State}
    (ready : state.InferenceReady)
    (originsBelow : ∀ origin ∈ origins,
      origin.metavariable.index < state.inference.next)
    (success : defaultIntegerLiteralTargets origins state = .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerLiteralTargets] at success
      cases success
      exact ⟨State.InferenceProgress.refl ready.solved, ready⟩
  | cons origin rest induction =>
      cases headResult : defaultIntegerLiteralTarget state origin with
      | error error =>
          simp [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
            at success
      | ok middle =>
          have tailResult :
              defaultIntegerLiteralTargets rest middle = .ok next := by
            simpa [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
              using success
          have headProperties := defaultIntegerLiteralTarget_inferenceProperties
            ready (originsBelow origin (by simp)) headResult
          have restBelow : ∀ candidate ∈ rest,
              candidate.metavariable.index < middle.inference.next := by
            intro candidate member
            exact Nat.lt_of_lt_of_le
              (originsBelow candidate (by simp [member]))
              headProperties.1.next_le
          have tailProperties := induction headProperties.2 restBelow tailResult
          exact ⟨headProperties.1.trans tailProperties.1, tailProperties.2⟩

/-- Defaulting one numeric pattern target preserves every type equality
already visible through the input inference state. -/
theorem defaultIntegerPatternTarget_preserves_resolve_eq
    {state next : State} {origin : IntegerPatternOrigin}
    {left right : Ty}
    (equal : state.resolve left = state.resolve right)
    (success : defaultIntegerPatternTarget state origin = .ok next) :
    next.resolve left = next.resolve right := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerPatternTarget, resolved] at success
  · exact unify_preserves_resolve_eq equal success
  all_goals cases success
  all_goals exact equal

/-- Pattern-target defaulting preserves every previously established resolved
type equality across the complete target list. -/
theorem defaultIntegerPatternTargets_preserves_resolve_eq
    {origins : List IntegerPatternOrigin} {state next : State}
    {left right : Ty}
    (equal : state.resolve left = state.resolve right)
    (success : defaultIntegerPatternTargets origins state = .ok next) :
    next.resolve left = next.resolve right := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerPatternTargets] at success
      cases success
      exact equal
  | cons origin rest induction =>
      cases headResult : defaultIntegerPatternTarget state origin with
      | error error =>
          simp [defaultIntegerPatternTargets, headResult, bind, Except.bind]
            at success
      | ok middle =>
          have tailResult :
              defaultIntegerPatternTargets rest middle = .ok next := by
            simpa [defaultIntegerPatternTargets, headResult, bind, Except.bind]
              using success
          exact induction
            (defaultIntegerPatternTarget_preserves_resolve_eq equal headResult)
            tailResult

/-- Defaulting one integer-literal target preserves every type equality
already visible through the input inference state. -/
theorem defaultIntegerLiteralTarget_preserves_resolve_eq
    {state next : State} {origin : IntegerLiteralOrigin}
    {left right : Ty}
    (equal : state.resolve left = state.resolve right)
    (success : defaultIntegerLiteralTarget state origin = .ok next) :
    next.resolve left = next.resolve right := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerLiteralTarget, resolved] at success
  · split at success
    · exact unify_preserves_resolve_eq equal success
    · cases success
  all_goals cases success
  all_goals exact equal

/-- Literal-target defaulting preserves every previously established resolved
type equality across the complete target list. -/
theorem defaultIntegerLiteralTargets_preserves_resolve_eq
    {origins : List IntegerLiteralOrigin} {state next : State}
    {left right : Ty}
    (equal : state.resolve left = state.resolve right)
    (success : defaultIntegerLiteralTargets origins state = .ok next) :
    next.resolve left = next.resolve right := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerLiteralTargets] at success
      cases success
      exact equal
  | cons origin rest induction =>
      cases headResult : defaultIntegerLiteralTarget state origin with
      | error error =>
          simp [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
            at success
      | ok middle =>
          have tailResult :
              defaultIntegerLiteralTargets rest middle = .ok next := by
            simpa [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
              using success
          exact induction
            (defaultIntegerLiteralTarget_preserves_resolve_eq equal headResult)
            tailResult

private theorem unify_toTypedSource
    {state next : State} {left right : Ty} {roots : List NodeId}
    (result : unify state left right = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  unfold unify at result
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at result
  cases result
  rfl

private theorem defaultIntegerPatternTarget_toTypedSource
    {state next : State} {origin : IntegerPatternOrigin}
    {roots : List NodeId}
    (result : defaultIntegerPatternTarget state origin = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerPatternTarget, resolved] at result
  · exact unify_toTypedSource result
  all_goals cases result <;> rfl

private theorem defaultIntegerPatternTargets_toTypedSource
    {origins : List IntegerPatternOrigin} {state next : State}
    {roots : List NodeId}
    (result : defaultIntegerPatternTargets origins state = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerPatternTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerPatternTarget state origin with
      | error error =>
          simp [defaultIntegerPatternTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerPatternTargets rest middle = .ok next := by
            simpa [defaultIntegerPatternTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerPatternTarget_toTypedSource headResult)

private theorem defaultIntegerLiteralTarget_toTypedSource
    {state next : State} {origin : IntegerLiteralOrigin}
    {roots : List NodeId}
    (result : defaultIntegerLiteralTarget state origin = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerLiteralTarget, resolved] at result
  · split at result
    · exact unify_toTypedSource result
    · cases result
  all_goals cases result <;> rfl

private theorem defaultIntegerLiteralTargets_toTypedSource
    {origins : List IntegerLiteralOrigin} {state next : State}
    {roots : List NodeId}
    (result : defaultIntegerLiteralTargets origins state = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerLiteralTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerLiteralTarget state origin with
      | error error =>
          simp [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerLiteralTargets rest middle = .ok next := by
            simpa [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerLiteralTarget_toTypedSource headResult)

/-! ### The weak trait arguments

Each fix of `fixWeakArguments` unifies a requirement's open arguments with closed ones through
`unify`, so it changes only `state.inference`. -/

theorem unify_frame {state next : State} {left right : Ty}
    (result : unify state left right = .ok next) :
    ∃ inference, next = { state with inference } := by
  unfold unify at result
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at result
  cases result
  exact ⟨_, rfl⟩

theorem unifyWeakArguments_frame {state next : State} {pairs : List (Ty × Ty)}
    (result : unifyWeakArguments state pairs = .ok next) :
    ∃ inference, next = { state with inference } := by
  induction pairs generalizing state with
  | nil =>
      simp [unifyWeakArguments] at result
      cases result
      exact ⟨_, rfl⟩
  | cons pair rest induction =>
      obtain ⟨source, target⟩ := pair
      cases head : unify state source target with
      | error error => simp [unifyWeakArguments, head, bind, Except.bind] at result
      | ok middle =>
          have tail : unifyWeakArguments middle rest = .ok next := by
            simpa [unifyWeakArguments, head, bind, Except.bind] using result
          obtain ⟨first, rfl⟩ := unify_frame head
          obtain ⟨second, rfl⟩ := induction tail
          exact ⟨second, rfl⟩

theorem unifyWeakArguments_inferenceProperties {state next : State}
    {pairs : List (Ty × Ty)} (ready : state.InferenceReady)
    (below : ∀ pair ∈ pairs, pair.1.VariablesBelow state.inference.next ∧
      pair.2.VariablesBelow state.inference.next)
    (result : unifyWeakArguments state pairs = .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady := by
  induction pairs generalizing state with
  | nil =>
      simp [unifyWeakArguments] at result
      cases result
      exact ⟨State.InferenceProgress.refl ready.solved, ready⟩
  | cons pair rest induction =>
      obtain ⟨source, target⟩ := pair
      cases head : unify state source target with
      | error error => simp [unifyWeakArguments, head, bind, Except.bind] at result
      | ok middle =>
          have tail : unifyWeakArguments middle rest = .ok next := by
            simpa [unifyWeakArguments, head, bind, Except.bind] using result
          have headBelow := below (source, target) (by simp)
          have progress :=
            unify_inferenceProgress ready.solved headBelow.1 headBelow.2 head
          have middleReady :=
            unify_preserves_inferenceReady ready headBelow.1 headBelow.2 head
          have restBelow : ∀ pair ∈ rest,
              pair.1.VariablesBelow middle.inference.next ∧
                pair.2.VariablesBelow middle.inference.next := by
            intro pair member
            have pairBelow := below pair (by simp [member])
            exact ⟨pairBelow.1.weaken progress.next_le,
              pairBelow.2.weaken progress.next_le⟩
          have tailProperties := induction middleReady restBelow tail
          exact ⟨progress.trans tailProperties.1, tailProperties.2⟩

theorem unifyWeakArguments_preserves_resolve_eq {state next : State}
    {pairs : List (Ty × Ty)} {left right : Ty}
    (equal : state.resolve left = state.resolve right)
    (result : unifyWeakArguments state pairs = .ok next) :
    next.resolve left = next.resolve right := by
  induction pairs generalizing state with
  | nil =>
      simp [unifyWeakArguments] at result
      cases result
      exact equal
  | cons pair rest induction =>
      obtain ⟨source, target⟩ := pair
      cases head : unify state source target with
      | error error => simp [unifyWeakArguments, head, bind, Except.bind] at result
      | ok middle =>
          have tail : unifyWeakArguments middle rest = .ok next := by
            simpa [unifyWeakArguments, head, bind, Except.bind] using result
          exact induction (unify_preserves_resolve_eq equal head) tail

theorem variablesBelow_of_variablesBelowNext {next : Nat} {type : Ty}
    (below : variablesBelowNext next type = true) : type.VariablesBelow next := by
  intro metavariable member
  exact of_decide_eq_true (List.all_eq_true.mp below metavariable member)

theorem variablesBelow_of_closed {next : Nat} {type : Ty}
    (closed : type.freeVariables.isEmpty = true) : type.VariablesBelow next := by
  intro metavariable member
  cases free : type.freeVariables with
  | nil => simp [free] at member
  | cons first rest => simp [free] at closed

/-- One fix of the weak step: a requirement's open arguments unified pair by pair with its
source's, which hold no metavariable, while its own lie below the allocator. -/
def WeakArgumentStep (before after : State) : Prop :=
  ∃ pairs : List (Ty × Ty), unifyWeakArguments before pairs = .ok after ∧
    ∀ pair ∈ pairs, pair.1.VariablesBelow 0 ∧
      pair.2.VariablesBelow before.inference.next

theorem fixWeakArgument_step {context : Context} {state next : State}
    {requirement : Requirement}
    (result : fixWeakArgument context state requirement = some next) :
    WeakArgumentStep state next := by
  dsimp only [fixWeakArgument] at result
  split at result
  · cases result
  · rename_i considered
    split at result
    · cases result
    · rename_i arguments _
      split at result
      · cases result
      · rename_i sized
        split at result
        · rename_i middle unified
          cases result
          have targetsBelow :
              (applyPredicate state requirement.predicate).arguments.all
                (variablesBelowNext state.inference.next) = true := by
            cases below : (applyPredicate state requirement.predicate).arguments.all
                (variablesBelowNext state.inference.next)
            · rw [below] at considered
              simp at considered
            · rfl
          have sourcesClosed :
              arguments.all (fun argument => argument.freeVariables.isEmpty) = true := by
            cases closed : arguments.all (fun argument => argument.freeVariables.isEmpty)
            · rw [closed] at sized
              simp at sized
            · rfl
          refine ⟨_, unified, ?_⟩
          intro ⟨source, target⟩ member
          have members := List.of_mem_zip member
          exact ⟨variablesBelow_of_closed (List.all_eq_true.mp sourcesClosed source members.1),
            variablesBelow_of_variablesBelowNext
              (List.all_eq_true.mp targetsBelow target members.2)⟩
        · cases result

/-- A relation that is reflexive and transitive and that every fix of the weak step makes
relates a state to the result of its weak arguments. -/
theorem fixWeakArguments_induction {context : Context} {motive : State → State → Prop}
    (refl : ∀ state, motive state state)
    (trans : ∀ {first second third : State}, motive first second →
      motive second third → motive first third)
    (step : ∀ {before after : State}, WeakArgumentStep before after → motive before after)
    (state : State) : motive state (fixWeakArguments context state) := by
  have round : ∀ (requirements : List Requirement) (state : State),
      motive state (weakArgumentRound context state requirements).1 := by
    intro requirements
    induction requirements with
    | nil => exact refl
    | cons requirement rest induction =>
        intro state
        rw [weakArgumentRound]
        split
        · rename_i next fixed
          exact trans (step (fixWeakArgument_step fixed)) (induction next)
        · exact induction state
  have passes : ∀ (fuel : Nat) (state : State),
      motive state (weakArgumentPasses context fuel state) := by
    intro fuel
    induction fuel with
    | zero => exact refl
    | succ fuel induction =>
        intro state
        rw [weakArgumentPasses]
        split
        · rename_i next fixed
          have first := round state.requirements state
          rw [fixed] at first
          exact trans first (induction next)
        · exact refl state
  exact passes _ state

theorem fixWeakArguments_frame {context : Context} {state : State} :
    ∃ inference, fixWeakArguments context state = { state with inference } := by
  refine fixWeakArguments_induction
    (motive := fun before after => ∃ inference, after = { before with inference })
    (fun state => ⟨state.inference, rfl⟩) ?_ ?_ state
  · intro first second third ⟨inner, secondEq⟩ ⟨outer, thirdEq⟩
    subst thirdEq
    subst secondEq
    exact ⟨outer, rfl⟩
  · intro before after ⟨_, unified, _⟩
    exact unifyWeakArguments_frame unified

theorem fixWeakArguments_requirements {context : Context} {state : State} :
    (fixWeakArguments context state).requirements = state.requirements := by
  obtain ⟨_, frame⟩ := fixWeakArguments_frame (context := context) (state := state)
  exact (congrArg State.requirements frame).trans rfl

theorem fixWeakArguments_localSchemeAssumptions {context : Context} {state : State} :
    (fixWeakArguments context state).localSchemeAssumptions =
      state.localSchemeAssumptions := by
  obtain ⟨_, frame⟩ := fixWeakArguments_frame (context := context) (state := state)
  exact (congrArg State.localSchemeAssumptions frame).trans rfl

theorem fixWeakArguments_integerLiterals {context : Context} {state : State} :
    (fixWeakArguments context state).integerLiterals = state.integerLiterals := by
  obtain ⟨_, frame⟩ := fixWeakArguments_frame (context := context) (state := state)
  exact (congrArg State.integerLiterals frame).trans rfl

theorem fixWeakArguments_integerPatterns {context : Context} {state : State} :
    (fixWeakArguments context state).integerPatterns = state.integerPatterns := by
  obtain ⟨_, frame⟩ := fixWeakArguments_frame (context := context) (state := state)
  exact (congrArg State.integerPatterns frame).trans rfl

private theorem fixWeakArguments_toTypedSource {context : Context} {state : State}
    {roots : List NodeId} :
    (fixWeakArguments context state).toTypedSource roots =
      state.toTypedSource roots := by
  obtain ⟨_, frame⟩ := fixWeakArguments_frame (context := context) (state := state)
  exact (congrArg (fun next : State => next.toTypedSource roots) frame).trans rfl

/-- The weak arguments are ordinary inference progress and keep readiness. -/
theorem fixWeakArguments_inferenceProperties {context : Context} {state : State}
    (ready : state.InferenceReady) :
    state.InferenceProgress (fixWeakArguments context state) ∧
      (fixWeakArguments context state).InferenceReady := by
  refine fixWeakArguments_induction
    (motive := fun before after => before.InferenceReady →
      before.InferenceProgress after ∧ after.InferenceReady)
    (fun state ready => ⟨State.InferenceProgress.refl ready.solved, ready⟩) ?_ ?_
    state ready
  · intro first second third firstStep secondStep ready
    have head := firstStep ready
    have tail := secondStep head.2
    exact ⟨head.1.trans tail.1, tail.2⟩
  · intro before after ⟨_, unified, below⟩ ready
    exact unifyWeakArguments_inferenceProperties ready
      (fun pair member => ⟨(below pair member).1.weaken (Nat.zero_le _),
        (below pair member).2⟩)
      unified

/-- The weak arguments keep every type equality visible through the input state. -/
theorem fixWeakArguments_preserves_resolve_eq {context : Context} {state : State}
    {left right : Ty} (equal : state.resolve left = state.resolve right) :
    (fixWeakArguments context state).resolve left =
      (fixWeakArguments context state).resolve right := by
  refine fixWeakArguments_induction
    (motive := fun before after => before.resolve left = before.resolve right →
      after.resolve left = after.resolve right)
    (fun _ equal => equal) ?_ ?_ state equal
  · intro first second third firstStep secondStep equal
    exact secondStep (firstStep equal)
  · intro before after ⟨_, unified, _⟩ equal
    exact unifyWeakArguments_preserves_resolve_eq equal unified

/-! ### Finalization's defaulting -/

/-- A successful `defaultTargets` is the weak arguments, the pattern targets, the literal
targets and the weak arguments again. -/
theorem defaultTargets_success {context : Context} {state next : State}
    (success : defaultTargets context state = .ok next) :
    ∃ patternState literalState,
      defaultIntegerPatternTargets (fixWeakArguments context state).integerPatterns
          (fixWeakArguments context state) = .ok patternState ∧
        defaultIntegerLiteralTargets patternState.integerLiterals patternState =
          .ok literalState ∧
        fixWeakArguments context literalState = next := by
  unfold defaultTargets at success
  cases patternResult : defaultIntegerPatternTargets
      (fixWeakArguments context state).integerPatterns
      (fixWeakArguments context state) with
  | error error => simp [patternResult, bind, Except.bind] at success
  | ok patternState =>
      cases literalResult :
          defaultIntegerLiteralTargets patternState.integerLiterals patternState with
      | error error =>
          simp [patternResult, literalResult, bind, Except.bind] at success
      | ok literalState =>
          simp only [patternResult, literalResult, bind, Except.bind] at success
          cases success
          exact ⟨patternState, literalState, rfl, literalResult, rfl⟩

theorem defaultTargets_requirements {context : Context} {state next : State}
    (success : defaultTargets context state = .ok next) :
    next.requirements = state.requirements := by
  obtain ⟨patternState, literalState, patternResult, literalResult, rfl⟩ :=
    defaultTargets_success success
  rw [fixWeakArguments_requirements,
    defaultIntegerLiteralTargets_requirements literalResult,
    defaultIntegerPatternTargets_requirements patternResult,
    fixWeakArguments_requirements]

theorem defaultTargets_localSchemeAssumptions {context : Context} {state next : State}
    (success : defaultTargets context state = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
  obtain ⟨patternState, literalState, patternResult, literalResult, rfl⟩ :=
    defaultTargets_success success
  rw [fixWeakArguments_localSchemeAssumptions,
    defaultIntegerLiteralTargets_localSchemeAssumptions literalResult,
    defaultIntegerPatternTargets_localSchemeAssumptions patternResult,
    fixWeakArguments_localSchemeAssumptions]

theorem defaultTargets_integerLiterals {context : Context} {state next : State}
    (success : defaultTargets context state = .ok next) :
    next.integerLiterals = state.integerLiterals := by
  obtain ⟨patternState, literalState, patternResult, literalResult, rfl⟩ :=
    defaultTargets_success success
  rw [fixWeakArguments_integerLiterals,
    defaultIntegerLiteralTargets_integerLiterals literalResult,
    defaultIntegerPatternTargets_integerLiterals patternResult,
    fixWeakArguments_integerLiterals]

theorem defaultTargets_integerPatterns {context : Context} {state next : State}
    (success : defaultTargets context state = .ok next) :
    next.integerPatterns = state.integerPatterns := by
  obtain ⟨patternState, literalState, patternResult, literalResult, rfl⟩ :=
    defaultTargets_success success
  rw [fixWeakArguments_integerPatterns,
    defaultIntegerLiteralTargets_integerPatterns literalResult,
    defaultIntegerPatternTargets_integerPatterns patternResult,
    fixWeakArguments_integerPatterns]

private theorem defaultTargets_toTypedSource {context : Context} {state next : State}
    {roots : List NodeId}
    (success : defaultTargets context state = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  obtain ⟨patternState, literalState, patternResult, literalResult, rfl⟩ :=
    defaultTargets_success success
  rw [fixWeakArguments_toTypedSource,
    defaultIntegerLiteralTargets_toTypedSource literalResult,
    defaultIntegerPatternTargets_toTypedSource patternResult,
    fixWeakArguments_toTypedSource]

/-- Finalization's defaulting is ordinary inference progress and keeps readiness when every
numeric origin lies below the allocator. -/
theorem defaultTargets_inferenceProperties {context : Context} {state next : State}
    (ready : state.InferenceReady) (originsBelow : state.NumericOriginsBelowNext)
    (success : defaultTargets context state = .ok next) :
    state.InferenceProgress next ∧ next.InferenceReady := by
  obtain ⟨patternState, literalState, patternResult, literalResult, rfl⟩ :=
    defaultTargets_success success
  have weakProperties :=
    fixWeakArguments_inferenceProperties (context := context) ready
  have patternOriginsBelow :
      ∀ origin ∈ (fixWeakArguments context state).integerPatterns,
        origin.metavariable.index < (fixWeakArguments context state).inference.next := by
    intro origin member
    rw [fixWeakArguments_integerPatterns] at member
    exact Nat.lt_of_lt_of_le (originsBelow.1 origin member) weakProperties.1.next_le
  have patternProperties := defaultIntegerPatternTargets_inferenceProperties
    weakProperties.2 patternOriginsBelow patternResult
  have literalOriginsBelow : ∀ origin ∈ patternState.integerLiterals,
      origin.metavariable.index < patternState.inference.next := by
    intro origin member
    rw [defaultIntegerPatternTargets_integerLiterals patternResult,
      fixWeakArguments_integerLiterals] at member
    exact Nat.lt_of_lt_of_le (originsBelow.2 origin member)
      (Nat.le_trans weakProperties.1.next_le patternProperties.1.next_le)
  have literalProperties := defaultIntegerLiteralTargets_inferenceProperties
    patternProperties.2 literalOriginsBelow literalResult
  have secondProperties :=
    fixWeakArguments_inferenceProperties (context := context) literalProperties.2
  exact ⟨weakProperties.1.trans
      (patternProperties.1.trans (literalProperties.1.trans secondProperties.1)),
    secondProperties.2⟩

/-- Finalization's defaulting keeps every type equality visible through the input state. -/
theorem defaultTargets_preserves_resolve_eq {context : Context} {state next : State}
    {left right : Ty} (equal : state.resolve left = state.resolve right)
    (success : defaultTargets context state = .ok next) :
    next.resolve left = next.resolve right := by
  obtain ⟨patternState, literalState, patternResult, literalResult, rfl⟩ :=
    defaultTargets_success success
  exact fixWeakArguments_preserves_resolve_eq
    (defaultIntegerLiteralTargets_preserves_resolve_eq
      (defaultIntegerPatternTargets_preserves_resolve_eq
        (fixWeakArguments_preserves_resolve_eq equal) patternResult)
      literalResult)

private theorem validateNumericOriginsBelow_success
    {α : Type} {next : Nat} {metavariable : α → TypeVarId}
    {origins : List α}
    (success : validateNumericOriginsBelow next metavariable origins = .ok ()) :
    ∀ origin ∈ origins, (metavariable origin).index < next := by
  induction origins with
  | nil => simp
  | cons head tail induction =>
      by_cases below : (metavariable head).index < next
      · have tailSuccess :
            validateNumericOriginsBelow next metavariable tail = .ok () := by
          simpa [validateNumericOriginsBelow, below] using success
        intro origin member
        rcases List.mem_cons.mp member with rfl | member
        · exact below
        · exact induction tailSuccess origin member
      · simp [validateNumericOriginsBelow, below] at success

/-- Successful executable numeric-origin validation establishes the allocator
bound consumed by the numeric-defaulting preservation lemmas. -/
theorem validateNumericOriginsBelowNext_success
    {state : State}
    (success : validateNumericOriginsBelowNext state = .ok ()) :
    state.NumericOriginsBelowNext := by
  unfold validateNumericOriginsBelowNext at success
  cases patternResult : validateNumericOriginsBelow state.inference.next
      (fun origin : IntegerPatternOrigin => origin.metavariable)
      state.integerPatterns with
  | error error =>
      simp [patternResult, bind, Except.bind] at success
  | ok patternValidation =>
      cases patternValidation
      have literalResult :
          validateNumericOriginsBelow state.inference.next
              (fun origin : IntegerLiteralOrigin => origin.metavariable)
              state.integerLiterals = .ok () := by
        simpa [patternResult, bind, Except.bind] using success
      exact ⟨validateNumericOriginsBelow_success patternResult,
        validateNumericOriginsBelow_success literalResult⟩

/-- A successful finalization necessarily passes its leading numeric-origin
allocator validation. -/
theorem finalize_validateNumericOriginsBelowNext
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    validateNumericOriginsBelowNext state = .ok () := by
  unfold finalize at success
  cases validation : validateNumericOriginsBelowNext state with
  | error error =>
      simp [validation, bind, Except.bind] at success
  | ok validated =>
      cases validated
      rfl

/-- Finalization success is a self-contained certificate that every retained
numeric origin lies below the input inference allocator. -/
theorem finalize_numericOriginsBelowNext
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    state.NumericOriginsBelowNext :=
  validateNumericOriginsBelowNext_success
    (finalize_validateNumericOriginsBelowNext success)

/-- Finalization succeeds only after every pre-substitution expression type
passes the declaration-scoped structural formation check. -/
theorem finalize_validateSourceExpressionTypeFormation
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    validateSourceExpressionTypeFormation context
      (state.toTypedSource roots) = .ok () := by
  have numericValidation := finalize_validateNumericOriginsBelowNext success
  unfold finalize at success
  simp only [numericValidation] at success
  cases graphResult : validateSourceGraph (state.toTypedSource roots) with
  | error error =>
      simp [graphResult, bind, Except.bind] at success
  | ok graphValue =>
      cases graphValue
      cases validation : validateSourceExpressionTypeFormation context
          (state.toTypedSource roots) with
      | error error =>
          simp [graphResult, validation, bind, Except.bind] at success
      | ok value =>
          cases value
          rfl

/-- Every expression retained by the input source of a successful finalizer
has a structurally formed open inference type. -/
theorem finalize_expressionTypeFormationValidated
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result)
    {node : ExpressionNode}
    (member : Node.expression node ∈ (state.toTypedSource roots).nodes) :
    InferenceTypeFormationValidated context.signatures
      context.scope.genericOwner context.typeParameters node.type.freeVariables
      node.type := by
  exact validateSourceExpressionTypeFormation_success
    (finalize_validateSourceExpressionTypeFormation success) member

/-- The complete successful execution trace of `finalize`.

Keeping the intermediate states and their exact equations together gives
downstream soundness proofs one stable inversion point instead of requiring
each proof to unfold the whole executable pipeline. -/
structure FinalizeSuccessWitness
    (context : Context) (type : Ty) (state : State)
    (roots : List NodeId) (result : Result) where
  finalState : State
  solvedRequirements : List SolvedRequirement
  graphValidation :
    validateSourceGraph (state.toTypedSource roots) = .ok ()
  localIdentityValidation :
    validateSourceLocalIdentities (state.toTypedSource roots) = .ok ()
  templateTrackingValidation :
    validateSourceTemplateTracking (state.toTypedSource roots) state = .ok ()
  ledgerValidation : validateIntegerLiteralLedger state = .ok ()
  /-- The weak trait arguments, the numeric targets and the weak arguments again. -/
  defaulting : defaultTargets context state = .ok finalState
  patternValidation :
    validateIntegerPatternTargets finalState finalState.integerPatterns =
      .ok ()
  literalValidation :
    validateIntegerLiteralTargets finalState finalState.integerLiterals =
      .ok ()
  requirementOwnershipValidation :
    validateSourceRequirementOwnership (finalState.toTypedSource roots)
      finalState.requirements = .ok ()
  templateScopeValidation :
    validateSourceTemplateScopes
      ((finalState.toTypedSource roots).applySubstitution
        finalState.inference.substitution) finalState = .ok ()
  requirementsSolved :
    solveRequirements context finalState finalState.requirements =
      .ok solvedRequirements
  result_eq : result = {
    type := finalState.resolve type
    substitution := finalState.inference.substitution
    solvedRequirements
    typedSource := (finalState.toTypedSource roots).applySubstitution
      finalState.inference.substitution
  }
  /-- Every value assignment's target type takes its operator, checked after
  the literal targets (kept last, so positional patterns keep their fields). -/
  assignmentValidation :
    validateAssignmentTargets finalState finalState.nodes = .ok ()
  /-- Every element place of a memory array has indexes that a read takes,
  checked after the assignment targets. -/
  placeElementValidation :
    validatePlaceElements finalState finalState.nodes = .ok ()
  /-- No operator that took its builtin at `word` or a fixed-width type meets a
  program's implementation of its trait there, checked after the element places. -/
  builtinOperatorValidation :
    validateBuiltinOperatorUses context finalState finalState.nodes = .ok ()

/-- Invert one successful `finalize` call into all successful pipeline stages
and the exact result assembled from the final state. -/
def finalize_success_witness
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    FinalizeSuccessWitness context type state roots result := by
  have numericOriginsValidation :=
    finalize_validateNumericOriginsBelowNext success
  have expressionTypeFormationValidation :=
    finalize_validateSourceExpressionTypeFormation success
  unfold finalize at success
  simp only [numericOriginsValidation] at success
  have graphValidation :
      validateSourceGraph (state.toTypedSource roots) = .ok () := by
    cases graphResult : validateSourceGraph (state.toTypedSource roots) with
    | error error =>
        simp [graphResult, bind, Except.bind] at success
    | ok graphValue =>
        cases graphValue
        simp at graphResult ⊢
  simp only [expressionTypeFormationValidation] at success
  have localIdentityValidation :
      validateSourceLocalIdentities (state.toTypedSource roots) = .ok () := by
    cases localResult :
        validateSourceLocalIdentities (state.toTypedSource roots) with
    | error error =>
        simp [graphValidation, localResult, bind, Except.bind] at success
    | ok localValue =>
        cases localValue
        simp at localResult ⊢
  have templateTrackingValidation :
      validateSourceTemplateTracking (state.toTypedSource roots) state =
        .ok () := by
    cases templateResult :
        validateSourceTemplateTracking (state.toTypedSource roots) state with
    | error error =>
        simp [graphValidation, localIdentityValidation, templateResult, bind,
          Except.bind] at success
    | ok templateValue =>
        cases templateValue
        simp at templateResult ⊢
  cases ledgerResult : validateIntegerLiteralLedger state with
  | error error =>
      simp [graphValidation, localIdentityValidation,
        templateTrackingValidation, ledgerResult, bind, Except.bind] at success
  | ok ledgerValue =>
      cases ledgerValue
      cases defaultingResult : defaultTargets context state with
      | error error =>
          simp [graphValidation, localIdentityValidation,
            templateTrackingValidation, ledgerResult, defaultingResult, bind,
            Except.bind] at success
      | ok finalState =>
          cases patternValidationResult :
              validateIntegerPatternTargets finalState
                finalState.integerPatterns with
          | error error =>
              simp [graphValidation, localIdentityValidation,
                templateTrackingValidation, ledgerResult, defaultingResult,
                patternValidationResult, bind, Except.bind]
                at success
          | ok patternValidation =>
              cases patternValidation
              cases literalValidationResult :
                  validateIntegerLiteralTargets finalState
                    finalState.integerLiterals with
              | error error =>
                  simp [graphValidation, localIdentityValidation,
                    templateTrackingValidation, ledgerResult,
                    defaultingResult, patternValidationResult,
                    literalValidationResult, bind, Except.bind] at success
              | ok literalValidation =>
                  cases literalValidation
                  have assignmentResult :
                      validateAssignmentTargets finalState finalState.nodes =
                        .ok () := by
                    cases assignmentRun :
                        validateAssignmentTargets finalState
                          finalState.nodes with
                    | error error =>
                        simp [graphValidation, localIdentityValidation,
                          templateTrackingValidation, ledgerResult,
                          defaultingResult,
                          patternValidationResult, literalValidationResult,
                          assignmentRun, bind, Except.bind] at success
                    | ok assignmentValue =>
                        cases assignmentValue
                        rfl
                  have placeElementResult :
                      validatePlaceElements finalState finalState.nodes =
                        .ok () := by
                    cases placeElementRun :
                        validatePlaceElements finalState
                          finalState.nodes with
                    | error error =>
                        simp [graphValidation, localIdentityValidation,
                          templateTrackingValidation, ledgerResult,
                          defaultingResult,
                          patternValidationResult, literalValidationResult,
                          assignmentResult, placeElementRun, bind, Except.bind] at success
                    | ok placeElementValue =>
                        cases placeElementValue
                        rfl
                  have builtinOperatorResult :
                      validateBuiltinOperatorUses context finalState
                        finalState.nodes = .ok () := by
                    cases builtinOperatorRun :
                        validateBuiltinOperatorUses context finalState
                          finalState.nodes with
                    | error error =>
                        simp [graphValidation, localIdentityValidation,
                          templateTrackingValidation, ledgerResult,
                          defaultingResult,
                          patternValidationResult, literalValidationResult,
                          assignmentResult, placeElementResult, builtinOperatorRun, bind,
                          Except.bind] at success
                    | ok builtinOperatorValue =>
                        cases builtinOperatorValue
                        rfl
                  cases ownershipResult :
                      validateSourceRequirementOwnership
                        (finalState.toTypedSource roots)
                        finalState.requirements with
                  | error error =>
                      simp [graphValidation, localIdentityValidation,
                        templateTrackingValidation, ledgerResult,
                        defaultingResult,
                        patternValidationResult, literalValidationResult, assignmentResult,
                        placeElementResult, builtinOperatorResult,
                        ownershipResult, bind, Except.bind] at success
                  | ok ownershipValidation =>
                      cases ownershipValidation
                      cases rangeResult :
                          validateFinalSubstitutionRangeFormation context
                            finalState.inference.substitution with
                      | error error =>
                          simp [graphValidation, localIdentityValidation,
                            templateTrackingValidation, ledgerResult,
                            defaultingResult,
                            patternValidationResult,
                            literalValidationResult, assignmentResult, placeElementResult, builtinOperatorResult,
                            ownershipResult,
                            rangeResult, bind, Except.bind]
                            at success
                      | ok rangeValidation =>
                          cases rangeValidation
                          cases captureResult :
                              validateSourceLocalSchemeNoCapture
                                (finalState.toTypedSource roots)
                                finalState.inference.substitution with
                          | error error =>
                              simp [graphValidation,
                                localIdentityValidation,
                                templateTrackingValidation, ledgerResult,
                                defaultingResult,
                                patternValidationResult,
                                literalValidationResult, assignmentResult, placeElementResult, builtinOperatorResult,
                                ownershipResult,
                                rangeResult, captureResult, bind,
                                Except.bind]
                                at success
                          | ok captureValidation =>
                              cases captureValidation
                              cases templateScopeResult :
                                  validateSourceTemplateScopes
                                    ((finalState.toTypedSource roots
                                      ).applySubstitution
                                        finalState.inference.substitution)
                                    finalState with
                              | error error =>
                                  simp [graphValidation,
                                    localIdentityValidation,
                                    templateTrackingValidation,
                                    ledgerResult, defaultingResult,
                                    patternValidationResult,
                                    literalValidationResult, assignmentResult,
                                    placeElementResult, builtinOperatorResult,
                                    ownershipResult, rangeResult,
                                    captureResult, templateScopeResult,
                                    bind, Except.bind]
                                    at success
                              | ok templateScopeValidation =>
                                  cases templateScopeValidation
                                  cases requirementsResult :
                                      solveRequirements context finalState
                                        finalState.requirements with
                                  | error error =>
                                      simp [graphValidation,
                                        localIdentityValidation,
                                        templateTrackingValidation,
                                        ledgerResult, defaultingResult,
                                        patternValidationResult,
                                        literalValidationResult, assignmentResult,
                                        placeElementResult, builtinOperatorResult,
                                        ownershipResult, rangeResult,
                                        captureResult, templateScopeResult,
                                        requirementsResult, bind,
                                        Except.bind]
                                        at success
                                  | ok requirements =>
                                      simp [graphValidation,
                                        localIdentityValidation,
                                        templateTrackingValidation,
                                        ledgerResult, defaultingResult,
                                        patternValidationResult,
                                        literalValidationResult, assignmentResult,
                                        placeElementResult, builtinOperatorResult,
                                        ownershipResult, rangeResult,
                                        captureResult, templateScopeResult,
                                        requirementsResult, bind,
                                        Except.bind]
                                        at success
                                      cases success
                                      exact {
                                        finalState
                                        solvedRequirements := requirements
                                        graphValidation
                                        localIdentityValidation
                                        templateTrackingValidation
                                        ledgerValidation := ledgerResult
                                        defaulting := defaultingResult
                                        patternValidation :=
                                          patternValidationResult
                                        literalValidation :=
                                          literalValidationResult
                                        requirementOwnershipValidation :=
                                          ownershipResult
                                        templateScopeValidation :=
                                          templateScopeResult
                                        requirementsSolved :=
                                          requirementsResult
                                        assignmentValidation := assignmentResult
                                        placeElementValidation := placeElementResult
                                        builtinOperatorValidation := builtinOperatorResult
                                        result_eq := rfl
                                      }

/-- Finalization validates numeric-origin allocator safety before composing
its defaulting as ordinary semantic inference progress.  The existential final
state is the internal state whose substitution is exposed by the public
result. -/
theorem finalize_inferenceProperties
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (ready : state.InferenceReady)
    (success : finalize context type state roots = .ok result) :
    ∃ finalState,
      state.InferenceProgress finalState ∧
        finalState.InferenceReady ∧
        result.substitution = finalState.inference.substitution := by
  have originsBelow := finalize_numericOriginsBelowNext success
  obtain ⟨finalState, _, _, _, _, _, defaulting, _, _, _, _, _, resultEq⟩ :=
    finalize_success_witness success
  subst result
  have properties := defaultTargets_inferenceProperties ready originsBelow defaulting
  exact ⟨finalState, properties.1, properties.2, rfl⟩

/-- The substitution returned by successful finalization is solved below the
allocator of its hidden final state.  The leading executable validation makes
the required numeric-origin bound internal to finalization. -/
theorem finalize_substitution_solvedBelow
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (ready : state.InferenceReady)
    (success : finalize context type state roots = .ok result) :
    ∃ next, result.substitution.SolvedBelow next := by
  obtain ⟨finalState, _, finalReady, substitutionEq⟩ :=
    finalize_inferenceProperties ready success
  refine ⟨finalState.inference.next, ?_⟩
  rw [substitutionEq]
  exact finalReady.solved

/-- Successful finalization includes successful structural validation of its
input typed-source graph. -/
theorem finalize_validateSourceGraph
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    validateSourceGraph (state.toTypedSource roots) = .ok () := by
  exact (finalize_success_witness success).graphValidation

/-- Successful finalization includes successful ownership and global
uniqueness validation for its input local binders. -/
theorem finalize_validateSourceLocalIdentities
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    validateSourceLocalIdentities (state.toTypedSource roots) = .ok () := by
  exact (finalize_success_witness success).localIdentityValidation

/-- Successful finalization includes exact source-to-state classification and
raw-ledger coverage for every qualified local-scheme template. -/
theorem finalize_validateSourceTemplateTracking
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    validateSourceTemplateTracking (state.toTypedSource roots) state =
      .ok () := by
  exact (finalize_success_witness success).templateTrackingValidation

private theorem finalize_success_witness_rangeFormationValidation
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    validateFinalSubstitutionRangeFormation context
      (finalize_success_witness success).finalState.inference.substitution =
        .ok () := by
  let witness := finalize_success_witness success
  have pipeline := success
  have numericValidation := finalize_validateNumericOriginsBelowNext success
  unfold finalize at pipeline
  simp only [numericValidation, bind, Except.bind] at pipeline
  simp only [witness.graphValidation] at pipeline
  simp only [finalize_validateSourceExpressionTypeFormation success] at pipeline
  simp only [witness.localIdentityValidation] at pipeline
  simp only [witness.templateTrackingValidation] at pipeline
  simp only [witness.ledgerValidation] at pipeline
  simp only [witness.defaulting] at pipeline
  simp only [witness.patternValidation] at pipeline
  simp only [witness.literalValidation] at pipeline
  simp only [witness.assignmentValidation] at pipeline
  simp only [witness.placeElementValidation] at pipeline
  simp only [witness.builtinOperatorValidation] at pipeline
  simp only [witness.requirementOwnershipValidation] at pipeline
  cases validation : validateFinalSubstitutionRangeFormation context
      witness.finalState.inference.substitution with
  | error error =>
      simp only [validation, reduceCtorEq] at pipeline
  | ok validated =>
      cases validated
      rfl

/-- Successful finalization exposes the hidden post-defaulting state at which
the complete inference-substitution range passed structural formation
validation. -/
theorem finalize_validateFinalSubstitutionRangeFormation
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    ∃ finalState : State,
      result.substitution = finalState.inference.substitution ∧
        validateFinalSubstitutionRangeFormation context
          finalState.inference.substitution = .ok () := by
  let witness := finalize_success_witness success
  exact ⟨witness.finalState,
    congrArg Result.substitution witness.result_eq,
    finalize_success_witness_rangeFormationValidation success⟩

/-- Finalization success is a reusable frontend certificate that every actual
entry of the returned inference substitution is structurally formed in the
declaration's open type scope. -/
theorem finalize_substitutionRangeFormationValidated
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    InferenceSubstitutionRangeFormationValidated context.signatures
      context.scope.genericOwner context.typeParameters result.substitution := by
  obtain ⟨finalState, substitutionEq, validation⟩ :=
    finalize_validateFinalSubstitutionRangeFormation success
  rw [substitutionEq]
  unfold validateFinalSubstitutionRangeFormation at validation
  cases rangeResult : validateInferenceSubstitutionRangeFormation
      context.signatures context.scope.genericOwner context.typeParameters
      finalState.inference.substitution with
  | error error => simp [rangeResult] at validation
  | ok validated =>
      cases validated
      exact validateInferenceSubstitutionRangeFormation_success rangeResult

/-- A successful function-body check exposes the open range-formation
certificate for the exact substitution retained by the checked function. -/
theorem checkFunctionBody_success_substitutionRangeFormationValidated
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat} {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    InferenceSubstitutionRangeFormationValidated signatures signature.id
      signature.scheme.parameters checked.substitution := by
  obtain ⟨declaration, body, finalState, result, declarationEq, _, _,
      finalizeEq, checkedEq⟩ := checkFunctionBody_success_witness success
  have declarationId : declaration.id = signature.id :=
    (ProgramEnvironment.declaration?_sound declarationEq).2
  have validated := finalize_substitutionRangeFormationValidated finalizeEq
  rw [checkedEq]
  simpa [ProgramTypeScope.ofDeclaration, declarationId] using validated

/-- Successful finalization exposes the hidden post-defaulting state at which
local-scheme capture was checked.  The source carrier is unchanged by the
defaulting and the state's substitution is exactly the public result
substitution. -/
theorem finalize_validateSourceLocalSchemeNoCapture
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    ∃ finalState : State,
      finalState.toTypedSource roots = state.toTypedSource roots ∧
        result.substitution = finalState.inference.substitution ∧
        validateSourceLocalSchemeNoCapture
          (finalState.toTypedSource roots)
          finalState.inference.substitution = .ok () := by
  let witness := finalize_success_witness success
  have sourceEq : witness.finalState.toTypedSource roots =
      state.toTypedSource roots :=
    defaultTargets_toTypedSource witness.defaulting
  have substitutionEq :
      result.substitution = witness.finalState.inference.substitution := by
    exact congrArg Result.substitution witness.result_eq
  have captureValidation :
      validateSourceLocalSchemeNoCapture
          (witness.finalState.toTypedSource roots)
          witness.finalState.inference.substitution = .ok () := by
    have pipeline := success
    have numericValidation := finalize_validateNumericOriginsBelowNext success
    unfold finalize at pipeline
    simp only [numericValidation, bind, Except.bind] at pipeline
    simp only [witness.graphValidation] at pipeline
    simp only [finalize_validateSourceExpressionTypeFormation success] at pipeline
    simp only [witness.localIdentityValidation] at pipeline
    simp only [witness.templateTrackingValidation] at pipeline
    simp only [witness.ledgerValidation] at pipeline
    simp only [witness.defaulting] at pipeline
    simp only [witness.patternValidation] at pipeline
    simp only [witness.literalValidation] at pipeline
    simp only [witness.assignmentValidation] at pipeline
    simp only [witness.placeElementValidation] at pipeline
    simp only [witness.builtinOperatorValidation] at pipeline
    simp only [witness.requirementOwnershipValidation] at pipeline
    have rangeValidation :
        validateFinalSubstitutionRangeFormation context
            witness.finalState.inference.substitution = .ok () :=
      finalize_success_witness_rangeFormationValidation success
    simp only [rangeValidation] at pipeline
    cases validation : validateSourceLocalSchemeNoCapture
        (witness.finalState.toTypedSource roots)
        witness.finalState.inference.substitution with
    | error error =>
        simp only [validation, reduceCtorEq] at pipeline
    | ok validated =>
        cases validated
        rfl
  exact ⟨witness.finalState, sourceEq, substitutionEq, captureValidation⟩

/-- Finalization success is a directly usable certificate that every
initialized binder in the input typed source is protected from capture by the
returned substitution. -/
theorem finalize_localBinderInstantiationNoCapture
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    ∀ binder, binder ∈ (state.toTypedSource roots).initializedLetBinders →
      LocalBinderInstantiationNoCapture result.substitution binder := by
  obtain ⟨finalState, sourceEq, substitutionEq, validation⟩ :=
    finalize_validateSourceLocalSchemeNoCapture success
  intro binder member
  have finalMember :
      binder ∈ (finalState.toTypedSource roots).initializedLetBinders := by
    rw [sourceEq]
    exact member
  rw [substitutionEq]
  exact validateSourceLocalSchemeNoCapture_success validation binder finalMember

/-- Successful finalization establishes the exact primary-to-ledger ownership
boundary.  The defaulting changes neither the source carrier nor the raw
requirement ledger, so the validation is exposed at the input state. -/
theorem finalize_validateSourceRequirementOwnership
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    validateSourceRequirementOwnership (state.toTypedSource roots)
      state.requirements = .ok () := by
  let witness := finalize_success_witness success
  have sourceEq : witness.finalState.toTypedSource roots =
      state.toTypedSource roots :=
    defaultTargets_toTypedSource witness.defaulting
  have requirementsEq : witness.finalState.requirements = state.requirements :=
    defaultTargets_requirements witness.defaulting
  rw [← sourceEq, ← requirementsEq]
  exact witness.requirementOwnershipValidation

/-- Successful finalization includes successful validation of its input
integer-literal ledger. -/
theorem finalize_validateIntegerLiteralLedger
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    validateIntegerLiteralLedger state = .ok () := by
  exact (finalize_success_witness success).ledgerValidation

/-- Successful finalization certifies the literal metadata and exact
requirement row of every integer-literal node in its input state. -/
theorem finalize_integerLiteralLedgerCorrespondence
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    state.IntegerLiteralLedgerCorrespondence := by
  exact validateIntegerLiteralLedger_success_correspondence
    (finalize_validateIntegerLiteralLedger success)

/-- Finalization closes every retained integer-pattern origin to a carrier
implemented by both the declarative semantics and runtime. -/
theorem finalize_integerPatternTarget_supported
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    ∀ origin, origin ∈ state.integerPatterns →
      (result.substitution.apply (.variable origin.metavariable)).IntegerPatternCarrier := by
  obtain ⟨finalState, _, _, _, _, _, defaulting, patternValidation, _, _, _, _,
      resultEq⟩ := finalize_success_witness success
  have finalOrigins := defaultTargets_integerPatterns defaulting
  have supported :=
    validateIntegerPatternTargets_success_supported patternValidation
  subst result
  intro origin member
  have finalMember : origin ∈ finalState.integerPatterns := by
    rw [finalOrigins]
    exact member
  simpa [State.resolve, TypeSystem.InferState.resolve] using
    supported origin finalMember

/-- Finalization closes every retained integer-literal origin to a carrier
implemented by both the declarative semantics and runtime. -/
theorem finalize_integerLiteralTarget_supported
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    ∀ origin, origin ∈ state.integerLiterals →
      (result.substitution.apply (.variable origin.metavariable)).IntegerLiteralCarrier := by
  obtain ⟨finalState, _, _, _, _, _, defaulting, _, literalValidation, _, _, _,
      resultEq⟩ := finalize_success_witness success
  have finalOrigins := defaultTargets_integerLiterals defaulting
  have supported :=
    validateIntegerLiteralTargets_success_supported literalValidation
  subst result
  intro origin member
  have finalMember : origin ∈ finalState.integerLiterals := by
    rw [finalOrigins]
    exact member
  simpa [State.resolve, TypeSystem.InferState.resolve] using
    supported origin finalMember

/-- Finalization bounds every literal node of a retained integer-literal origin
by its final carrier: at a fixed-width type it is at most the greatest value. -/
theorem finalize_integerLiteral_fits
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    ∀ origin, origin ∈ state.integerLiterals →
      ∀ {node : ExpressionNode} {source : Syntax.CoreLiteralValue}
        {resolution : IntegerLiteralResolution},
        Node.expression node ∈ state.nodes → node.id = origin.expression →
        node.form = .integerLiteral source resolution →
        signedLiteralFitsTarget source (result.substitution.apply (.variable origin.metavariable))
          resolution.rawValue = true := by
  obtain ⟨finalState, _, _, _, _, _, defaulting, _, literalValidation, _, _, _,
      resultEq⟩ := finalize_success_witness success
  have finalOrigins := defaultTargets_integerLiterals defaulting
  have finalNodes : finalState.nodes = state.nodes :=
    congrArg TypedSource.nodes
      (defaultTargets_toTypedSource (roots := roots) defaulting)
  have fits := validateIntegerLiteralTargets_success_fits literalValidation
  subst result
  intro origin member node source resolution nodeMember identity form
  have finalMember : origin ∈ finalState.integerLiterals := by
    rw [finalOrigins]
    exact member
  have finalNode : Node.expression node ∈ finalState.nodes := by
    rw [finalNodes]
    exact nodeMember
  simpa [State.resolve, TypeSystem.InferState.resolve] using
    literalNodesFit_member (fits origin finalMember) finalNode identity form

/-- Finalization may extend the inference substitution while fixing weak
trait arguments and defaulting numeric targets, but it cannot invalidate a type
equality already established by the input state. -/
theorem finalize_preserves_resolve_eq
    {context : Context} {type left right : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (equal : state.resolve left = state.resolve right)
    (success : finalize context type state roots = .ok result) :
    result.substitution.apply left = result.substitution.apply right := by
  obtain ⟨finalState, _, _, _, _, _, defaulting, _, _, _, _, _, resultEq⟩ :=
    finalize_success_witness success
  have finalEqual := defaultTargets_preserves_resolve_eq equal defaulting
  subst result
  exact finalEqual

/-- A unification equality survives numeric defaulting and finalization under
the final substitution returned to callers. -/
theorem unify_then_finalize_eq
    {context : Context} {type left right : Ty} {state unified : State}
    {roots : List NodeId} {result : Result}
    (unification : unify state left right = .ok unified)
    (finalization : finalize context type unified roots = .ok result) :
    result.substitution.apply left = result.substitution.apply right := by
  exact finalize_preserves_resolve_eq
    (by simpa [State.resolve] using unify_resolve_eq unification)
    finalization

/-- When the right-hand side is a successfully resolved source annotation,
unification followed by finalization fixes the inferred type to that exact
rigid annotation. -/
theorem unify_then_finalize_annotation_eq
    {context : Context} {sourceType : Syntax.TypeExpr}
    {annotationType inferredType resultType : Ty} {state unified : State}
    {roots : List NodeId} {result : Result}
    (annotation : resolveSourceType context sourceType = .ok annotationType)
    (unification : unify state inferredType annotationType = .ok unified)
    (finalization : finalize context resultType unified roots = .ok result) :
    result.substitution.apply inferredType = annotationType := by
  calc
    result.substitution.apply inferredType =
        result.substitution.apply annotationType :=
      unify_then_finalize_eq unification finalization
    _ = annotationType :=
      resolveSourceType_success_apply_eq_self result.substitution annotation

/-- A successful finalization reports the input type under its final inference
substitution. -/
theorem finalize_type
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.type = result.substitution.apply type := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, resultEq⟩ :=
    finalize_success_witness success
  subst result
  rfl

/-- Finalization changes only inference metadata before applying the final
substitution to the source carrier supplied by its input state. -/
theorem finalize_typedSource
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource =
      (state.toTypedSource roots).applySubstitution result.substitution := by
  obtain ⟨_, _, _, _, _, _, defaulting, _, _, _, _, _, resultEq⟩ :=
    finalize_success_witness success
  subst result
  rw [defaultTargets_toTypedSource defaulting]

/-- Finalization preserves the declaration owning the inferred source. -/
theorem finalize_typedSource_owner
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.owner = state.owner := by
  rw [finalize_typedSource success]
  rfl

/-- A successful finalization applies its final inference substitution
pointwise to the exact input binders retained by the input state. -/
theorem finalize_typedSource_inputs
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.inputs =
      state.inputs.map (TypedBinder.applySubstitution result.substitution) := by
  rw [finalize_typedSource success]
  rfl

/-- Final substitution preserves the stable identities of every input. -/
theorem finalize_typedSource_inputIds
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.inputs.map (fun binder => binder.id) =
      state.inputs.map (fun binder => binder.id) := by
  rw [finalize_typedSource success]
  simp [State.toTypedSource]

/-- Final substitution cannot rename the inputs retained by finalization. -/
theorem finalize_typedSource_inputNames
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.inputs.map (fun binder => binder.name) =
      state.inputs.map (fun binder => binder.name) := by
  rw [finalize_typedSource success]
  simp [State.toTypedSource]

/-- Final substitution cannot change input staging markers. -/
theorem finalize_typedSource_inputComptime
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.inputs.map (fun binder => binder.comptime) =
      state.inputs.map (fun binder => binder.comptime) := by
  rw [finalize_typedSource success]
  simp [State.toTypedSource]

/-- Every integer-literal node of the finalized source fits its closed carrier:
at a fixed-width type a literal is at most the type's greatest value, and a
negative literal's magnitude at most that of its least value. -/
theorem finalize_typedSource_integerLiteral_fits
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    ∀ {node : ExpressionNode} {source : Syntax.CoreLiteralValue}
      {resolution : IntegerLiteralResolution},
      Node.expression node ∈ result.typedSource.nodes →
      node.form = .integerLiteral source resolution →
      signedLiteralFitsTarget source resolution.targetType resolution.rawValue = true := by
  have ledger := finalize_integerLiteralLedgerCorrespondence success
  have fits := finalize_integerLiteral_fits success
  intro node source resolution member form
  rw [finalize_typedSource success] at member
  obtain ⟨original, originalMember, originalEq⟩ := List.mem_map.mp member
  cases original with
  | statement statementNode => cases originalEq
  | expression originalNode =>
    have nodeEq : originalNode.applySubstitution result.substitution = node := by
      simpa [Node.applySubstitution] using originalEq
    subst nodeEq
    have originalState : Node.expression originalNode ∈ state.nodes := originalMember
    cases originalForm : originalNode.form with
    | integerLiteral originalSource originalResolution =>
        have formEq : ExpressionForm.integerLiteral originalSource
            (originalResolution.applySubstitution result.substitution) =
              .integerLiteral source resolution := by
          simpa [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
            originalForm] using form
        obtain ⟨sourceEq, resolutionEq⟩ := ExpressionForm.integerLiteral.inj formEq
        subst sourceEq
        subst resolutionEq
        obtain ⟨_, origin, originMember, expressionEq, targetEq, _, _⟩ :=
          ledger originalNode originalSource originalResolution originalState originalForm
        have fitsOrigin := fits origin originMember originalState expressionEq.symm originalForm
        simpa [IntegerLiteralResolution.applySubstitution, targetEq] using fitsOrigin
    | _ =>
        simp [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
          originalForm] at form

end Solcore.Frontend.SourceInference.Detail

namespace Solcore.Frontend.SourceInference

open TypeSystem

private theorem functionParameterEnvironment_names
    (parameters : List ProgramFunctionParameter) :
    ((((parameters.map (fun parameter => parameter.name)).zip
        (parameters.map (fun parameter => parameter.type))).map
          fun parameter => (parameter.1, Scheme.mono parameter.2)).map
      fun entry => entry.1) =
        parameters.map (fun parameter => parameter.name) := by
  induction parameters with
  | nil => rfl
  | cons parameter rest induction => simp [induction]

private theorem functionParameterEnvironment_eq
    (parameters : List ProgramFunctionParameter) :
    (((parameters.map (fun parameter => parameter.name)).zip
        (parameters.map (fun parameter => parameter.type))).map
      fun parameter => (parameter.1, Scheme.mono parameter.2)) =
        parameters.map fun parameter =>
          (parameter.name, Scheme.mono parameter.type) := by
  induction parameters with
  | nil => rfl
  | cons parameter rest induction => simp [induction]

private theorem map_mapIdx {alpha beta gamma : Type}
    (items : List alpha) (prepare : alpha → beta)
    (indexed : Nat → beta → gamma) :
    (items.map prepare).mapIdx indexed =
      items.mapIdx fun index item => indexed index (prepare item) := by
  induction items generalizing indexed with
  | nil => rfl
  | cons item rest induction =>
      simp only [List.map_cons, List.mapIdx_cons]
      exact congrArg (indexed 0 (prepare item) :: ·)
        (induction (fun index item => indexed (index + 1) item))

/-- Pointwise substitution invariance of every parameter type makes a
source-ordered row of monomorphic parameter binders invariant too.  The
indexed constructor is abstract so the result also covers the stable IDs,
names, staging markers, and spans assigned by `State.initial`. -/
private theorem functionParameterBinders_applySubstitution_eq_self
    {parameters : List ProgramFunctionParameter}
    (substitution : Substitution)
    (typesFixed :
      (parameters.map fun parameter => parameter.type).map
          substitution.apply =
        parameters.map fun parameter => parameter.type)
    (indexed : Nat → ProgramFunctionParameter → TypedBinder)
    (schemes : ∀ index parameter,
      (indexed index parameter).scheme = Scheme.mono parameter.type)
    (requirements : ∀ index parameter,
      (indexed index parameter).schemeRequirements = []) :
    (parameters.mapIdx indexed).map
        (TypedBinder.applySubstitution substitution) =
      parameters.mapIdx indexed := by
  induction parameters generalizing indexed with
  | nil => rfl
  | cons parameter parameters induction =>
      simp only [List.map_cons, List.cons.injEq] at typesFixed
      rcases typesFixed with ⟨headFixed, tailFixed⟩
      simp only [List.mapIdx_cons, List.map_cons, List.cons.injEq]
      constructor
      · have schemeEq := schemes 0 parameter
        have requirementsEq := requirements 0 parameter
        cases binderEq : indexed 0 parameter with
        | mk id name scheme schemeRequirements comptime span =>
            simp only [binderEq] at schemeEq requirementsEq
            subst scheme
            subst schemeRequirements
            simp [TypedBinder.applySubstitution, Scheme.apply,
              Scheme.mono, Substitution.without, headFixed]
      · exact induction tailFixed
          (fun index parameter => indexed (index + 1) parameter)
          (fun index parameter => schemes (index + 1) parameter)
          (fun index parameter => requirements (index + 1) parameter)

/-- Successful checking of a cataloged function exposes the body-inference
stage together with the semantic state invariants needed by downstream
soundness proofs.  This deliberately projects only the declaration and body
from the larger execution witness, before return unification and finalization.
-/
theorem checkFunctionBody_success_body_inferenceProperties
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (validated : ProgramSignatureFormationValidated signatures)
    (member : signature ∈ signatures.functions)
    (canonical : ∀ candidate ∈ signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ∃ declaration body,
      environment.declaration? signature.id = some declaration ∧
        Detail.inferStatementsFuel fuel
            {
              environment
              signatures
              scope := .ofDeclaration declaration
              typeParameters := signature.scheme.parameters
              assumptions := signature.scheme.predicates
            }
            signature.source.value.body.value
            (Ty.productMany signature.returnTypes)
            (State.initial declaration.id
              ((signature.parameterNames.zip signature.parameterTypes).map
                fun parameter => (parameter.1, Scheme.mono parameter.2))
              signature.parameterComptime) = .ok body ∧
          (State.initial declaration.id
              ((signature.parameterNames.zip signature.parameterTypes).map
                fun parameter => (parameter.1, Scheme.mono parameter.2))
              signature.parameterComptime).InferenceProgress body.state ∧
            body.state.InferenceReady ∧
              body.type.VariablesBelow body.state.inference.next := by
  obtain ⟨declaration, body, _, _, declarationEq, bodyEq, _, _, _⟩ :=
    checkFunctionBody_success_witness success
  let locals : TypeSystem.Environment :=
    (signature.parameterNames.zip signature.parameterTypes).map
      fun parameter => (parameter.1, Scheme.mono parameter.2)
  let initial := State.initial declaration.id locals signature.parameterComptime
  have initialReady : initial.InferenceReady := by
    simpa only [initial, locals] using
      State.InferenceReady.initial declaration.id locals
        signature.parameterComptime
  have returnBelow : (Ty.productMany signature.returnTypes).VariablesBelow
      initial.inference.next :=
    Ty.variablesBelow_productMany
      ((validated.functions signature member).2.1.variablesBelow
        initial.inference.next)
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    initialReady validated canonical returnBelow (by
      simpa only [initial, locals] using bodyEq)
  refine ⟨declaration, body, declarationEq, bodyEq, ?_⟩
  simpa only [initial, locals] using bodyProperties

/-- Successful checking retains the callable type assembled by the signature
builder. -/
theorem checkFunctionBody_success_type
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.type = signature.scheme.body := by
  obtain ⟨_, _, _, _, _, _, _, _, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  rfl

/-- Successful checking retains the signature's independent return-staging
marker. -/
theorem checkFunctionBody_success_returnComptime
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.returnComptime = signature.returnComptime := by
  obtain ⟨_, _, _, _, _, _, _, _, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  rfl

/-- The checked body's reported result type is the declared return bundle
under the final inference substitution. -/
theorem checkFunctionBody_success_inferredBodyType
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.inferredBodyType = checked.substitution.apply
      (Ty.productMany signature.returnTypes) := by
  obtain ⟨_, _, _, _, _, _, _, finalizeEq, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact Detail.finalize_type finalizeEq

/-- Once executable formation has closed the signature's return row, final
inference substitution cannot change its declared return bundle. -/
theorem checkFunctionBody_success_inferredBodyType_eq_declared
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (formation : SignatureTypesFormationValidated signatures signature.id
      signature.scheme.parameters signature.returnTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.inferredBodyType = Ty.productMany signature.returnTypes := by
  rw [checkFunctionBody_success_inferredBodyType success,
    formation.apply_productMany_eq_self checked.substitution]

/-- Successful body inference and finalization retain the source declaration
that owns the checked function. -/
theorem checkFunctionBody_success_typedBody_owner
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.owner = signature.id := by
  obtain ⟨declaration, body, finalState, result, declarationEq, bodyEq,
    unifyEq, finalizeEq, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  have bodyHeader := Detail.inferStatementsFuel_state_header bodyEq
  have finalHeader := Detail.unify_state_header unifyEq
  have finalOwner : finalState.owner = declaration.id := by
    have headerOwner := congrArg (fun header : State.Header => header.owner)
      (finalHeader.trans bodyHeader)
    simpa [State.header] using headerOwner
  exact (Detail.finalize_typedSource_owner finalizeEq).trans
    (finalOwner.trans
      (ProgramEnvironment.declaration?_sound declarationEq).2)

/-- Successful body inference retains the exact initial function-parameter
binders and applies only the final flexible inference substitution to them. -/
theorem checkFunctionBody_success_typedBody_inputs
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs =
      (State.initial signature.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs.map
          (TypedBinder.applySubstitution checked.substitution) := by
  obtain ⟨declaration, body, finalState, result, declarationEq, bodyEq,
    unifyEq, finalizeEq, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  have bodyHeader := Detail.inferStatementsFuel_state_header bodyEq
  have finalHeader := Detail.unify_state_header unifyEq
  have finalInputs : finalState.inputs =
      (State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
    exact congrArg (fun header : State.Header => header.inputs)
      (finalHeader.trans bodyHeader)
  rw [Detail.finalize_typedSource_inputs finalizeEq, finalInputs,
    (ProgramEnvironment.declaration?_sound declarationEq).2]

/-- If the final inference substitution fixes every declared parameter type,
it leaves the complete initial monomorphic input-binder row unchanged. -/
theorem checkFunctionBody_success_typedBody_inputs_eq_initial_of_types_fixed
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (typesFixed : signature.parameterTypes.map checked.substitution.apply =
      signature.parameterTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs =
      (State.initial signature.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
  rw [checkFunctionBody_success_typedBody_inputs success]
  rw [State.initial_inputs_definition]
  simp only [ProgramFunctionSignature.parameterNames,
    ProgramFunctionSignature.parameterTypes,
    ProgramFunctionSignature.parameterComptime,
    functionParameterEnvironment_eq, map_mapIdx]
  apply functionParameterBinders_applySubstitution_eq_self
  · simpa [ProgramFunctionSignature.parameterTypes] using typesFixed
  · intro index parameter
    rfl
  · intro index parameter
    rfl

/-- Once executable signature formation has closed all declared parameter
types, the final inference substitution leaves the complete initial input
binder row unchanged. -/
theorem checkFunctionBody_success_typedBody_inputs_eq_initial
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (formation : SignatureTypesFormationValidated signatures signature.id
      signature.scheme.parameters signature.parameterTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs =
      (State.initial signature.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
  exact checkFunctionBody_success_typedBody_inputs_eq_initial_of_types_fixed
    (formation.apply_eq_self checked.substitution) success

/-- Successful checking preserves the exact source-order input names from the
function signature in the finalized typed body. -/
theorem checkFunctionBody_success_typedBody_inputNames
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs.map (fun binder => binder.name) =
      signature.parameterNames := by
  obtain ⟨declaration, body, finalState, result, _, bodyEq, unifyEq,
    finalizeEq, checkedEq⟩ := checkFunctionBody_success_witness success
  subst checked
  have bodyHeader := Detail.inferStatementsFuel_state_header bodyEq
  have finalHeader := Detail.unify_state_header unifyEq
  have finalInputs : finalState.inputs =
      (State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
    exact congrArg (fun header : State.Header => header.inputs)
      (finalHeader.trans bodyHeader)
  rw [Detail.finalize_typedSource_inputNames finalizeEq, finalInputs,
    State.initial_input_names]
  simpa [ProgramFunctionSignature.parameterNames,
    ProgramFunctionSignature.parameterTypes] using
      functionParameterEnvironment_names signature.parameters

/-- Successful checking preserves the exact source-order staging markers from
the function signature in the finalized typed body. -/
theorem checkFunctionBody_success_typedBody_inputComptime
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs.map (fun binder => binder.comptime) =
      signature.parameterComptime := by
  obtain ⟨declaration, body, finalState, result, _, bodyEq, unifyEq,
    finalizeEq, checkedEq⟩ := checkFunctionBody_success_witness success
  subst checked
  have bodyHeader := Detail.inferStatementsFuel_state_header bodyEq
  have finalHeader := Detail.unify_state_header unifyEq
  have finalInputs : finalState.inputs =
      (State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
    exact congrArg (fun header : State.Header => header.inputs)
      (finalHeader.trans bodyHeader)
  rw [Detail.finalize_typedSource_inputComptime finalizeEq, finalInputs]
  apply State.initial_input_comptime_eq
  simp

end Solcore.Frontend.SourceInference
