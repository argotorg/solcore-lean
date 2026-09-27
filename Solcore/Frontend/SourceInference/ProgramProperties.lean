import Solcore.Frontend.ProgramEnvironmentProperties
import Solcore.Frontend.ProgramSignatureFormationProperties
import Solcore.Frontend.ProgramSignaturesProperties
import Solcore.Frontend.SourceInference.ExpressionProperties
import Solcore.Frontend.SourceInference.Program
import Solcore.Frontend.SourceInference.TypedIRProperties

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

/-- Successful pattern-target validation exposes exactly the two carriers
implemented by source pattern matching. -/
theorem validateIntegerPatternTarget_success_supported
    {state : State} {origin : IntegerPatternOrigin}
    (success : validateIntegerPatternTarget origin state = .ok ()) :
    state.resolve (.variable origin.metavariable) = .word ∨
      state.resolve (.variable origin.metavariable) = .integer := by
  simp only [validateIntegerPatternTarget] at success
  by_cases supported : supportedIntegerTarget
      (state.resolve (.variable origin.metavariable)) = true
  · exact (supportedIntegerTarget_eq_true_iff _).mp supported
  · simp [supported] at success

/-- Successful validation of the complete pattern-origin row supports every
retained integer-pattern target. -/
theorem validateIntegerPatternTargets_success_supported
    {state : State} {origins : List IntegerPatternOrigin}
    (success : validateIntegerPatternTargets state origins = .ok ()) :
    ∀ origin, origin ∈ origins →
      state.resolve (.variable origin.metavariable) = .word ∨
        state.resolve (.variable origin.metavariable) = .integer := by
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

/-- Successful literal-target validation exposes exactly the two carriers
implemented by source literal materialization. -/
theorem validateIntegerLiteralTarget_success_supported
    {state : State} {origin : IntegerLiteralOrigin}
    (success : validateIntegerLiteralTarget origin state = .ok ()) :
    state.resolve (.variable origin.metavariable) = .word ∨
      state.resolve (.variable origin.metavariable) = .integer := by
  simp only [validateIntegerLiteralTarget] at success
  by_cases supported : supportedIntegerTarget
      (state.resolve (.variable origin.metavariable)) = true
  · exact (supportedIntegerTarget_eq_true_iff _).mp supported
  · simp [supported] at success

/-- Successful validation of the complete origin row supports every retained
integer-literal target. -/
theorem validateIntegerLiteralTargets_success_supported
    {state : State} {origins : List IntegerLiteralOrigin}
    (success : validateIntegerLiteralTargets state origins = .ok ()) :
    ∀ origin, origin ∈ origins →
      state.resolve (.variable origin.metavariable) = .word ∨
        state.resolve (.variable origin.metavariable) = .integer := by
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
    Frontend.numericLiteralValue? source = some resolution.rawValue ∧
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
      Frontend.numericLiteralValue? source = some resolution.rawValue ∧
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
  · exact unify_localSchemeAssumptions result
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
  · exact unify_integerLiterals result
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
  · exact unify_integerPatterns result
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
  · exact unify_requirements_eq result
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
  · exact unify_preserves_resolve_eq equal success
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
  · exact unify_toTypedSource result
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

/-- The complete successful execution trace of `finalize`.

Keeping the intermediate states and their exact equations together gives
downstream soundness proofs one stable inversion point instead of requiring
each proof to unfold the whole executable pipeline. -/
structure FinalizeSuccessWitness
    (context : Context) (type : Ty) (state : State)
    (roots : List NodeId) (result : Result) where
  patternState : State
  finalState : State
  solvedRequirements : List SolvedRequirement
  graphValidation :
    validateSourceGraph (state.toTypedSource roots) = .ok ()
  ledgerValidation : validateIntegerLiteralLedger state = .ok ()
  patternDefault :
    defaultIntegerPatternTargets state.integerPatterns state =
      .ok patternState
  literalDefault :
    defaultIntegerLiteralTargets patternState.integerLiterals patternState =
      .ok finalState
  patternValidation :
    validateIntegerPatternTargets finalState finalState.integerPatterns =
      .ok ()
  literalValidation :
    validateIntegerLiteralTargets finalState finalState.integerLiterals =
      .ok ()
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

/-- Invert one successful `finalize` call into all successful pipeline stages
and the exact result assembled from the final state. -/
def finalize_success_witness
    {context : Context} {type : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (success : finalize context type state roots = .ok result) :
    FinalizeSuccessWitness context type state roots result := by
  unfold finalize at success
  have graphValidation :
      validateSourceGraph (state.toTypedSource roots) = .ok () := by
    cases graphResult : validateSourceGraph (state.toTypedSource roots) with
    | error error =>
        simp [graphResult, bind, Except.bind] at success
    | ok graphValue =>
        cases graphValue
        simp at graphResult ⊢
  have localIdentityValidation :
      validateSourceLocalIdentities (state.toTypedSource roots) = .ok () := by
    cases localResult :
        validateSourceLocalIdentities (state.toTypedSource roots) with
    | error error =>
        simp [graphValidation, localResult, bind, Except.bind] at success
    | ok localValue =>
        cases localValue
        simp at localResult ⊢
  cases ledgerResult : validateIntegerLiteralLedger state with
  | error error =>
      simp [graphValidation, localIdentityValidation, ledgerResult, bind,
        Except.bind] at success
  | ok ledgerValue =>
      cases ledgerValue
      cases patternResult :
          defaultIntegerPatternTargets state.integerPatterns state with
      | error error =>
          simp [graphValidation, localIdentityValidation, ledgerResult,
            patternResult, bind, Except.bind] at success
      | ok patternState =>
          cases literalResult :
              defaultIntegerLiteralTargets patternState.integerLiterals
                patternState with
          | error error =>
              simp [graphValidation, localIdentityValidation, ledgerResult,
                patternResult, literalResult, bind, Except.bind] at success
          | ok finalState =>
              cases patternValidationResult :
                  validateIntegerPatternTargets finalState
                    finalState.integerPatterns with
              | error error =>
                  simp [graphValidation, localIdentityValidation, ledgerResult,
                    patternResult, literalResult, patternValidationResult,
                    bind, Except.bind] at success
              | ok patternValidation =>
                  cases patternValidation
                  cases literalValidationResult :
                      validateIntegerLiteralTargets finalState
                        finalState.integerLiterals with
                  | error error =>
                      simp [graphValidation, localIdentityValidation,
                        ledgerResult, patternResult, literalResult,
                        patternValidationResult, literalValidationResult, bind,
                        Except.bind] at success
                  | ok literalValidation =>
                      cases literalValidation
                      cases requirementsResult :
                          solveRequirements context finalState
                            finalState.requirements with
                      | error error =>
                          simp [graphValidation, localIdentityValidation,
                            ledgerResult, patternResult, literalResult,
                            patternValidationResult, literalValidationResult,
                            requirementsResult, bind, Except.bind] at success
                      | ok requirements =>
                          simp [graphValidation, localIdentityValidation,
                            ledgerResult, patternResult, literalResult,
                            patternValidationResult, literalValidationResult,
                            requirementsResult, bind, Except.bind] at success
                          cases success
                          exact {
                            patternState
                            finalState
                            solvedRequirements := requirements
                            graphValidation
                            ledgerValidation := ledgerResult
                            patternDefault := patternResult
                            literalDefault := literalResult
                            patternValidation := patternValidationResult
                            literalValidation := literalValidationResult
                            requirementsSolved := requirementsResult
                            result_eq := rfl
                          }

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
  unfold finalize at success
  cases graphResult : validateSourceGraph (state.toTypedSource roots) with
  | error error => simp [graphResult, bind, Except.bind] at success
  | ok graphValue =>
      cases graphValue
      cases localResult :
          validateSourceLocalIdentities (state.toTypedSource roots) with
      | error error =>
          simp [graphResult, localResult, bind, Except.bind] at success
      | ok localValue =>
          cases localValue
          rfl

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
      result.substitution.apply (.variable origin.metavariable) = .word ∨
        result.substitution.apply (.variable origin.metavariable) = .integer := by
  obtain ⟨patternState, finalState, _, _, _, patternResult, literalResult,
      patternValidation, _, _, resultEq⟩ := finalize_success_witness success
  have patternOrigins :=
    defaultIntegerPatternTargets_integerPatterns patternResult
  have finalOrigins :=
    defaultIntegerLiteralTargets_integerPatterns literalResult
  have supported :=
    validateIntegerPatternTargets_success_supported patternValidation
  subst result
  intro origin member
  have finalMember : origin ∈ finalState.integerPatterns := by
    rw [finalOrigins, patternOrigins]
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
      result.substitution.apply (.variable origin.metavariable) = .word ∨
        result.substitution.apply (.variable origin.metavariable) = .integer := by
  obtain ⟨patternState, finalState, _, _, _, patternResult, literalResult, _,
      literalValidation, _, resultEq⟩ := finalize_success_witness success
  have patternOrigins :=
    defaultIntegerPatternTargets_integerLiterals patternResult
  have finalOrigins :=
    defaultIntegerLiteralTargets_integerLiterals literalResult
  have supported :=
    validateIntegerLiteralTargets_success_supported literalValidation
  subst result
  intro origin member
  have finalMember : origin ∈ finalState.integerLiterals := by
    rw [finalOrigins, patternOrigins]
    exact member
  simpa [State.resolve, TypeSystem.InferState.resolve] using
    supported origin finalMember

/-- Finalization may extend the inference substitution while defaulting
numeric targets, but it cannot invalidate a type equality already established
by the input state. -/
theorem finalize_preserves_resolve_eq
    {context : Context} {type left right : Ty} {state : State}
    {roots : List NodeId} {result : Result}
    (equal : state.resolve left = state.resolve right)
    (success : finalize context type state roots = .ok result) :
    result.substitution.apply left = result.substitution.apply right := by
  obtain ⟨patternState, finalState, _, _, _, patternResult, literalResult,
      _, _, _, resultEq⟩ := finalize_success_witness success
  have patternEqual :=
    defaultIntegerPatternTargets_preserves_resolve_eq equal patternResult
  have finalEqual :=
    defaultIntegerLiteralTargets_preserves_resolve_eq patternEqual literalResult
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, resultEq⟩ :=
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
  obtain ⟨patternState, _, _, _, _, patternResult, literalResult, _, _, _,
      resultEq⟩ := finalize_success_witness success
  subst result
  rw [defaultIntegerLiteralTargets_toTypedSource literalResult,
    defaultIntegerPatternTargets_toTypedSource patternResult]

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
