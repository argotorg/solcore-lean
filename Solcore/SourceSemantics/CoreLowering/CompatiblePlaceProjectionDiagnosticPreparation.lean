import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationCoverage

/-! Actual projected-place reasons retain the first fixed diagnostic issued by
preparation. Checked fresh numbers keep those rows outside zero and the
original escaped-control reason. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticPreparation
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites

/-- The actual first fixed row for a retained projected-place entry. -/
structure FixedReceipt (original : List Word) (fixed : List (Word × Diagnostic))
    (place : SourceCoreDataPlaceFaultSites.Site) : Prop where
  positive : 0 < place.reason.val
  separate : ∀ token, token ∈ original → place.reason ≠ token
  found : fixed.find? (fun row => decide (row.1 = place.reason)) = some (place.reason, place.diagnostic)
  error : place.diagnostic.error = .invalidPlaceProjection

private structure Inventory (capacity next : Nat) (indices : List SourceCoreDataFaultSites.IndexSite)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite)
    (original : List Word) (fixed : List (Word × Diagnostic)) : Prop where
  positive : 0 < next
  below : ∀ token, token ∈ original ++ fixed.map Prod.fst → token.val < next
  retained : ∀ place, place ∈ places → place.missingType = none → FixedReceipt original fixed place

private theorem Inventory.mono {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {later : Nat} (grows : next ≤ later) : Inventory capacity later indices places missing original fixed := by
  refine ⟨by have := inventory.positive; omega, ?_, inventory.retained⟩
  intro token member
  have bounded := inventory.below token member
  omega

private theorem Inventory.append_missing {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed) {site : MissingSite} :
    Inventory capacity next indices places (missing ++ [site]) original fixed :=
  ⟨inventory.positive, inventory.below, inventory.retained⟩

private theorem Inventory.index_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {index : SourceCoreDataFaultSites.IndexSite} :
    Inventory capacity (next + capacity + 1) (indices ++ [index]) places missing original fixed := by
  have later := inventory.mono (later := next + capacity + 1) (by omega)
  exact ⟨later.positive, later.below, later.retained⟩

private theorem Inventory.place_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {place : SourceCoreDataPlaceFaultSites.Site} {type : TypeSystem.Ty}
    (kind : place.missingType = some type) :
    Inventory capacity (next + capacity + 1) indices (places ++ [place]) missing original fixed := by
  have later := inventory.mono (later := next + capacity + 1) (by omega)
  refine ⟨later.positive, later.below, ?_⟩
  intro entry member none
  rcases List.mem_append.mp member with old | fresh
  · exact later.retained entry old none
  · have same := List.mem_singleton.mp fresh
    subst entry
    rw [kind] at none
    cases none

private theorem Inventory.place_fixed {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {place : SourceCoreDataPlaceFaultSites.Site} (number : place.reason.val = next)
    (error : place.diagnostic.error = .invalidPlaceProjection) :
    Inventory capacity (next + 1) indices (places ++ [place]) missing original
      (fixed ++ [(place.reason, place.diagnostic)]) := by
  refine ⟨by have := inventory.positive; omega, ?_, ?_⟩
  · intro token member
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with old | old | rfl
    · have bounded := inventory.below token (List.mem_append_left _ old); omega
    · have bounded := inventory.below token (List.mem_append_right _ old); omega
    · omega
  · intro entry member kind
    rcases List.mem_append.mp member with old | fresh
    · have prior := inventory.retained entry old kind
      exact ⟨prior.positive, prior.separate, by rw [List.find?_append, prior.found]; rfl, prior.error⟩
    · have same := List.mem_singleton.mp fresh
      subst entry
      have absent : fixed.find? (fun row => decide (row.1 = place.reason)) = none := by
        apply List.find?_eq_none.mpr
        intro row member
        intro same
        have bounded := inventory.below row.1
          (List.mem_append_right _ (List.mem_map.mpr ⟨row, member, rfl⟩))
        have equal := congrArg Fin.val (of_decide_eq_true same)
        omega
      refine ⟨by have := inventory.positive; omega, ?_, ?_, error⟩
      · intro token member same
        have bounded := inventory.below token (List.mem_append_left _ member)
        have equal := congrArg Fin.val same
        omega
      · rw [List.find?_append, absent]
        simp

private theorem foldl_max_initial (values : List Nat) (start : Nat) : start ≤ values.foldl max start := by
  induction values generalizing start with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem foldl_max_member (values : List Nat) {value : Nat} (member : value ∈ values) (start : Nat) :
    value ≤ values.foldl max start := by
  induction values generalizing start with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_initial tail _)
    · exact ih member _

private theorem word_number {number : Nat} {reason : Word}
    (accepted : (match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok reason) :
    reason.val = number := by
  split at accepted
  · rename_i converted
    have same := Except.ok.inj accepted
    subst reason
    unfold Word.ofNat? at converted
    split at converted
    · exact congrArg Fin.val (Option.some.inj converted).symm
    · cases converted
  · cases accepted

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem expression_resume {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {mapping key : ExpressionId}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {seen : List ExpressionId}
    {original : List Word} {reason : Word}
    (inventory : Inventory capacity next indices places missing original fixed)
    {outcome : ForInStep (Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic) × List ExpressionId)}
    (ran : (do
      let baseNode ← match source.lookupExpression? mapping with
        | some base => pure base
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression mapping))
      let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
        | .mapping keyType valueType => pure (keyType, valueType)
        | _ => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      unless SourceCoreRawMetadata.runtimeType node.type = valueType do
        throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression node.id))
      pure (.yield (next, indices, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩],
        fixed, node.id :: seen))) = Except.ok outcome) :
    ∃ updated, outcome = .yield updated ∧
      Inventory capacity updated.1 updated.2.1 updated.2.2.1 updated.2.2.2.1
        original updated.2.2.2.2.1 := by
  split at ran
  · rename_i base found
    try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    split at ran
    · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · exact ⟨_, (Except.ok.inj ran).symm, inventory.append_missing⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
    · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
      cases ran
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

private theorem place_resume {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution} {key : ExpressionId} {valueType : TypeSystem.Ty}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)}
    {original : List Word} {reason : Word}
    (inventory : Inventory capacity next indices places missing original fixed)
    {outcome : ForInStep (Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite)}
    (ran : (do
      let keyNode ← match source.lookupExpression? key with
        | some keyNode => pure keyNode
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      pure (.yield (next, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
          keyNode.type, valueType, node.span, reason⟩]))) = Except.ok outcome) :
    ∃ updated, outcome = .yield updated ∧
      Inventory capacity updated.1 indices updated.2.1 updated.2.2 original fixed := by
  split at ran
  · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    exact ⟨_, (Except.ok.inj ran).symm, inventory.append_missing⟩
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

private theorem route_ranges {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {original : List Word}
    {steps : List SourceCoreCompatibleDataPlaces.Step}
    {issue : Nat → Except SourceCoreCompatibleDataPlaceFaultSites.Error Word}
    (_wordEq : ∀ number, issue number = match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted)
    (inventory : Inventory capacity next indices places missing original fixed)
    {result : Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite}
    (ran : forIn steps (next, places, missing) (fun step current => do
      let mut next := current.1
      let mut places := current.2.1
      let mut missing := current.2.2
      match step with
      | .index _ key valueType =>
          let reason ← match places.find? (fun previous => decide
              (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
               previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) with
            | some previous => pure previous.reason
            | none => do
                let reason ← issue next
                discard <| issue (next + (capacity + 1) - 1)
                next := next + (capacity + 1)
                let diagnostic : Diagnostic := ⟨.typeMismatch valueType none,
                  .occurrence node.id.occurrence, some node.span⟩
                places := places ++ [⟨owner, .occurrence node.id.occurrence, assignment.target.root,
                  some valueType, reason, diagnostic⟩]
                pure reason
          let keyNode ← match source.lookupExpression? key with
            | some keyNode => pure keyNode | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
          missing := missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
            keyNode.type, valueType, node.span, reason⟩]
      | _ => pure ()
      pure (.yield (next, places, missing))) = Except.ok result) :
    Inventory capacity result.1 indices result.2.1 result.2.2 original fixed := by
  apply CompatibleMemberCertificates.forIn_preserves ran (fun _ current =>
    Inventory capacity current.1 indices current.2.1 current.2.2 original fixed) inventory
  intro seen step remaining current outcome _split previous ran
  obtain ⟨next, places, missing⟩ := current
  dsimp only at ran
  cases step with
  | member => exact ⟨_, (Except.ok.inj ran).symm, previous⟩
  | index layout key valueType =>
    dsimp only at ran
    split at ran
    · rename_i _prior _found
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      exact place_resume previous ran
    · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
      obtain ⟨_endpoint, _checked, ran⟩ := bind_ok ran
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      have issued := previous.place_range (place := ⟨owner, .occurrence node.id.occurrence,
        assignment.target.root, some valueType, reason,
        ⟨.typeMismatch valueType none, .occurrence node.id.occurrence, some node.span⟩⟩) rfl
      simp only [Nat.add_assoc] at issued
      exact place_resume issued ran

/-- Every actual None-place entry keeps its first fixed diagnostic and lies
outside zero and the original escaped-control reason. -/
theorem prepare_fixed {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program) :
    ∀ place, place ∈ program.program.places → place.missingType = none →
      0 < place.reason.val ∧ place.reason ≠ program.program.rootTable.escapedReason ∧
      program.fixed.find? (fun row => decide (row.1 = place.reason)) = some (place.reason, place.diagnostic) ∧
      place.diagnostic.error = .invalidPlaceProjection := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, _baseAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨state, loop, accepted⟩ := bind_ok accepted
  let original := base.rootTable.reads.map (·.reason) ++ [base.rootTable.escapedReason]
  let capacity := context.registry.limits.maxEntries
  let invariant := fun (_ : List (Key × TypedSource))
    (state : Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic)) =>
    Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 original state.2.2.2.2
  have generated : invariant (plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources) state := by
    apply CompatibleMemberCertificates.forIn_preserves loop invariant
    · change Inventory capacity _ [] [] [] original base.rootTable.additional
      refine ⟨by omega, ?_, ?_⟩
      · intro token member
        have used : token.val ∈ base.rootTable.reads.map (·.reason.val) ++
              base.rootTable.additional.map (·.1.val) ++ [base.rootTable.escapedReason.val] := by
          simp only [original, List.mem_append, List.mem_map, List.mem_singleton] at member ⊢
          grind
        have bounded := foldl_max_member _ used 0
        omega
      · intro place member; cases member
    · intro seen item remaining current outcome _split previous ran
      obtain ⟨next, indices, places, missing, fixed⟩ := current
      obtain ⟨owner, source⟩ := item
      dsimp only at ran
      by_cases ownerMismatch : source.owner ≠ owner.declaration
      · rw [if_pos ownerMismatch] at ran
        change (Except.error (.sourceOwnerMismatch owner.declaration source.owner) :
          Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
      · rw [if_neg ownerMismatch] at ran
        obtain ⟨current, nodesLoop, finished⟩ := bind_ok ran
        refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
        let nodeInvariant := fun (_ : List Node)
          (state : Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
            List MissingSite × List (Word × Diagnostic) × List ExpressionId) =>
          Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 original state.2.2.2.2.1
        change nodeInvariant source.nodes current
        apply CompatibleMemberCertificates.forIn_preserves nodesLoop nodeInvariant previous
        intro seen retained remaining current outcome _split previous ran
        obtain ⟨next, indices, places, missing, fixed, seenIndices⟩ := current
        dsimp only at ran
        cases retained with
        | expression node =>
          cases form : node.form <;> simp only [form] at ran
          all_goals first
            | exact ⟨_, (Except.ok.inj ran).symm, previous⟩
            | skip
          case index mapping key =>
            by_cases nodeOwner : node.id.occurrence.owner ≠ source.owner
            · rw [if_pos nodeOwner] at ran
              change (Except.error (.ownerMismatch node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
              cases ran
            · rw [if_neg nodeOwner] at ran
              by_cases mappingOwner : mapping.occurrence.owner ≠ source.owner
              · rw [if_pos mappingOwner] at ran
                change (Except.error (.ownerMismatch mapping) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                cases ran
              · rw [if_neg mappingOwner] at ran
                by_cases keyOwner : key.occurrence.owner ≠ source.owner
                · rw [if_pos keyOwner] at ran
                  change (Except.error (.ownerMismatch key) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                  cases ran
                · rw [if_neg keyOwner] at ran
                  by_cases duplicate : seenIndices.contains node.id = true
                  · rw [if_pos duplicate] at ran
                    change (Except.error (.duplicateOccurrence node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                    cases ran
                  · rw [if_neg duplicate] at ran
                    split at ran
                    · rename_i _prior _found
                      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                      exact expression_resume previous ran
                    · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
                      obtain ⟨_endpoint, _checked, ran⟩ := bind_ok ran
                      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                      have issued := previous.index_range (index := ⟨owner, node.id, reason,
                        ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩)
                      simp only [Nat.add_assoc] at issued
                      exact expression_resume issued ran
        | statement node =>
          obtain ⟨current, targetsLoop, finished⟩ := bind_ok ran
          refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
          change Inventory capacity current.1 indices current.2.1 current.2.2.1
            original current.2.2.2
          apply CompatibleMemberCertificates.forIn_preserves targetsLoop (fun _ current =>
            Inventory capacity current.1 indices current.2.1 current.2.2.1
              original current.2.2.2) previous
          intro seen assignment remaining current outcome _split previous ran
          obtain ⟨next, places, missing, fixed⟩ := current
          dsimp only at ran
          split at ran
          · obtain ⟨route, _described, ran⟩ := bind_ok ran
            split at ran
            · obtain ⟨current, stepsLoop, finished⟩ := bind_ok ran
              exact ⟨_, (Except.ok.inj finished).symm, route_ranges (owner := owner) (source := source) (node := node) (assignment := assignment) (steps := route.steps) (fun _ => rfl) previous stepsLoop⟩
            · obtain ⟨reason, generated, ran⟩ := bind_ok ran
              have number := word_number generated
              have issued := previous.place_fixed (place := ⟨owner, .occurrence node.id.occurrence,
                assignment.target.root, none, reason,
                ⟨.invalidPlaceProjection, .occurrence node.id.occurrence, some node.span⟩⟩) number rfl
              try dsimp only [pure, Except.pure, bind, Except.bind] at ran
              obtain ⟨current, stepsLoop, finished⟩ := bind_ok ran
              refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
              apply route_ranges (owner := owner) (source := source) (node := node) (assignment := assignment) (steps := route.steps) (fun _ => rfl) _ stepsLoop
              simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc] using issued
          · exact ⟨_, (Except.ok.inj ran).symm, previous⟩
  obtain ⟨extra, _extraAccepted, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst program
  obtain ⟨next, indices, places, missing, fixed⟩ := state
  change Inventory capacity next indices places missing original fixed at generated
  intro place member kind
  have receipt := generated.retained place member kind
  exact ⟨receipt.positive, receipt.separate _
    (List.mem_append_right _ (List.mem_singleton_self _)), receipt.found, receipt.error⟩

/-- The real rebuilt table preserves the first fixed row before later
missing-default rows. Its exact error is the emitted projection rejection. -/
theorem table_diagnostic {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {place : SourceCoreDataPlaceFaultSites.Site} (member : place ∈ program.program.places)
    (kind : place.missingType = none)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table) :
    table.diagnostic? place.reason = some place.diagnostic ∧
      place.diagnostic.error = .invalidPlaceProjection := by
  obtain ⟨positive, separate, found, error⟩ := prepare_fixed accepted place member kind
  unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at rebuilt
  obtain ⟨extra, _generated, finished⟩ := bind_ok rebuilt
  have same := Except.ok.inj finished
  subst table
  have nonzero : place.reason ≠ Word.zero := by
    intro zero
    have equal := congrArg Fin.val zero
    change place.reason.val = 0 at equal
    omega
  refine ⟨?_, error⟩
  simp only [SourceCoreFaultSites.Table.diagnostic?, nonzero, separate, if_false,
    List.find?_append, found]
  rfl

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticPreparation
