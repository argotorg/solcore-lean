import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticAssociation

/-! Static range receipts follow actual allocation and reuse of diagnostic
reasons. The original preparation performs each checked conversion. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingDiagnosticAssociation

private structure Bounds (capacity next : Nat) (bases blocked : List Word) : Prop where
  positive : ∀ base, base ∈ bases → 0 < base.val
  reserved : ∀ base, base ∈ bases → base.val + capacity < wordModulus
  issued : ∀ base, base ∈ bases → base.val + capacity < next
  blockedBelow : ∀ token, token ∈ blocked → token.val < next
  separated : ∀ left, left ∈ bases → ∀ right, right ∈ bases →
    left = right ∨ left.val + capacity < right.val ∨ right.val + capacity < left.val
  outside : ∀ base, base ∈ bases → ∀ token, token ∈ blocked →
    token.val ≤ base.val ∨ base.val + capacity < token.val

private theorem Bounds.mono {capacity next : Nat} {bases blocked : List Word}
    (bounds : Bounds capacity next bases blocked) {later : Nat} (grows : next ≤ later)
    {otherBases otherBlocked : List Word}
    (sameBases : ∀ base, base ∈ otherBases ↔ base ∈ bases)
    (sameBlocked : ∀ token, token ∈ otherBlocked ↔ token ∈ blocked) :
    Bounds capacity later otherBases otherBlocked := by
  refine ⟨fun base member => bounds.positive base ((sameBases base).mp member),
    fun base member => bounds.reserved base ((sameBases base).mp member),
    ?_, ?_, ?_, ?_⟩
  · intro base member
    have issued := bounds.issued base ((sameBases base).mp member)
    omega
  · intro token member
    have issued := bounds.blockedBelow token ((sameBlocked token).mp member)
    omega
  · intro left leftMember right rightMember
    exact bounds.separated left ((sameBases left).mp leftMember) right ((sameBases right).mp rightMember)
  · intro base baseMember token tokenMember
    exact bounds.outside base ((sameBases base).mp baseMember) token ((sameBlocked token).mp tokenMember)

private theorem Bounds.range {capacity next : Nat} {bases blocked : List Word}
    (bounds : Bounds capacity next bases blocked) (positive : 0 < next)
    {reason : Word} (number : reason.val = next) (reserved : next + capacity < wordModulus)
    {otherBases : List Word} (members : ∀ base, base ∈ otherBases ↔ base ∈ bases ∨ base = reason) :
    Bounds capacity (next + capacity + 1) otherBases blocked := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro base member
    rcases (members base).mp member with old | rfl
    · exact bounds.positive base old
    · omega
  · intro base member
    rcases (members base).mp member with old | rfl
    · exact bounds.reserved base old
    · omega
  · intro base member
    rcases (members base).mp member with old | rfl
    · have issued := bounds.issued base old; omega
    · omega
  · intro token member
    have issued := bounds.blockedBelow token member; omega
  · intro left leftMember right rightMember
    rcases (members left).mp leftMember with leftOld | rfl
    · rcases (members right).mp rightMember with rightOld | rfl
      · exact bounds.separated left leftOld right rightOld
      · exact .inr (.inl (by have issued := bounds.issued left leftOld; omega))
    · rcases (members right).mp rightMember with rightOld | rfl
      · exact .inr (.inr (by have issued := bounds.issued right rightOld; omega))
      · exact .inl rfl
  · intro base baseMember token tokenMember
    rcases (members base).mp baseMember with old | rfl
    · exact bounds.outside base old token tokenMember
    · exact .inl (by have issued := bounds.blockedBelow token tokenMember; omega)

private theorem Bounds.fixed {capacity next : Nat} {bases blocked : List Word}
    (bounds : Bounds capacity next bases blocked) {reason : Word} (number : reason.val = next)
    {otherBlocked : List Word} (members : ∀ token, token ∈ otherBlocked ↔ token ∈ blocked ∨ token = reason) :
    Bounds capacity (next + 1) bases otherBlocked := by
  refine ⟨bounds.positive, bounds.reserved, ?_, ?_, bounds.separated, ?_⟩
  · intro base member
    have issued := bounds.issued base member; omega
  · intro token member
    rcases (members token).mp member with old | rfl
    · have issued := bounds.blockedBelow token old; omega
    · omega
  · intro base baseMember token tokenMember
    rcases (members token).mp tokenMember with old | rfl
    · exact bounds.outside base baseMember token old
    · exact .inr (by have issued := bounds.issued base baseMember; omega)

private def bases (indices : List SourceCoreDataFaultSites.IndexSite)
    (places : List SourceCoreDataPlaceFaultSites.Site) : List Word :=
  indices.map (·.reason) ++ places.filterMap (fun place => place.missingType.map (fun _ => place.reason))

private structure Inventory (capacity next : Nat) (indices : List SourceCoreDataFaultSites.IndexSite)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite)
    (blocked : List Word) : Prop where
  positive : 0 < next
  bounds : Bounds capacity next (bases indices places) blocked
  missing : ∀ site, site ∈ missing → site.base ∈ bases indices places

private theorem Inventory.mono {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked)
    {later : Nat} (grows : next ≤ later) : Inventory capacity later indices places missing blocked := by
  exact ⟨by have := inventory.positive; omega,
    inventory.bounds.mono grows (fun _ => Iff.rfl) (fun _ => Iff.rfl), inventory.missing⟩

private theorem Inventory.append_missing {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked) {site : MissingSite}
    (issued : site.base ∈ bases indices places) :
    Inventory capacity next indices places (missing ++ [site]) blocked := by
  refine ⟨inventory.positive, inventory.bounds, ?_⟩
  intro current member
  rcases List.mem_append.mp member with old | fresh
  · exact inventory.missing current old
  · exact List.mem_singleton.mp fresh ▸ issued

private theorem Inventory.index_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked) {index : SourceCoreDataFaultSites.IndexSite}
    (number : index.reason.val = next) (reserved : next + capacity < wordModulus) :
    Inventory capacity (next + capacity + 1) (indices ++ [index]) places missing blocked := by
  have members : ∀ base, base ∈ bases (indices ++ [index]) places ↔ base ∈ bases indices places ∨ base = index.reason := by
    intro base
    simp only [bases, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    grind
  refine ⟨by omega, inventory.bounds.range inventory.positive number reserved members, ?_⟩
  intro site member
  exact (members site.base).mpr (.inl (inventory.missing site member))

private theorem Inventory.place_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked) {place : SourceCoreDataPlaceFaultSites.Site}
    {type : TypeSystem.Ty} (kind : place.missingType = some type)
    (number : place.reason.val = next) (reserved : next + capacity < wordModulus) :
    Inventory capacity (next + capacity + 1) indices (places ++ [place]) missing blocked := by
  have members : ∀ base, base ∈ bases indices (places ++ [place]) ↔ base ∈ bases indices places ∨ base = place.reason := by
    intro base
    simp only [bases, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, kind, Option.map_some,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    grind
  refine ⟨by omega, inventory.bounds.range inventory.positive number reserved members, ?_⟩
  intro site member
  exact (members site.base).mpr (.inl (inventory.missing site member))

private theorem Inventory.place_fixed {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (inventory : Inventory capacity next indices places missing blocked) {place : SourceCoreDataPlaceFaultSites.Site}
    (kind : place.missingType = none) (number : place.reason.val = next) :
    Inventory capacity (next + 1) indices (places ++ [place]) missing (blocked ++ [place.reason]) := by
  have same : bases indices (places ++ [place]) = bases indices places := by
    simp only [bases, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, kind, Option.map_none,
      List.append_nil]
  refine ⟨by omega, ?_, ?_⟩
  · rw [same]
    exact inventory.bounds.fixed number (fun _ => by simp only [List.mem_append, List.mem_singleton])
  · rw [same]
    exact inventory.missing

private theorem Inventory.reused_index {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (_inventory : Inventory capacity next indices places missing blocked) {index : SourceCoreDataFaultSites.IndexSite}
    (member : index ∈ indices) : index.reason ∈ bases indices places := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨index, member, rfl⟩)

private theorem Inventory.reused_place {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite} {blocked : List Word}
    (_inventory : Inventory capacity next indices places missing blocked) {place : SourceCoreDataPlaceFaultSites.Site}
    (member : place ∈ places) {type : TypeSystem.Ty} (kind : place.missingType = some type) :
    place.reason ∈ bases indices places := by
  apply List.mem_append_right
  apply List.mem_filterMap.mpr
  exact ⟨place, member, by simp only [kind, Option.map_some]⟩

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

private theorem checked_word {number : Nat} {endpoint : PUnit}
    (accepted : discard (match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok endpoint) :
    number < wordModulus := by
  cases converted : Word.ofNat? number with
  | none =>
    rw [converted] at accepted
    change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok endpoint at accepted
    cases accepted
  | some reason =>
    unfold Word.ofNat? at converted
    split at converted
    · assumption
    · cases converted

private theorem expression_resume {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {mapping key : ExpressionId}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {seen : List ExpressionId}
    {original : List Word} {reason : Word}
    (inventory : Inventory capacity next indices places missing (original ++ fixed.map Prod.fst))
    (issued : reason ∈ bases indices places)
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
        (original ++ updated.2.2.2.2.1.map Prod.fst) := by
  split at ran
  · rename_i base found
    try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    split at ran
    · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · exact ⟨_, (Except.ok.inj ran).symm, inventory.append_missing issued⟩
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
    (inventory : Inventory capacity next indices places missing (original ++ fixed.map Prod.fst))
    (issued : reason ∈ bases indices places)
    {outcome : ForInStep (Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite)}
    (ran : (do
      let keyNode ← match source.lookupExpression? key with
        | some keyNode => pure keyNode
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      pure (.yield (next, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
          keyNode.type, valueType, node.span, reason⟩]))) = Except.ok outcome) :
    ∃ updated, outcome = .yield updated ∧
      Inventory capacity updated.1 indices updated.2.1 updated.2.2 (original ++ fixed.map Prod.fst) := by
  split at ran
  · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    exact ⟨_, (Except.ok.inj ran).symm, inventory.append_missing issued⟩
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

private theorem route_ranges {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {original : List Word}
    {steps : List SourceCoreCompatibleDataPlaces.Step}
    {issue : Nat → Except SourceCoreCompatibleDataPlaceFaultSites.Error Word}
    (wordEq : ∀ number, issue number = match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted)
    (inventory : Inventory capacity next indices places missing (original ++ fixed.map Prod.fst))
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
    Inventory capacity result.1 indices result.2.1 result.2.2 (original ++ fixed.map Prod.fst) := by
  apply CompatibleMemberCertificates.forIn_preserves ran (fun _ current =>
    Inventory capacity current.1 indices current.2.1 current.2.2 (original ++ fixed.map Prod.fst)) inventory
  intro seen step remaining current outcome _split previous ran
  obtain ⟨next, places, missing⟩ := current
  dsimp only at ran
  cases step with
  | member => exact ⟨_, (Except.ok.inj ran).symm, previous⟩
  | index layout key valueType =>
    dsimp only at ran
    split at ran
    · rename_i prior found
      have member := List.mem_of_find?_eq_some found
      have sameSite := of_decide_eq_true (List.find?_some (p := fun previous : SourceCoreDataPlaceFaultSites.Site =>
        decide (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
          previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) found)
      have kind := sameSite.2.2.2
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      exact place_resume previous (previous.reused_place member kind) ran
    · obtain ⟨reason, generated, ran⟩ := bind_ok ran
      rw [wordEq] at generated
      have number := word_number generated
      obtain ⟨endpoint, checked, ran⟩ := bind_ok ran
      rw [wordEq] at checked
      have within : next + capacity < wordModulus := by
        have bounded := checked_word checked
        omega
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      have issued := previous.place_range (place := ⟨owner, .occurrence node.id.occurrence,
        assignment.target.root, some valueType, reason,
        ⟨.typeMismatch valueType none, .occurrence node.id.occurrence, some node.span⟩⟩) rfl number within
      simp only [Nat.add_assoc] at issued
      apply place_resume issued _ ran
      exact issued.reused_place (List.mem_append_right _ (List.mem_singleton_self _)) rfl

/-- The accepted producer checks all actual reserved ranges, including reused
reasons, and separates them from its original and later fixed diagnostics. -/
theorem prepare_ranges {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program) :
    Ranges context.registry.limits.maxEntries program.missing ∧
    (∀ site, site ∈ program.missing → 0 < site.base.val) ∧
    (∀ site, site ∈ program.missing → ∀ row, row ∈ program.fixed →
      row.1.val ≤ site.base.val ∨ site.base.val + context.registry.limits.maxEntries < row.1.val) ∧
    (∀ site, site ∈ program.missing →
      program.program.rootTable.escapedReason.val ≤ site.base.val ∨
        site.base.val + context.registry.limits.maxEntries < program.program.rootTable.escapedReason.val) := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, _baseAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨state, loop, accepted⟩ := bind_ok accepted
  let original := base.rootTable.reads.map (·.reason) ++ [base.rootTable.escapedReason]
  let capacity := context.registry.limits.maxEntries
  let invariant := fun (_ : List (Key × TypedSource))
    (state : Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic)) =>
    Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 (original ++ state.2.2.2.2.map Prod.fst)
  have generated : invariant (plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources) state := by
    apply CompatibleMemberCertificates.forIn_preserves loop invariant
    · change Inventory capacity _ [] [] [] (original ++ base.rootTable.additional.map Prod.fst)
      refine ⟨by omega, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro token member; cases member
        · intro token member; cases member
        · intro token member; cases member
        · intro token member
          have used : token.val ∈ base.rootTable.reads.map (·.reason.val) ++
              base.rootTable.additional.map (·.1.val) ++ [base.rootTable.escapedReason.val] := by
            simp only [original, List.mem_append, List.mem_map, List.mem_singleton] at member ⊢
            grind
          have bounded := foldl_max_member _ used 0
          omega
        · intro left member; cases member
        · intro token member; cases member
      · intro site member; cases member
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
          Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 (original ++ state.2.2.2.2.1.map Prod.fst)
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
                    · rename_i prior found
                      have member := List.mem_of_find?_eq_some found
                      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                      exact expression_resume previous (previous.reused_index member) ran
                    · obtain ⟨reason, generated, ran⟩ := bind_ok ran
                      have number : reason.val = next := by
                        apply word_number
                        exact generated
                      obtain ⟨endpoint, checked, ran⟩ := bind_ok ran
                      have within : next + capacity < wordModulus := by
                        have bounded := checked_word checked
                        omega
                      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                      have issued := previous.index_range (index := ⟨owner, node.id, reason,
                        ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩) number within
                      simp only [Nat.add_assoc] at issued
                      apply expression_resume issued _ ran
                      exact issued.reused_index (List.mem_append_right _ (List.mem_singleton_self _))
        | statement node =>
          obtain ⟨current, targetsLoop, finished⟩ := bind_ok ran
          refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
          change Inventory capacity current.1 indices current.2.1 current.2.2.1
            (original ++ current.2.2.2.map Prod.fst)
          apply CompatibleMemberCertificates.forIn_preserves targetsLoop (fun _ current =>
            Inventory capacity current.1 indices current.2.1 current.2.2.1
              (original ++ current.2.2.2.map Prod.fst)) previous
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
                ⟨.invalidPlaceProjection, .occurrence node.id.occurrence, some node.span⟩⟩) rfl number
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
  change Inventory capacity next indices places missing (original ++ fixed.map Prod.fst) at generated
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro site member
    exact generated.bounds.reserved site.base (generated.missing site member)
  · intro left leftMember right rightMember
    exact generated.bounds.separated left.base (generated.missing left leftMember) right.base (generated.missing right rightMember)
  · intro site member
    exact generated.bounds.positive site.base (generated.missing site member)
  · intro site member row rowMember
    exact generated.bounds.outside site.base (generated.missing site member) row.1
      (List.mem_append_right _ (List.mem_map.mpr ⟨row, rowMember, rfl⟩))
  · intro site member
    exact generated.bounds.outside site.base (generated.missing site member) base.rootTable.escapedReason
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))

/-- The real preparation and actual table rebuild discharge all decoder range
and priority checks for an authenticated member of their missing inventory. -/
theorem table_diagnostic {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (prepared : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {site : MissingSite} (member : site ∈ program.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType) :
    ∃ diagnostic, table.diagnostic? (site.base.add header) = some diagnostic ∧
      diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨ranges, positive, fixed, escaped⟩ := prepare_ranges prepared
  have limits : registry.limits.maxEntries = context.registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  have actualRanges : Ranges registry.limits.maxEntries program.missing := limits.symm ▸ ranges
  have budget := CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata) budget
  have reserved := actualRanges.reserved site member
  have sameEscape : table.escapedReason = program.program.rootTable.escapedReason := by
    unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at rebuilt
    obtain ⟨extra, _, finished⟩ := bind_ok rebuilt
    cases finished
    rfl
  have headerPositive : 0 < header.val := by
    by_cases zero : header.val = 0
    · exact False.elim (metadata.nonzero (Fin.ext zero))
    · omega
  have number := token_nonWrapping site.base header registry.limits.maxEntries reserved bounded
  apply CompatiblePlaceMissingDiagnosticAssociation.table_diagnostic rebuilt actualRanges member metadata keyView valueView
  · intro row rowMember
    simpa only [limits] using fixed site member row rowMember
  · intro zero
    have same := congrArg Fin.val zero
    have positive := positive site member
    rw [number] at same
    change site.base.val + header.val = 0 at same
    omega
  · intro same
    have same := congrArg Fin.val same
    rw [number, sameEscape] at same
    have separate := escaped site member
    rw [← limits] at separate
    rcases separate with before | after <;> omega

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges
