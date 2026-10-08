import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticPreparation

/-! Accepted preparation retains the first projected-target place entry for
each actual concrete assignment occurrence. Duplicate sites use the entry
already selected by the original producer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticCoverage
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites

abbrev targets := CompatiblePlaceMissingPreparationCoverage.targets
abbrev concrete := CompatiblePlaceMissingPreparationCoverage.concrete

private def selects (owner : Key) (node : StatementNode) (assignment : AssignmentResolution)
    (entry : SourceCoreDataPlaceFaultSites.Site) : Bool :=
  decide (entry.owner = owner ∧ entry.location = .occurrence node.id.occurrence ∧
    entry.binder = assignment.target.root ∧ entry.missingType = none)

private structure Growth (places later : List SourceCoreDataPlaceFaultSites.Site)
    (missing more : List MissingSite) : Prop where
  places : ∃ suffix, later = places ++ suffix
  missing : ∃ suffix, more = missing ++ suffix

private theorem Growth.refl (places : List SourceCoreDataPlaceFaultSites.Site)
    (missing : List MissingSite) : Growth places places missing missing :=
  ⟨⟨[], (List.append_nil _).symm⟩, ⟨[], (List.append_nil _).symm⟩⟩

private theorem Growth.trans {first middle last : List SourceCoreDataPlaceFaultSites.Site}
    {before current after : List MissingSite}
    (one : Growth first middle before current) (two : Growth middle last current after) :
    Growth first last before after := by
  obtain ⟨left, rfl⟩ := one.places
  obtain ⟨right, rfl⟩ := two.places
  obtain ⟨leftMissing, rfl⟩ := one.missing
  obtain ⟨rightMissing, rfl⟩ := two.missing
  exact ⟨⟨left ++ right, List.append_assoc _ _ _⟩,
    ⟨leftMissing ++ rightMissing, List.append_assoc _ _ _⟩⟩

/-- The actual first matching uninitialized-target entry. Its diagnostic
span is the one retained by preparation, including genuine earlier reuse. -/
structure Receipt (owner : Key) (node : StatementNode) (assignment : AssignmentResolution)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite) : Prop where
  retained : ∃ entry, places.find? (selects owner node assignment) = some entry

private theorem Receipt.grows {owner : Key} {node : StatementNode} {assignment : AssignmentResolution}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : Receipt owner node assignment places missing)
    (growth : Growth places later missing more) : Receipt owner node assignment later more := by
  obtain ⟨entry, found⟩ := receipt.retained
  obtain ⟨suffix, rfl⟩ := growth.places
  exact ⟨⟨entry, by rw [List.find?_append, found]; rfl⟩⟩

private theorem receipt_of_any {owner : Key} {node : StatementNode} {assignment : AssignmentResolution}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    (present : places.any (selects owner node assignment) = true) :
    Receipt owner node assignment places missing := by
  cases found : places.find? (selects owner node assignment) with
  | some entry => exact ⟨⟨entry, found⟩⟩
  | none =>
    obtain ⟨entry, member, selected⟩ := List.any_eq_true.mp present
    have absent := List.find?_eq_none.mp found entry member
    exact False.elim (absent selected)

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_receipts {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)}
    (accepted : forIn items initial step = .ok final)
    (grows : β → β → Prop) (reflexive : ∀ state, grows state state)
    (transitive : ∀ first middle last, grows first middle → grows middle last → grows first last)
    (receipt : α → β → Prop)
    (transport : ∀ item before after, receipt item before → grows before after → receipt item after)
    (next : ∀ seen item remaining state outcome,
      items = seen ++ item :: remaining → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ grows state updated ∧ receipt item updated) :
    grows initial final ∧ ∀ item, item ∈ items → receipt item final := by
  apply CompatibleMemberCertificates.forIn_preserves accepted
    (fun seen state => grows initial state ∧ ∀ item, item ∈ seen → receipt item state)
  · exact ⟨reflexive _, fun _ member => False.elim (List.not_mem_nil member)⟩
  · intro seen item remaining state outcome split previous ran
    obtain ⟨updated, actual, growth, current⟩ := next seen item remaining state outcome split ran
    refine ⟨updated, actual, transitive _ _ _ previous.1 growth, ?_⟩
    intro prior member
    rcases List.mem_append.mp member with old | new
    · exact transport prior state updated (previous.2 prior old) growth
    · exact List.mem_singleton.mp new ▸ current

private theorem route_receipts {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {steps : List SourceCoreCompatibleDataPlaces.Step}
    {issue : Nat → Except SourceCoreCompatibleDataPlaceFaultSites.Error Word}
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
    Growth places result.2.1 missing result.2.2 := by
  apply CompatibleMemberCertificates.forIn_preserves ran (fun _ current =>
    Growth places current.2.1 missing current.2.2) (Growth.refl _ _)
  intro seen step remaining current outcome _split previous ran
  obtain ⟨next, places, missing⟩ := current
  dsimp only at ran
  cases step with
  | member => exact ⟨_, (Except.ok.inj ran).symm, previous⟩
  | index layout key valueType =>
    dsimp only at ran
    split at ran
    · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
        exact ⟨_, (Except.ok.inj ran).symm,
          previous.trans ⟨⟨[], (List.append_nil _).symm⟩, ⟨[_], rfl⟩⟩⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
    · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
      obtain ⟨_endpoint, _checked, ran⟩ := bind_ok ran
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
        exact ⟨_, (Except.ok.inj ran).symm,
          previous.trans ⟨⟨[_], rfl⟩, ⟨[_], rfl⟩⟩⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran

private def AssignmentReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (owner : Key) (source : TypedSource) (node : StatementNode) (assignment : AssignmentResolution)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite) : Prop :=
  ∀ route, concrete source assignment = true →
    SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route →
    route.steps ≠ [] → Receipt owner node assignment places missing

private def NodeReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (owner : Key) (source : TypedSource) (retained : Node)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite) : Prop :=
  match retained with
  | .statement node => ∀ assignment, assignment ∈ targets node →
      AssignmentReceipt context owner source node assignment places missing
  | .expression _ => True

private def SourceReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (item : Key × TypedSource) (places : List SourceCoreDataPlaceFaultSites.Site)
    (missing : List MissingSite) : Prop :=
  ∀ retained, retained ∈ item.2.nodes → NodeReceipt context item.1 item.2 retained places missing

private theorem AssignmentReceipt.grows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {owner : Key} {source : TypedSource} {node : StatementNode} {assignment : AssignmentResolution}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : AssignmentReceipt context owner source node assignment places missing)
    (growth : Growth places later missing more) :
    AssignmentReceipt context owner source node assignment later more := by
  intro route concrete described nonempty
  exact (receipt route concrete described nonempty).grows growth

private theorem NodeReceipt.grows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {owner : Key} {source : TypedSource} {retained : Node}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : NodeReceipt context owner source retained places missing)
    (growth : Growth places later missing more) :
    NodeReceipt context owner source retained later more := by
  cases retained with
  | expression => trivial
  | statement => exact fun assignment member => (receipt assignment member).grows growth

private theorem SourceReceipt.grows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {item : Key × TypedSource}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : SourceReceipt context item places missing)
    (growth : Growth places later missing more) : SourceReceipt context item later more :=
  fun retained member => (receipt retained member).grows growth

private theorem expression_growth {next : Nat} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {mapping key : ExpressionId}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {seen : List ExpressionId}
    {reason : Word}
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
    ∃ updated, outcome = .yield updated ∧ Growth places updated.2.2.1 missing updated.2.2.2.1 := by
  split at ran
  · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    split at ran
    · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · exact ⟨_, (Except.ok.inj ran).symm, ⟨⟨[], (List.append_nil _).symm⟩, ⟨[_], rfl⟩⟩⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
    · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
      cases ran
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

/-- Every actual concrete projected target has the real first None-place
entry retained by the accepted producer. -/
theorem prepare_coverage {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {owner : Key} {source : TypedSource}
    (collected : (owner, source) ∈ plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources)
    {node : StatementNode} (statement : .statement node ∈ source.nodes)
    {assignment : AssignmentResolution} (target : assignment ∈ targets node)
    (gate : concrete source assignment = true)
    {route : SourceCoreCompatibleDataPlaces.Route}
    (described : SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route)
    (nonempty : route.steps ≠ []) :
    ∃ entry, entry ∈ program.program.places ∧ entry.missingType = none ∧
      program.program.places.find? (fun previous => decide
        (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
          previous.binder = assignment.target.root ∧ previous.missingType = none)) = some entry ∧
      program.program.placeReason owner (.occurrence node.id.occurrence) assignment.target.root none = entry.reason := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, _baseAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨state, loop, accepted⟩ := bind_ok accepted
  have generated :
      ∀ item, item ∈ plan.specializations.map (fun specialized =>
        (specialized.key, specialized.function.typedBody)) ++ sources →
      SourceReceipt context item state.2.2.1 state.2.2.2.1 := by
    apply (forIn_receipts loop
      (fun before after => Growth before.2.2.1 after.2.2.1 before.2.2.2.1 after.2.2.2.1)
      (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
      (fun item state => SourceReceipt context item state.2.2.1 state.2.2.2.1)
      (fun _ _ _ receipt growth => receipt.grows growth) ?_).2
    intro seen item remaining current outcome _split ran
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
      have nodes : Growth places current.2.2.1 missing current.2.2.2.1 ∧
          ∀ retained, retained ∈ source.nodes →
            NodeReceipt context owner source retained current.2.2.1 current.2.2.2.1 := by
        apply forIn_receipts nodesLoop
          (fun before after => Growth before.2.2.1 after.2.2.1 before.2.2.2.1 after.2.2.2.1)
          (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
          (fun retained state => NodeReceipt context owner source retained state.2.2.1 state.2.2.2.1)
        · exact fun _ _ _ receipt growth => receipt.grows growth
        · intro seen retained remaining current outcome _split ran
          obtain ⟨next, indices, places, missing, fixed, seenIndices⟩ := current
          dsimp only at ran
          cases retained with
          | expression node =>
            cases form : node.form <;> simp only [form] at ran
            all_goals first
              | exact ⟨_, (Except.ok.inj ran).symm, Growth.refl _ _, True.intro⟩
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
                      · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                        obtain ⟨updated, actual, growth⟩ := expression_growth ran
                        exact ⟨updated, actual, growth, True.intro⟩
                      · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
                        obtain ⟨endpoint, _checked, ran⟩ := bind_ok ran
                        try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                        obtain ⟨updated, actual, growth⟩ := expression_growth ran
                        exact ⟨updated, actual, growth, True.intro⟩
          | statement node =>
            obtain ⟨current, targetsLoop, finished⟩ := bind_ok ran
            have assignments : Growth places current.2.1 missing current.2.2.1 ∧
                ∀ assignment, assignment ∈ targets node →
                  AssignmentReceipt context owner source node assignment current.2.1 current.2.2.1 := by
              apply forIn_receipts targetsLoop
                (fun before after => Growth before.2.1 after.2.1 before.2.2.1 after.2.2.1)
                (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
                (fun assignment state => AssignmentReceipt context owner source node assignment state.2.1 state.2.2.1)
              · exact fun _ _ _ receipt growth => receipt.grows growth
              · intro seen assignment remaining current outcome _split ran
                obtain ⟨next, places, missing, fixed⟩ := current
                dsimp only at ran
                split at ran
                · rename_i visited
                  obtain ⟨route, actualDescription, ran⟩ := bind_ok ran
                  split at ran
                  · rename_i skippedPlace
                    obtain ⟨updated, stepsLoop, finished⟩ := bind_ok ran
                    have growth := route_receipts (owner := owner) (source := source)
                      (node := node) (assignment := assignment) (steps := route.steps) stepsLoop
                    refine ⟨_, (Except.ok.inj finished).symm, growth, ?_⟩
                    intro requested _concrete described nonempty
                    rw [described] at actualDescription
                    have same := Except.ok.inj actualDescription
                    subst route
                    have present : places.any (selects owner node assignment) = true := by
                      have notEmpty : requested.steps.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
                      change places.any (fun previous => decide
                        (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
                          previous.binder = assignment.target.root ∧ previous.missingType = none)) = true
                      simpa only [notEmpty, Bool.false_or] using skippedPlace
                    exact (receipt_of_any present).grows growth
                  · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
                    try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                    obtain ⟨updated, stepsLoop, finished⟩ := bind_ok ran
                    have growth := route_receipts (owner := owner) (source := source)
                      (node := node) (assignment := assignment) (steps := route.steps) stepsLoop
                    refine ⟨_, (Except.ok.inj finished).symm,
                      (Growth.mk ⟨[_], rfl⟩ ⟨[], (List.append_nil _).symm⟩).trans growth, ?_⟩
                    intro requested _concrete described _nonempty
                    rw [described] at actualDescription
                    have same := Except.ok.inj actualDescription
                    subst route
                    have created : Receipt owner node assignment (places ++ [⟨owner,
                      .occurrence node.id.occurrence, assignment.target.root, none, reason,
                      ⟨.invalidPlaceProjection, .occurrence node.id.occurrence, some node.span⟩⟩]) missing := by
                      apply receipt_of_any
                      simp [List.any_append, selects]
                    exact created.grows growth
                · rename_i skipped
                  refine ⟨_, (Except.ok.inj ran).symm, Growth.refl _ _, ?_⟩
                  intro route required
                  change concrete source assignment ≠ true at skipped
                  exact False.elim (skipped required)
            exact ⟨_, (Except.ok.inj finished).symm, assignments.1, assignments.2⟩
      exact ⟨_, (Except.ok.inj finished).symm, nodes.1, nodes.2⟩
  obtain ⟨extra, _extraAccepted, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst program
  obtain ⟨next, indices, places, missing, fixed⟩ := state
  have receipt := generated (owner, source) collected (.statement node) statement assignment target
    route gate described nonempty
  obtain ⟨entry, found⟩ := receipt.retained
  have selected := of_decide_eq_true (List.find?_some
    (p := fun previous : SourceCoreDataPlaceFaultSites.Site => decide
      (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
        previous.binder = assignment.target.root ∧ previous.missingType = none)) found)
  exact ⟨entry, List.mem_of_find?_eq_some found, selected.2.2.2, found, by
    unfold SourceCoreDataPlaceFaultSites.Program.placeReason
    change (match places.find? (selects owner node assignment) with
      | some candidate => candidate.reason | none => Word.zero) = entry.reason
    rw [found]⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticCoverage
