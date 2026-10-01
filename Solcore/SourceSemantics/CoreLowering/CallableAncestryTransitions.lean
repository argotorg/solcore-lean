import Solcore.Frontend.SourceCoreCallableAncestryPreparation
import Solcore.SourceSemantics.CoreLowering.CallableAncestryCache

/-! Actual preparation transition factories and independent owned metadata
receipts. These facts concern finite static metadata, not execution history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryTransitions
open Frontend SourceInference TypeSystem CallableAncestryMetadata CallableAncestryCache
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs
abbrev State := CallableAncestryMetadata.State

theorem views_eq {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base) :
    inputs.views = owned.views := Except.ok.inj (inputs.viewsPrepared.symm.trans owned.viewsPrepared)
theorem templates_eq {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base) :
    inputs.templates = owned.templates := Except.ok.inj (inputs.templatesPrepared.symm.trans owned.templatesPrepared)
theorem callable_eq {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base) :
    inputs.callable = owned.callable := Option.some.inj (inputs.callableSelected.symm.trans owned.callableSelected)

theorem named_equation {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    (id : Core.Word) : SourceCoreCallableAncestryPreparation.named? inputs id =
      (named owned id).toOption.map (fun receipt => nativeState receipt.state) := by
  unfold named
  split
  · next selected =>
    simp [SourceCoreCallableAncestryPreparation.named?, callable_eq owned inputs, selected, Except.toOption, throw, throwThe, MonadExceptOf.throw]
  · next entry selected =>
    split
    · next owner origin =>
      split <;> rename_i caller found <;>
        simp [SourceCoreCallableAncestryPreparation.named?, callable_eq owned inputs, selected, origin, found,
          Except.toOption, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, Named.state, nativeState]
    · next excluded =>
      cases shape : entry.origin <;>
        simp_all [SourceCoreCallableAncestryPreparation.named?, callable_eq owned inputs, Except.toOption, throw, throwThe, MonadExceptOf.throw]

theorem named_sound {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {id : Core.Word} {state : SourceCoreCallableAncestryCache.State}
    (accepted : SourceCoreCallableAncestryPreparation.named? inputs id = some state) :
    ∃ receipt : Named owned id, state = nativeState receipt.state := by
  rw [named_equation owned inputs] at accepted
  cases result : named owned id with
  | error error => simp [result, Except.toOption] at accepted
  | ok receipt => simpa only using (show ∃ receipt : Named owned id, state = nativeState receipt.state from
      ⟨receipt, by simpa [result, Except.toOption] using accepted.symm⟩)

theorem named_complete {checked : Checked} {base : Base checked} {owned : Owned base} (inputs : Inputs base)
    {id : Core.Word} (receipt : Named owned id) :
    SourceCoreCallableAncestryPreparation.named? inputs id = some (nativeState receipt.state) := by
  simp [SourceCoreCallableAncestryPreparation.named?, callable_eq owned inputs,
    receipt.selected, receipt.origin, receipt.found, Named.state, nativeState, Except.toOption]

theorem lambda_complete {checked : Checked} {base : Base checked} {owned : Owned base} (inputs : Inputs base)
    {id : Core.Word} {state : State} (receipt : LambdaAt owned id) (metadata : LambdaSource receipt state) :
    SourceCoreCallableAncestryPreparation.lambdaAllowed inputs (nativeState state) id = true := by
  simp only [SourceCoreCallableAncestryPreparation.lambdaAllowed, templates_eq owned inputs,
    callable_eq owned inputs, receipt.selected, receipt.descriptorSelected, receipt.origin,
    nativeState, metadata.owner, metadata.active, and_self, ↓reduceIte, metadata.found]
  rw [if_pos metadata.sameForm, metadata.shape]
  rfl

private theorem lambdaAt_exists {checked : Checked} {base : Base checked} {owned : Owned base}
    {id : Core.Word} {template : Lambda} {entry : SourceCoreStageCodebook.Entry}
    (selected : owned.templates.lambdaAt? id = some template)
    (descriptor : owned.callable.table.entryAt? id = some entry)
    (origin : entry.origin = .lambda template.owner template.id template.active) :
    ∃ receipt : LambdaAt owned id, lambdaAt owned id = .ok receipt ∧ receipt.template = template ∧ receipt.entry = entry := by
  unfold lambdaAt
  split
  · next missing => rw [selected] at missing; cases missing
  · next actual found =>
    have same := Option.some.inj (found.symm.trans selected)
    subst actual
    split
    · next missing => rw [descriptor] at missing; cases missing
    · next actual found =>
      have same := Option.some.inj (found.symm.trans descriptor)
      subst actual
      rw [dif_pos origin]
      exact ⟨_, rfl, rfl, rfl⟩

private theorem lambdaSource_exists {checked : Checked} {base : Base checked} {owned : Owned base}
    {id : Core.Word} {state : State} (receipt : LambdaAt owned id) {node : ExpressionNode}
    (owner : state.owner = receipt.template.owner) (active : state.active = receipt.template.active)
    (found : state.source.lookupExpression? receipt.template.id = some node)
    (sameForm : node.form = receipt.template.node.form)
    {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (shape : node.form = .lambda parameters result body) : Nonempty (LambdaSource receipt state) := by
  have success : ∃ metadata, lambdaSource receipt state = .ok metadata := by
    unfold lambdaSource
    rw [dif_pos owner, dif_pos active]
    split
    · next missing => rw [found] at missing; cases missing
    · next actual selected =>
      have same := Option.some.inj (selected.symm.trans found)
      subst actual
      rw [dif_pos sameForm]
      split
      · exact ⟨_, rfl⟩
      · next impossible => exact (impossible _ _ _ shape).elim
  obtain ⟨metadata, _⟩ := success
  exact ⟨metadata⟩

theorem lambda_sound {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {id : Core.Word} {state : State}
    (accepted : SourceCoreCallableAncestryPreparation.lambdaAllowed inputs (nativeState state) id = true) :
    ∃ receipt : LambdaAt owned id, Nonempty (LambdaSource receipt state) := by
  unfold SourceCoreCallableAncestryPreparation.lambdaAllowed at accepted
  rw [templates_eq owned inputs, callable_eq owned inputs] at accepted
  simp only [nativeState, Id.run, pure] at accepted
  split at accepted <;> try cases accepted
  next template selected =>
    split at accepted <;> try cases accepted
    next entry descriptor =>
      split at accepted <;> try cases accepted
      next origin =>
        split at accepted <;> try cases accepted
        next context =>
          split at accepted <;> try cases accepted
          next node found =>
            split at accepted <;> try cases accepted
            next sameForm =>
              split at accepted <;> try cases accepted
              next parameters result body shape =>
                obtain ⟨receipt, _, same, _⟩ := lambdaAt_exists selected descriptor origin
                refine ⟨receipt, ?_⟩
                apply lambdaSource_exists receipt (node := node)
                · simpa only [same] using context.1
                · simpa only [same] using context.2
                · simpa only [same] using found
                · simpa only [same] using sameForm
                · exact shape

theorem view_complete {checked : Checked} {base : Base checked} {owned : Owned base} (inputs : Inputs base)
    {id target : Core.Word} {state : State} (receipt : ViewAt owned id target) (step : ViewStep receipt state) :
    SourceCoreCallableAncestryPreparation.view? inputs (nativeState state) id target = some (nativeState step.after) := by
  simp only [SourceCoreCallableAncestryPreparation.view?, views_eq owned inputs, templates_eq owned inputs,
    callable_eq owned inputs, receipt.selected, receipt.targetLambda.selected,
    receipt.targetLambda.descriptorSelected, bind, Option.bind, receipt.targetLambda.origin, ne_eq,
    not_true_eq_false, ↓reduceIte]
  have target := receipt.targetOrigin
  rw [receipt.targetLambda.origin] at target
  simp only [target, receipt.generalized, not_true_eq_false, ↓reduceIte,
    nativeState, step.owner, step.active, or_self]
  rw [← step.owner, ← step.active]
  simp only [step.callerFound, Except.toOption, step.found, step.reference, not_true_eq_false, ↓reduceIte,
    ← step.binderExact, step.declaration, step.requirementLayout]
  have factory := step.factory
  rw [step.reference] at factory
  rw [factory]
  simp only [step.substitutionExact, not_true_eq_false, ↓reduceIte, pure]
  simp only [ViewStep.after, step.substitutionExact]

private theorem viewAt_exists {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan}
    (selected : owned.views.entryAt? id = some entry) (lambda : LambdaAt owned target)
    (generated : lambdaAt owned target = .ok lambda)
    (origin : lambda.entry.origin = .lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative)
    (generalized : entry.view.wrapsPrincipal = true) :
    ∃ receipt : ViewAt owned id target, viewAt owned id target = .ok receipt ∧ receipt.entry = entry := by
  unfold viewAt
  split
  · next missing => rw [selected] at missing; cases missing
  · next actual found =>
    have same := Option.some.inj (found.symm.trans selected)
    subst actual
    simp only [generated, bind, Except.bind]
    rw [dif_pos origin, dif_pos generalized]
    exact ⟨_, rfl, rfl⟩

private theorem prepareStep_exists {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} (receipt : ViewAt owned id target) (state : State)
    (owner : state.owner = receipt.entry.view.owner) (active : state.active = receipt.entry.view.parentActive)
    {caller : SourceSpecialization.SpecializedFunction}
    (callerFound : SourceCompilationPlan.exactSpecialization base.plan state.owner = .ok caller)
    {node : ExpressionNode} (found : state.source.lookupExpression? receipt.entry.view.read = some node)
    {name : String} (reference : node.form = .reference name (.local receipt.entry.view.binding.binder.id))
    (declaration : (⟨receipt.entry.view.binding.binder.applySubstitution state.active,
      receipt.entry.view.principal.initializer⟩ : SourceCoreCallablePrincipals.Declaration) ∈
      SourceCoreCallablePrincipals.declarations state.source)
    {requirements : List RequirementId} (requirementLayout : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements)
    {substitution : Substitution} {witnesses : List Witness}
    (factory : SourceCompilationPlan.localRequirementWitnesses caller receipt.entry.view.principal.evidence
      (receipt.entry.view.binding.binder.applySubstitution state.active)
      {node with type := node.rawType, requirements, coercions := []} = .ok (substitution, witnesses))
    (substitutionExact : substitution = receipt.entry.view.ownSubstitution) :
    ∃ step : ViewStep receipt state, step.after = ⟨state.owner, substitution.compose state.active,
      SourceTypedRuntime.rewriteLocalRequirements witnesses (state.source.applySubstitution substitution)⟩ := by
  have success : ∃ step, prepareStep receipt state = .ok step := by
    unfold prepareStep
    rw [dif_pos owner, dif_pos active]
    split
    · next error failed => rw [callerFound] at failed; cases failed
    · next actual selected =>
      have same := Except.ok.inj (selected.symm.trans callerFound)
      subst actual
      split
      · next missing => rw [found] at missing; cases missing
      · next actual selected =>
        have same := Option.some.inj (selected.symm.trans found)
        subst actual
        split
        · next readName binderId shape =>
          have same := ExpressionForm.reference.inj (shape.symm.trans reference)
          obtain ⟨rfl, same⟩ := same
          cases same
          rw [dif_pos rfl, dif_pos declaration]
          split
          · next missing => rw [requirementLayout] at missing; cases missing
          · next actual selected =>
            have same := Option.some.inj (selected.symm.trans requirementLayout)
            subst actual
            split
            · next error failed => rw [factory] at failed; cases failed
            · next result generated =>
              have same := Except.ok.inj (generated.symm.trans factory)
              cases same
              rw [dif_pos substitutionExact]
              exact ⟨_, rfl⟩
        · next excluded => exact (excluded _ _ reference).elim
  obtain ⟨step, _⟩ := success
  have sameCaller := Except.ok.inj (step.callerFound.symm.trans callerFound)
  have sameNode := Option.some.inj (step.found.symm.trans found)
  have sameRequirements := Option.some.inj ((sameNode ▸ step.requirementLayout).symm.trans requirementLayout)
  have sameFactory := step.factory
  rw [sameCaller, sameNode, step.binderExact, sameRequirements] at sameFactory
  have same := Except.ok.inj (sameFactory.symm.trans factory)
  exact ⟨step, by simp only [ViewStep.after, Prod.mk.injEq] at same ⊢; rw [same.1, same.2]⟩

theorem view_sound {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {id target : Core.Word} {state : State} {result : SourceCoreCallableAncestryCache.State}
    (accepted : SourceCoreCallableAncestryPreparation.view? inputs (nativeState state) id target = some result) :
    ∃ (receipt : ViewAt owned id target) (step : ViewStep receipt state), result = nativeState step.after := by
  unfold SourceCoreCallableAncestryPreparation.view? at accepted
  simp only [views_eq owned inputs, templates_eq owned inputs, callable_eq owned inputs,
    nativeState, bind, Option.bind, ne_eq, ite_not] at accepted
  split at accepted <;> try cases accepted
  next entry selected =>
    try dsimp only at accepted
    split at accepted <;> try cases accepted
    next template templateSelected =>
      try dsimp only at accepted
      split at accepted <;> try cases accepted
      next descriptor descriptorSelected =>
        try dsimp only at accepted
        split at accepted <;> try cases accepted
        next origin =>
          try dsimp only at accepted
          split at accepted <;> try cases accepted
          next targetOrigin =>
            try dsimp only at accepted
            split at accepted <;> try cases accepted
            next generalized =>
              try dsimp only at accepted
              split at accepted <;> try cases accepted
              next context =>
                try dsimp only at accepted
                have context : state.owner = entry.view.owner ∧ state.active = entry.view.parentActive := by
                  exact ⟨Classical.byContradiction (fun h => context (.inl h)),
                    Classical.byContradiction (fun h => context (.inr h))⟩
                cases callerFound : SourceCompilationPlan.exactSpecialization base.plan state.owner with
                | error error => simp [callerFound, Except.toOption] at accepted
                | ok caller =>
                  simp only [callerFound, Except.toOption] at accepted
                  split at accepted <;> try cases accepted
                  next node found =>
                    try dsimp only at accepted
                    split at accepted <;> try cases accepted
                    next name binderId reference =>
                      try dsimp only at accepted
                      split at accepted <;> try cases accepted
                      next sameBinder =>
                        try dsimp only at accepted
                        subst binderId
                        split at accepted <;> try cases accepted
                        next declaration =>
                          try dsimp only at accepted
                          split at accepted <;> try cases accepted
                          next requirements layout =>
                            try dsimp only at accepted
                            cases factory : SourceCompilationPlan.localRequirementWitnesses caller entry.view.principal.evidence
                                (entry.view.binding.binder.applySubstitution state.active)
                                {node with type := node.rawType, requirements, coercions := []} with
                            | error error => simp [factory] at accepted
                            | ok pair =>
                              obtain ⟨substitution, witnesses⟩ := pair
                              simp only [factory] at accepted
                              split at accepted <;> try cases accepted
                              next substitutionExact =>
                                try dsimp only at accepted
                                obtain ⟨lambda, generated, _, lambdaEntry⟩ := lambdaAt_exists templateSelected descriptorSelected origin
                                obtain ⟨receipt, _, sameEntry⟩ := viewAt_exists selected lambda generated
                                  (by simpa only [lambdaEntry] using targetOrigin) generalized
                                have completed := prepareStep_exists receipt state
                                  (node := node) (requirements := requirements)
                                  (substitution := substitution) (witnesses := witnesses)
                                  (by simpa only [sameEntry] using context.1)
                                  (by simpa only [sameEntry] using context.2) callerFound
                                  (by simpa only [sameEntry] using found)
                                  (by simpa only [sameEntry] using reference)
                                  (by rw [sameEntry]; exact declaration)
                                  layout (by rw [sameEntry]; exact factory)
                                  (by simpa only [sameEntry] using substitutionExact)
                                obtain ⟨step, after⟩ := completed
                                exact ⟨receipt, step, by rw [after]; rfl⟩



private theorem namedEdge {table : SourceCoreCallableAncestryCache.Table} {id : Core.Word} {position : Nat}
    (found : table.namedAt? id = some position) :
    ∃ edge ∈ table.named, edge.origin = id ∧ edge.destination = position := by
  unfold SourceCoreCallableAncestryCache.Table.namedAt? at found
  cases selected : table.named.find? (fun edge => decide (edge.origin = id)) with
  | none => simp [selected] at found
  | some edge =>
    have member := List.mem_of_find?_eq_some selected
    have origin : edge.origin = id := by simpa using List.find?_some selected
    exact ⟨edge, member, origin, by simpa [selected] using found⟩

private theorem lambdaEdge {table : SourceCoreCallableAncestryCache.Table} {id : Core.Word} {position : Nat}
    (found : table.lambdaAllowed position id = true) :
    ∃ edge ∈ table.lambdas, edge.state = position ∧ edge.origin = id := by
  simpa only [SourceCoreCallableAncestryCache.Table.lambdaAllowed, List.any_eq_true, decide_eq_true_eq] using found

private theorem viewEdge {table : SourceCoreCallableAncestryCache.Table} {id target : Core.Word} {position destination : Nat}
    (found : table.viewAt? position id target = some destination) :
    ∃ edge ∈ table.views, edge.state = position ∧ edge.view = id ∧ edge.target = target ∧ edge.destination = destination := by
  unfold SourceCoreCallableAncestryCache.Table.viewAt? at found
  cases selected : table.views.find? (fun edge => decide (edge.state = position ∧ edge.view = id ∧ edge.target = target)) with
  | none => rw [selected] at found; cases found
  | some edge =>
    have member := List.mem_of_find?_eq_some selected
    have shape : edge.state = position ∧ edge.view = id ∧ edge.target = target := by simpa using List.find?_some selected
    exact ⟨edge, member, shape.1, shape.2.1, shape.2.2, by simpa only [selected, Option.map_some, Option.some.injEq] using found⟩

/-- Actual finite-row validation implies independent owned transition
soundness. No runtime evaluation or preselected list of frames is assumed. -/
theorem valid_sound {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {table : SourceCoreCallableAncestryCache.Table}
    (validated : SourceCoreCallableAncestryPreparation.valid inputs table = true) : Sound owned table := by
  simp only [SourceCoreCallableAncestryPreparation.valid, Bool.and_eq_true] at validated
  obtain ⟨⟨⟨⟨namedRows, lambdaRows⟩, viewRows⟩, _⟩, _⟩ := validated
  constructor
  · intro id position found
    obtain ⟨edge, member, origin, destination⟩ := namedEdge found
    have row := List.all_eq_true.mp namedRows edge member
    rw [origin, destination] at row
    cases generated : SourceCoreCallableAncestryPreparation.named? inputs id with
    | none => simp [generated] at row
    | some state =>
      have stored : table.stateAt? position = some state := by simpa only [generated, decide_eq_true_eq] using row
      obtain ⟨receipt, same⟩ := named_sound owned inputs generated
      exact ⟨receipt, by simpa only [same] using stored⟩
  · intro position state id stored allowed
    obtain ⟨edge, member, index, origin⟩ := lambdaEdge allowed
    have row := List.all_eq_true.mp lambdaRows edge member
    simp only [index, origin, stored] at row
    exact lambda_sound owned inputs row
  · intro position state id target destination stored found
    obtain ⟨edge, member, index, viewId, targetId, next⟩ := viewEdge found
    have row := List.all_eq_true.mp viewRows edge member
    simp only [index, viewId, targetId, next, stored] at row
    cases generated : SourceCoreCallableAncestryPreparation.view? inputs (nativeState state) id target with
    | none => simp [generated] at row
    | some result =>
      have final : table.stateAt? destination = some result := by simpa only [generated, decide_eq_true_eq] using row
      obtain ⟨receipt, step, same⟩ := view_sound owned inputs generated
      exact ⟨receipt, step, by simpa only [same] using final⟩

/-- Every independently valid named/lambda/view transition is included by
actual validation of the completed table. -/
theorem valid_closed {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {table : SourceCoreCallableAncestryCache.Table}
    (validated : SourceCoreCallableAncestryPreparation.valid inputs table = true) : Closed owned table := by
  simp only [SourceCoreCallableAncestryPreparation.valid, Bool.and_eq_true] at validated
  obtain ⟨⟨_, namedRows⟩, transitions⟩ := validated
  rw [callable_eq owned inputs] at namedRows
  rw [templates_eq owned inputs, views_eq owned inputs] at transitions
  constructor
  · intro id receipt
    have member : receipt.entry ∈ owned.callable.table.entries := List.mem_of_find?_eq_some receipt.selected
    have identifier : receipt.entry.id = id := by simpa using List.find?_some receipt.selected
    have row := List.all_eq_true.mp namedRows receipt.entry member
    simp only [identifier, named_complete inputs receipt] at row
    cases selected : table.namedAt? id with
    | none => simp [selected] at row
    | some position => exact ⟨position, rfl, by simpa only [selected, decide_eq_true_eq] using row⟩
  · intro position state id stored receipt metadata
    have member : (nativeState state, position) ∈ table.states.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr stored
    have both := List.all_eq_true.mp transitions (nativeState state, position) member
    simp only [Bool.and_eq_true] at both
    have rows := both.1
    have templateMember : receipt.template ∈ owned.templates.lambdas := List.mem_of_find?_eq_some receipt.selected
    have identifier : receipt.template.descriptor = id := by simpa using List.find?_some receipt.selected
    have row := List.all_eq_true.mp rows receipt.template templateMember
    simpa only [identifier, lambda_complete inputs receipt metadata, Bool.not_true, Bool.false_or] using row
  · intro position state id target stored receipt step
    have member : (nativeState state, position) ∈ table.states.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr stored
    have both := List.all_eq_true.mp transitions (nativeState state, position) member
    simp only [Bool.and_eq_true] at both
    have rows := both.2
    have viewMember : receipt.entry ∈ owned.views.entries := List.mem_of_find?_eq_some receipt.selected
    have identifier : receipt.entry.id = id := by simpa using List.find?_some receipt.selected
    have row := List.all_eq_true.mp rows receipt.entry viewMember
    have templateMember : receipt.targetLambda.template ∈ owned.templates.lambdas := List.mem_of_find?_eq_some receipt.targetLambda.selected
    have targetId : receipt.targetLambda.template.descriptor = target := by simpa using List.find?_some receipt.targetLambda.selected
    have row := List.all_eq_true.mp row receipt.targetLambda.template templateMember
    simp only [identifier, targetId, view_complete inputs receipt step] at row
    cases selected : table.viewAt? position id target with
    | none => simp [selected] at row
    | some destination => exact ⟨destination, rfl, by simpa only [selected, decide_eq_true_eq] using row⟩

/-- Successful actual preparation provides the static completed-worklist
certificate. Proving that preparation cannot exhaust its computed cardinality
is a distinct totality obligation, not a premise hidden in this theorem. -/
def certified {checked : Checked} {base : Base checked} (owned : Owned base)
    (prepared : SourceCoreCallableAncestryPreparation.Prepared base) : CallableAncestryCache.Prepared owned :=
  certify prepared.table (valid_sound owned prepared.inputs prepared.validated)
    (valid_closed owned prepared.inputs prepared.validated)

theorem prepared_lookup_iff {checked : Checked} {base : Base checked} (owned : Owned base)
    (prepared : SourceCoreCallableAncestryPreparation.Prepared base) {frame : ContextFrame} {state : Option State} :
    prepared.table.lookup? frame = some (state.map nativeState) ↔ Authenticates owned frame state :=
  (certified owned prepared).lookup_iff

end Solcore.SourceSemantics.CoreLowering.CallableAncestryTransitions
