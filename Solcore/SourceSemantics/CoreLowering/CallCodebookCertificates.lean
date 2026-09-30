import Solcore.SourceSemantics.CoreLowering.CallableLedger
import Solcore.SourceSemantics.CoreLowering.DataPatternExecution

/-! Static receipts extracted from the actual finite codebook traversal.
This module enumerates proof targets only; it contains no source evaluator,
Core evaluator, or replacement metadata compiler. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallCodebookCertificates
open Frontend Frontend.SourceInference SourceCoreStageCodebook
open DataPatternValues CallContractCertificates

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Extract one relation-certified output batch per successful metadata-loop
iteration. Every step yields; compiler errors cannot fabricate a batch. -/
private theorem forIn_batches {α β γ ε : Type} {items : List α} {initial final : List β}
    {step : α → List β → Except ε (ForInStep (List β))} {targets : α → List γ} {relation : γ → β → Prop}
    (accepted : forIn items initial step = .ok final)
    (each : ∀ item, item ∈ items → ∀ state outcome, step item state = .ok outcome →
      ∃ added, outcome = .yield (state ++ added) ∧ ListRel relation (targets item) added) :
    ∃ added, final = initial ++ added ∧ ListRel relation (items.flatMap targets) added := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst final
    exact ⟨[], (List.append_nil _).symm, .nil⟩
  | cons item items ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨added, rfl, related⟩ := each item (List.mem_cons_self) initial outcome ran
    obtain ⟨rest, final_eq, more⟩ := ih accepted (fun next member => each next (List.mem_cons_of_mem item member))
    exact ⟨added ++ rest, by simpa only [List.append_assoc] using final_eq,
      DataPatternExecution.ListRel.append related more⟩

private theorem flatMap_singleton {α β : Type} (f : α → β) (items : List α) :
    items.flatMap (fun item => [f item]) = items.map f := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, List.map_cons, ih, List.singleton_append]

structure Request where
  sidecar : Sidecar
  call : ExpressionId
  arguments : List ExpressionId
  entry : Entry

def nodeRequests (sidecar : Sidecar) (entries : List Entry) : Node → List Request
  | .expression { id, form := .call _ arguments (.indirect _), .. } =>
      entries.map (fun entry => ⟨sidecar, id, arguments, entry⟩)
  | _ => []

def requests (sidecars : List Sidecar) (entries : List Entry) : List Request :=
  sidecars.flatMap (fun sidecar => sidecar.source.nodes.flatMap (nodeRequests sidecar entries))

structure Generated (request : Request) (row : Decision) : Prop where
  caller : row.caller = request.sidecar.caller.key
  call : row.call = request.call
  entry : row.entry = request.entry
  argumentCount : row.argumentCount = request.arguments.length
  user : ∀ contract, request.entry.contract = some contract → ∃ guard,
    SourceCoreStageContracts.prepareGuard request.sidecar request.call contract = .ok guard ∧
      row.guard = some guard ∧ guard.arguments = request.arguments
  builtin : request.entry.contract = none → row.guard = none

/-- The actual nested loop emits exactly one certified decision per indirect
call occurrence and entry, in traversal order, when its budget succeeds. -/
theorem collectDecisions_certifies {limits : Limits} {sidecars : List Sidecar} {entries : List Entry} {rows : List Decision}
    (accepted : collectDecisions limits sidecars entries = .ok rows) : ListRel Generated (requests sidecars entries) rows := by
  unfold collectDecisions at accepted
  obtain ⟨final, loopAccepted, accepted⟩ := bind_ok accepted
  cases accepted
  obtain ⟨added, equal, certificate⟩ := forIn_batches (targets := fun sidecar =>
    sidecar.source.nodes.flatMap (nodeRequests sidecar entries)) (relation := Generated) loopAccepted (by
    intro sidecar _ state outcome sidecarAccepted
    dsimp only at sidecarAccepted
    obtain ⟨updated, nodeLoop, sidecarAccepted⟩ := bind_ok sidecarAccepted
    cases sidecarAccepted
    obtain ⟨added, equal, certificate⟩ := forIn_batches (targets := nodeRequests sidecar entries)
      (relation := Generated) nodeLoop (by
      intro sourceNode member state outcome nodeAccepted
      cases sourceNode with
      | statement statement =>
        cases nodeAccepted
        exact ⟨[], by simp, .nil⟩
      | expression node =>
        cases node with
        | mk id span type form requirements coercions localStart =>
          cases form <;> try (cases nodeAccepted; exact ⟨[], by simp, .nil⟩)
          rename_i callee arguments resolution
          cases resolution <;> try (cases nodeAccepted; exact ⟨[], by simp, .nil⟩)
          rename_i metadata
          dsimp only at nodeAccepted
          obtain ⟨updated, entryLoop, nodeAccepted⟩ := bind_ok nodeAccepted
          cases nodeAccepted
          obtain ⟨added, equal, certificate⟩ := forIn_batches
            (targets := fun entry => [Request.mk sidecar id arguments entry]) (relation := Generated) entryLoop (by
            intro entry _ state outcome entryAccepted
            split at entryAccepted
            · cases entryAccepted
            · cases retained : entry.contract with
              | none =>
                simp only [retained, pure, Except.pure, bind, Except.bind] at entryAccepted
                cases entryAccepted
                refine ⟨_, rfl, .cons ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ .nil⟩
                · intro contract impossible; rw [retained] at impossible; cases impossible
                · intro _; rfl
              | some contract =>
                simp only [retained] at entryAccepted
                cases prepared : SourceCoreStageContracts.prepareGuard sidecar id contract with
                | error error => simp [prepared, Except.map, Except.mapError, bind, Except.bind] at entryAccepted
                | ok guard =>
                  simp only [prepared, Except.map, Except.mapError, pure, Except.pure, bind, Except.bind] at entryAccepted
                  cases entryAccepted
                  refine ⟨_, rfl, .cons ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ .nil⟩
                  · intro other found
                    cases Option.some.inj (retained.symm.trans found)
                    exact ⟨guard, prepared, rfl, guard_arguments prepared ⟨member, rfl⟩ rfl⟩
                  · intro impossible; rw [retained] at impossible; cases impossible)
          exact ⟨added, congrArg ForInStep.yield equal,
            by simpa only [nodeRequests, flatMap_singleton] using certificate⟩)
    exact ⟨added, congrArg ForInStep.yield equal, certificate⟩)
  simpa only [List.nil_append] using equal ▸ certificate

private theorem related_member {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : ListRel relation inputs outputs) {input : α} (member : input ∈ inputs) :
    ∃ output, output ∈ outputs ∧ relation input output := by
  induction related with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, first⟩
    · obtain ⟨output, found, related⟩ := ih member
      exact ⟨output, List.mem_cons_of_mem _ found, related⟩

private theorem nodup_map_injective {α β : Type} {key : α → β} {items : List α}
    (unique : (items.map key).Nodup) {left right : α}
    (leftMember : left ∈ items) (rightMember : right ∈ items) (same : key left = key right) : left = right := by
  induction items with
  | nil => cases leftMember
  | cons item items ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightMember
      · rfl
      · exact False.elim (parts.1 (List.mem_map.mpr ⟨right, rightMember, same.symm⟩))
    · rcases List.mem_cons.mp rightMember with rfl | rightMember
      · exact False.elim (parts.1 (List.mem_map.mpr ⟨left, leftTail, same⟩))
      · exact ih parts.2 leftTail rightMember

private theorem nodeRequests_call (sidecar : Sidecar) (entries : List Entry) (node : ExpressionNode)
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (form : node.form = .call callee arguments (.indirect metadata)) :
    nodeRequests sidecar entries (.expression node) = entries.map (fun entry => ⟨sidecar, node.id, arguments, entry⟩) := by
  cases node
  simp_all only [nodeRequests]

private theorem rowAt_of_generated {site : SourceCoreCallableContracts.Callsite} {request : Request} {row : Decision}
    (member : row ∈ site.table.decisions) (generated : Generated request row)
    (caller : site.caller = request.sidecar.caller.key) (call : site.call = request.call) :
    site.rowAt? request.entry.id = some row := by
  have inRows : row ∈ site.rows := by
    apply List.mem_filter.mpr
    exact ⟨member, by simp [generated.caller, generated.call, caller, call]⟩
  cases selected : site.rowAt? request.entry.id with
  | none =>
    have absent := List.find?_eq_none.mp selected row inRows
    exact False.elim (absent (by simp only [generated.entry, beq_self_eq_true]))
  | some chosen =>
    have chosenMember : chosen ∈ site.rows := List.mem_of_find?_eq_some selected
    obtain ⟨chosenInTable, chosenSite⟩ := List.mem_filter.mp chosenMember
    have sites : chosen.caller = site.caller ∧ chosen.call = site.call := of_decide_eq_true chosenSite
    have idEq : request.entry.id = chosen.entry.id := beq_iff_eq.mp (List.find?_some (p := fun candidate : Decision => request.entry.id == candidate.entry.id) selected)
    have sameKey : chosen.key = row.key := by
      simp only [Decision.key, sites.1, sites.2, caller, call, generated.caller, generated.call,
        generated.entry, idEq]
    have same := nodup_map_injective site.table.decisionsUnique chosenInTable member sameKey
    exact congrArg some same

/-- Every selected source call obtains all retained callable rows from the
actual successful codebook loop. Uniqueness fixes the row selected by its
contract word, so callers do not assume an arbitrary guard association. -/
theorem rows_of_collectDecisions {limits : Limits} {sidecars : List Sidecar}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : Sidecar} {call : ExpressionId}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : collectDecisions limits sidecars site.table.entries = .ok site.table.decisions)
    (sidecarMember : sidecar ∈ sidecars) (contains : ContainsExpression sidecar.source call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (caller : site.caller = sidecar.caller.key) (call_eq : site.call = call) :
    CallableLedger.Rows sidecar site call arguments := by
  intro entry member
  have target : Request.mk sidecar call arguments entry ∈ requests sidecars site.table.entries := by
    apply List.mem_flatMap.mpr
    refine ⟨sidecar, sidecarMember, List.mem_flatMap.mpr ⟨.expression node, contains.1, ?_⟩⟩
    rw [nodeRequests_call sidecar site.table.entries node form, contains.2]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  obtain ⟨row, rowMember, generated⟩ := related_member (collectDecisions_certifies accepted) target
  exact ⟨⟨row, rowAt_of_generated rowMember generated caller call_eq, generated.entry,
    generated.user, generated.builtin⟩⟩

private theorem mapError_ok {α ε δ : Type} {result : Except ε α} {value : α} {f : ε → δ}
    (accepted : result.mapError f = .ok value) : result = .ok value := by
  cases result with
  | error => cases accepted
  | ok selected => cases accepted; rfl

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item, item ∈ items → ∀ state outcome, invariant state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant updated) : invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item items ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

/-- The complete public factory retains the actual successful decision pass
and the original prepared sidecars. Local-instance discovery is not replaced
or assumed to have evaluated any source body. -/
theorem prepare_collects {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {table : Table}
    (accepted : prepare program plan checked limits firstId = .ok table) :
    ∃ sidecars, (∀ sidecar, sidecar ∈ sidecars →
      SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar) ∧
      collectDecisions limits sidecars table.entries = .ok table.decisions := by
  unfold prepare at accepted
  split at accepted
  · cases accepted
  · obtain ⟨state, originals, accepted⟩ := bind_ok accepted
    have preparedSidecars : ∀ sidecar, sidecar ∈ state.2 →
        SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar := by
      apply forIn_invariant (invariant := fun current : List Entry × List Sidecar =>
        ∀ sidecar, sidecar ∈ current.2 → SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar) originals
      · intro sidecar member; cases member
      · intro specialized _ state outcome previous iteration
        dsimp only at iteration
        obtain ⟨sidecar, selected, iteration⟩ := bind_ok iteration
        have selected := mapError_ok selected
        obtain ⟨contract, _, iteration⟩ := bind_ok iteration
        obtain ⟨entries, _, iteration⟩ := bind_ok iteration
        obtain ⟨entries, _, iteration⟩ := bind_ok iteration
        cases iteration
        refine ⟨_, rfl, ?_⟩
        intro other member
        rcases List.mem_append.mp member with old | fresh
        · exact previous other old
        · have same := List.mem_singleton.mp fresh
          subst other
          rw [(sidecar_of_accepted selected).2]
          exact selected
    obtain ⟨entries, _, accepted⟩ := bind_ok accepted
    obtain ⟨locals, _, accepted⟩ := bind_ok accepted
    dsimp only at accepted
    split at accepted
    · cases accepted
    · obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      obtain ⟨rows, collected, accepted⟩ := bind_ok accepted
      split at accepted
      · split at accepted
        · split at accepted
          · cases accepted; exact ⟨state.2, preparedSidecars, collected⟩
          · cases accepted
        · cases accepted
      · cases accepted

private theorem related_output {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : ListRel relation inputs outputs) {output : β} (member : output ∈ outputs) :
    ∃ input, input ∈ inputs ∧ relation input output := by
  induction related with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, first⟩
    · obtain ⟨input, found, related⟩ := ih member
      exact ⟨input, List.mem_cons_of_mem _ found, related⟩

private theorem request_sidecar {sidecars : List Sidecar} {entries : List Entry} {request : Request}
    (member : request ∈ requests sidecars entries) : request.sidecar ∈ sidecars := by
  obtain ⟨sidecar, present, inSource⟩ := List.mem_flatMap.mp member
  obtain ⟨node, nodePresent, requestMember⟩ := List.mem_flatMap.mp inSource
  cases node with
  | statement => cases requestMember
  | expression node =>
    cases node with
    | mk id span type form requirements coercions localStart =>
      cases form <;> try cases requestMember
      rename_i callee arguments resolution
      cases resolution <;> try cases requestMember
      obtain ⟨entry, _, same⟩ := List.mem_map.mp requestMember
      cases same
      exact present

/-- The public table factory suffices for the row ledger. The supplied caller
receipt and call occurrence are source metadata; no selected guard, stage
verdict, child execution, or prepared sidecar list is assumed. -/
theorem rows_of_prepare {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {site : SourceCoreCallableContracts.Callsite} {sidecar : Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : prepare program plan checked limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata)) :
    CallableLedger.Rows sidecar site site.call arguments := by
  obtain ⟨sidecars, prepared, collected⟩ := prepare_collects accepted
  have nonempty : ∃ row, row ∈ site.rows := by
    cases rows : site.rows with
    | nil => exact False.elim (site.present rows)
    | cons row rest => exact ⟨row, List.mem_cons_self⟩
  obtain ⟨row, member⟩ := nonempty
  obtain ⟨inTable, atSite⟩ := List.mem_filter.mp member
  have callerEq : row.caller = site.caller := (of_decide_eq_true atSite).1
  obtain ⟨request, requested, generated⟩ := related_output (collectDecisions_certifies collected) inTable
  have sidecarMember := request_sidecar requested
  have actualCaller := prepared request.sidecar sidecarMember
  have originalKey : request.sidecar.caller.key = site.caller := generated.caller.symm.trans callerEq
  rw [originalKey] at actualCaller
  have same := Except.ok.inj (actualCaller.symm.trans caller)
  have present : sidecar ∈ sidecars := same ▸ sidecarMember
  exact rows_of_collectDecisions collected present contains form (sidecar_of_accepted caller).2.symm rfl

end Solcore.SourceSemantics.CoreLowering.CallCodebookCertificates
