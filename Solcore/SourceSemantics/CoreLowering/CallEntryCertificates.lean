import Solcore.SourceSemantics.CoreLowering.CallContractCertificates

/-! Origin certificates from the actual codebook entry builders. Each retained
contract points to its original metadata factory, including the full cumulative
substitution for contextual lambdas. Duplicate origins preserve the earlier
authenticated entry. This proves metadata provenance, not callable execution. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallEntryCertificates
open Frontend Frontend.SourceInference SourceCoreStageCodebook CallContractCertificates

inductive OriginContract (plan : Plan) : Origin → Nat → Option Contract → Prop where
  | named {key : Key} {contract : Contract}
      (prepared : SourceCoreStageContracts.Contract.named plan key = .ok contract) :
      OriginContract plan (.named key) contract.parameters.length (some contract)
  | originalLambda {sidecar : Sidecar} {id : ExpressionId} {contract : Contract}
      (original : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar)
      (prepared : SourceCoreStageContracts.Contract.lambda sidecar id = .ok contract) :
      OriginContract plan (.lambda sidecar.caller.key id []) contract.parameters.length (some contract)
  | contextualLambda {sidecar : Sidecar} {prepared : SourceCoreLocalEvidence.Prepared} {id : ExpressionId} {contract : Contract}
      (original : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar)
      (checked : SourceCoreStageContracts.Contract.contextualLambda sidecar prepared id = .ok contract) :
      OriginContract plan (.lambda sidecar.caller.key id prepared.substitution) contract.parameters.length (some contract)
  | builtin (function : BuiltinFunctionId) : OriginContract plan (.builtin function) function.parameterTypes.length none

def Authenticated (plan : Plan) (entry : Entry) : Prop := OriginContract plan entry.origin entry.parameterCount entry.contract

def AllAuthenticated (plan : Plan) (entries : List Entry) : Prop := ∀ entry, entry ∈ entries → Authenticated plan entry

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

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

theorem insert_preserves {plan : Plan} {limits : Limits} {firstId count : Nat}
    {entries final : List Entry} {origin : Origin} {contract : Option Contract}
    (old : AllAuthenticated plan entries) (new : OriginContract plan origin count contract)
    (accepted : insert limits firstId entries origin count contract = .ok final) : AllAuthenticated plan final := by
  unfold SourceCoreStageCodebook.insert at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted; exact old
  · split at accepted
    · cases accepted
    · split at accepted
      · next selected found =>
        cases accepted
        intro entry member
        rcases List.mem_append.mp member with previous | fresh
        · exact old entry previous
        · have same := List.mem_singleton.mp fresh
          subst entry
          exact new
      · cases accepted

theorem collectLambdas_preserves {plan : Plan} {limits : Limits} {firstId : Nat} {sidecar : Sidecar}
    {prepared : Option SourceCoreLocalEvidence.Prepared} {entries final : List Entry}
    (original : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar) (old : AllAuthenticated plan entries)
    (accepted : collectLambdas limits firstId sidecar prepared entries = .ok final) : AllAuthenticated plan final := by
  unfold collectLambdas at accepted
  obtain ⟨updated, loop, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant loop old
  intro id _ state outcome previous iteration
  dsimp only at iteration
  cases prepared with
  | none =>
    cases prepared : SourceCoreStageContracts.Contract.lambda sidecar id with
    | error error =>
      cases error <;> simp only [prepared] at iteration <;> try cases iteration
      exact ⟨state, rfl, previous⟩
    | ok contract =>
      simp only [prepared] at iteration
      obtain ⟨updated, inserted, iteration⟩ := bind_ok iteration
      cases iteration
      exact ⟨updated, rfl, insert_preserves previous (.originalLambda original prepared) inserted⟩
  | some contextual =>
    cases prepared : SourceCoreStageContracts.Contract.contextualLambda sidecar contextual id with
    | error error =>
      cases error <;> simp only [prepared] at iteration <;> try cases iteration
      exact ⟨state, rfl, previous⟩
    | ok contract =>
      simp only [prepared] at iteration
      obtain ⟨updated, inserted, iteration⟩ := bind_ok iteration
      cases iteration
      exact ⟨updated, rfl, insert_preserves previous (.contextualLambda original prepared) inserted⟩

/-- Public codebook preparation authenticates every retained entry. Contextual
instances keep their actual sealed local-evidence receipt; no runtime closure
or arbitrary type erasure is used to reconstruct its flags. -/
theorem prepare_authenticates {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {table : Table}
    (accepted : prepare program plan checked limits firstId = .ok table) : AllAuthenticated plan table.entries := by
  unfold prepare at accepted
  split at accepted
  · cases accepted
  · obtain ⟨state, originals, accepted⟩ := bind_ok accepted
    have initial : AllAuthenticated plan state.1 := by
      apply forIn_invariant (invariant := fun current : List Entry × List Sidecar => AllAuthenticated plan current.1) originals
      · intro entry member; cases member
      · intro specialized _ state outcome previous iteration
        dsimp only at iteration
        obtain ⟨sidecar, selected, iteration⟩ := bind_ok iteration
        have selected := mapError_ok selected
        obtain ⟨contract, prepared, iteration⟩ := bind_ok iteration
        have prepared := mapError_ok prepared
        obtain ⟨entries, inserted, iteration⟩ := bind_ok iteration
        obtain ⟨entries, collected, iteration⟩ := bind_ok iteration
        cases iteration
        exact ⟨_, rfl, collectLambdas_preserves (by rw [(sidecar_of_accepted selected).2]; exact selected)
          (insert_preserves previous (.named prepared) inserted) collected⟩
    obtain ⟨entries, builtins, accepted⟩ := bind_ok accepted
    have builtinEntries : AllAuthenticated plan entries := by
      apply forIn_invariant builtins initial
      intro function _ state outcome previous iteration
      dsimp only at iteration
      obtain ⟨updated, inserted, iteration⟩ := bind_ok iteration
      cases iteration
      exact ⟨updated, rfl, insert_preserves previous (.builtin function) inserted⟩
    obtain ⟨locals, _, accepted⟩ := bind_ok accepted
    dsimp only at accepted
    split at accepted
    · cases accepted
    · obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, contextual, accepted⟩ := bind_ok accepted
      have final : AllAuthenticated plan entries := by
        apply forIn_invariant contextual builtinEntries
        intro contextual _ state outcome previous iteration
        obtain ⟨sidecar, selected, iteration⟩ := bind_ok iteration
        obtain ⟨updated, collected, iteration⟩ := bind_ok iteration
        cases iteration
        exact ⟨updated, rfl, collectLambdas_preserves (by
          have prepared := mapError_ok selected
          rw [(sidecar_of_accepted prepared).2]
          exact prepared) previous collected⟩
      obtain ⟨rows, _, accepted⟩ := bind_ok accepted
      split at accepted
      · split at accepted
        · split at accepted
          · cases accepted; exact final
          · cases accepted
        · cases accepted
      · cases accepted

/-- A descriptor's selected entry retains the full original origin. -/
theorem descriptor_entry {table : Table} {origin : Origin}
    (descriptor : SourceCoreCallableContracts.Descriptor table origin) :
    ∃ entry, entry ∈ table.entries ∧ entry.origin = origin ∧ entry.id = descriptor.id := by
  have found := descriptor.found
  unfold Table.idAt? at found
  cases selected : table.entries.find? (fun entry => decide (entry.origin = origin)) with
  | none => simp [selected] at found
  | some entry =>
    simp only [selected, Option.map_some, Option.some.injEq] at found
    exact ⟨entry, List.mem_of_find?_eq_some selected,
      of_decide_eq_true (List.find?_some (p := fun candidate : Entry => decide (candidate.origin = origin)) selected), found⟩

end Solcore.SourceSemantics.CoreLowering.CallEntryCertificates
