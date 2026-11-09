import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AppliedViews
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Patterns
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.Heaps
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.PrimitiveExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues

/-!
# General expressions and call codebooks

General expression meaning, the certificates of call codebooks, and fault contracts of scalar members.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScalarMemberFaultPostContracts
/-! Member fault transport retains the selected parent, child and layout. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ScalarMemberFaultPostContracts
open Core Frontend SourceInference CompatibleExpressionReads CompatibleExpressionMembers ExpressionFailurePostContracts

structure Joins (post : ExpressionFaultPost) (values : CompatibleExpressionReads.ValuesContext)
    (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  base : ∀ {id node child childNode name index identity branches result childType
      environment before reason after token mapping world store},
    Metadata values.checked source id node result →
    Metadata values.checked source child childNode childType →
    node.form = .member child name index →
    Layout values.checked (.occurrence id.occurrence) childNode.type node.type index identity branches result →
    Dynamic.ExpressionFaults program context evidence source environment before child reason after →
    post program context evidence source environment before child reason after token mapping world store →
    post program context evidence source environment before id reason after token mapping world store

theorem trivial_joins (values : CompatibleExpressionReads.ValuesContext) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins TrivialExpressionPost values program context evidence source where
  base := by intros; trivial

theorem base_fault_outcome {post : ExpressionFaultPost} {values : CompatibleExpressionReads.ValuesContext}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} (joins : Joins post values program context evidence source)
    {id child : ExpressionId} {node childNode : ExpressionNode} {name : String} {index : Nat}
    {identity : DataTypeId} {branches : List Expr} {result childType : Ty}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {token : Word} {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {store : Store}
    (metadata : Metadata values.checked source id node result)
    (baseMetadata : Metadata values.checked source child childNode childType)
    (form : node.form = .member child name index)
    (layout : Layout values.checked (.occurrence id.occurrence) childNode.type node.type index identity branches result)
    (failed : Dynamic.ExpressionFaults program context evidence source environment before child reason after)
    (retained : OutcomePost post program context evidence source environment before child childType
      (.fault reason) after (.inLeft childType (.word token)) mapping world store) :
    OutcomePost post program context evidence source environment before id result
      (.fault reason) after (.inLeft result (.word token)) mapping world store :=
  ⟨token, rfl, joins.base metadata baseMetadata form layout failed (OutcomePost.fault retained)⟩

end Solcore.SourceSemantics.CoreLowering.ScalarMemberFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallCodebookCertificates
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
theorem prepareWithProjection_collects {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {table : Table}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok table) :
    ∃ sidecars, (∀ sidecar, sidecar ∈ sidecars →
      SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar) ∧
      collectDecisions limits sidecars table.entries = .ok table.decisions := by
  unfold prepareWithProjection at accepted
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

/-- The strict wrapper uses the same original sidecar and decision pass. -/
theorem prepare_collects {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {table : Table}
    (accepted : prepare program plan checked limits firstId = .ok table) :
    ∃ sidecars, (∀ sidecar, sidecar ∈ sidecars →
      SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar) ∧
      collectDecisions limits sidecars table.entries = .ok table.decisions :=
  prepareWithProjection_collects accepted

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
theorem rows_of_prepareWithProjection {program : CheckedProgram} {plan : Plan}
    {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {site : SourceCoreCallableContracts.Callsite} {sidecar : Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata)) :
    CallableLedger.Rows sidecar site site.call arguments := by
  obtain ⟨sidecars, prepared, collected⟩ := prepareWithProjection_collects accepted
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

/-- The strict catalog remains a wrapper of the shared authenticated pass. -/
theorem rows_of_prepare {program : CheckedProgram} {plan : Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : Limits} {firstId : Nat} {site : SourceCoreCallableContracts.Callsite} {sidecar : Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : prepare program plan checked limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata)) :
    CallableLedger.Rows sidecar site site.call arguments :=
  rows_of_prepareWithProjection accepted caller contains form

end Solcore.SourceSemantics.CoreLowering.CallCodebookCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralExpressions
/-! Scalar/product expression correspondence over a mapped heap that may also
contain administrative function cells. The existing structural compilation
certificates are reused. Exact temporary-binder insertion follows from the
restricted Core expression syntax, without a first-order store premise. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.GeneralExpressions

open Frontend Frontend.SourceInference TypeSystem LocalCell

private theorem appendContext {context : Core.Context} {expression : Core.Expr} {type : Core.Ty}
    (typed : Core.HasType context expression type) (administrative : Core.Context) :
    Core.HasType (context ++ administrative) expression type := by
  have respects : Core.Renaming.Respects Core.Renaming.id context (context ++ administrative) := by
    intro index foundType found
    change (context ++ administrative)[index]? = some foundType
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simpa using typed.rename respects

private theorem success_readOnly {expression : Core.Expr} (restricted : Core.ReadOnly.Expression expression) :
    Core.ReadOnly.Expression (Core.LanguageResult.success expression) := .inRight restricted

private theorem bind_readOnly {computation body : Core.Expr} (type : Core.Ty)
    (computationRestricted : Core.ReadOnly.Expression computation) (bodyRestricted : Core.ReadOnly.Expression body) :
    Core.ReadOnly.Expression (Core.LanguageResult.bind type computation body) :=
  .caseE computationRestricted (.inLeft .var) bodyRestricted

private theorem pair_readOnly {left right : Core.Expr} (leftType rightType : Core.Ty)
    (leftRestricted : Core.ReadOnly.Expression left) (rightRestricted : Core.ReadOnly.Expression right) :
    Core.ReadOnly.Expression (Core.LocalSequence.pair leftType rightType left right) :=
  bind_readOnly _ leftRestricted (bind_readOnly _ (rightRestricted.weakenAt 0) (.inRight (.pair .var .var)))

private theorem choose_readOnly {condition thenBranch elseBranch : Core.Expr} (type : Core.Ty)
    (conditionRestricted : Core.ReadOnly.Expression condition)
    (thenRestricted : Core.ReadOnly.Expression thenBranch) (elseRestricted : Core.ReadOnly.Expression elseBranch) :
    Core.ReadOnly.Expression (Core.LocalControl.choose type condition thenBranch elseBranch) :=
  bind_readOnly _ conditionRestricted (.ifE .var (thenRestricted.weakenAt 0) (elseRestricted.weakenAt 0))

namespace Control

open ControlExpressions

theorem readOnly {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type code depth) : Core.ReadOnly.Expression code := by
  induction tree with
  | unit => exact .inRight .unit
  | bool => exact .inRight .bool
  | word => exact .inRight .word
  | localRead => exact .caseE (.loadCell .var) (.inLeft .word) (.inRight .var)
  | group _ _ _ ih => exact ih
  | pair _ _ _ _ left right => exact pair_readOnly _ _ left right
  | conditional _ _ _ _ _ condition thenBranch elseBranch => exact choose_readOnly _ condition thenBranch elseBranch

private theorem map_root
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {reasonAt : ExpressionId → Core.Word} {root parent : ExpressionId} {type : Core.Ty}
    {sourceOutcome : Dynamic.ExpressionOutcome} {coreValue : Core.Value}
    (related : OutcomeRepresents program context evidence source environment heap reasonAt root type sourceOutcome coreValue)
    (lift : ∀ site location, UninitializedAt program context evidence source environment heap root site location →
      UninitializedAt program context evidence source environment heap parent site location) :
    OutcomeRepresents program context evidence source environment heap reasonAt parent type sourceOutcome coreValue := by
  cases related with
  | value staged typed => exact .value staged typed
  | uninitialized site location provenance => exact .uninitialized site location (lift site location provenance)

private theorem word_constructs {span : Syntax.SourceSpan}
    {literal : Syntax.CoreLiteralValue} {value : Core.Word}
    (meaning : WordLiteralDenotes ⟨span, literal⟩ value) :
    Dynamic.LiteralConstructs literal (.word value) := by
  have modulo : Core.Word.ofNatModulo value.val = value := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt
  rw [← modulo]
  exact .word meaning

theorem preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store expression coreValue store := by
  induction tree with
  | unit metadata form =>
      refine ⟨.value .unit, .inRight .word .unit, .value ?_, .value .unit rfl, .inRight .unit⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .tuple rfl .nil .nil
      · rw [metadata.coercions]; exact .nil
  | bool value metadata form =>
      refine ⟨.value (.bool value), .inRight .word (.bool value), .value ?_,
        .value (.bool value) rfl, .inRight .bool⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]; exact .builtinBoolean rfl
      · rw [metadata.coercions]; exact .nil
  | word value metadata form meaning =>
      refine ⟨.value (.word value), .inRight .word (.word value), .value ?_,
        .value (.word value) rfl, .inRight .word⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .literal rfl (word_constructs meaning)
      · rw [metadata.coercions]; exact .nil
  | @localRead id node type binder name index metadata form owned slot =>
      obtain ⟨location, target, cell, stored, lookup, coreLookup, _, read, coreRead, related⟩ :=
        environments.lookup_heap heaps slot
      have cellType := related.types.source_unique metadata.types
      let site : ReadSite source scope id type := {
        node, binder, name, index, contains := metadata.contains, form, owner := owned
        requirements := metadata.requirements, coercions := metadata.coercions
        slot, types := metadata.types
      }
      cases related with
      | uninitialized types =>
          refine ⟨_, _, .fault ?_, .uninitialized id location (.localRead site lookup read cellType rfl rfl),
            Core.OptionalCell.read_failure (reasonAt id) (.var coreLookup) coreRead⟩
          apply Dynamic.ExpressionFaults.form metadata.contains
          rw [form, metadata.requirements, metadata.coercions]
          exact .localUninitialized (owned := []) rfl lookup read rfl rfl types.not_mapping
      | initialized value =>
          refine ⟨_, _, .value ?_, .value value rfl,
            Core.OptionalCell.read_success (reasonAt id) (.var coreLookup) coreRead⟩
          apply Dynamic.ExpressionEvaluates.intro metadata.contains
          · rw [form, metadata.requirements, metadata.coercions]
            exact .local rfl lookup read rfl rfl
          · rw [metadata.coercions]; exact .nil
  | group metadata form child inductionHypothesis =>
      obtain ⟨outcome, coreValue, evaluated, related, coreEvaluated⟩ := inductionHypothesis
      refine ⟨outcome, coreValue, ?_, map_root related (fun _ _ trace => .group metadata form trace), coreEvaluated⟩
      cases evaluated with
      | value evaluated =>
          apply Dynamic.ExpressionEvaluatesOutcome.value
          apply Dynamic.ExpressionEvaluates.intro metadata.contains
          · rw [form, metadata.requirements, metadata.coercions]; exact .group rfl evaluated
          · rw [metadata.coercions]; exact .nil
      | fault fault =>
          apply Dynamic.ExpressionEvaluatesOutcome.fault
          apply Dynamic.ExpressionFaults.form metadata.contains
          rw [form, metadata.requirements, metadata.coercions]
          exact .group rfl fault
  | @pair id left right node leftType rightType leftCode rightCode leftDepth rightDepth
      metadata form leftTree rightTree leftInduction rightInduction =>
      obtain ⟨leftOutcome, leftValue, leftSource, leftRelated, leftCore⟩ := leftInduction
      cases leftRelated with
      | uninitialized faultSite location provenance =>
          cases leftSource with
          | fault fault =>
              refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairLeft metadata form provenance),
                Core.LocalSequence.pair_left_failure leftType rightType leftCore⟩
              apply Dynamic.ExpressionFaults.form metadata.contains
              rw [form, metadata.requirements, metadata.coercions]
              exact .tuple rfl (.head fault)
      | value leftValue leftTypeEq =>
          cases leftSource with
          | value leftSource =>
              obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightInduction
              have weakened := (readOnly rightTree).evaluation_weakenAt_zero rightCore (SourceStagedValue.toCore leftValue)
              cases rightRelated with
              | uninitialized faultSite location provenance =>
                  cases rightSource with
                  | fault fault =>
                      refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairRight metadata form leftSource provenance),
                        Core.LocalSequence.pair_right_failure leftType rightType leftCore weakened⟩
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .tuple rfl (.tail leftSource (.head fault))
              | value rightValue rightTypeEq =>
                  cases rightSource with
                  | value rightSource =>
                      refine ⟨.value (StagedValue.toSource (.product leftValue rightValue)),
                        .inRight .word (SourceStagedValue.toCore (.product leftValue rightValue)),
                        .value ?_, .value (.product leftValue rightValue) ?_,
                        Core.LocalSequence.pair_success leftType rightType leftCore weakened⟩
                      · apply Dynamic.ExpressionEvaluates.intro metadata.contains
                        · rw [form, metadata.requirements, metadata.coercions]
                          exact .tuple rfl (.cons leftSource (.cons rightSource .nil))
                            (.cons (.singleton _))
                        · rw [metadata.coercions]; exact .nil
                      · simp [SourceStagedValue.coreType, leftTypeEq, rightTypeEq]
  | @conditional id condition thenId elseId node type conditionCode thenCode elseCode
      conditionDepth thenDepth elseDepth metadata form conditionTree thenTree elseTree
      conditionIH thenIH elseIH =>
      obtain ⟨conditionOutcome, conditionValue, conditionSource, conditionRelated, conditionCore⟩ := conditionIH
      cases conditionRelated with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.condition metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            Core.LocalControl.choose_failure type conditionCore⟩
      | value staged typed =>
          have boolean : ∃ value, staged = .bool value := by
            cases staged <;> simp_all [SourceStagedValue.coreType]
          obtain ⟨boolean, rfl⟩ := boolean
          cases conditionSource with
          | value conditionSource =>
              cases boolean with
              | true =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := thenIH
                  have shifted := (readOnly thenTree).evaluation_weakenAt_zero branchCore (.bool true)
                  refine ⟨outcome, coreValue, ?_,
                    map_root branchRelated (fun _ _ trace => .thenBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_true type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalTrue rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalTrueBranch rfl conditionSource fault
              | false =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := elseIH
                  have shifted := (readOnly elseTree).evaluation_weakenAt_zero branchCore (.bool false)
                  refine ⟨outcome, coreValue, ?_,
                    map_root branchRelated (fun _ _ trace => .elseBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_false type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalFalse rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalFalseBranch rfl conditionSource fault


theorem lowerExpression_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store lowered.expression coreValue store := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact preserves tree program context evidence environments heaps

/-- Completed runs agree even when the unmapped cells contain closures.
Only the finite expression grammar is covered. -/
theorem lowerExpression_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered.expression =
      some (Core.LanguageResult.resultType lowered.type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done coreValue store) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, related, coreEvaluation⟩ :=
    lowerExpression_preserves unique accepted program context evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨Core.infer_complete (appendContext (ControlExpressions.lowerExpression_hasType unique accepted) administrativeContext),
    sourceOutcome, coreValue, required, sourceEvaluation, related, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Control

namespace Primitive

open PrimitiveExpressions

private theorem strictBody_readOnly (operator : Syntax.BinaryOp) :
    Core.ReadOnly.Expression (SourceCorePrimitive.strictBinaryBody operator) := by
  cases operator <;> first | exact .binary .var .var | exact .unary (.binary .var .var) | exact .ifE .var .var .bool | exact .ifE .var .bool .var

private theorem binary_readOnly {left right : Core.Expr} (operator : Syntax.BinaryOp)
    (leftRestricted : Core.ReadOnly.Expression left) (rightRestricted : Core.ReadOnly.Expression right) :
    Core.ReadOnly.Expression (SourceCorePrimitive.binary operator left right) := by
  cases operator <;> first
    | exact choose_readOnly _ leftRestricted rightRestricted (.inRight .bool)
    | exact choose_readOnly _ leftRestricted (.inRight .bool) rightRestricted
    | exact bind_readOnly _ leftRestricted
        (bind_readOnly _ (rightRestricted.weakenAt 0) (success_readOnly (strictBody_readOnly _)))
    | exact bind_readOnly _ leftRestricted
        (bind_readOnly _ (rightRestricted.weakenAt 0)
          (.ifE (.binary .var .word) (.inLeft .word) (success_readOnly (strictBody_readOnly _))))

theorem readOnly {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth) : Core.ReadOnly.Expression code := by
  induction tree with
  | control tree => exact Control.readOnly tree
  | integerLiteral => exact .inRight .word
  | unary _ _ _ _ operand => exact bind_readOnly _ operand (.inRight (.unary .var))
  | binary operator _ _ _ _ _ left right => exact binary_readOnly operator left right
  | group _ _ _ ih => exact ih
  | pair _ _ _ _ left right => exact pair_readOnly _ _ left right
  | conditional _ _ _ _ _ condition thenBranch elseBranch => exact choose_readOnly _ condition thenBranch elseBranch

private theorem map_root
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {reasonAt : ExpressionId → Core.Word} {root parent : ExpressionId} {type : Core.Ty}
    {sourceOutcome : Dynamic.ExpressionOutcome} {coreValue : Core.Value}
    (related : OutcomeRepresents program context evidence source environment heap reasonAt root type sourceOutcome coreValue)
    (lift : ∀ site location, UninitializedAt program context evidence source environment heap root site location →
      UninitializedAt program context evidence source environment heap parent site location) :
    OutcomeRepresents program context evidence source environment heap reasonAt parent type sourceOutcome coreValue := by
  cases related with
  | value staged typed => exact .value staged typed
  | uninitialized site location provenance => exact .uninitialized site location (lift site location provenance)

private theorem binary_evaluates
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id left right : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    {operator : Syntax.BinaryOp} {leftValue rightValue result : Dynamic.Value}
    (metadata : Metadata source id node type) (form : node.form = .binary left operator right)
    (leftSource : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
    (evaluateRight : Dynamic.EvaluatesRightOperand operator leftValue)
    (rightSource : Dynamic.ExpressionEvaluates program context evidence source environment heap right rightValue heap)
    (applied : Dynamic.BinaryPrimitiveApplies operator leftValue rightValue result) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id result heap := by
  apply Dynamic.ExpressionEvaluates.intro metadata.contains
  · rw [form, metadata.requirements, metadata.coercions]
    exact .binaryEvaluateRight (owned := []) rfl leftSource evaluateRight rightSource (.primitive applied)
  · rw [metadata.coercions]; exact .nil

private theorem shortCircuit_evaluates
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id left right : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    {operator : Syntax.BinaryOp} {leftValue result : Dynamic.Value}
    (metadata : Metadata source id node type) (form : node.form = .binary left operator right)
    (leftSource : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
    (circuit : Dynamic.ShortCircuits operator leftValue result) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id result heap := by
  apply Dynamic.ExpressionEvaluates.intro metadata.contains
  · rw [form, metadata.requirements, metadata.coercions]
    exact .binaryShortCircuit (owned := []) rfl leftSource circuit rfl
  · rw [metadata.coercions]; exact .nil


theorem preserves {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store expression coreValue store := by
  induction tree with
  | control tree =>
      obtain ⟨outcome, value, sourceEvaluation, related, coreEvaluation⟩ :=
        Control.preserves tree program context evidence environments heaps
      refine ⟨outcome, value, sourceEvaluation, ?_, coreEvaluation⟩
      cases related with
      | value staged typed => exact .value staged typed
      | uninitialized site location provenance => exact .uninitialized site location (.control provenance)
  | @integerLiteral id node literal resolution metadata form =>
      have proves : RequirementProves context resolution.requirement (ProgramSignatures.builtinIntPredicate .word) := by
        obtain ⟨solved, member, identifier, predicate⟩ := metadata.requirement
        have contains : solved ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
        exact ⟨solved, ⟨contains, identifier⟩, predicate, valid.valid.entriesValid solved contains⟩
      have constructs : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution
          (.word (Core.Word.ofNatModulo resolution.rawValue)) := by
        cases resolution with
        | mk raw target requirement =>
            have targetEq := metadata.target
            dsimp only at targetEq
            subst target
            exact .word metadata.meaning proves
      refine ⟨_, _, .value ?_, .value (.word _) rfl, .inRight .word⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .integerLiteral rfl constructs
      · rw [metadata.coercions]; exact .nil
  | @unary id operand node operandCode operandDepth operator metadata form child ih =>
      obtain ⟨outcome, coreValue, sourceEvaluation, related, coreEvaluation⟩ := ih
      cases related with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.unary metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            Core.LocalPrimitiveResults.unary_failure coreEvaluation⟩
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨result, resultTyped, sourceApplied, coreApplied⟩ := unary_value operator staged typed
              refine ⟨_, _, .value ?_, .value result resultTyped,
                Core.LocalPrimitiveResults.unary_success coreEvaluation coreApplied⟩
              apply Dynamic.ExpressionEvaluates.intro metadata.contains
              · rw [form, metadata.requirements, metadata.coercions]
                exact .unary (owned := []) rfl sourceEvaluation (.primitive sourceApplied)
              · rw [metadata.coercions]; exact .nil
  | @binary id left right node leftCode rightCode leftDepth rightDepth operator metadata form total
      leftTree rightTree leftIH rightIH =>
      obtain ⟨leftOutcome, leftValue, leftSource, leftRelated, leftCore⟩ := leftIH
      cases leftRelated with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.binaryLeft metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            binary_left_failure leftCore⟩
      | value leftValue leftTyped =>
          cases leftSource with
          | value leftSource =>
              by_cases strict : Dynamic.StrictBinaryOperator operator
              · have leftWord := word_of_type leftValue (leftTyped.trans (strict_operand_word strict))
                obtain ⟨leftWord, rfl⟩ := leftWord
                obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightIH
                have shifted := (readOnly rightTree).evaluation_weakenAt_zero rightCore (.word leftWord)
                cases rightRelated with
                | uninitialized site location provenance =>
                    have propagated := UninitializedAt.binaryRight metadata form leftSource (.strict strict) provenance
                    refine ⟨_, _, .fault propagated.faults, .uninitialized site location propagated, ?_⟩
                    rw [binary_strict strict]
                    exact Core.LocalPrimitiveResults.binaryWith_right_failure leftCore shifted
                | value rightValue rightTyped =>
                    cases rightSource with
                    | value rightSource =>
                        obtain ⟨rightWord, rfl⟩ := word_of_type rightValue (rightTyped.trans (strict_operand_word strict))
                        obtain ⟨result, resultTyped, applied, bodyEvaluation⟩ := strict_binary_value strict leftWord rightWord
                        refine ⟨_, _, .value (binary_evaluates metadata form leftSource (.strict strict) rightSource applied),
                          .value result resultTyped, ?_⟩
                        rw [binary_strict strict]
                        exact Core.LocalPrimitiveResults.binaryWith_success leftCore shifted (bodyEvaluation _ _)
              · rcases binary_nonstrict strict total with isAnd | isOr
                · subst operator
                  obtain ⟨leftBoolean, rfl⟩ := bool_of_type leftValue leftTyped
                  cases leftBoolean with
                  | false =>
                      exact ⟨_, _, .value (shortCircuit_evaluates metadata form leftSource .andFalse),
                        .value (.bool false) rfl, Core.LocalPrimitiveResults.logicalAnd_shortCircuit leftCore⟩
                  | true =>
                      obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightIH
                      have shifted := (readOnly rightTree).evaluation_weakenAt_zero rightCore (.bool true)
                      cases rightRelated with
                      | uninitialized site location provenance =>
                          have propagated := UninitializedAt.binaryRight metadata form leftSource .andTrue provenance
                          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
                            Core.LocalPrimitiveResults.logicalAnd_right leftCore shifted⟩
                      | value rightValue rightTyped =>
                          cases rightSource with
                          | value rightSource =>
                              obtain ⟨rightBoolean, rfl⟩ := bool_of_type rightValue rightTyped
                              exact ⟨_, _, .value (binary_evaluates metadata form leftSource .andTrue rightSource
                                (.logicalAnd true rightBoolean)), .value (.bool rightBoolean) rfl,
                                Core.LocalPrimitiveResults.logicalAnd_right leftCore shifted⟩
                · subst operator
                  obtain ⟨leftBoolean, rfl⟩ := bool_of_type leftValue leftTyped
                  cases leftBoolean with
                  | true =>
                      exact ⟨_, _, .value (shortCircuit_evaluates metadata form leftSource .orTrue),
                        .value (.bool true) rfl, Core.LocalPrimitiveResults.logicalOr_shortCircuit leftCore⟩
                  | false =>
                      obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightIH
                      have shifted := (readOnly rightTree).evaluation_weakenAt_zero rightCore (.bool false)
                      cases rightRelated with
                      | uninitialized site location provenance =>
                          have propagated := UninitializedAt.binaryRight metadata form leftSource .orFalse provenance
                          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
                            Core.LocalPrimitiveResults.logicalOr_right leftCore shifted⟩
                      | value rightValue rightTyped =>
                          cases rightSource with
                          | value rightSource =>
                              obtain ⟨rightBoolean, rfl⟩ := bool_of_type rightValue rightTyped
                              exact ⟨_, _, .value (binary_evaluates metadata form leftSource .orFalse rightSource
                                (.logicalOr false rightBoolean)), .value (.bool rightBoolean) rfl,
                                Core.LocalPrimitiveResults.logicalOr_right leftCore shifted⟩
  | group metadata form child inductionHypothesis =>
      obtain ⟨outcome, coreValue, evaluated, related, coreEvaluated⟩ := inductionHypothesis
      refine ⟨outcome, coreValue, ?_, map_root related (fun _ _ trace => .group metadata form trace), coreEvaluated⟩
      cases evaluated with
      | value evaluated =>
          apply Dynamic.ExpressionEvaluatesOutcome.value
          apply Dynamic.ExpressionEvaluates.intro metadata.contains
          · rw [form, metadata.requirements, metadata.coercions]; exact .group rfl evaluated
          · rw [metadata.coercions]; exact .nil
      | fault fault =>
          apply Dynamic.ExpressionEvaluatesOutcome.fault
          apply Dynamic.ExpressionFaults.form metadata.contains
          rw [form, metadata.requirements, metadata.coercions]
          exact .group rfl fault
  | @pair id left right node leftType rightType leftCode rightCode leftDepth rightDepth
      metadata form leftTree rightTree leftInduction rightInduction =>
      obtain ⟨leftOutcome, leftValue, leftSource, leftRelated, leftCore⟩ := leftInduction
      cases leftRelated with
      | uninitialized faultSite location provenance =>
          cases leftSource with
          | fault fault =>
              refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairLeft metadata form provenance),
                Core.LocalSequence.pair_left_failure leftType rightType leftCore⟩
              apply Dynamic.ExpressionFaults.form metadata.contains
              rw [form, metadata.requirements, metadata.coercions]
              exact .tuple rfl (.head fault)
      | value leftValue leftTypeEq =>
          cases leftSource with
          | value leftSource =>
              obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightInduction
              have weakened := (readOnly rightTree).evaluation_weakenAt_zero rightCore
                (SourceStagedValue.toCore leftValue)
              cases rightRelated with
              | uninitialized faultSite location provenance =>
                  cases rightSource with
                  | fault fault =>
                      refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairRight metadata form leftSource provenance),
                        Core.LocalSequence.pair_right_failure leftType rightType leftCore weakened⟩
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .tuple rfl (.tail leftSource (.head fault))
              | value rightValue rightTypeEq =>
                  cases rightSource with
                  | value rightSource =>
                      refine ⟨.value (StagedValue.toSource (.product leftValue rightValue)),
                        .inRight .word (SourceStagedValue.toCore (.product leftValue rightValue)),
                        .value ?_, .value (.product leftValue rightValue) ?_,
                        Core.LocalSequence.pair_success leftType rightType leftCore weakened⟩
                      · apply Dynamic.ExpressionEvaluates.intro metadata.contains
                        · rw [form, metadata.requirements, metadata.coercions]
                          exact .tuple rfl (.cons leftSource (.cons rightSource .nil))
                            (.cons (.singleton _))
                        · rw [metadata.coercions]; exact .nil
                      · simp [SourceStagedValue.coreType, leftTypeEq, rightTypeEq]
  | @conditional id condition thenId elseId node type conditionCode thenCode elseCode
      conditionDepth thenDepth elseDepth metadata form conditionTree thenTree elseTree
      conditionIH thenIH elseIH =>
      obtain ⟨conditionOutcome, conditionValue, conditionSource, conditionRelated, conditionCore⟩ := conditionIH
      cases conditionRelated with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.condition metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            Core.LocalControl.choose_failure type conditionCore⟩
      | value staged typed =>
          have boolean : ∃ value, staged = .bool value := by
            cases staged <;> simp_all [SourceStagedValue.coreType]
          obtain ⟨boolean, rfl⟩ := boolean
          cases conditionSource with
          | value conditionSource =>
              cases boolean with
              | true =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := thenIH
                  have shifted := (readOnly thenTree).evaluation_weakenAt_zero branchCore (.bool true)
                  refine ⟨outcome, coreValue, ?_,
                    map_root branchRelated (fun _ _ trace => .thenBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_true type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalTrue rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalTrueBranch rfl conditionSource fault
              | false =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := elseIH
                  have shifted := (readOnly elseTree).evaluation_weakenAt_zero branchCore (.bool false)
                  refine ⟨outcome, coreValue, ?_,
                    map_root branchRelated (fun _ _ trace => .elseBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_false type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalFalse rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalFalseBranch rfl conditionSource fault



theorem lowerExpression_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store lowered.expression coreValue store := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact preserves tree program context evidence valid environments heaps

/-- All completed runs agree with the derived source outcome, including exact
executed read reasons. Sufficient fuel follows from this finite expression
grammar; no unrestricted source normalization or fault completeness is claimed. -/
theorem lowerExpression_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered.expression =
      some (Core.LanguageResult.resultType lowered.type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done coreValue store) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, related, coreEvaluation⟩ :=
    lowerExpression_preserves unique accepted program context evidence valid environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨Core.infer_complete (appendContext (PrimitiveExpressions.lowerExpression_hasType unique accepted) administrativeContext),
    sourceOutcome, coreValue, required, sourceEvaluation, related, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Primitive

namespace Basic

/-- Constant read reasons embed into the occurrence-aware control certificate. -/
theorem toControl {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reason : Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : BasicExpressions.Tree source scope reason id type code depth) :
    ControlExpressions.Tree source scope (fun _ => reason) id type code depth := by
  induction tree with
  | unit metadata form => exact .unit metadata form
  | bool value metadata form => exact .bool value metadata form
  | word value metadata form meaning => exact .word value metadata form meaning
  | localRead metadata form owned slot => exact .localRead metadata form owned slot
  | group metadata form _ child => exact .group metadata form child
  | pair metadata form _ _ left right => exact .pair metadata form left right

theorem readOnly {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reason : Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : BasicExpressions.Tree source scope reason id type code depth) : Core.ReadOnly.Expression code :=
  Control.readOnly (toControl tree)

theorem preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reason : Core.Word}
    {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : BasicExpressions.Tree source scope reason id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      ControlExpressions.OutcomeRepresents program context evidence source environment heap (fun _ => reason)
        id type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store expression coreValue store :=
  Control.preserves (toControl tree) program context evidence environments heaps

theorem lowerExpression_preserves {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id reason = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      ControlExpressions.OutcomeRepresents program context evidence source environment heap (fun _ => reason)
        id lowered.type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store lowered.expression coreValue store := by
  obtain ⟨_, _, tree⟩ := BasicExpressions.tree_of_lowerExpression accepted
  exact preserves tree program context evidence environments heaps

end Basic

end Solcore.SourceSemantics.CoreLowering.GeneralExpressions
end
