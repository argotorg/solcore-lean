import Solcore.Frontend.SourceCoreCallableFaultSites
import Solcore.SourceSemantics.CoreLowering.CompatibleMemberCertificates

/-! Exact callable diagnostic rows from successful artifact preparation.
The static inventory retains the actual first token lookup and the raw error;
it makes no claim about arbitrary semantic faults or staged rejection. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation
open Core Frontend SourceInference SourceCoreCallableFaultSites

private def selects (row : SourceCoreStageCodebook.Decision) (phase : Phase)
    (error : RuntimeError) (site : Site) : Bool :=
  decide (site.caller = row.caller ∧ site.call = row.call ∧ site.contract = row.entry.id ∧
    site.phase = phase ∧ site.error = error)

/-- The actual issued rows have fresh positive tokens, exact token lookup and
unchanged diagnostic errors. Bounds retain the original allocator offset. -/
structure Inventory (start : Nat) (sites : List Site) : Prop where
  bounds : ∀ site, site ∈ sites → start < site.reason.val ∧ site.reason.val ≤ start + sites.length
  found : ∀ site, site ∈ sites → sites.find? (fun candidate => decide (candidate.reason = site.reason)) = some site
  error : ∀ site, site ∈ sites → site.diagnostic.error = site.error

private theorem Inventory.empty (start : Nat) : Inventory start [] := by
  constructor <;> intro site member <;> cases member

private theorem Inventory.append {start : Nat} {sites : List Site} (before : Inventory start sites)
    {site : Site} (number : site.reason.val = start + 1 + sites.length)
    (error : site.diagnostic.error = site.error) : Inventory start (sites ++ [site]) := by
  have distinct : ∀ candidate, candidate ∈ sites → candidate.reason ≠ site.reason := by
    intro candidate member same
    have bound := (before.bounds candidate member).2
    have numbers := congrArg Fin.val same
    omega
  have absent : sites.find? (fun candidate => decide (candidate.reason = site.reason)) = none := by
    apply List.find?_eq_none.mpr
    intro candidate member
    intro same
    exact distinct candidate member (of_decide_eq_true same)
  constructor
  · intro candidate member
    rcases List.mem_append.mp member with old | fresh
    · have bound := before.bounds candidate old
      simp only [List.length_append, List.length_singleton]
      omega
    · have same := List.mem_singleton.mp fresh
      subst candidate
      simp only [List.length_append, List.length_singleton]
      omega
  · intro candidate member
    rcases List.mem_append.mp member with old | fresh
    · rw [List.find?_append, before.found candidate old]; rfl
    · have same := List.mem_singleton.mp fresh
      subst candidate
      rw [List.find?_append, absent]
      simp
  · intro candidate member
    rcases List.mem_append.mp member with old | fresh
    · exact before.error candidate old
    · exact List.mem_singleton.mp fresh ▸ error

private def answer (row : SourceCoreStageCodebook.Decision) : Phase → Except RuntimeError Unit
  | .beforeArguments => row.beforeArguments
  | .beforeApplication => row.afterArguments

/-- Every actually rejected phase has a real emitted row. Its raw error and
contract identify the same selected artifact decision. -/
def Covered (row : SourceCoreStageCodebook.Decision) (sites : List Site) : Prop :=
  ∀ phase error, answer row phase = .error error →
    ∃ site, site ∈ sites ∧ selects row phase error site = true

private theorem Covered.grows {row : SourceCoreStageCodebook.Decision}
    {before after : List Site} (covered : Covered row before)
    (growth : ∃ suffix, after = before ++ suffix) : Covered row after := by
  obtain ⟨suffix, rfl⟩ := growth
  intro phase error failed
  obtain ⟨site, member, same⟩ := covered phase error failed
  exact ⟨site, List.mem_append_left _ member, same⟩

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem word_number {number : Nat} {reason : Word}
    (accepted : (match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCallableFaultSites.Error.reasonSpaceExhausted) = .ok reason) :
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

private theorem phase_inventory {start : Nat} {row : SourceCoreStageCodebook.Decision}
    {node : ExpressionNode} {sites result : List Site}
    {issue : Nat → Except SourceCoreCallableFaultSites.Error Word}
    (wordEq : ∀ number, issue number = match Word.ofNat? number with
      | some value => Except.ok value | none => Except.error .reasonSpaceExhausted)
    (before : Inventory start sites)
    (ran : forIn ([.beforeArguments, .beforeApplication] : List Phase) sites (fun (phase : Phase) (current : List Site) => do
      let answer : Except RuntimeError Unit := match phase with
        | .beforeArguments => row.beforeArguments | .beforeApplication => row.afterArguments
      match answer with
      | .ok _ => pure (ForInStep.yield current)
      | .error error =>
          let reason ← issue (start + 1 + current.length)
          let diagnostic : SourceCoreFaultSites.Diagnostic :=
            { error, site := .occurrence row.call.occurrence, span := some node.span }
          pure (ForInStep.yield (current ++ [(⟨row.caller, row.call, row.entry.id, phase, error, reason, diagnostic⟩ : Site)]))) = .ok result) :
    Inventory start result ∧ (∃ suffix, result = sites ++ suffix) ∧ Covered row result := by
  have retained := CompatibleMemberCertificates.forIn_preserves ran
    (fun seen current => Inventory start current ∧ (∃ suffix, current = sites ++ suffix) ∧
      (∀ phase, phase ∈ seen → ∀ error, answer row phase = .error error →
        ∃ site, site ∈ current ∧ selects row phase error site = true))
  have final : Inventory start result ∧ (∃ suffix, result = sites ++ suffix) ∧
      (∀ phase, phase ∈ ([.beforeArguments, .beforeApplication] : List Phase) →
        ∀ error, answer row phase = .error error → ∃ site, site ∈ result ∧ selects row phase error site = true) := by
    apply retained
    · exact ⟨before, ⟨[], (List.append_nil _).symm⟩, fun _ member => False.elim (List.not_mem_nil member)⟩
    · intro seen phase remaining current outcome _split previous step
      change (match answer row phase with
        | .ok _ => Except.ok (ForInStep.yield current)
        | .error error => do
            let reason ← issue (start + 1 + current.length)
            pure (ForInStep.yield (current ++ [(⟨row.caller, row.call, row.entry.id, phase, error, reason,
              ⟨error, .occurrence row.call.occurrence, some node.span⟩⟩ : Site)]))) = .ok outcome at step
      split at step
      · rename_i accepted
        refine ⟨current, (Except.ok.inj step).symm, previous.1, previous.2.1, ?_⟩
        intro prior member error failed
        rcases List.mem_append.mp member with old | fresh
        · exact previous.2.2 prior old error failed
        · have same := List.mem_singleton.mp fresh
          subst prior
          change answer row _ = .ok _ at accepted
          rw [accepted] at failed
          cases failed
      · rename_i error failed
        obtain ⟨reason, issued, step⟩ := bind_ok step
        rw [wordEq] at issued
        have number := word_number issued
        let site : Site := ⟨row.caller, row.call, row.entry.id, phase, error, reason,
          ⟨error, .occurrence row.call.occurrence, some node.span⟩⟩
        have inventory := previous.1.append (site := site) number rfl
        obtain ⟨suffix, growth⟩ := previous.2.1
        refine ⟨current ++ [site], (Except.ok.inj step).symm, inventory,
          ⟨suffix ++ [site], by rw [growth, List.append_assoc]⟩, ?_⟩
        intro prior member actualError actualFailed
        rcases List.mem_append.mp member with old | fresh
        · obtain ⟨oldSite, oldMember, oldSame⟩ := previous.2.2 prior old actualError actualFailed
          exact ⟨oldSite, List.mem_append_left _ oldMember, oldSame⟩
        · have same := List.mem_singleton.mp fresh
          subst prior
          change answer row _ = .error error at failed
          have sameError := Except.error.inj (failed.symm.trans actualFailed)
          subst actualError
          exact ⟨site, List.mem_append_right _ (List.mem_singleton_self _), by simp [site, selects]⟩
  refine ⟨final.1, final.2.1, ?_⟩
  intro phase error failed
  exact final.2.2 phase (by cases phase <;> simp) error failed

/-- The original allocator begins above every used base-table token. -/
def offset (base : SourceCoreFaultSites.Table) (minimum : Nat) : Nat :=
  max (((base.reads.map (·.reason.val) ++ base.additional.map (·.1.val) ++
    [base.escapedReason.val]).foldl max 0) + 1) minimum

/-- Finite static facts about the actual successful callable diagnostic factory. -/
structure Receipt (contracts : Table) (base : SourceCoreFaultSites.Table) (minimum : Nat)
    (program : SourceCoreCallableFaultSites.Program) : Prop where
  unknown : program.unknown.val = offset base minimum
  inventory : Inventory (offset base minimum) program.sites
  covered : ∀ row, row ∈ contracts.decisions → Covered row program.sites
  table : program.rootTable = { base with
    additional := base.additional ++ [(program.unknown,
      ⟨.deepSafetyInputsRejected, .declaration base.owner, none⟩)] ++
      program.sites.map (fun site => (site.reason, site.diagnostic)) }

/-- Successful artifact preparation itself proves row coverage and fresh token
lookup. The only traversal is the existing static compiler loop. -/
theorem prepare_receipt {plan : SourceCoreStageCodebook.Plan} {contracts : Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (prepared : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program) :
    Receipt contracts base minimum program := by
  unfold SourceCoreCallableFaultSites.prepare at prepared
  obtain ⟨unknown, issued, prepared⟩ := bind_ok prepared
  have unknownNumber : unknown.val = offset base minimum := word_number issued
  obtain ⟨sites, loop, returned⟩ := bind_ok prepared
  have final : Inventory (offset base minimum) sites ∧
      ∀ row, row ∈ contracts.decisions → Covered row sites := by
    apply CompatibleMemberCertificates.forIn_preserves loop
      (fun seen current => Inventory (offset base minimum) current ∧
        ∀ row, row ∈ seen → Covered row current)
    · exact ⟨Inventory.empty _, fun _ member => False.elim (List.not_mem_nil member)⟩
    · intro seen row remaining current outcome _split previous step
      dsimp only at step
      split at step
      · rename_i caller callerFound
        try dsimp only [pure, Except.pure, bind, Except.bind] at step
        split at step
        · rename_i node nodeFound
          try dsimp only [pure, Except.pure, bind, Except.bind] at step
          obtain ⟨updated, phases, returned⟩ := bind_ok step
          have receipt := phase_inventory (start := offset base minimum) (row := row) (node := node)
            (fun _ => rfl) previous.1 phases
          refine ⟨updated, (Except.ok.inj returned).symm, receipt.1, ?_⟩
          intro prior member
          rcases List.mem_append.mp member with old | fresh
          · exact (previous.2 prior old).grows receipt.2.1
          · exact List.mem_singleton.mp fresh ▸ receipt.2.2
        · change (Except.error _ : Except SourceCoreCallableFaultSites.Error _) = .ok outcome at step
          cases step
      · change (Except.error _ : Except SourceCoreCallableFaultSites.Error _) = .ok outcome at step
        cases step
  cases Except.ok.inj returned
  exact ⟨unknownNumber, final.1, final.2, rfl⟩

private theorem foldl_max_initial (values : List Nat) (initial : Nat) : initial ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem foldl_max_member (values : List Nat) {value : Nat} (member : value ∈ values) (initial : Nat) :
    value ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_initial tail _)
    · exact ih member _

private theorem offset_used {base : SourceCoreFaultSites.Table} {minimum number : Nat}
    (used : number ∈ base.reads.map (·.reason.val) ++ base.additional.map (·.1.val) ++
      [base.escapedReason.val]) : number < offset base minimum := by
  have bound := foldl_max_member _ used 0
  have start := Nat.le_max_left
    ((base.reads.map (·.reason.val) ++ base.additional.map (·.1.val) ++ [base.escapedReason.val]).foldl max 0 + 1) minimum
  unfold offset
  omega

/-- The authentic selected rejection token decodes to its own raw diagnostic
error in the actual extended table. No semantic FaultRep is assumed. -/
theorem Receipt.diagnostic {contracts : Table} {base : SourceCoreFaultSites.Table}
    {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (receipt : Receipt contracts base minimum program)
    {row : SourceCoreStageCodebook.Decision} (member : row ∈ contracts.decisions)
    {phase : Phase} {error : RuntimeError} (failed : answer row phase = .error error) :
    ∃ diagnostic,
      program.rootTable.diagnostic? (program.reasonAt row.caller row.call row.entry.id phase error) = some diagnostic ∧
      diagnostic.error = error := by
  obtain ⟨emitted, emittedMember, emittedMatches⟩ := receipt.covered row member phase error failed
  have covered : (program.sites.find? (selects row phase error)).isSome :=
    List.find?_isSome.mpr ⟨emitted, emittedMember, emittedMatches⟩
  cases selected : program.sites.find? (selects row phase error) with
  | none => simp only [selected, Option.isSome_none, Bool.false_eq_true] at covered
  | some site =>
    have siteMember := List.mem_of_find?_eq_some selected
    have same := of_decide_eq_true (List.find?_some (p := selects row phase error) selected)
    have token : program.reasonAt row.caller row.call row.entry.id phase error = site.reason := by
      simp only [SourceCoreCallableFaultSites.Program.reasonAt]
      change (match program.sites.find? (selects row phase error) with
        | some chosen => chosen.reason | none => program.unknown) = site.reason
      rw [selected]
    have high := (receipt.inventory.bounds site siteMember).1
    have positive : site.reason ≠ Word.zero := by intro zero; have zeroVal := congrArg Fin.val zero; change site.reason.val = 0 at zeroVal; omega
    have escaped : site.reason ≠ base.escapedReason := by
      intro equal
      have before := offset_used (base := base) (minimum := minimum) (number := base.escapedReason.val)
        (List.mem_append_right _ (List.mem_singleton_self _))
      have numbers := congrArg Fin.val equal
      omega
    have baseAbsent : base.additional.find? (fun candidate => decide (candidate.1 = site.reason)) = none := by
      apply List.find?_eq_none.mpr
      intro candidate contained equal
      have before := offset_used (base := base) (minimum := minimum) (number := candidate.1.val)
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨candidate, contained, rfl⟩)))
      have numbers := congrArg Fin.val (of_decide_eq_true equal)
      omega
    have unknownDistinct : program.unknown ≠ site.reason := by
      intro equal
      have numbers := congrArg Fin.val equal
      have actual := receipt.unknown
      omega
    have siteFound : (program.sites.map (fun actual => (actual.reason, actual.diagnostic))).find?
        (fun candidate => decide (candidate.1 = site.reason)) = some (site.reason, site.diagnostic) := by
      rw [List.find?_map]
      change (program.sites.find? (fun candidate => decide (candidate.reason = site.reason))).map
        (fun actual => (actual.reason, actual.diagnostic)) = _
      rw [receipt.inventory.found site siteMember]; rfl
    refine ⟨site.diagnostic, ?_, (receipt.inventory.error site siteMember).trans same.2.2.2.2⟩
    rw [token, receipt.table]
    simp only [SourceCoreFaultSites.Table.diagnostic?, positive, escaped, if_false]
    rw [List.find?_append, List.find?_append, baseAbsent]
    simp only [List.find?_cons, decide_eq_false unknownDistinct,
      List.find?_nil, Option.or_none, siteFound, Option.or_some]
    rfl

/-- The real first phase rejection retains its raw stage diagnostic. -/
theorem prepared_before_arguments {plan : SourceCoreStageCodebook.Plan} {contracts : Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (prepared : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program)
    {row : SourceCoreStageCodebook.Decision} (member : row ∈ contracts.decisions)
    {error : RuntimeError} (failed : row.beforeArguments = .error error) :
    ∃ diagnostic, program.rootTable.diagnostic?
      (program.reasonAt row.caller row.call row.entry.id .beforeArguments error) = some diagnostic ∧
      diagnostic.error = error :=
  (prepare_receipt prepared).diagnostic member failed

/-- The real second phase rejection retains its raw invocation diagnostic. -/
theorem prepared_after_arguments {plan : SourceCoreStageCodebook.Plan} {contracts : Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (prepared : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program)
    {row : SourceCoreStageCodebook.Decision} (member : row ∈ contracts.decisions)
    {error : RuntimeError} (failed : row.afterArguments = .error error) :
    ∃ diagnostic, program.rootTable.diagnostic?
      (program.reasonAt row.caller row.call row.entry.id .beforeApplication error) = some diagnostic ∧
      diagnostic.error = error :=
  (prepare_receipt prepared).diagnostic member failed

/-- The application arity rejection uses the exact same issued phase row. -/
theorem prepared_application_arity {plan : SourceCoreStageCodebook.Plan} {contracts : Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (prepared : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program)
    {row : SourceCoreStageCodebook.Decision} (member : row ∈ contracts.decisions)
    (different : row.entry.parameterCount ≠ row.argumentCount) :
    ∃ diagnostic, program.rootTable.diagnostic?
      (program.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount row.argumentCount)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch row.entry.parameterCount row.argumentCount :=
  (prepare_receipt prepared).diagnostic member (SourceCoreStageCodebook.Decision.afterArguments_mismatch row different)

end Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation
