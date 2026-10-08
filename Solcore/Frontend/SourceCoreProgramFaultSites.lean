import Solcore.Frontend.SourceCoreAssignmentFaultSites
import Solcore.Frontend.SourceCompilationPlan

/-! Program-wide, nonwrapping failure identities. Each specialization keeps its
own read provider; the root entry carries their combined diagnostic table.
This pass only processes source metadata. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreProgramFaultSites

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure Function where
  key : Key
  table : SourceCoreFaultSites.Table
  assignments : SourceCoreAssignmentFaultSites.Table
  fellThroughReason : Core.Word
  deriving Repr

structure Program where
  functions : List Function
  rootTable : SourceCoreFaultSites.Table
  deriving Repr

inductive Error where
  | sites (error : SourceCoreFaultSites.Error)
  | assignments (error : SourceCoreAssignmentFaultSites.Error)
  | plan (error : SourceCompilationPlan.Error)
  | invalidFunctionType (key : Key)
  deriving Repr, DecidableEq

private def reason (index : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? index with
  | some value => pure value
  | none => .error (.sites .reasonSpaceExhausted)

private def collect : Nat → List SourceSpecialization.SpecializedFunction → Except Error (List Function)
  | _, [] => pure []
  | next, specialized :: rest => do
      let sourceResult ← match specialized.function.type with
        | .function _ result => pure result
        | _ => .error (.invalidFunctionType specialized.key)
      let baseSites ← (SourceCoreFaultSites.prepare specialized.function.typedBody sourceResult).mapError Error.sites
      let reads ← baseSites.reads.zipIdx.mapM fun (site, index) => do
        let token ← reason (next + index)
        pure { site with reason := token }
      let assignments ← (SourceCoreAssignmentFaultSites.prepare specialized.function.typedBody
        (next + reads.length)).mapError Error.assignments
      let fellThroughReason ← reason (next + reads.length + assignments.length)
      let escapedReason ← reason (next + reads.length + assignments.length + 1)
      let remaining ← collect (next + reads.length + assignments.length + 2) rest
      let function : Function := {
        key := specialized.key
        table := { baseSites with
          reads := reads
          escapedReason := escapedReason
          additional := assignments.diagnostics }
        assignments
        fellThroughReason := fellThroughReason
      }
      pure (function :: remaining)

def Program.find? (program : Program) (key : Key) : Option Function :=
  program.functions.find? fun function => decide (function.key = key)

/-- Call after canonical plan authentication. Zero remains the root's public
fallthrough token; positive boundary reasons identify the actual callee. -/
def prepare (plan : Plan) (root : Key) : Except Error Program := do
  let functions ← collect 1 plan.specializations
  let selected ← match functions.find? (fun function => decide (function.key = root)) with
    | some function => pure function
    | none => .error (.plan (.missingSpecialization root))
  let reads := functions.flatMap (·.table.reads)
  let additional := functions.flatMap fun function => function.assignments.diagnostics ++ [
    (function.fellThroughReason, {
      error := SourceTypedRuntime.RuntimeError.functionFellThrough function.table.resultType
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none
    }),
    (function.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none
    })]
  pure { functions, rootTable := { selected.table with reads, additional } }

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- A program read row keeps its original Source identity while the genuine
checked conversion replaces only its reason. The input index is retained. -/
inductive ReadRetokening (first : Nat) :
    List (SourceCoreFaultSites.ReadSite × Nat) → List SourceCoreFaultSites.ReadSite → Prop where
  | nil : ReadRetokening first [] []
  | cons {site index rest result token}
      (issued : Core.Word.ofNat? (first + index) = some token)
      (remaining : ReadRetokening first rest result) :
      ReadRetokening first ((site, index) :: rest) ({ site with reason := token } :: result)

private theorem retoken_receipt {first : Nat} {pairs : List (SourceCoreFaultSites.ReadSite × Nat)}
    {result : List SourceCoreFaultSites.ReadSite}
    (accepted : pairs.mapM (fun (site, index) => do
      let token ← reason (first + index)
      pure { site with reason := token }) = .ok result) : ReadRetokening first pairs result := by
  induction pairs generalizing result with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted; subst result; exact .nil
  | cons pair rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨head, made, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    rcases pair with ⟨site, index⟩
    dsimp only at made
    unfold reason at made
    split at made
    · next token issued =>
      simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at made
      subst head
      exact .cons issued (ih remaining)
    · simp [bind, Except.bind] at made

/-- The selected function retains its actual source preparation, original
retokening, assignment start and both issued boundary identities. -/
inductive FunctionIssuance (first : Nat) (row : SourceSpecialization.SpecializedFunction)
    (own : Function) : Prop where
  | intro {parameter result : TypeSystem.Ty} {base : SourceCoreFaultSites.Table}
      (key : own.key = row.key)
      (functionType : row.function.type = .function parameter result)
      (prepared : SourceCoreFaultSites.prepare row.function.typedBody result = .ok base)
      (reads : ReadRetokening first base.reads.zipIdx own.table.reads)
      (assignments : SourceCoreAssignmentFaultSites.prepare row.function.typedBody
        (first + own.table.reads.length) = .ok own.assignments)
      (fellThrough : Core.Word.ofNat? (first + own.table.reads.length + own.assignments.length) = some own.fellThroughReason)
      (escaped : Core.Word.ofNat? (first + own.table.reads.length + own.assignments.length + 1) = some own.table.escapedReason)
      (owner : own.table.owner = base.owner)
      (resultType : own.table.resultType = base.resultType)
      (additional : own.table.additional = own.assignments.diagnostics) : FunctionIssuance first row own

/-- This static receipt follows the same original ordered program collection. -/
inductive ProgramIssuance : Nat → List SourceSpecialization.SpecializedFunction → List Function → Prop where
  | nil {first} : ProgramIssuance first [] []
  | cons {first row rows own functions}
      (issued : FunctionIssuance first row own)
      (remaining : ProgramIssuance (first + own.table.reads.length + own.assignments.length + 2) rows functions) :
      ProgramIssuance first (row :: rows) (own :: functions)

private theorem reason_ok {index : Nat} {token : Core.Word} (accepted : reason index = .ok token) :
    Core.Word.ofNat? index = some token := by
  unfold reason at accepted
  split at accepted
  · next actual issued => cases accepted; exact issued
  · cases accepted

private theorem collect_issuance {first : Nat} {rows : List SourceSpecialization.SpecializedFunction} {functions : List Function}
    (accepted : collect first rows = .ok functions) : ProgramIssuance first rows functions := by
  induction rows generalizing first functions with
  | nil => simp only [collect, pure, Except.pure, Except.ok.injEq] at accepted; subst functions; exact .nil
  | cons row rows ih =>
    simp only [collect] at accepted
    split at accepted
    · next parameter result functionType =>
      obtain ⟨actualResult, resultMade, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, Except.ok.injEq] at resultMade
      subst actualResult
      obtain ⟨base, baseMade, accepted⟩ := bind_ok accepted
      obtain ⟨reads, readsMade, accepted⟩ := bind_ok accepted
      obtain ⟨assignments, assignmentsMade, accepted⟩ := bind_ok accepted
      obtain ⟨fellThrough, fellMade, accepted⟩ := bind_ok accepted
      obtain ⟨escaped, escapedMade, accepted⟩ := bind_ok accepted
      obtain ⟨remaining, remainingMade, accepted⟩ := bind_ok accepted
      cases accepted
      exact .cons (.intro rfl functionType (mapError_ok baseMade) (retoken_receipt readsMade)
        (mapError_ok assignmentsMade) (reason_ok fellMade) (reason_ok escapedMade) rfl rfl rfl) (ih remainingMade)
    · simp [bind, Except.bind] at accepted

private theorem collect_assignments_member {next : Nat}
    {rows : List SourceSpecialization.SpecializedFunction} {functions : List Function} {own : Function}
    (accepted : collect next rows = .ok functions) (member : own ∈ functions) :
    ∃ row, row ∈ rows ∧ row.key = own.key ∧
      ∃ first, SourceCoreAssignmentFaultSites.prepare row.function.typedBody first = .ok own.assignments := by
  induction rows generalizing next functions with
  | nil =>
    simp only [collect, pure, Except.pure] at accepted
    cases accepted
    simp at member
  | cons row rest ih =>
    simp only [collect] at accepted
    split at accepted
    · obtain ⟨result, _resultMade, accepted⟩ := bind_ok accepted
      obtain ⟨sites, _sitesMade, accepted⟩ := bind_ok accepted
      obtain ⟨reads, _readsMade, accepted⟩ := bind_ok accepted
      obtain ⟨assignments, assignmentsMade, accepted⟩ := bind_ok accepted
      obtain ⟨fellThrough, _fellThroughMade, accepted⟩ := bind_ok accepted
      obtain ⟨escaped, _escapedMade, accepted⟩ := bind_ok accepted
      obtain ⟨remaining, remainingMade, accepted⟩ := bind_ok accepted
      cases accepted
      rcases List.mem_cons.mp member with same | member
      · subst own
        exact ⟨row, List.mem_cons_self, rfl, next + reads.length, mapError_ok assignmentsMade⟩
      · obtain ⟨selected, belongs, key, first, prepared⟩ := ih remainingMade member
        exact ⟨selected, List.mem_cons_of_mem row belongs, key, first, prepared⟩
    · simp [bind, Except.bind] at accepted

private theorem exact_member {plan : Plan} {key : Key}
    {original candidate : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok original)
    (member : candidate ∈ plan.specializations) (same : candidate.key = key) : candidate = original := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have retained : candidate ∈ plan.specializations.filter (fun item => decide (item.key = key)) :=
      List.mem_filter.mpr ⟨member, by simpa using same⟩
    rw [found] at retained
    exact List.mem_singleton.mp retained
  · cases accepted

/-- The actual selected diagnostic row retains the assignment preparation
for its exact specialization Source, including its allocated first token. -/
theorem prepare_assignments_at {plan : Plan} {root key : Key} {diagnostics : Program}
    {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (accepted : prepare plan root = .ok diagnostics)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (found : diagnostics.find? key = some own) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare row.function.typedBody first = .ok own.assignments := by
  unfold prepare at accepted
  obtain ⟨functions, collected, accepted⟩ := bind_ok accepted
  split at accepted
  · obtain ⟨selected, _selectedFound, accepted⟩ := bind_ok accepted
    cases accepted
    have member : own ∈ functions := List.mem_of_find?_eq_some found
    have key : own.key = key := of_decide_eq_true (List.find?_some (p := fun candidate : Function => decide (candidate.key = key)) found)
    obtain ⟨candidate, belongs, same, first, prepared⟩ := collect_assignments_member collected member
    have actual := exact_member record belongs (same.trans key)
    subst candidate
    exact ⟨first, prepared⟩
  · simp [bind, Except.bind] at accepted

/-- Retokening preserves every row's complete Source identity. -/
theorem ReadRetokening.origin {first : Nat} {pairs : List (SourceCoreFaultSites.ReadSite × Nat)}
    {reads : List SourceCoreFaultSites.ReadSite} (receipt : ReadRetokening first pairs reads) :
    ∀ site ∈ reads, ∃ original index,
      (original, index) ∈ pairs ∧ site.expression = original.expression ∧
      site.binder = original.binder ∧ site.span = original.span ∧
      Core.Word.ofNat? (first + index) = some site.reason := by
  induction receipt with
  | nil => intro site member; simp at member
  | @cons original index rest result token issued remaining ih =>
    intro site member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨original, index, List.mem_cons_self, rfl, rfl, rfl, issued⟩
    · obtain ⟨original, index, belongs, expression, binder, span, issued⟩ := ih site member
      exact ⟨original, index, List.mem_cons_of_mem _ belongs, expression, binder, span, issued⟩

/-- Every input row is retained with the same index and exact checked token. -/
theorem ReadRetokening.covers {first : Nat} {pairs : List (SourceCoreFaultSites.ReadSite × Nat)}
    {reads : List SourceCoreFaultSites.ReadSite} (receipt : ReadRetokening first pairs reads) :
    ∀ original index, (original, index) ∈ pairs → ∃ site ∈ reads,
      site.expression = original.expression ∧ site.binder = original.binder ∧
      site.span = original.span ∧ Core.Word.ofNat? (first + index) = some site.reason := by
  induction receipt with
  | nil => intro original index member; simp at member
  | @cons head position rest result token issued remaining ih =>
    intro original index member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact ⟨_, List.mem_cons_self, rfl, rfl, rfl, issued⟩
    · obtain ⟨site, belongs, expression, binder, span, issued⟩ := ih original index member
      exact ⟨site, List.mem_cons_of_mem _ belongs, expression, binder, span, issued⟩

theorem ReadRetokening.length {first : Nat} {pairs : List (SourceCoreFaultSites.ReadSite × Nat)}
    {reads : List SourceCoreFaultSites.ReadSite} (receipt : ReadRetokening first pairs reads) :
    reads.length = pairs.length := by
  induction receipt with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

private theorem program_word_value {number : Nat} {word : Core.Word}
    (accepted : Core.Word.ofNat? number = some word) : word.val = number := by
  unfold Core.Word.ofNat? at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

/-- Checked program read tokens occupy exactly their genuine input interval. -/
theorem ReadRetokening.bounds {first : Nat} {original reads : List SourceCoreFaultSites.ReadSite}
    (receipt : ReadRetokening first original.zipIdx reads) :
    ∀ site ∈ reads, first ≤ site.reason.val ∧ site.reason.val < first + reads.length := by
  intro site member
  obtain ⟨before, index, belongs, _expression, _binder, _span, issued⟩ := receipt.origin site member
  have bound := List.snd_lt_of_mem_zipIdx belongs
  have number := program_word_value issued
  have count : reads.length = original.length := by simpa only [List.length_zipIdx] using receipt.length
  simp only [Nat.add_zero] at bound
  omega

/-- An actual selected function retains its precise row and allocated start. -/
theorem ProgramIssuance.member {first : Nat} {rows : List SourceSpecialization.SpecializedFunction}
    {functions : List Function} (receipt : ProgramIssuance first rows functions) :
    ∀ own ∈ functions, ∃ row ∈ rows, ∃ start, first ≤ start ∧ FunctionIssuance start row own := by
  induction receipt with
  | nil => intro own member; simp at member
  | @cons first row rows own functions issued remaining ih =>
    intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨row, List.mem_cons_self, first, Nat.le_refl _, issued⟩
    · obtain ⟨row, belongs, start, bound, issued⟩ := ih selected member
      exact ⟨row, List.mem_cons_of_mem _ belongs, start, by omega, issued⟩

/-- The original program preparation retains its actual ordered rows, selected
root, full read inventory and exact boundary diagnostics. -/
theorem prepare_issuance {plan : Plan} {root : Key} {diagnostics : Program}
    (accepted : prepare plan root = .ok diagnostics) :
    ∃ selected,
      ProgramIssuance 1 plan.specializations diagnostics.functions ∧
      diagnostics.functions.find? (fun function => decide (function.key = root)) = some selected ∧
      diagnostics.rootTable = { selected.table with
        reads := diagnostics.functions.flatMap (·.table.reads)
        additional := diagnostics.functions.flatMap (fun function => function.assignments.diagnostics ++ [
          (function.fellThroughReason, {
            error := SourceTypedRuntime.RuntimeError.functionFellThrough function.table.resultType
            site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
            span := none }),
          (function.table.escapedReason, {
            error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
            site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
            span := none })]) } := by
  unfold prepare at accepted
  obtain ⟨functions, collected, accepted⟩ := bind_ok accepted
  split at accepted
  · next selected found =>
    obtain ⟨actualSelected, same, accepted⟩ := bind_ok accepted
    cases same
    cases accepted
    exact ⟨selected, collect_issuance collected, found, rfl⟩
  · simp [bind, Except.bind] at accepted

/-- Canonical specialization selection exposes its original read preparation
and checked program retokening, rather than recovering Source from native code. -/
theorem prepare_function_issuance {plan : Plan} {root key : Key} {diagnostics : Program}
    {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (accepted : prepare plan root = .ok diagnostics)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (found : diagnostics.find? key = some own) :
    ∃ first, 0 < first ∧ FunctionIssuance first row own := by
  obtain ⟨_selected, collection, _found, _table⟩ := prepare_issuance accepted
  have member : own ∈ diagnostics.functions := List.mem_of_find?_eq_some found
  have foundKey : own.key = key := of_decide_eq_true
    (List.find?_some (p := fun candidate : Function => decide (candidate.key = key)) found)
  obtain ⟨candidate, belongs, first, positive, issued⟩ := collection.member own member
  have sameKey : candidate.key = key := by cases issued with | intro same _ _ _ _ _ _ _ _ _ => exact same.symm.trans foundKey
  have same := exact_member record belongs sameKey
  subst candidate
  exact ⟨first, by omega, issued⟩

/-- Distinct original indices give distinct checked read reasons. -/
theorem ReadRetokening.unique_reasons {first : Nat} {original reads : List SourceCoreFaultSites.ReadSite}
    (receipt : ReadRetokening first original.zipIdx reads) :
    ∀ left ∈ reads, ∀ right ∈ reads, left.reason = right.reason → left = right := by
  intro left leftMember right rightMember same
  obtain ⟨beforeLeft, leftIndex, leftPair, leftExpression, leftBinder, leftSpan, leftIssued⟩ := receipt.origin left leftMember
  obtain ⟨beforeRight, rightIndex, rightPair, rightExpression, rightBinder, rightSpan, rightIssued⟩ := receipt.origin right rightMember
  have leftNumber := program_word_value leftIssued
  have rightNumber := program_word_value rightIssued
  have equal := congrArg Fin.val same
  have indices : leftIndex = rightIndex := by omega
  subst rightIndex
  have originals : beforeLeft = beforeRight := Option.some.inj
    ((List.mk_mem_zipIdx_iff_getElem?.mp leftPair).symm.trans (List.mk_mem_zipIdx_iff_getElem?.mp rightPair))
  subst beforeRight
  have expression := leftExpression.trans rightExpression.symm
  have binder := leftBinder.trans rightBinder.symm
  have span := leftSpan.trans rightSpan.symm
  cases left
  cases right
  dsimp only at expression binder span same
  cases expression
  cases binder
  cases span
  cases same
  rfl

private def boundaries (function : Function) : List (Core.Word × SourceCoreFaultSites.Diagnostic) :=
  function.assignments.diagnostics ++ [
    (function.fellThroughReason, {
      error := SourceTypedRuntime.RuntimeError.functionFellThrough function.table.resultType
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none }),
    (function.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none })]

private theorem FunctionIssuance.ranges {first : Nat} {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (receipt : FunctionIssuance first row own) :
    (∀ site ∈ own.table.reads, first ≤ site.reason.val ∧ site.reason.val < first + own.table.reads.length) ∧
    (∀ pair ∈ boundaries own, first + own.table.reads.length ≤ pair.1.val ∧
      pair.1.val < first + own.table.reads.length + own.assignments.length + 2) ∧
    (∀ left ∈ own.table.reads, ∀ right ∈ own.table.reads, left.reason = right.reason → left = right) := by
  cases receipt with
  | intro _ _ _ reads assignments fell escaped _ _ _ =>
    refine ⟨reads.bounds, ?_, reads.unique_reasons⟩
    intro pair member
    have assigned := (SourceCoreAssignmentFaultSites.prepare_token_range assignments).2.1
    have fellNumber := program_word_value fell
    have escapedNumber := program_word_value escaped
    rcases List.mem_append.mp member with member | member
    · have bounds := assigned pair member; exact ⟨bounds.1, by omega⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> dsimp only <;> omega

private structure ProgramReadInventory (first : Nat) (functions : List Function) : Prop where
  readsBelow : ∀ site ∈ functions.flatMap (·.table.reads), first ≤ site.reason.val
  boundariesBelow : ∀ pair ∈ functions.flatMap boundaries, first ≤ pair.1.val
  unique : ∀ left ∈ functions.flatMap (·.table.reads), ∀ right ∈ functions.flatMap (·.table.reads),
    left.reason = right.reason → left = right
  separate : ∀ site ∈ functions.flatMap (·.table.reads), ∀ pair ∈ functions.flatMap boundaries,
    site.reason ≠ pair.1

private theorem ProgramIssuance.inventory {first : Nat} {rows : List SourceSpecialization.SpecializedFunction}
    {functions : List Function} (receipt : ProgramIssuance first rows functions) : ProgramReadInventory first functions := by
  induction receipt with
  | nil => constructor <;> simp
  | @cons first row rows own functions issued remaining ih =>
    obtain ⟨ownReads, ownBoundaries, ownUnique⟩ := issued.ranges
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro site member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · exact (ownReads site member).1
      · have bound := ih.readsBelow site member; omega
    · intro pair member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · have bound := ownBoundaries pair member; omega
      · have bound := ih.boundariesBelow pair member; omega
    · intro left leftMember right rightMember same
      simp only [List.flatMap_cons, List.mem_append] at leftMember rightMember
      rcases leftMember with leftMember | leftMember
      · rcases rightMember with rightMember | rightMember
        · exact ownUnique left leftMember right rightMember same
        · have leftBound := ownReads left leftMember
          have rightBound := ih.readsBelow right rightMember
          have equal := congrArg Fin.val same; omega
      · rcases rightMember with rightMember | rightMember
        · have rightBound := ownReads right rightMember
          have leftBound := ih.readsBelow left leftMember
          have equal := congrArg Fin.val same; omega
        · exact ih.unique left leftMember right rightMember same
    · intro site siteMember pair pairMember same
      simp only [List.flatMap_cons, List.mem_append] at siteMember pairMember
      rcases siteMember with siteMember | siteMember
      · have readBound := ownReads site siteMember
        rcases pairMember with pairMember | pairMember
        · have bound := ownBoundaries pair pairMember
          have equal := congrArg Fin.val same; omega
        · have bound := ih.boundariesBelow pair pairMember
          have equal := congrArg Fin.val same; omega
      · have readBound := ih.readsBelow site siteMember
        rcases pairMember with pairMember | pairMember
        · have bound := ownBoundaries pair pairMember
          have equal := congrArg Fin.val same; omega
        · exact ih.separate site siteMember pair pairMember same

private theorem program_find_read_unique {α : Type} [DecidableEq α]
    {sites : List SourceCoreFaultSites.ReadSite} {site : SourceCoreFaultSites.ReadSite}
    (key : SourceCoreFaultSites.ReadSite → α) (member : site ∈ sites)
    (unique : ∀ candidate ∈ sites, key candidate = key site → candidate = site) :
    sites.find? (fun candidate => decide (key candidate = key site)) = some site := by
  induction sites with
  | nil => simp at member
  | cons head tail ih =>
    by_cases sameKey : key head = key site
    · have same := unique head List.mem_cons_self sameKey
      simp [same]
    · have tailMember : site ∈ tail := by
        rcases List.mem_cons.mp member with same | member
        · exact (sameKey (same ▸ rfl)).elim
        · exact member
      simpa only [List.find?_cons, decide_eq_false_iff_not.mpr sameKey, Bool.false_eq_true, ↓reduceIte] using
        ih tailMember (fun candidate belongs => unique candidate (List.mem_cons_of_mem head belongs))

/-- Actual program preparation prevents every read token from being shadowed
by another read, assignment, function fallthrough or escaped-control row. -/
theorem prepare_read_diagnostic {plan : Plan} {root : Key} {diagnostics : Program}
    (accepted : prepare plan root = .ok diagnostics)
    {site : SourceCoreFaultSites.ReadSite} (member : site ∈ diagnostics.rootTable.reads) :
    site.reason ≠ Core.Word.zero ∧ site.reason ≠ diagnostics.rootTable.escapedReason ∧
    diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = site.reason)) = none ∧
    diagnostics.rootTable.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site ∧
    diagnostics.rootTable.diagnostic? site.reason = some {
      error := SourceTypedRuntime.RuntimeError.uninitializedLocal site.binder
      site := SourceCoreElaboration.ErrorSite.occurrence site.expression.occurrence
      span := some site.span } := by
  obtain ⟨selected, collection, found, table⟩ := prepare_issuance accepted
  have reads : diagnostics.rootTable.reads = diagnostics.functions.flatMap (·.table.reads) := congrArg (·.reads) table
  have additional : diagnostics.rootTable.additional = diagnostics.functions.flatMap boundaries := congrArg (·.additional) table
  have escaped : diagnostics.rootTable.escapedReason = selected.table.escapedReason := congrArg (·.escapedReason) table
  have inventory := collection.inventory
  have belongs : site ∈ diagnostics.functions.flatMap (·.table.reads) := reads ▸ member
  have positive : site.reason ≠ Core.Word.zero := by
    intro same
    have bound := inventory.readsBelow site belongs
    have number := congrArg Fin.val same
    change site.reason.val = 0 at number
    omega
  have selectedMember : selected ∈ diagnostics.functions := List.mem_of_find?_eq_some found
  have escapedMember : (selected.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration selected.table.owner
      span := none }) ∈ diagnostics.functions.flatMap boundaries :=
    List.mem_flatMap.mpr ⟨selected, selectedMember, by simp [boundaries]⟩
  have ordinary : site.reason ≠ diagnostics.rootTable.escapedReason := by
    rw [escaped]
    exact inventory.separate site belongs _ escapedMember
  have noAdditional : diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = site.reason)) = none := by
    rw [additional]
    simp only [List.find?_eq_none]
    intro candidate candidateMember same
    exact inventory.separate site belongs candidate candidateMember (of_decide_eq_true same).symm
  have byReason : diagnostics.rootTable.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site :=
    program_find_read_unique (·.reason) member (fun candidate candidateMember same =>
      inventory.unique candidate (reads ▸ candidateMember) site belongs same)
  exact ⟨positive, ordinary, noAdditional, byReason,
    SourceCoreFaultSites.Table.read_diagnostic positive ordinary noAdditional byReason⟩

/-- A genuine Source local-read occurrence selects its actual globally
retokened row and restores the same binder, occurrence and span. -/
theorem prepare_local_read {plan : Plan} {root key : Key} {diagnostics : Program}
    {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (accepted : prepare plan root = .ok diagnostics)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (found : diagnostics.find? key = some own)
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (member : .expression node ∈ row.function.typedBody.nodes)
    (form : node.form = .reference name (.local binder)) :
    ∃ site,
      own.table.reads.find? (fun candidate => decide (candidate.expression = node.id)) = some site ∧
      site.expression = node.id ∧ site.binder = binder ∧ site.span = node.span ∧
      own.table.reasonAt node.id = site.reason ∧
      site ∈ diagnostics.rootTable.reads ∧
      site.reason ≠ Core.Word.zero ∧ site.reason ≠ diagnostics.rootTable.escapedReason ∧
      diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = site.reason)) = none ∧
      diagnostics.rootTable.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site ∧
      diagnostics.rootTable.diagnostic? site.reason = some {
        error := SourceTypedRuntime.RuntimeError.uninitializedLocal binder
        site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
        span := some node.span } := by
  obtain ⟨first, _positive, issuance⟩ := prepare_function_issuance accepted record found
  cases issuance with
  | @intro parameter result base _key _functionType prepared retokened _assignments _fell _escaped _owner _result _additional =>
    obtain ⟨original, originalFound, originalExpression, originalBinder, originalSpan, _reason, _positive, _ordinary, _byReason, _diagnostic⟩ :=
      SourceCoreFaultSites.prepare_local_read prepared member form
    have originalMember : original ∈ base.reads := List.mem_of_find?_eq_some originalFound
    have zipped : original ∈ base.reads.zipIdx.map Prod.fst := by
      rw [List.zipIdx_map_fst]; exact originalMember
    obtain ⟨pair, pairMember, pairEq⟩ := List.mem_map.mp zipped
    rcases pair with ⟨before, index⟩
    dsimp only at pairEq
    subst before
    obtain ⟨reached, reachedMember, reachedExpression, _binder, _span, _issued⟩ := retokened.covers original index pairMember
    have existsFound : ∃ site, own.table.reads.find? (fun candidate => decide (candidate.expression = node.id)) = some site := by
      cases selected : own.table.reads.find? (fun candidate => decide (candidate.expression = node.id)) with
      | some site => exact ⟨site, rfl⟩
      | none =>
        have absent := List.find?_eq_none.mp selected reached reachedMember
        exact (absent (by simp only [reachedExpression, originalExpression, decide_true])).elim
    obtain ⟨site, selected⟩ := existsFound
    have selectedMember : site ∈ own.table.reads := List.mem_of_find?_eq_some selected
    have expression : site.expression = node.id := of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreFaultSites.ReadSite => decide (candidate.expression = node.id)) selected)
    obtain ⟨before, index, belongs, beforeExpression, beforeBinder, beforeSpan, _issued⟩ := retokened.origin site selectedMember
    have beforeMember := List.fst_mem_of_mem_zipIdx belongs
    have same : before = original := SourceCoreFaultSites.prepare_read_occurrences_unique prepared
      before beforeMember original originalMember (beforeExpression.symm.trans (expression.trans originalExpression.symm))
    subst before
    have binderEq := beforeBinder.trans originalBinder
    have spanEq := beforeSpan.trans originalSpan
    obtain ⟨_root, _collection, _selectedRoot, table⟩ := prepare_issuance accepted
    have ownMember : own ∈ diagnostics.functions := List.mem_of_find?_eq_some found
    have reads : diagnostics.rootTable.reads = diagnostics.functions.flatMap (·.table.reads) := congrArg (·.reads) table
    have rootMember : site ∈ diagnostics.rootTable.reads := by
      rw [reads]; exact List.mem_flatMap.mpr ⟨own, ownMember, selectedMember⟩
    obtain ⟨positive, ordinary, noAdditional, byReason, diagnostic⟩ := prepare_read_diagnostic accepted rootMember
    refine ⟨site, selected, expression, binderEq, spanEq, ?_, rootMember, positive, ordinary, noAdditional, byReason, ?_⟩
    · unfold SourceCoreFaultSites.Table.reasonAt; rw [selected]
    · simpa only [expression, binderEq, spanEq] using diagnostic

end Solcore.Frontend.SourceCoreProgramFaultSites
