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

end Solcore.Frontend.SourceCoreProgramFaultSites
