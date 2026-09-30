import Solcore.Frontend.SourceCoreStageCodebook
import Solcore.Core.CallableContract

/-! Translate authenticated finite source contracts to ordinary Core gates.
The source compiler selects an exact original callable origin; public function
values keep this descriptor hidden inside artifact-owned handles. This module
does not authenticate arbitrary Core closure code against a chosen source
origin, and does not expose a public runtime handle constructor.

The codebook keeps exact source diagnostics until the artifact assigns language
reason words. Native gate selection preserves those words and has no store
effects. Whole source meaning preservation and the dynamic stage-guard source
specification remain separate proof boundaries. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCallableContracts

open SourceInference
abbrev Key := SourceCoreStageCodebook.Key
abbrev Origin := SourceCoreStageCodebook.Origin
abbrev Table := SourceCoreStageCodebook.Table
abbrev Decision := SourceCoreStageCodebook.Decision
abbrev RuntimeError := SourceCoreStageCodebook.RuntimeError
abbrev Phase := Core.CallableContract.Phase

/-- The artifact's codebook assigns words once. Phase and contract ID remain
available when registering/restoring the exact caller/use/callee diagnostic. -/
abbrev ReasonAt := Key → ExpressionId → Core.Word → Phase → RuntimeError → Core.Word

inductive Error where
  | missingOrigin (origin : Origin)
  | missingCallsite (caller : Key) (call : ExpressionId)
  deriving Repr

structure Descriptor (table : Table) (origin : Origin) where private mk ::
  id : Core.Word
  found : table.idAt? origin = some id

def descriptor (table : Table) (origin : Origin) : Except Error (Descriptor table origin) :=
  match found : table.idAt? origin with
  | none => .error (.missingOrigin origin)
  | some id => .ok (.mk id found)

namespace Descriptor

def wrap {table : Table} {origin : Origin} (descriptor : Descriptor table origin) (function : Core.Expr) : Core.Expr :=
  Core.CallableContract.wrap descriptor.id function

theorem wrap_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {table : Table} {origin : Origin} {parameter result : Core.Ty} {function : Core.Expr}
    (descriptor : Descriptor table origin)
    (typed : Core.HasType context function (Core.TaggedFunction.functionType parameter result) definitions) :
    Core.HasType context (descriptor.wrap function) (Core.CallableContract.functionType parameter result) definitions :=
  Core.CallableContract.wrap_hasType descriptor.id typed

theorem wrap_evaluates {table : Table} {origin : Origin} {environment : Core.Environment}
    {before after : Core.Store} {function : Core.Expr} {value : Core.Value}
    (descriptor : Descriptor table origin)
    (evaluation : Core.Evaluates environment before function value after) :
    Core.Evaluates environment before (descriptor.wrap function) (.pair value (.word descriptor.id)) after :=
  Core.CallableContract.wrap_evaluates descriptor.id evaluation

end Descriptor

def phaseAnswer (row : Decision) : Phase → Except RuntimeError Unit
  | .beforeArguments => row.beforeArguments
  | .beforeApplication => row.afterArguments

def reason (row : Decision) (reasonAt : ReasonAt) (phase : Phase) : Option Core.Word :=
  match phaseAnswer row phase with
  | .ok () => none
  | .error error => some (reasonAt row.caller row.call row.entry.id phase error)

def gate (row : Decision) (reasonAt : ReasonAt) : Core.CallableContract.Gate := {
  contract := row.entry.id
  beforeArguments := reason row reasonAt .beforeArguments
  beforeApplication := reason row reasonAt .beforeApplication
}

theorem gate_reason (row : Decision) (reasonAt : ReasonAt) (phase : Phase) :
    (gate row reasonAt).reason phase = reason row reasonAt phase := by cases phase <;> rfl

theorem gate_contract (row : Decision) (reasonAt : ReasonAt) :
    (gate row reasonAt).contract = row.entry.id := rfl

theorem reason_accepted (row : Decision) (reasonAt : ReasonAt) (phase : Phase)
    (accepted : phaseAnswer row phase = .ok ()) : reason row reasonAt phase = none := by
  simp only [reason, accepted]

theorem reason_rejected (row : Decision) (reasonAt : ReasonAt) (phase : Phase) (error : RuntimeError)
    (rejected : phaseAnswer row phase = .error error) :
    reason row reasonAt phase = some (reasonAt row.caller row.call row.entry.id phase error) := by
  simp only [reason, rejected]

structure Callsite where private mk ::
  table : Table
  caller : Key
  call : ExpressionId
  reasonAt : ReasonAt
  present : table.casesAt caller call ≠ []

def prepareCallsite (table : Table) (caller : Key) (call : ExpressionId) (reasonAt : ReasonAt) : Except Error Callsite :=
  if present : table.casesAt caller call ≠ [] then .ok (.mk table caller call reasonAt present)
  else .error (.missingCallsite caller call)

namespace Callsite

def rows (site : Callsite) : List Decision := site.table.casesAt site.caller site.call
def gates (site : Callsite) : List Core.CallableContract.Gate := site.rows.map (fun row => gate row site.reasonAt)
def rowAt? (site : Callsite) (id : Core.Word) : Option Decision :=
  site.rows.find? (fun row => id == row.entry.id)

private theorem decision_rows (rows : List Decision) (reasonAt : ReasonAt) (phase : Phase) (unknown id : Core.Word) :
    Core.CallableContract.decision (rows.map (fun row => gate row reasonAt)) phase unknown id =
      match rows.find? (fun row => id == row.entry.id) with
      | none => some unknown
      | some row => reason row reasonAt phase := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases same : (id == row.entry.id) <;>
        simp only [List.map_cons, Core.CallableContract.decision, gate_contract, same,
          Bool.false_eq_true, ↓reduceIte, List.find?_cons, ih, gate_reason]

theorem decision_known (site : Callsite) (phase : Phase) (unknown id : Core.Word) (row : Decision)
    (found : site.rowAt? id = some row) :
    Core.CallableContract.decision site.gates phase unknown id = reason row site.reasonAt phase := by
  have evaluated := decision_rows site.rows site.reasonAt phase unknown id
  change site.rows.find? (fun row => id == row.entry.id) = some row at found
  simpa only [gates, found] using evaluated

theorem decision_unknown (site : Callsite) (phase : Phase) (unknown id : Core.Word)
    (missing : site.rowAt? id = none) :
    Core.CallableContract.decision site.gates phase unknown id = some unknown := by
  have evaluated := decision_rows site.rows site.reasonAt phase unknown id
  change site.rows.find? (fun row => id == row.entry.id) = none at missing
  simpa only [gates, missing] using evaluated

def lower (site : Callsite) (unknown : Core.Word) (result : Core.Ty) (callee arguments : Core.Expr) : Core.Expr :=
  Core.CallableContract.call site.gates unknown result callee arguments

theorem lower_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {parameter result : Core.Ty} {callee arguments : Core.Expr} (site : Callsite) (unknown : Core.Word)
    (wellFormed : Core.Ty.WellFormed definitions result)
    (calleeTyped : Core.HasType context callee
      (Core.LanguageResult.resultType (Core.CallableContract.functionType parameter result)) definitions)
    (argumentsTyped : Core.HasType context arguments (Core.LanguageResult.resultType parameter) definitions) :
    Core.HasType context (site.lower unknown result callee arguments) (Core.LanguageResult.resultType result) definitions :=
  Core.CallableContract.call_hasType site.gates unknown wellFormed calleeTyped argumentsTyped

theorem dispatch_known {environment : Core.Environment} {store : Core.Store} {expression : Core.Expr}
    (site : Callsite) (phase : Phase) (unknown id : Core.Word) (row : Decision)
    (found : site.rowAt? id = some row)
    (read : Core.Evaluates environment store expression (.word id) store) :
    Core.Evaluates environment store (Core.CallableContract.dispatch site.gates phase unknown expression)
      (Core.CallableContract.resultValue (reason row site.reasonAt phase)) store := by
  simpa only [site.decision_known phase unknown id row found] using
    Core.CallableContract.dispatch_evaluates site.gates phase unknown id read

theorem lower_stage_failure {environment : Core.Environment} {before after : Core.Store}
    {result : Core.Ty} {callee arguments : Core.Expr} {function : Core.Value} {id : Core.Word}
    (site : Callsite) (unknown : Core.Word) (row : Decision) (error : RuntimeError)
    (found : site.rowAt? id = some row) (rejected : row.beforeArguments = .error error)
    (evaluation : Core.Evaluates environment before callee (.inRight .word (.pair function (.word id))) after) :
    Core.Evaluates environment before (site.lower unknown result callee arguments)
      (.inLeft result (.word (site.reasonAt row.caller row.call row.entry.id .beforeArguments error))) after := by
  apply Core.CallableContract.call_stage_failure site.gates unknown evaluation
  rw [site.decision_known .beforeArguments unknown id row found]
  exact reason_rejected row site.reasonAt .beforeArguments error rejected

theorem lower_arity_failure {environment : Core.Environment} {before middle after : Core.Store}
    {result : Core.Ty} {callee arguments : Core.Expr} {function argument : Core.Value} {id : Core.Word}
    (site : Callsite) (unknown : Core.Word) (row : Decision) (error : RuntimeError)
    (found : site.rowAt? id = some row)
    (accepted : row.beforeArguments = .ok ()) (rejected : row.afterArguments = .error error)
    (calleeEvaluation : Core.Evaluates environment before callee (.inRight .word (.pair function (.word id))) middle)
    (argumentsEvaluation : Core.Evaluates (.unit :: .pair function (.word id) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inRight .word argument) after) :
    Core.Evaluates environment before (site.lower unknown result callee arguments)
      (.inLeft result (.word (site.reasonAt row.caller row.call row.entry.id .beforeApplication error))) after := by
  have stageAccepted : Core.CallableContract.decision site.gates .beforeArguments unknown id = none := by
    rw [site.decision_known .beforeArguments unknown id row found]
    exact reason_accepted row site.reasonAt .beforeArguments accepted
  have arityRejected : Core.CallableContract.decision site.gates .beforeApplication unknown id =
      some (site.reasonAt row.caller row.call row.entry.id .beforeApplication error) := by
    rw [site.decision_known .beforeApplication unknown id row found]
    exact reason_rejected row site.reasonAt .beforeApplication error rejected
  exact Core.CallableContract.call_arity_failure site.gates unknown calleeEvaluation stageAccepted argumentsEvaluation arityRejected

end Callsite

end Solcore.Frontend.SourceCoreCallableContracts
