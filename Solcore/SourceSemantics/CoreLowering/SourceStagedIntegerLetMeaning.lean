import Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
import Solcore.SourceSemantics.CoreLowering.SourceStagingHeapRelation

/-! One accepted Integer let is erased from the resolved body while its source
execution allocates an ordinary Integer cell. Recursive body correctness is a
separate structural obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerLetMeaning
open Frontend SourceInference SourceCoreElaboration
open SourceStagedClosedEvaluationMeaning SourceStagedIntegerStatementsMeaning
open SourceCoreElaboration.Internal

section Step
variable {program : Program} {context next : Context} {evidence : Dynamic.EvidenceEnvironment}
    {solved : List SolvedRequirement} {source : TypedSource} {scope : Resolved.Context}
    {actual : Staged.Environment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    {fuel : Nat} {expected : Core.Ty} {site : ErrorSite} {reason : ErrorReason}
    {statement : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {result : LoweredExpression}

/-- The actual compiler receipt and the independently typed source allocation
share the same initializer and full source heap. No tail execution law is used. -/
theorem let_source_step
    (receipt : Staged.IntegerLet.LetAccepted solved source scope actual fuel expected site reason
      statement rest node binder initializer result)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements)
    (extension : BinderExtends source.owner context binder next) :
    ∃ initial body location after,
      Staged.integer solved source actual true fuel initializer = .ok initial ∧
      Staged.IntegerLet.lower solved source scope (Staged.Statements.bind binder initial.value :: actual)
        fuel expected site reason rest = .ok body ∧
      result.resolved = body.resolved ∧
      result.consumedRequirements = initial.consumedRequirements ++ body.consumedRequirements ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer (.integer initial.value) before ∧
      Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after ∧
      Dynamic.StatementExecutes program context evidence source environment before statement next
        (.fallthrough ((binder.id, location) :: environment)) after ∧
      EnvironmentRep (Staged.Statements.bind binder initial.value :: actual)
        ((binder.id, location) :: environment) after ∧
      Extends before after [initial.value] := by
  cases receipt with
  | intro found form unit scopeFresh environmentFresh owned monomorphic binderType initialAccepted initialChecked bodyAccepted output =>
      rename_i initial body
      have used : UsedValid context solved initial.consumedRequirements := by
        apply valid.mono
        intro id member
        rw [output]
        exact List.mem_append_left _ member
      have evaluated := (checked_meaning (program := program) (evidence := evidence) ledger environments fuel).1 initialChecked used
      let location : Dynamic.Location := ⟨before.cells.length⟩
      let after : Dynamic.Heap := ⟨before.cells ++ [integerCell initial.value]⟩
      have allocated : Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after := .append
      have bound : Dynamic.Binds environment before binder.id .integer (some (.integer initial.value))
          ((binder.id, location) :: environment) after := .intro allocated
      have represented := SourceStagedIntegerStatementsMeaning.EnvironmentRep.bind
        (Staged.Statements.bind binder initial.value) environments bound
      refine ⟨initial, body, location, after, initialAccepted, bodyAccepted,
        (by simpa using congrArg (fun r : LoweredExpression => r.resolved) output),
        (by simpa using congrArg (fun r : LoweredExpression => r.consumedRequirements) output),
        evaluated, allocated, ?_, represented, ?_⟩
      · exact .letInitialized (lookupStatement?_sound found) form evaluated monomorphic extension (binderType ▸ allocated)
      · simpa using (Extends.refl before).allocate allocated

/-- Acceptance supplies the initializer certificate; source typing supplies the
binder extension. These two facts are kept independent. -/
theorem let_of_accepted
    (accepted : Staged.IntegerLet.lower solved source scope actual (fuel + 1) expected site reason
      (statement :: rest) = .ok result)
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .letDecl binder (some initializer))
    (binderType : binder.scheme.body = .integer)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements)
    (extension : BinderExtends source.owner context binder next) :
    ∃ initial body location after,
      Staged.IntegerLet.LetAccepted solved source scope actual fuel expected site reason
        statement rest node binder initializer result ∧
      Staged.integer solved source actual true fuel initializer = .ok initial ∧
      Staged.IntegerLet.lower solved source scope (Staged.Statements.bind binder initial.value :: actual)
        fuel expected site reason rest = .ok body ∧
      result.resolved = body.resolved ∧
      result.consumedRequirements = initial.consumedRequirements ++ body.consumedRequirements ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer (.integer initial.value) before ∧
      Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after ∧
      Dynamic.StatementExecutes program context evidence source environment before statement next
        (.fallthrough ((binder.id, location) :: environment)) after ∧
      EnvironmentRep (Staged.Statements.bind binder initial.value :: actual)
        ((binder.id, location) :: environment) after ∧ Extends before after [initial.value] := by
  have receipt := Staged.IntegerLet.let_of_accepted accepted found form binderType
  obtain ⟨initial, body, location, after, step⟩ := let_source_step (program := program) (evidence := evidence)
    receipt ledger environments valid extension
  exact ⟨initial, body, location, after, receipt, step⟩

/-- Actual source typing yields the exact extension used by the accepted head.
No source-context freshness follows merely from the compiler's duplicate check. -/
theorem typed_extension {control : ControlContext} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = [])
    (typed : StatementHasType source control context statement next facts) :
    BinderExtends source.owner context binder next :=
  StaticViews.typed_let unique found form mono typed
end Step

/-- A public draft whose first source statement is an Integer let reaches the
same erased head. The returned draft keeps its complete unconsumed remainder. -/
theorem function_head_source_step
    {program : Program} {function : CheckedFunction} {draft : BodyDraft}
    {context next : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap}
    {statement : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId}
    (accepted : lowerFunctionBody function = .ok draft)
    (roots : function.typedBody.roots = (statement :: rest).map NodeId.statement)
    (found : function.typedBody.lookupStatement? statement = some node)
    (form : node.form = .letDecl binder (some initializer))
    (binderType : binder.scheme.body = .integer)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (extension : BinderExtends function.typedBody.owner context binder next) :
    Staged.IntegerLet.FunctionAccepted function draft ∧
    ∃ initial body location after,
      Staged.integer function.solvedRequirements function.typedBody [] true function.typedBody.nodes.length initializer = .ok initial ∧
      Staged.IntegerLet.lower function.solvedRequirements function.typedBody draft.inputs
        [Staged.Statements.bind binder initial.value] function.typedBody.nodes.length draft.returnType
        (match Staged.IntegerLet.lastStatement (statement :: rest) with
          | some last => .occurrence last.occurrence | none => .declaration function.declaration)
        .statementListFallthrough rest = .ok body ∧
      draft.resolved = body.resolved ∧
      reconcileConsumedRequirements function.declaration (function.solvedRequirements.map (·.id))
        (initial.consumedRequirements ++ body.consumedRequirements) = .ok draft.unconsumedRequirements ∧
      Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after ∧
      Dynamic.StatementExecutes program context evidence function.typedBody environment before statement next
        (.fallthrough ((binder.id, location) :: environment)) after ∧
      EnvironmentRep [Staged.Statements.bind binder initial.value] ((binder.id, location) :: environment) after ∧
      Extends before after [initial.value] := by
  have receipt := Staged.IntegerLet.function_of_accepted accepted
  refine ⟨receipt, ?_⟩
  cases receipt with
  | intro owned rootsAccepted rootsSame nonempty inputsAccepted expectedAccepted bodyAccepted reconciled declaration inputEq resolved returnType rootOccurrence =>
      rename_i statements head tail inputs expected lowered
      rw [nonempty] at rootsSame bodyAccepted
      have same : head :: tail = statement :: rest :=
        (List.map_inj_right (fun a b h => NodeId.statement.inj h)).mp (rootsSame.trans roots)
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      have used : UsedValid context function.solvedRequirements lowered.consumedRequirements := by
        intro row proof member consumed implementation
        exact valid row proof member (List.mem_map.mpr ⟨row, member, rfl⟩) implementation
      have letReceipt := Staged.IntegerLet.let_of_accepted bodyAccepted found form binderType
      obtain ⟨initial, body, location, after, initialEq, bodyEq, resultEq, consumedEq, evaluated,
        allocated, executed, represented, cells⟩ := let_source_step (program := program) (evidence := evidence)
          letReceipt ledger (EnvironmentRep.empty environment before) used extension
      refine ⟨initial, body, location, after, initialEq, ?_, resolved.trans resultEq, ?_, allocated, executed, represented, cells⟩
      · cases lastEq : Staged.IntegerLet.lastStatement (head :: tail) <;>
          simpa only [inputEq, returnType, lastEq] using bodyEq
      · exact consumedEq ▸ reconciled


/-- The actual accepted let authorizes exactly this source-only Integer cell.
The residual heap and every retained cell/capture remain related by the fixed
structural relation. The ordinary closed source step needs no mapping premise. -/
theorem let_erased_step
    {program : Program} {context next : Context} {evidence : Dynamic.EvidenceEnvironment}
    {solved : List SolvedRequirement} {source : TypedSource} {scope : Resolved.Context}
    {actual : Staged.Environment} {environment : Dynamic.Environment} {before residual : Dynamic.Heap}
    {mapping : SourceStagingHeapRelation.LocationMap}
    {fuel : Nat} {expected : Core.Ty} {site : ErrorSite} {reason : ErrorReason}
    {statement : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {result : LoweredExpression}
    (receipt : Staged.IntegerLet.LetAccepted solved source scope actual fuel expected site reason
      statement rest node binder initializer result)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements)
    (extension : BinderExtends source.owner context binder next)
    (related : SourceStagingHeapRelation.HeapRel mapping before residual) :
    ∃ initial body location after,
      Staged.integer solved source actual true fuel initializer = .ok initial ∧
      Staged.IntegerLet.lower solved source scope (Staged.Statements.bind binder initial.value :: actual)
        fuel expected site reason rest = .ok body ∧
      result.resolved = body.resolved ∧
      result.consumedRequirements = initial.consumedRequirements ++ body.consumedRequirements ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer (.integer initial.value) before ∧
      Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location after ∧
      Dynamic.StatementExecutes program context evidence source environment before statement next
        (.fallthrough ((binder.id, location) :: environment)) after ∧
      EnvironmentRep (Staged.Statements.bind binder initial.value :: actual)
        ((binder.id, location) :: environment) after ∧
      Extends before after [initial.value] ∧
      SourceStagingHeapRelation.HeapRel (mapping ++ [none]) after residual := by
  obtain ⟨initial, body, location, after, initialEq, bodyEq, output, consumed, evaluated,
    allocated, executed, represented, cells⟩ := let_source_step (program := program) (evidence := evidence)
      receipt ledger environments valid extension
  exact ⟨initial, body, location, after, initialEq, bodyEq, output, consumed, evaluated,
    allocated, executed, represented, cells, related.erase_allocated allocated⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerLetMeaning
