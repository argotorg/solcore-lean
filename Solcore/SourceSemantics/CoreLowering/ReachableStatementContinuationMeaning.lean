import Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuations
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion

/-! Stopped continuations are justified separately in the original source and
Core relations. Source inversion keeps lexical environments and heaps; native
inversion retains the original strict head subderivation. Neither an Agreement
nor a freshly constructed derivation is used to infer a native size bound.
These lemmas are a foundation for future terminal Tree cases, not a replacement
for the existing whole lexical/imperative meaning consumers. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuations

open Frontend Frontend.SourceInference CoreProof

theorem StoppingStatement.not_tail {source : TypedSource} {id : StatementId}
    {summary : ControlSummary} (stops : StoppingStatement source id summary) :
    ∃ node, source.lookupStatement? id = some node ∧
      ∀ expression, node.form ≠ .expression expression false := by
  cases stops with
  | returnUnit found form | returnValue found form | breaking found form | continuing found form
  | block found form _ | conditional found form _ _ => exact ⟨_, found, by simp [form]⟩

private theorem restore_terminal {outcome : Dynamic.ControlOutcome}
    (outer : Dynamic.Environment) (terminal : Dynamic.TerminalControl outcome) :
    Dynamic.TerminalControl (Dynamic.restoreControl outer outcome) := by
  cases terminal with
  | returned value => exact .returned value
  | breaking _ => exact .breaking outer
  | continuing _ => exact .continuing outer
  | fault reason => exact .fault reason

def StatementTerminates (source : TypedSource) (id : StatementId) : Prop :=
  ∀ {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome},
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after →
      Dynamic.TerminalControl outcome

def ListTerminates (source : TypedSource) (statements : List StatementId) : Prop :=
  ∀ {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome},
    ∀ mode, ScalarStatementViews.ListExecutes mode program context evidence source environment before
      statements finalContext outcome after → Dynamic.TerminalControl outcome

theorem source_statement_terminal {source : TypedSource} {id : StatementId} {summary : ControlSummary}
    (unique : NodeOccurrencesUnique source) (stops : StoppingStatement source id summary) :
    StatementTerminates source id := by
  refine @StoppingStatement.rec source
    (fun id _ _ => StatementTerminates source id)
    (fun statements _ _ => ListTerminates source statements)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ id summary stops
  · intro _ _ found form
    intro _ _ _ _ _ _ _ _ trace
    obtain ⟨_, same, _⟩ := ScalarStatementViews.returnUnit unique (lookupStatement?_sound found) form trace
    exact same ▸ .returned .unit
  · intro _ _ _ found form
    intro _ _ _ _ _ _ _ _ trace
    obtain ⟨_, value, same, _⟩ := ScalarStatementViews.returnValue unique (lookupStatement?_sound found) form trace
    exact same ▸ .returned value
  · intro _ _ found form
    intro _ _ _ _ _ _ _ _ trace
    obtain ⟨_, same, _⟩ := ScalarStatementViews.breaking unique (lookupStatement?_sound found) form trace
    exact same ▸ .breaking _
  · intro _ _ found form
    intro _ _ _ _ _ _ _ _ trace
    obtain ⟨_, same, _⟩ := ScalarStatementViews.continuing unique (lookupStatement?_sound found) form trace
    exact same ▸ .continuing _
  · intro _ _ _ _ found form _ bodyIH
    intro _ _ _ _ environment _ _ _ trace
    obtain ⟨_, _, _, same, body⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form trace
    exact same ▸ restore_terminal environment (bodyIH false body)
  · intro _ _ _ _ _ _ _ found form _ _ leftIH rightIH
    intro _ _ _ _ environment _ _ _ trace
    obtain ⟨_, boolean, _, _, _, _, same, body⟩ :=
        ScalarStatementViews.ifThen unique (lookupStatement?_sound found) form trace
    cases boolean with
    | false => exact same ▸ restore_terminal environment (rightIH false body)
    | true => exact same ▸ restore_terminal environment (leftIH false body)
  · intro _ _ _ head headIH
    intro _ _ _ _ _ _ _ _ mode trace
    obtain ⟨_, found, notTail⟩ := head.not_tail
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found)
        (by intro _ _; exact notTail) trace with ⟨_, _, _, first, _⟩ | ⟨_, terminal⟩
    · cases headIH first
    · exact terminal
  · intro _ _ _ _ _ _ _ _ found _ tail tailIH
    intro _ _ _ _ _ _ _ _ mode trace
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found)
        (by intro _ empty; exact False.elim (tail.nonempty empty)) trace with ⟨_, _, _, _, rest⟩ | ⟨_, terminal⟩
    · exact tailIH mode rest
    · exact terminal

theorem source_statements_terminal {source : TypedSource} {statements : List StatementId} {summary : ControlSummary}
    (unique : NodeOccurrencesUnique source) (stops : StoppingStatements source statements summary) :
    ListTerminates source statements := by
  refine @StoppingStatements.rec source
    (fun id _ _ => StatementTerminates source id)
    (fun statements _ _ => ListTerminates source statements)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ statements summary stops
  · intro _ _ found form
    intro _ _ _ _ _ _ _ _ trace
    obtain ⟨_, same, _⟩ := ScalarStatementViews.returnUnit unique (lookupStatement?_sound found) form trace
    exact same ▸ .returned .unit
  · intro _ _ _ found form
    intro _ _ _ _ _ _ _ _ trace
    obtain ⟨_, value, same, _⟩ := ScalarStatementViews.returnValue unique (lookupStatement?_sound found) form trace
    exact same ▸ .returned value
  · intro _ _ found form
    intro _ _ _ _ _ _ _ _ trace
    obtain ⟨_, same, _⟩ := ScalarStatementViews.breaking unique (lookupStatement?_sound found) form trace
    exact same ▸ .breaking _
  · intro _ _ found form
    intro _ _ _ _ _ _ _ _ trace
    obtain ⟨_, same, _⟩ := ScalarStatementViews.continuing unique (lookupStatement?_sound found) form trace
    exact same ▸ .continuing _
  · intro _ _ _ _ found form _ bodyIH
    intro _ _ _ _ environment _ _ _ trace
    obtain ⟨_, _, _, same, body⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form trace
    exact same ▸ restore_terminal environment (bodyIH false body)
  · intro _ _ _ _ _ _ _ found form _ _ leftIH rightIH
    intro _ _ _ _ environment _ _ _ trace
    obtain ⟨_, boolean, _, _, _, _, same, body⟩ :=
        ScalarStatementViews.ifThen unique (lookupStatement?_sound found) form trace
    cases boolean with
    | false => exact same ▸ restore_terminal environment (rightIH false body)
    | true => exact same ▸ restore_terminal environment (leftIH false body)
  · intro _ _ _ head headIH
    intro _ _ _ _ _ _ _ _ mode trace
    obtain ⟨_, found, notTail⟩ := head.not_tail
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found)
        (by intro _ _; exact notTail) trace with ⟨_, _, _, first, _⟩ | ⟨_, terminal⟩
    · cases headIH first
    · exact terminal
  · intro _ _ _ _ _ _ _ _ found _ tail tailIH
    intro _ _ _ _ _ _ _ _ mode trace
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found)
        (by intro _ empty; exact False.elim (tail.nonempty empty)) trace with ⟨_, _, _, _, rest⟩ | ⟨_, terminal⟩
    · exact tailIH mode rest
    · exact terminal

/-- A terminal head retains its own complete execution; no suffix trace is
required or extracted. This also covers a nonempty, compiled dead suffix. -/
theorem source_stopped_head {source : TypedSource} {id : StatementId} {rest : List StatementId}
    {summary : ControlSummary} {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ControlOutcome} (mode : Bool) (unique : NodeOccurrencesUnique source)
    (stops : StoppingStatement source id summary)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧
      Dynamic.TerminalControl outcome := by
  obtain ⟨_, found, notTail⟩ := stops.not_tail
  rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found)
    (by intro _ _; exact notTail) trace with ⟨_, _, _, first, _⟩ | terminal
  · cases source_statement_terminal unique stops first
  · exact terminal

theorem source_stopped_fault {source : TypedSource} {id : StatementId} {rest : List StatementId}
    {summary : ControlSummary} {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {reason : Dynamic.SemanticFault} (mode : Bool) (unique : NodeOccurrencesUnique source)
    (stops : StoppingStatement source id summary)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after := by
  obtain ⟨_, found, notTail⟩ := stops.not_tail
  rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found)
    (by intro _ _; exact notTail) trace with terminal | ⟨_, _, _, first, _⟩
  · exact terminal
  · cases source_statement_terminal unique stops first

/-- Native terminal payloads have no branch which invokes a sequence suffix. -/
inductive NativeTerminal (type : Core.Ty) : Core.Value → Prop where
  | failure (reason : Core.Word) : NativeTerminal type (.inLeft (Core.LocalLoop.controlType type) (.word reason))
  | returned (value : Core.Value) : NativeTerminal type (Core.LocalLoop.returnedValue value)
  | transfer (value : Core.Value) : NativeTerminal type
      (.inRight .word (.inRight (Core.LocalControl.controlType type) value))

theorem native_sequence_terminal {type : Core.Ty} {environment : Core.Environment} {before after : Core.Store}
    {head suffix : Core.Expr} {value : Core.Value} (terminal : NativeTerminal type value)
    (executed : Core.Evaluates environment before head value after) :
    Core.Evaluates environment before (Core.LocalLoop.sequence type head suffix) value after := by
  cases terminal with
  | failure _ => exact Core.LocalLoop.sequence_failure type executed
  | returned _ => exact Core.LocalLoop.sequence_returned type executed
  | transfer _ => exact Core.LocalLoop.sequence_transfer type executed

/-- The head witness comes from the original evaluation, before any comparison
with a terminal payload. The stopping obligation is pointwise at that actual
child; it is not placed in the compiler receipt. -/
theorem native_sequence_stopped {size : Nat} {type : Core.Ty} {environment : Core.Environment}
    {before after : Core.Store} {head suffix : Core.Expr} {value : Core.Value}
    (original : EvaluationSize size environment before (Core.LocalLoop.sequence type head suffix) value after)
    (headStops : ∀ {child middle result}, child < size →
      EvaluationSize child environment before head result middle → NativeTerminal type result) :
    ∃ child, child < size ∧ EvaluationSize child environment before head value after ∧ NativeTerminal type value := by
  obtain ⟨child, middle, result, smaller, executed⟩ := original.bind_computation
  have terminal := headStops smaller executed
  have whole := native_sequence_terminal (suffix := suffix) terminal executed.sound
  obtain ⟨same, sameStore⟩ := Core.evaluation_deterministic original.sound whole
  cases same
  cases sameStore
  exact ⟨child, smaller, executed, terminal⟩

end Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuations
