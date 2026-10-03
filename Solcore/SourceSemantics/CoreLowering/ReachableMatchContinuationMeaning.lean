import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuations
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceTrace
import Solcore.SourceSemantics.Dynamic.PatternCompletenessProperties
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-! Match stopping uses original source traces and original native head
subderivations. A present default closes universal source control from static
branch stopping. No-default exhaustiveness is consumed only with the actual
typed scrutinee; typed control soundness has its full source runtime premises.
None of these pointwise laws is cast into the old universal statement Tree.
Suffix lowering provenance is retained, but suffix execution is never assumed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuations

open Frontend Frontend.SourceInference GenericLexicalStatements CoreProof

theorem selected_arm_body {context : Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)}
    {body : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.arm body bindings)) :
    ∃ arm ∈ cases, body = arm.body := by
  cases selected with
  | head => exact ⟨_, List.mem_cons_self, rfl⟩
  | tail _ next =>
    obtain ⟨arm, member, same⟩ := selected_arm_body next
    exact ⟨arm, List.mem_cons_of_mem _ member, same⟩
termination_by cases.length

private theorem restore_terminal {outcome : Dynamic.ControlOutcome}
    (outer : Dynamic.Environment) (terminal : Dynamic.TerminalControl outcome) :
    Dynamic.TerminalControl (Dynamic.restoreControl outer outcome) := by
  cases terminal with
  | returned value => exact .returned value
  | breaking _ => exact .breaking outer
  | continuing _ => exact .continuing outer
  | fault reason => exact .fault reason

theorem DefaultStopped.trace_terminal {source : TypedSource} {id : StatementId}
    {resolution : MatchResolution} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (stops : DefaultStopped source id resolution)
    (trace : DataMatchSourceTrace.Trace program context evidence source environment before resolution outcome after) :
    Dynamic.TerminalControl outcome := by
  have branches := stops.current_branches
  cases trace with
  | scrutineeFault _ | patternFault _ _ _ _ => exact .fault _
  | arm _ _ _ selected _ _ body =>
    obtain ⟨arm, member, same⟩ := selected_arm_body selected
    cases same
    cases body with
    | control executed => exact restore_terminal environment ((branches.arms arm member).terminates unique false executed)
    | fault _ => exact .fault _
  | default _ _ _ selected body =>
    have same := selected.defaultBody_eq
    cases body with
    | control executed => exact restore_terminal environment ((branches.fallback _ same).terminates unique false executed)
    | fault _ => exact .fault _
  | noBranch _ _ _ selected =>
    obtain ⟨fallback, present⟩ := stops.default_present
    have absent := selected.noBranch_defaultBody_eq
    rw [present] at absent
    cases absent

theorem DefaultStopped.terminates {source : TypedSource} {id : StatementId}
    {resolution : MatchResolution} (unique : NodeOccurrencesUnique source)
    (stops : DefaultStopped source id resolution) :
    ReachableStatementContinuations.StatementTerminates source id := by
  intro program context finalContext evidence environment before after outcome executed
  obtain ⟨node, found, form⟩ := stops.lookup
  obtain ⟨_, trace⟩ := DataMatchSourceTrace.of_outcome unique (lookupStatement?_sound found) form (.control executed)
  exact stops.trace_terminal unique trace

/-- Source sequence inversion keeps the actual stopped match execution and
its complete heap, including pattern binders and hidden match allocation. -/
theorem source_stopped_head {source : TypedSource} {id : StatementId} {rest : List StatementId}
    {resolution : MatchResolution} {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (mode : Bool) (unique : NodeOccurrencesUnique source) (stops : DefaultStopped source id resolution)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧
      Dynamic.TerminalControl outcome := by
  obtain ⟨node, found, form⟩ := stops.lookup
  rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found)
    (by intro _ _; simp [form]) trace with ⟨_, _, _, first, _⟩ | terminal
  · cases stops.terminates unique first
  · exact terminal

theorem source_stopped_fault {source : TypedSource} {id : StatementId} {rest : List StatementId}
    {resolution : MatchResolution} {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source) (stops : DefaultStopped source id resolution)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after := by
  obtain ⟨node, found, form⟩ := stops.lookup
  rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found)
    (by intro _ _; simp [form]) trace with terminal | ⟨_, _, _, first, _⟩
  · exact terminal
  · cases stops.terminates unique first

theorem TypedNoDefault.no_branch {source : TypedSource} {control : ControlContext} {context : Context}
    {resolution : MatchResolution} {scrutineeType : TypeSystem.Ty} {caseFacts : List BodyFacts}
    {heap : Dynamic.Heap} {value : Dynamic.Value}
    (typed : TypedNoDefault source control context resolution scrutineeType caseFacts)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (valueTyped : Dynamic.ValueHasType context heap value scrutineeType)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) : False := by
  rw [typed.absent] at selected
  exact selected.noBranch_impossible_of_exhaustive catalog typed.cases_typed valueTyped typed.exhaustive

/-- The actual selected arm is typed at its actual body context and has no
ordinary continuation. Heap typing of the scrutinee remains independent. -/
theorem TypedNoDefault.arm_control {source : TypedSource} {control : ControlContext} {context : Context}
    {resolution : MatchResolution} {scrutineeType : TypeSystem.Ty} {caseFacts : List BodyFacts}
    {value : Dynamic.Value} {body : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    {summary : ControlSummary}
    (typed : TypedNoDefault source control context resolution scrutineeType caseFacts)
    (merged : mergeBodyControls caseFacts none = some summary) (stops : summary.fallthrough = none)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm body bindings)) :
    ∃ facts armContext finalContext,
      StatementsHaveType source control armContext body finalContext facts ∧ facts.control.fallthrough = none := by
  obtain ⟨facts, armContext, finalContext, member, bodyTyped⟩ := Dynamic.MatchCasesSelect.arm_body_typed typed.cases_typed selected
  exact ⟨facts, armContext, finalContext, bodyTyped, merged_arm_stops merged stops member⟩

/-- Typed stopping is pointwise at this actual source environment and heap.
It does not upgrade no-default matching to the universal old Tree interface. -/
theorem MatchControlStopped.terminal_at {source : TypedSource} {control : ControlContext} {context : Context}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution} {facts : StatementFacts}
    {program : Program} {finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (stops : MatchControlStopped source control context id node resolution facts)
    (programWF : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (executed : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    Dynamic.TerminalControl outcome := by
  cases outcome with
  | fallthrough next =>
    have falls := executed.controlCanFallthrough programWF runtime covers agrees heapTyped stops.typed (.intro next)
    simp [ControlSummary.canFallthrough, stops.no_fallthrough] at falls
  | returned value => exact .returned value
  | breaking next => exact .breaking next
  | continuing next => exact .continuing next
  | fault reason => exact .fault reason

theorem source_typed_stopped_head {source : TypedSource} {control : ControlContext} {context : Context}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution} {facts : StatementFacts}
    {rest : List StatementId} {program : Program} {finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (stops : MatchControlStopped source control context id node resolution facts)
    (programWF : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧
      Dynamic.TerminalControl outcome := by
  rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound stops.found)
    (by intro _ _; simp [stops.form]) trace with ⟨_, _, _, first, _⟩ | terminal
  · cases stops.terminal_at programWF runtime covers agrees heapTyped first
  · exact terminal

theorem source_typed_stopped_fault {source : TypedSource} {control : ControlContext} {context : Context}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution} {facts : StatementFacts}
    {rest : List StatementId} {program : Program} {finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (stops : MatchControlStopped source control context id node resolution facts)
    (programWF : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after := by
  rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound stops.found)
    (by intro _ _; simp [stops.form]) trace with terminal | ⟨_, _, _, first, _⟩
  · exact terminal
  · cases stops.terminal_at programWF runtime covers agrees heapTyped first

/-- Native stopping uses the original sequence's strict match child. The
pointwise head obligation is a theorem argument, separate from IssuedSuffix. -/
theorem native_issued_stopped {size : Nat} {type : Core.Ty} {native : Core.Environment}
    {before after : Core.Store} {code matched suffix : Core.Expr} {value : Core.Value}
    (equation : code = Core.LocalLoop.sequence type matched suffix)
    (original : EvaluationSize size native before code value after)
    (headStops : ∀ {child middle result}, child < size →
      EvaluationSize child native before matched result middle →
        ReachableStatementContinuations.NativeTerminal type result) :
    ∃ child, child < size ∧ EvaluationSize child native before matched value after ∧
      ReachableStatementContinuations.NativeTerminal type value := by
  subst code
  exact ReachableStatementContinuations.native_sequence_stopped original headStops

end Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuations
