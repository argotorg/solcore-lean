import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.Frontend.SourceCore.Lowering
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Payloads

/-!
# Reachable statement continuations

Reachable continuations of statements and their meaning.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuations
/-! Static certificates for statement fragments whose successful control cannot
reach their suffix. These certificates retain actual source occurrences and
the compiler's emitted suffix. They neither change the existing lexical grammar
nor infer its Syntax from BodyCompletes. No execution law is stored here. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuations

open Frontend Frontend.SourceInference

mutual
  /-- A source statement stops sequencing by its actual form. Both conditional
  branches must stop; annotations remain the actual node annotations. -/
  inductive StoppingStatement (source : TypedSource) : StatementId → ControlSummary → Prop where
    | returnUnit {id node}
        (found : source.lookupStatement? id = some node)
        (form : node.form = .returnStmt none) :
        StoppingStatement source id .returned
    | returnValue {id node expression}
        (found : source.lookupStatement? id = some node)
        (form : node.form = .returnStmt (some expression)) :
        StoppingStatement source id .returned
    | breaking {id node}
        (found : source.lookupStatement? id = some node)
        (form : node.form = .breakStmt) :
        StoppingStatement source id .breaking
    | continuing {id node}
        (found : source.lookupStatement? id = some node)
        (form : node.form = .continueStmt) :
        StoppingStatement source id .continuing
    | block {id node statements summary}
        (found : source.lookupStatement? id = some node)
        (form : node.form = .block statements)
        (body : StoppingStatements source statements summary) :
        StoppingStatement source id summary.eraseValue
    | conditional {id node condition left right leftSummary rightSummary}
        (found : source.lookupStatement? id = some node)
        (form : node.form = .ifThen condition left (some right))
        (leftStops : StoppingStatements source left leftSummary)
        (rightStops : StoppingStatements source right rightSummary) :
        StoppingStatement source id (.branches leftSummary rightSummary)


    | matchDefault {id node resolution fallback control context scrutineeType
        caseFacts defaultFinal defaultFacts summary}
        (found : source.lookupStatement? id = some node)
        (form : node.form = .matchWith resolution)
        (present : resolution.defaultBody = some fallback)
        (casesTyped : MatchCasesHaveType source control context scrutineeType resolution.cases caseFacts)
        (defaultTyped : StatementsHaveType source control context fallback defaultFinal defaultFacts)
        (merged : mergeBodyControls caseFacts (some defaultFacts) = some summary)
        (arms : ∀ arm fact, (arm, fact) ∈ resolution.cases.zip caseFacts →
          StoppingStatements source arm.body fact.control)
        (defaultStops : StoppingStatements source fallback defaultFacts.control) :
        StoppingStatement source id summary.eraseValue

  /-- The stopped suffix may follow ordinary prefixes. Prefix summaries come
  from independent source typing, rather than an arbitrary summary field. -/
  inductive StoppingStatements (source : TypedSource) : List StatementId → ControlSummary → Prop where
    | stop {id rest summary} (head : StoppingStatement source id summary) :
        StoppingStatements source (id :: rest) summary
    | prefix {id node rest summary control context next facts}
        (found : source.lookupStatement? id = some node)
        (head : StatementHasType source control context id next facts)
        (tail : StoppingStatements source rest summary) :
        StoppingStatements source (id :: rest) (.sequence facts.control summary)
end


private theorem typed_stopped_merge {source : TypedSource} {control : ControlContext} {context : Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase} {caseFacts : List BodyFacts}
    {fallback : BodyFacts}
    (typed : MatchCasesHaveType source control context scrutineeType cases caseFacts)
    (arms : ∀ arm fact, (arm, fact) ∈ cases.zip caseFacts → fact.control.fallthrough = none)
    (defaultStops : fallback.control.fallthrough = none) :
    ∃ summary, mergeBodyControls caseFacts (some fallback) = some summary ∧ summary.fallthrough = none := by
  cases typed with
  | nil => exact ⟨fallback.control, rfl, defaultStops⟩
  | @cons control context scrutineeType arm cases fact facts head tail =>
    obtain ⟨rest, merged, stopped⟩ := typed_stopped_merge tail (fun arm fact member => arms arm fact (List.mem_cons_of_mem _ member)) defaultStops
    have first := arms arm fact List.mem_cons_self
    exact ⟨fact.control.branches rest, by simp [mergeBodyControls, merged],
      by simp [ControlSummary.branches, ControlSummary.canFallthrough, first, stopped]⟩
termination_by cases.length

theorem StoppingStatement.no_fallthrough {source : TypedSource} {id : StatementId}
    {summary : ControlSummary} (stops : StoppingStatement source id summary) :
    summary.fallthrough = none := by
  induction stops using StoppingStatement.rec
      (motive_2 := fun _ summary _ => summary.fallthrough = none) with
  | returnUnit | returnValue | breaking | continuing => rfl
  | block _ _ _ body => simp [ControlSummary.eraseValue, body]
  | conditional _ _ _ _ left right =>
      simp [ControlSummary.branches, ControlSummary.canFallthrough, left, right]
  | matchDefault _ _ _ casesTyped _ merged _ _ armsIH defaultIH =>
      obtain ⟨actual, equation, stopped⟩ := typed_stopped_merge casesTyped armsIH defaultIH
      have same := Option.some.inj (equation.symm.trans merged)
      cases same
      simp [ControlSummary.eraseValue, stopped]
  | stop _ head => exact head
  | «prefix» _ _ _ tail => simp [ControlSummary.sequence, tail]

theorem StoppingStatements.no_fallthrough {source : TypedSource} {statements : List StatementId}
    {summary : ControlSummary} (stops : StoppingStatements source statements summary) :
    summary.fallthrough = none := by
  induction stops using StoppingStatements.rec
      (motive_1 := fun _ summary _ => summary.fallthrough = none) with
  | returnUnit | returnValue | breaking | continuing => rfl
  | block _ _ _ body => simp [ControlSummary.eraseValue, body]
  | conditional _ _ _ _ left right =>
      simp [ControlSummary.branches, ControlSummary.canFallthrough, left, right]
  | matchDefault _ _ _ casesTyped _ merged _ _ armsIH defaultIH =>
      obtain ⟨actual, equation, stopped⟩ := typed_stopped_merge casesTyped armsIH defaultIH
      have same := Option.some.inj (equation.symm.trans merged)
      cases same
      simp [ControlSummary.eraseValue, stopped]
  | stop _ head => exact head
  | «prefix» _ _ _ tail => simp [ControlSummary.sequence, tail]

theorem StoppingStatements.nonempty {source : TypedSource} {statements : List StatementId}
    {summary : ControlSummary} (stops : StoppingStatements source statements summary) : statements ≠ [] := by
  cases stops <;> simp

/-- The suffix is the actual successful lowering, even when execution stops
before it. No type restriction is imposed on the enclosing block/if annotation. -/
structure Issued (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLoops.Scope) (statements : List StatementId) (type : Core.Ty)
    (reasonAt : ExpressionId → Core.Word) (mode : Bool) (escaped : Core.Word) (code : Core.Expr) : Prop where
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements
    type reasonAt mode escaped = .ok code

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error reason => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

section Compiler

variable {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
  {scope : SourceCoreLoops.Scope} {id : StatementId} {node : StatementNode} {rest : List StatementId}
  {type readType : Core.Ty} {reasonAt : ExpressionId → Core.Word} {mode : Bool} {escaped : Core.Word}
  {code : Core.Expr}

theorem block_issued {statements : List StatementId}
    (read : policy.readStatement source id = .ok (node, readType))
    (form : node.form = .block statements)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
      (id :: rest) type reasonAt mode escaped = .ok code) :
    ∃ inner suffix, Issued policy fuel source scope statements type reasonAt false escaped inner ∧
      Issued policy fuel source scope rest type reasonAt mode escaped suffix ∧
      code = Core.LocalLoop.sequence type inner suffix := by
  simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, bind, Except.bind, form] at accepted
  obtain ⟨inner, innerEq, accepted⟩ := bind_ok accepted
  obtain ⟨suffix, suffixEq, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨inner, suffix, ⟨innerEq⟩, ⟨suffixEq⟩, rfl⟩

theorem conditional_issued {condition : ExpressionId} {left right : List StatementId}
    (read : policy.readStatement source id = .ok (node, readType))
    (form : node.form = .ifThen condition left (some right))
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
      (id :: rest) type reasonAt mode escaped = .ok code) :
    ∃ lowered leftCode rightCode suffix,
      policy.lowerExpression fuel source scope condition reasonAt = .ok lowered ∧
      SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool lowered.type = .ok () ∧
      Issued policy fuel source scope left type reasonAt false escaped leftCode ∧
      Issued policy fuel source scope right type reasonAt false escaped rightCode ∧
      Issued policy fuel source scope rest type reasonAt mode escaped suffix ∧
      code = Core.LocalLoop.sequence type
        (Core.LocalLoop.conditional type lowered.expression leftCode rightCode) suffix := by
  simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, bind, Except.bind, form] at accepted
  obtain ⟨lowered, loweredEq, accepted⟩ := bind_ok accepted
  obtain ⟨checked, checkedEq, accepted⟩ := bind_ok accepted
  cases checked
  obtain ⟨leftCode, leftEq, accepted⟩ := bind_ok accepted
  obtain ⟨rightCode, rightEq, accepted⟩ := bind_ok accepted
  obtain ⟨suffix, suffixEq, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨lowered, leftCode, rightCode, suffix, loweredEq, checkedEq,
    ⟨leftEq⟩, ⟨rightEq⟩, ⟨suffixEq⟩, rfl⟩

end Compiler
end Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuationMeaning
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
  | block found form _ | conditional found form _ _
  | matchDefault found form _ _ _ _ _ _ => exact ⟨_, found, by simp [form]⟩

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


private theorem typed_cases_length {origin : TypedSource} {control : ControlContext} {context : Context}
    {type : TypeSystem.Ty} {cases : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType origin control context type cases facts) : cases.length = facts.length := by
  apply MatchCasesHaveType.rec (source := origin) (t := typed)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ cases facts _ => cases.length = facts.length)
  all_goals intros; first | exact True.intro | simp_all

private theorem zip_fact_of_mem {cases : List TypedMatchCase} {facts : List BodyFacts} {arm : TypedMatchCase}
    (same : cases.length = facts.length) (member : arm ∈ cases) :
    ∃ fact, (arm, fact) ∈ cases.zip facts := by
  cases cases with
  | nil => cases member
  | cons head tail =>
    cases facts with
    | nil => simp at same
    | cons fact rest =>
      have lengths : tail.length = rest.length := Nat.succ.inj same
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨fact, List.mem_cons_self⟩
      · obtain ⟨chosen, present⟩ := zip_fact_of_mem lengths member
        exact ⟨chosen, List.mem_cons_of_mem _ present⟩
termination_by cases.length

private theorem selected_arm_body {context : Context} {value : Dynamic.Value}
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

/-- A present default excludes the untyped no-branch result. The original
selected body consumes only its own recursively established stopping proof. -/
theorem source_match_terminal {origin source : TypedSource} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {fallback : List StatementId}
    {control : ControlContext} {context : Context} {type : TypeSystem.Ty} {caseFacts : List BodyFacts}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback)
    (typed : MatchCasesHaveType origin control context type resolution.cases caseFacts)
    (arms : ∀ arm fact, (arm, fact) ∈ resolution.cases.zip caseFacts → ListTerminates source arm.body)
    (defaultStops : ListTerminates source fallback) : StatementTerminates source id := by
  intro program actualContext finalContext evidence environment before after outcome executed
  obtain ⟨_, trace⟩ := DataMatchSourceTrace.of_outcome unique (lookupStatement?_sound found) form (.control executed)
  cases trace with
  | scrutineeFault _ | patternFault _ _ _ _ => exact .fault _
  | arm _ _ _ selected _ _ body =>
    obtain ⟨arm, member, same⟩ := selected_arm_body selected
    cases same
    obtain ⟨fact, member⟩ := zip_fact_of_mem (typed_cases_length typed) member
    cases body with
    | control executed => exact restore_terminal environment (arms arm fact member false executed)
    | fault _ => exact .fault _
  | default _ _ _ selected body =>
    have same := Option.some.inj (selected.defaultBody_eq.symm.trans present)
    cases same
    cases body with
    | control executed => exact restore_terminal environment (defaultStops false executed)
    | fault _ => exact .fault _
  | noBranch _ _ _ selected =>
    have absent := selected.noBranch_defaultBody_eq
    rw [present] at absent
    cases absent

theorem source_statement_terminal {source : TypedSource} {id : StatementId} {summary : ControlSummary}
    (unique : NodeOccurrencesUnique source) (stops : StoppingStatement source id summary) :
    StatementTerminates source id := by
  refine @StoppingStatement.rec source
    (fun id _ _ => StatementTerminates source id)
    (fun statements _ _ => ListTerminates source statements)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ id summary stops
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
  · intro _ _ _ _ _ _ _ _ _ _ _ found form present casesTyped _ _ _ _ armsIH defaultIH
    exact source_match_terminal unique found form present casesTyped armsIH defaultIH
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ statements summary stops
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
  · intro _ _ _ _ _ _ _ _ _ _ _ found form present casesTyped _ _ _ _ armsIH defaultIH
    exact source_match_terminal unique found form present casesTyped armsIH defaultIH
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
end
