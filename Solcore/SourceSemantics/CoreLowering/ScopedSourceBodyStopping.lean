import Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts

/-! Finite stopping receipts refer only to original statement forms. Independent
Source typing supplies every prefix and branch context and raw result fact. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyStopping
open Frontend SourceInference ReachableStatementContinuations

inductive ReturnStopped (source : TypedSource) : List StatementId → Prop where
  | returning {id node value rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt value) :
      ReturnStopped source (id :: rest)
  | block {id node body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .block body)
      (inner : ReturnStopped source body) : ReturnStopped source (id :: rest)
  | conditional {id node condition left right rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .ifThen condition left (some right))
      (first : ReturnStopped source left) (second : ReturnStopped source right) :
      ReturnStopped source (id :: rest)
  | matching {id node resolution fallback rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .matchWith resolution)
      (present : resolution.defaultBody = some fallback)
      (arms : ∀ arm ∈ resolution.cases, ReturnStopped source arm.body)
      (default : ReturnStopped source fallback) : ReturnStopped source (id :: rest)
  | prefix {id rest} (remaining : ReturnStopped source rest) : ReturnStopped source (id :: rest)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

/-- The budget controls this finite form inspection. A failed earlier candidate
may still be followed by an actual stopped suffix. -/
def returnStopped? (source : TypedSource) : (fuel : Nat) → (statements : List StatementId) →
    Option (PLift (ReturnStopped source statements))
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, id :: rest =>
    let tail := do
      let ⟨stopped⟩ ← returnStopped? source fuel rest
      pure ⟨ReturnStopped.prefix stopped⟩
    match found : source.lookupStatement? id with
    | none => tail
    | some node =>
      match form : node.form with
      | .returnStmt _value => some ⟨.returning found form⟩
      | .block body =>
        match returnStopped? source fuel body with
        | some ⟨inner⟩ => some ⟨.block found form inner⟩
        | none => tail
      | .ifThen _condition left (some right) =>
        match returnStopped? source fuel left, returnStopped? source fuel right with
        | some ⟨first⟩, some ⟨second⟩ => some ⟨.conditional found form first second⟩
        | _, _ => tail
      | .matchWith resolution =>
        match present : resolution.defaultBody with
        | none => tail
        | some fallback =>
          match allProof? (fun arm : TypedMatchCase => ReturnStopped source arm.body)
              (fun arm => returnStopped? source fuel arm.body) resolution.cases,
              returnStopped? source fuel fallback with
          | some ⟨arms⟩, some ⟨default⟩ => some ⟨.matching found form present arms default⟩
          | _, _ => tail
      | _ => tail

theorem ReturnStopped.nonempty {source statements} (stopped : ReturnStopped source statements) :
    statements ≠ [] := by cases stopped <;> simp

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts ∧
      facts.control = (if rest.isEmpty then headFacts.control else headFacts.control.sequence tailFacts.control) ∧
      facts.sawReturn = (headFacts.sawReturn || tailFacts.sawReturn) := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _, rfl, by simp [BodyFacts.singleton, BodyFacts.empty]⟩
  | cons head tail => exact ⟨_, _, _, head, tail, rfl, rfl⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementControlFormTyping source control context node.form facts := by
  obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.controlFormTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact formTyped

private theorem head_stops {source : TypedSource} {id : StatementId} {rest : List StatementId}
    {head tail summary : ControlSummary}
    (stopped : StoppingStatement source id head)
    (same : summary = if rest.isEmpty then head else head.sequence tail) :
    StoppingStatements source (id :: rest) summary := by
  have sequence : head.sequence tail = head := by
    have absent := stopped.no_fallthrough
    cases head
    simp_all [ControlSummary.sequence, ControlSummary.canFallthrough]
  rw [sequence] at same
  simp only [ite_self] at same
  exact same ▸ .stop stopped

private theorem cases_stopping {source : TypedSource} {cases : List TypedMatchCase}
    (bodies : ∀ arm ∈ cases, ∀ {control : ControlContext}
      {context final : SourceSemantics.Context} {facts : BodyFacts},
      StatementsHaveType source control context arm.body final facts →
      StoppingStatements source arm.body facts.control ∧ facts.sawReturn = true)
    {control : ControlContext} {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type cases facts) :
    (∀ arm fact, (arm, fact) ∈ cases.zip facts →
      StoppingStatements source arm.body fact.control) ∧ allBodiesSawReturn facts = true := by
  induction cases generalizing facts with
  | nil =>
    cases typed
    refine ⟨?_, rfl⟩
    intro arm fact member
    cases member
  | cons arm rest ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | intro pattern extended body =>
        obtain ⟨stops, returns⟩ := bodies arm List.mem_cons_self body
        obtain ⟨tails, allReturn⟩ := ih (fun candidate member => bodies candidate (List.mem_cons_of_mem _ member)) tail
        refine ⟨?_, ?_⟩
        · intro candidate fact member
          rcases List.mem_cons.mp member with same | member
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
            exact stops
          · exact tails candidate fact member
        · simp only [allBodiesSawReturn, List.all_cons, returns, Bool.true_and]
          exact allReturn

private theorem ReturnStopped.typed {source statements} (stopped : ReturnStopped source statements)
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    StoppingStatements source statements facts.control ∧ facts.sawReturn = true := by
  induction stopped generalizing control context final facts with
  | returning found form =>
    obtain ⟨_, _, _, head, _, same, returned⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | returnUnit => exact ⟨head_stops (.returnUnit found form) same, by simpa using returned⟩
    | returnValue => exact ⟨head_stops (.returnValue found form) same, by simpa using returned⟩
  | block found form inner ih =>
    obtain ⟨_, _, _, head, _, same, returned⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | block body =>
      obtain ⟨stops, returns⟩ := ih body
      exact ⟨head_stops (.block found form stops) same, by simpa [returns] using returned⟩
  | conditional found form first second firstIH secondIH =>
    obtain ⟨_, _, _, head, _, same, returned⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | ifWithElse condition left right =>
      obtain ⟨firstStop, firstReturn⟩ := firstIH left
      obtain ⟨secondStop, secondReturn⟩ := secondIH right
      exact ⟨head_stops (.conditional found form firstStop secondStop) same,
        by simpa [firstReturn, secondReturn] using returned⟩
  | matching found form present arms default armIH defaultIH =>
    obtain ⟨_, _, _, head, _, same, returned⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | matchWithoutDefault absent scrutinee casesTyped exhaustive merged =>
      simp [present] at absent
    | matchWithDefault actual scrutinee casesTyped defaultTyped merged =>
      cases Option.some.inj (actual.symm.trans present)
      obtain ⟨armStops, armReturns⟩ := cases_stopping armIH casesTyped
      obtain ⟨defaultStops, defaultReturns⟩ := defaultIH defaultTyped
      exact ⟨head_stops (.matchDefault found form present casesTyped defaultTyped merged armStops defaultStops) same,
        by simpa [armReturns, defaultReturns] using returned⟩
  | «prefix» remaining ih =>
    cases typed with
    | singleton head => exact False.elim (remaining.nonempty rfl)
    | cons head tail =>
      obtain ⟨stops, returns⟩ := ih tail
      obtain ⟨node, contains, _⟩ := Dynamic.StatementHasType.controlFormTyping head
      exact ⟨.prefix (lookupStatement?_complete unique contains) head stops,
        by simp [BodyFacts.cons, returns]⟩

/-- Stopping is justified at the original typed contexts. Its exact summary and
return annotation are retained independently of compiled native types. -/
theorem ReturnStopped.facts {source statements} (stopped : ReturnStopped source statements)
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    StoppingStatements source statements facts.control ∧ facts.sawReturn = true ∧
      facts.type = control.returnType := by
  obtain ⟨stops, returns⟩ := stopped.typed unique typed
  exact ⟨stops, returns, RecursiveNamedStatementSyntaxFacts.returned_type typed returns⟩

theorem ReturnStopped.stopped {source statements} (stopped : ReturnStopped source statements)
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    GenericLexicalStatements.Stopped source statements :=
  GenericLexicalStatements.Stopped.of_source (stopped.facts unique typed).1

/-- Every original arm and the present default retain genuine Source stopping.
The actual typed case row supplies its full ordered branch facts. -/
theorem ReturnStopped.match_default {source : TypedSource} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {fallback : List StatementId}
    (arms : ∀ arm ∈ resolution.cases, ReturnStopped source arm.body)
    (default : ReturnStopped source fallback)
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : StatementFacts}
    (typed : StatementHasType source control context id final facts) :
    ReachableMatchContinuations.DefaultStopped source id resolution := by
  have receipt : ReturnStopped source [id] := .matching found form present arms default
  have stops := (receipt.facts unique (.singleton typed)).1
  have head_only : ∀ {summary}, StoppingStatements source [id] summary →
      ∃ head, StoppingStatement source id head := by
    intro summary stopped
    cases stopped with
    | stop head => exact ⟨_, head⟩
    | «prefix» _ _ tail => cases tail
  obtain ⟨_, head⟩ := head_only stops
  exact RecursiveNamedStatementSyntaxFacts.stopped_match found form head

end Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyStopping
