import Solcore.SourceSemantics.Staging.SelectedControlPreservationContracts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem statement_head_tail
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts,
      StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts ∧
      (∀ expected, rest ≠ [] → headFacts.control.canFallthrough = true →
        BodyCompletes expected facts → BodyCompletes expected tailFacts) ∧
      (headFacts.control.canFallthrough = true → tailFacts.control.canFallthrough = true → facts.control.canFallthrough = true) := by
  cases typed with
  | singleton head =>
      exact ⟨_, _, _, head, .nil _ _, by intro expected nonempty; exact (nonempty rfl).elim, by intro falls _; exact falls⟩
  | cons head tail =>
      exact ⟨_, _, _, head, tail,
        fun _ _ falls complete => BodyCompletes.tail_of_cons_of_hasOutcome falls tail.controlHasOutcome complete,
        ControlSummary.sequence_canFallthrough⟩

theorem statement_form
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {node : StatementNode} {shape : StatementForm} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context id final facts)
    (contains : ContainsStatement source id node) (form : node.form = shape) :
    Solcore.SourceSemantics.Dynamic.StatementHasType.FormTyping source control context shape final := by
  obtain ⟨actual, found, formTyped⟩ := Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique found).symm.trans
    (lookupStatement?_complete unique contains))
  cases same
  exact form ▸ formTyped

theorem statement_control_form
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {node : StatementNode} {shape : StatementForm} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context id final facts)
    (contains : ContainsStatement source id node) (form : node.form = shape) :
    StatementControlFormTyping source control context shape facts := by
  obtain ⟨actual, found, formTyped⟩ := Solcore.SourceSemantics.Dynamic.StatementHasType.controlFormTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique found).symm.trans
    (lookupStatement?_complete unique contains))
  cases same
  exact form ▸ formTyped

theorem continue_tail
    {size : Nat} {mode : Bool} {scope : Scope} {context staticFinal runtimeFinal : Context}
    {environment : Dynamic.Environment} {before after : Heap} {rest : List StatementId}
    {facts tailFacts : BodyFacts} {headFacts : StatementFacts} {type : Ty} {outcome : BodyOutcome}
    (headFalls : headFacts.control.canFallthrough = true)
    (completeTail : ∀ expected, rest ≠ [] → headFacts.control.canFallthrough = true →
      BodyCompletes expected facts → BodyCompletes expected tailFacts)
    (fallthroughWhole : headFacts.control.canFallthrough = true → tailFacts.control.canFallthrough = true → facts.control.canFallthrough = true)
    (trace : Size.StatementsIn program registry mode size scope context environment before rest runtimeFinal outcome after)
    (post : StatementsPreserved context staticFinal runtimeFinal before after type outcome
      (mode = true → BodyCompletes type tailFacts) (tailFacts.control.canFallthrough = true)) :
    StatementsPreserved context staticFinal runtimeFinal before after type outcome
      (mode = true → BodyCompletes type facts) (facts.control.canFallthrough = true) := by
  refine ⟨post.heap_typed, post.heap_extends, ?_, ?_⟩
  · intro complete value returned
    by_cases empty : rest = []
    · subst rest
      cases trace
      cases returned
    · exact post.returned (fun same => completeTail type empty headFalls (complete same)) value returned
  · intro result equal
    obtain ⟨same, locals, allowed⟩ := post.fallthrough result equal
    exact ⟨same, locals, fallthroughWhole headFalls allowed⟩

theorem StatementsPreserved.prepend
    {context staticFinal runtimeFinal : Context} {before middle after : Heap}
    {type : Ty} {outcome : BodyOutcome} {complete allowed : Prop}
    (extended : HeapTypesExtend before middle)
    (post : StatementsPreserved context staticFinal runtimeFinal middle after type outcome complete allowed) :
    StatementsPreserved context staticFinal runtimeFinal before after type outcome complete allowed :=
  ⟨post.heap_typed, extended.trans post.heap_extends, post.returned, post.fallthrough⟩

theorem StatementsPreserved.transportEntry
    {program : Program} {source : TypedSource} {context middle staticFinal runtimeFinal : Context}
    {before after : Heap} {type : Ty} {outcome : BodyOutcome} {complete allowed : Prop}
    (runtime : SourceRuntimeValid program context source)
    (fields : RuntimeContextFields context middle)
    (post : StatementsPreserved middle staticFinal runtimeFinal before after type outcome complete allowed) :
    StatementsPreserved context staticFinal runtimeFinal before after type outcome complete allowed := by
  have closed := fields.targetClosed runtime.closed
  exact ⟨post.heap_typed.transportClosed fields.signatures.symm closed runtime.closed
      (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
    post.heap_extends,
    fun completion value equal => (post.returned completion value equal).transportClosed
      fields.signatures.symm closed runtime.closed
      (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
    post.fallthrough⟩

theorem fault_statements
    {context staticFinal runtimeFinal : Context} {before after : Heap}
    {type : Ty} {failure : Failure} {complete allowed : Prop}
    (heap : HeapWellTyped context after) (extended : HeapTypesExtend before after) :
    StatementsPreserved context staticFinal runtimeFinal before after type (.fault failure) complete allowed :=
  ⟨heap, extended, (by intro _ value equal; cases equal), (by intro environment equal; cases equal)⟩

theorem terminal_statements
    {context staticFinal runtimeFinal : Context} {before after : Heap}
    {type : Ty} {outcome : BodyOutcome} {complete allowed : Prop}
    (post : ControlPreserved context before after type outcome)
    (terminal : ∀ environment, outcome ≠ .fallthrough environment) :
    StatementsPreserved context staticFinal runtimeFinal before after type outcome complete allowed :=
  ⟨post.heap_typed, post.heap_extends, fun _ => post.returned,
    fun environment equal => (terminal environment equal).elim⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
