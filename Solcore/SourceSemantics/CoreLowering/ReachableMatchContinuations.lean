import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree
import Solcore.SourceSemantics.Dynamic.Control

/-! Static stopping receipts for match continuations. A present default and
stopped branch bodies justify universal source stopping. Without a default,
exhaustiveness only excludes no-branch selection at a well-typed scrutinee.
The two boundaries stay separate. Actual suffix lowering is retained in its
original source; no execution law is stored in these receipts. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuations

open Frontend Frontend.SourceInference GenericLexicalStatements

structure BranchStops (source : TypedSource) (resolution : MatchResolution) : Prop where
  arms : ∀ arm, arm ∈ resolution.cases → Stopped source arm.body
  fallback : ∀ body, resolution.defaultBody = some body → Stopped source body

/-- The issuing source and full statement identity survive metadata views.
The default is required for this universal stopping receipt. -/
def DefaultStopped (source : TypedSource) (id : StatementId)
    (resolution : MatchResolution) : Prop :=
  ∃ origin node fallback, StatementSourceIdentity origin source ∧
    origin.lookupStatement? id = some node ∧ node.form = .matchWith resolution ∧
    resolution.defaultBody = some fallback ∧ BranchStops origin resolution

theorem DefaultStopped.of_source {source : TypedSource} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {fallback : List StatementId}
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback) (branches : BranchStops source resolution) :
    DefaultStopped source id resolution :=
  ⟨source, node, fallback, .refl source, found, form, present, branches⟩

theorem DefaultStopped.transport {origin source : TypedSource} {id : StatementId}
    {resolution : MatchResolution} (identity : StatementSourceIdentity origin source)
    (stops : DefaultStopped origin id resolution) : DefaultStopped source id resolution := by
  obtain ⟨issuing, node, fallback, original, found, form, present, branches⟩ := stops
  exact ⟨issuing, node, fallback, original.trans identity, found, form, present, branches⟩

theorem DefaultStopped.lookup {source : TypedSource} {id : StatementId}
    {resolution : MatchResolution} (stops : DefaultStopped source id resolution) :
    ∃ node, source.lookupStatement? id = some node ∧ node.form = .matchWith resolution := by
  obtain ⟨origin, node, _, identity, found, form, _, _⟩ := stops
  exact ⟨node, (identity.lookup id).symm.trans found, form⟩

theorem DefaultStopped.current_branches {source : TypedSource} {id : StatementId}
    {resolution : MatchResolution} (stops : DefaultStopped source id resolution) :
    BranchStops source resolution := by
  obtain ⟨origin, _, _, identity, _, _, _, branches⟩ := stops
  exact ⟨fun arm member => (branches.arms arm member).transport identity,
    fun body same => (branches.fallback body same).transport identity⟩

theorem DefaultStopped.default_present {source : TypedSource} {id : StatementId}
    {resolution : MatchResolution} (stops : DefaultStopped source id resolution) :
    ∃ fallback, resolution.defaultBody = some fallback := by
  obtain ⟨_, _, fallback, _, _, _, present, _⟩ := stops
  exact ⟨fallback, present⟩

/-- Static control stopping does not imply an untyped, universal execution law.
Its source meaning consumer requires the actual source typing environment. -/
structure MatchControlStopped (source : TypedSource) (control : ControlContext)
    (context : Context) (id : StatementId) (node : StatementNode)
    (resolution : MatchResolution) (facts : StatementFacts) : Prop where
  found : source.lookupStatement? id = some node
  form : node.form = .matchWith resolution
  typed : StatementHasType source control context id context facts
  no_fallthrough : facts.control.fallthrough = none

private theorem singleton_erased_stops {expected : TypeSystem.Ty} {facts : StatementFacts}
    {summary : ControlSummary} (erased : facts.control = summary.eraseValue)
    (complete : BodyCompletes expected (BodyFacts.singleton facts)) (nonunit : expected ≠ .unit) :
    facts.control.fallthrough = none := by
  rcases complete.2.2 with stopped | ordinary
  · exact stopped.1
  · rw [BodyFacts.singleton, erased] at ordinary
    cases summary with
    | mk fallthrough mayReturn mayBreak mayContinue =>
      cases fallthrough <;> simp_all [ControlSummary.eraseValue]

/-- The match's actual merged summary erases an ordinary value to Unit.
Consequently non-Unit singleton completion must use its no-fallthrough branch.
This conclusion is specific to the actual typed match, not BodyCompletes alone. -/
theorem MatchControlStopped.of_singleton_completes {source : TypedSource}
    {control : ControlContext} {context : Context} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {facts : StatementFacts} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (typed : StatementHasType source control context id context facts)
    (complete : BodyCompletes expected (BodyFacts.singleton facts)) (nonunit : expected ≠ .unit) :
    MatchControlStopped source control context id node resolution facts := by
  refine ⟨found, form, typed, ?_⟩
  have shape : ∀ other, ContainsStatement source id other → other.form = .matchWith resolution := by
    intro other contains
    have same : other = node := Option.some.inj
      ((lookupStatement?_complete unique contains).symm.trans found)
    exact same ▸ form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all
  all_goals exact singleton_erased_stops rfl complete nonunit

theorem merged_arm_stops {cases : List BodyFacts} {fallback : Option BodyFacts}
    {summary : ControlSummary} {facts : BodyFacts}
    (merged : mergeBodyControls cases fallback = some summary)
    (stops : summary.fallthrough = none) (member : facts ∈ cases) :
    facts.control.fallthrough = none := by
  cases actual : facts.control.fallthrough with
  | none => rfl
  | some type =>
    have falls := Dynamic.MergeBodyControls.canFallthrough_of_mem merged member
      (by simp [ControlSummary.canFallthrough, actual])
    simp [ControlSummary.canFallthrough, stops] at falls

theorem merged_default_stops {cases : List BodyFacts} {summary : ControlSummary} {facts : BodyFacts}
    (merged : mergeBodyControls cases (some facts) = some summary)
    (stops : summary.fallthrough = none) : facts.control.fallthrough = none := by
  cases actual : facts.control.fallthrough with
  | none => rfl
  | some type =>
    have falls := Dynamic.MergeBodyControls.canFallthrough_of_fallback merged
      (by simp [ControlSummary.canFallthrough, actual])
    simp [ControlSummary.canFallthrough, stops] at falls

/-- Exhaustive no-default selection retains the actual static cases and
scrutinee type. Its dynamic consumer separately supplies ValueHasType. -/
structure TypedNoDefault (source : TypedSource) (control : ControlContext) (context : Context)
    (resolution : MatchResolution) (scrutineeType : TypeSystem.Ty)
    (caseFacts : List BodyFacts) : Prop where
  absent : resolution.defaultBody = none
  cases_typed : MatchCasesHaveType source control context scrutineeType resolution.cases caseFacts
  exhaustive : MatchExhaustive context scrutineeType resolution.cases none

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error reason => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

/-- The actual match callback and the whole accepted dead suffix are recovered
from the original lowering equation, including the callback's child lowerer. -/
theorem match_issued {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLoops.Scope} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {resolution : MatchResolution} {type readType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {mode : Bool} {escaped : Core.Word} {code : Core.Expr}
    (read : policy.readStatement source id = .ok (node, readType))
    (form : node.form = .matchWith resolution)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
      (id :: rest) type reasonAt mode escaped = .ok code) :
    ∃ callback matched suffix,
      policy.lowerMatch = some callback ∧
      callback policy.lowerExpression
        (fun _ childSource childScope statements resultType childReasonAt childSelfReason =>
          SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel childSource childScope statements
            resultType childReasonAt false childSelfReason)
        fuel source scope id resolution type reasonAt escaped = .ok matched ∧
      ReachableStatementContinuations.Issued policy fuel source scope rest type reasonAt mode escaped suffix ∧
      code = Core.LocalLoop.sequence type matched suffix := by
  simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, bind, Except.bind, form] at accepted
  cases callbackEq : policy.lowerMatch with
  | none => simp [callbackEq] at accepted
  | some callback =>
    simp only [callbackEq] at accepted
    obtain ⟨matched, matchedEq, accepted⟩ := bind_ok accepted
    obtain ⟨suffix, suffixEq, accepted⟩ := bind_ok accepted
    cases accepted
    exact ⟨callback, matched, suffix, rfl, matchedEq, ⟨suffixEq⟩, rfl⟩

end Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuations
