import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews
import Solcore.Frontend.SourceCoreLoops

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
