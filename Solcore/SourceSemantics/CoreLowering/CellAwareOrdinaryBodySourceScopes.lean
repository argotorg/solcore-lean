import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourcePrefixes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardInversion
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning

/-! Exact ordinary Source lifting restores lexical environments at each block
while retaining every reached heap change. Only an actual fallthrough uses the suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
open Core Frontend SourceInference Staging.Recursive
open SelectedCompilationStageScopedLiftBounds (PlainStatements)
variable {program : Program} {registry : Registry} {invocation : Scope}

theorem Post.trans {context before middle after outcome}
    (extension : Dynamic.HeapTypesExtend before middle)
    (post : Post context middle after outcome) : Post context before after outcome := by
  cases outcome <;> try exact trivial
  all_goals exact ⟨post.1,extension.trans post.2⟩

theorem discard (wellFormed : ProgramWellFormed program)
    {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context scope mode semicolon id node expression expressionNode lowered rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
    (continuing : semicolon = true ∨ mode = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope expression lowered)
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) context mode rest) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  rcases SelectedCompilationStageDiscardInversion.child_and_tail state.runtime.graph.nodeOccurrencesUnique found form continuing trace with failed | done
  · obtain ⟨_,_,_,rfl,rfl,child⟩ := failed
    exact ⟨.expressionFault (lookupStatement?_sound found) form (CellAwareOrdinaryBodySourceState.expression certificate state.runtime.graph.nodeOccurrencesUnique child),trivial⟩
  · obtain ⟨_,_,_,_,_,_,child,tail⟩ := done
    have first := CellAwareOrdinaryBodySourceState.expression (registry := registry) certificate state.runtime.graph.nodeOccurrencesUnique child
    obtain ⟨_,reached,extension⟩ := expression_typed wellFormed certificate expressionFound state child
    obtain ⟨lifted,post⟩ := remaining reached tail
    refine ⟨?_,post.trans extension⟩
    rcases continuing with rfl | rfl
    · exact .discard (lookupStatement?_sound found) form first lifted
    · cases semicolon with
      | false => exact .discardValue (lookupStatement?_sound found) form first lifted
      | true => exact .discard (lookupStatement?_sound found) form first lifted

theorem block {context mode id node statements rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Lifts (program := program) (registry := registry) (invocation := invocation) context false statements)
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) context mode rest ∨
      GenericLexicalStatements.Stopped invocation.source statements) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  have unique := state.runtime.graph.nodeOccurrencesUnique
  have notTail : ∀ expression, node.form ≠ .expression expression false := by
    intro expression same; rw [form] at same; cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨_,reason,_,rfl,rfl,failed⟩ | ⟨_,_,stopped,executed⟩ | ⟨_,_,middleContext,nextEnvironment,middle,_,_,executed,tail⟩
  · obtain ⟨_,innerContext,_,innerTrace⟩ := SelectedCompilationStageScopedSourceInversion.block_fault unique found form failed
    obtain ⟨lifted,_⟩ := inner state (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .fault innerTrace)
    exact ⟨.blockFault (lookupStatement?_sound found) form lifted,trivial⟩
  · obtain ⟨_,innerContext,innerOutcome,_,sameContext,sameOutcome,innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst finalContext outcome
    obtain ⟨lifted,post⟩ := inner state (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .control innerTrace)
    cases innerOutcome with
    | returned value => exact ⟨.blockReturned (lookupStatement?_sound found) form lifted,post⟩
    | breaking innerEnvironment => exact ⟨.blockBreaking (lookupStatement?_sound found) form lifted,post⟩
    | continuing innerEnvironment => exact ⟨.blockContinuing (lookupStatement?_sound found) form lifted,post⟩
    | fault reason => exact ⟨.blockFault (lookupStatement?_sound found) form lifted,trivial⟩
    | fallthrough innerEnvironment =>
      rcases stopped with impossible | rfl
      · cases impossible
      · exact ⟨.blockFallthrough (lookupStatement?_sound found) form lifted .nil,post⟩
  · obtain ⟨_,innerContext,innerOutcome,_,sameContext,restored,innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl,Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      obtain ⟨lifted,post⟩ := inner state (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .control innerTrace)
      rcases remaining with remaining | stopped
      · have reached : State (program := program) (invocation := invocation) context environment middle :=
          ⟨state.runtime,state.covers,state.locals.mono post.2,post.1⟩
        obtain ⟨restTrace,restPost⟩ := remaining reached tail
        exact ⟨.blockFallthrough (lookupStatement?_sound found) form lifted restTrace,restPost.trans post.2⟩
      · have impossible := stopped.terminates unique false innerTrace.sound
        cases impossible
    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
