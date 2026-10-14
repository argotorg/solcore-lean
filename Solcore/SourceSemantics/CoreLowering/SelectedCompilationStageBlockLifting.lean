import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBlockLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchPreserves)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

include bridge functions condition in
/-- A scoped block keeps the physical state reached by its inner execution.
Its suffix starts with the restored outer bindings and that same heap. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest statements : List StatementId} {node : StatementNode}
    {expected : TypeSystem.Ty} {type : Ty} {innerCode : Expr}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope false statements budget)
    (preservation : ∀ childSize, BranchPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope statements expected type innerCode childSize)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget ∨
      GenericLexicalStatements.Stopped invocation.source statements) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  have notTail : ∀ expression, node.form ≠ .expression expression false := by
    intro expression same
    rw [form] at same
    cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨headSize, reason, strict, contextEq, outcomeEq, failed⟩ |
    ⟨headSize, strict, stopped, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, executed, tail⟩
  · subst finalContext
    subst outcome
    obtain ⟨innerSize, innerContext, innerStrict, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_fault unique found form failed
    obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans innerStrict strict)) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      (show PlainStatements program false innerSize invocation context environment before statements
        innerContext (.fault reason) after from .fault innerTrace)
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
  · obtain ⟨innerSize, innerContext, innerOutcome, innerStrict, contextEq, outcomeEq, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst finalContext
    subst outcome
    obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans innerStrict strict)) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      (show PlainStatements program false innerSize invocation context environment before statements
        innerContext innerOutcome after from .control innerTrace)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
    | completed matched =>
      cases matched with
      | returned value =>
        exact ⟨context, _, _, .blockReturned (lookupStatement?_sound found) form lifted, .completed (.returned value)⟩
      | breaking innerEnvironment =>
        exact ⟨context, _, _, .blockBreaking (lookupStatement?_sound found) form lifted, .completed (.breaking environment)⟩
      | continuing innerEnvironment =>
        exact ⟨context, _, _, .blockContinuing (lookupStatement?_sound found) form lifted, .completed (.continuing environment)⟩
      | fault reason =>
        exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        rcases stopped with impossible | rfl
        · cases impossible
        · exact ⟨context, _, _, .blockFallthrough (lookupStatement?_sound found) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨innerSize, innerContext, innerOutcome, innerStrict, contextEq, restored, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl, Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
        (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans innerStrict strict)) within)
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
        (show PlainStatements program false innerSize invocation context environment before statements
          innerContext (.fallthrough innerEnvironment) middle from .control innerTrace)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
      | completed matched =>
        cases matched
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace lifted
        rcases remaining with remaining | stopped
        · obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
            preservation stagedSize (Nat.le_refl _) environments heaps locals agrees actualTyped
              reference read unmapped initial conditioned admitted measured
          obtain ⟨lastContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
            (Nat.le_trans (Nat.le_of_lt tailStrict) within)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            reference ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned post tail
          exact ⟨lastContext, result, finalHeap, .blockFallthrough (lookupStatement?_sound found) form lifted restTrace,
            restAdapted⟩
        · exact False.elim (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.stopped_not_fallthrough unique stopped measured)

    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBlockLifting
