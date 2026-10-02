import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts
import Solcore.Test.SourceCoreRecursiveNamedCatalog

/-! These consumers use finite independent source derivations. A size is
obtained from every original rule, and actual call/loop children lie below
their containing derivation. Fault sizes also include completed successful
prefixes. Cached Core regressions retain self/mutual calls, writes and resume;
this unit does not yet prove recursive source/native correspondence. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedTraceBounds
open Solcore Frontend SourceInference SourceSemantics
open SourceSemantics.CoreLowering

#check_failure SourceTypedRuntime.run

section Leaves
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {heap : Dynamic.Heap} {id : ExpressionId}

example : SourceExecutionSize.ExpressionsEvaluate program 1 context evidence source
    environment heap [] [] heap := .nil

example (absent : Dynamic.ExpressionMissing source id) :
    SourceExecutionSize.ExpressionFaults program 1 context evidence source environment
      heap id (.missingExpression id) heap := .missing absent
end Leaves

section Calls
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
  {function : Dynamic.GlobalFunction} {arguments : List Dynamic.Value}
  {result : Dynamic.Value} {size : Nat}

/-- Actual named dispatch exposes its retained source body strictly below the
whole call. The instantiation fact is recovered from that dispatch. -/
theorem callee_below
    (trace : SourceExecutionSize.CallableApplies program size context caller invocation before
      (.global function) arguments result after) :
    ∃ body child,
      Dynamic.FunctionInstantiates program function.instantiation body ∧
      SourceExecutionSize.BodyInvokes program child body invocation before arguments result after ∧ child < size := by
  cases trace with
  | global instantiated _ _ invoked =>
    exact ⟨_, _, instantiated, invoked, SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- Existence is proved from the original independent dispatch, including
self or mutual calls represented by its finite body derivation. -/
theorem original_callee_below
    (trace : Dynamic.CallableApplies program context caller invocation before
      (.global function) arguments result after) :
    ∃ total body child,
      SourceExecutionSize.CallableApplies program total context caller invocation before
        (.global function) arguments result after ∧
      Dynamic.FunctionInstantiates program function.instantiation body ∧
      SourceExecutionSize.BodyInvokes program child body invocation before arguments result after ∧ child < total := by
  obtain ⟨total, sized⟩ := SourceExecutionSize.CallableApplies.has_size trace
  obtain ⟨body, child, instantiated, invoked, smaller⟩ := callee_below sized
  exact ⟨total, body, child, sized, instantiated, invoked, smaller⟩

/-- A body fault after parameter allocation remains a smaller actual child
of the source named-call fault rule. -/
theorem fault_callee_below {body : Dynamic.BodyInstance} {reason : Dynamic.SemanticFault}
    (instantiated : Dynamic.FunctionInstantiates program function.instantiation body)
    (same : invocation = function.evidence)
    (trace : SourceExecutionSize.BodyFaults program size body invocation before arguments reason after) :
    ∃ total,
      SourceExecutionSize.CallableFaults program total context caller invocation before
        (.global function) arguments reason after ∧ size < total :=
  ⟨_, .globalBody instantiated same trace, SourceExecutionSize.child_lt_stepSize (by simp)⟩
end Calls

section Prefixes
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before middle after : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
  {value : Dynamic.Value} {reason : Dynamic.SemanticFault}

/-- The preceding successful expression is counted even when the rest of
the ordered argument vector faults. Both original children erase unchanged. -/
theorem successful_prefix_in_fault
    (head : Dynamic.ExpressionEvaluates program context evidence source environment before id value middle)
    (tail : Dynamic.ExpressionsFault program context evidence source environment middle ids reason after) :
    ∃ total first second,
      SourceExecutionSize.ExpressionsFault program total context evidence source environment before (id :: ids) reason after ∧
      SourceExecutionSize.ExpressionEvaluates program first context evidence source environment before id value middle ∧
      SourceExecutionSize.ExpressionsFault program second context evidence source environment middle ids reason after ∧
      first < total ∧ second < total := by
  obtain ⟨first, head⟩ := SourceExecutionSize.ExpressionEvaluates.has_size head
  obtain ⟨second, tail⟩ := SourceExecutionSize.ExpressionsFault.has_size tail
  exact ⟨_, first, second, .tail head tail, head, tail,
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- Escaped control is a fault rule containing a successful body derivation.
That successful premise is retained rather than treated as a leaf. -/
theorem escaped_success_is_counted
    {body : Dynamic.BodyInstance} {arguments : List Dynamic.Value} {roots : List StatementId}
    {inputTypes : List TypeSystem.Ty} {lexicalContext finalContext : SourceSemantics.Context}
    {bound : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (root : Dynamic.StatementRoots body.source.roots roots)
    (inputs : MonoBindersExtend body.source.owner body.context body.source.inputs inputTypes lexicalContext)
    (allocate : Dynamic.BindersAllocate [] before body.source.inputs arguments environment bound)
    (execute : Dynamic.FunctionStatementsExecute program lexicalContext evidence body.source
      environment bound roots finalContext outcome after)
    (escaped : (∃ env, outcome = .breaking env) ∨ (∃ env, outcome = .continuing env)) :
    ∃ total child,
      SourceExecutionSize.BodyFaults program total body evidence before arguments .controlEscapedFunction after ∧
      SourceExecutionSize.FunctionStatementsExecute program child lexicalContext evidence body.source
        environment bound roots finalContext outcome after ∧ child < total := by
  obtain ⟨child, execute⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size execute
  exact ⟨_, child, .controlEscape root inputs allocate execute escaped, execute,
    SourceExecutionSize.child_lt_stepSize (by simp)⟩
end Prefixes

section Loops
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before conditionHeap bodyHeap postHeap after : Dynamic.Heap} {condition : ExpressionId}
  {body : List StatementId} {post : List ForItemForm}
  {bodyContext postContext : SourceSemantics.Context} {bodyEnvironment postEnvironment : Dynamic.Environment}
  {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

/-- A continuing source for loop counts condition, body, post and the next
iteration as separate actual children, in execution order. -/
theorem for_continue_children
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : Dynamic.StatementsExecute program context evidence source environment
      conditionHeap body bodyContext (.continuing bodyEnvironment) bodyHeap)
    (postTrace : Dynamic.ForItemsExecute program context evidence source environment
      bodyHeap post postContext postEnvironment postHeap)
    (nextTrace : Dynamic.ForLoopExecutes program context evidence source environment
      postHeap condition post body context outcome after) :
    ∃ total c b p n,
      SourceExecutionSize.ForLoopExecutes program total context evidence source environment before
        condition post body context outcome after ∧
      SourceExecutionSize.ExpressionEvaluates program c context evidence source environment before
        condition (.bool true) conditionHeap ∧
      SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap
        body bodyContext (.continuing bodyEnvironment) bodyHeap ∧
      SourceExecutionSize.ForItemsExecute program p context evidence source environment bodyHeap
        post postContext postEnvironment postHeap ∧
      SourceExecutionSize.ForLoopExecutes program n context evidence source environment postHeap
        condition post body context outcome after ∧ c < total ∧ b < total ∧ p < total ∧ n < total := by
  obtain ⟨c, conditionTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size conditionTrace
  obtain ⟨b, bodyTrace⟩ := SourceExecutionSize.StatementsExecute.has_size bodyTrace
  obtain ⟨p, postTrace⟩ := SourceExecutionSize.ForItemsExecute.has_size postTrace
  obtain ⟨n, nextTrace⟩ := SourceExecutionSize.ForLoopExecutes.has_size nextTrace
  exact ⟨_, c, b, p, n, .nextContinue conditionTrace bodyTrace postTrace nextTrace,
    conditionTrace, bodyTrace, postTrace, nextTrace,
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp),
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- A later loop fault still counts all three successful prefixes. It is
strictly smaller than the parent without claiming equal source/Core cost. -/
theorem for_later_fault_children
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : Dynamic.StatementsExecute program context evidence source environment
      conditionHeap body bodyContext (.fallthrough bodyEnvironment) bodyHeap)
    (postTrace : Dynamic.ForItemsExecute program context evidence source environment
      bodyHeap post postContext postEnvironment postHeap)
    (nextTrace : Dynamic.ForLoopFaults program context evidence source environment
      postHeap condition post body reason after) :
    ∃ total c b p n,
      SourceExecutionSize.ForLoopFaults program total context evidence source environment before condition post body reason after ∧
      c < total ∧ b < total ∧ p < total ∧ n < total ∧
      SourceExecutionSize.ExpressionEvaluates program c context evidence source environment before condition (.bool true) conditionHeap ∧
      SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap body bodyContext
        (.fallthrough bodyEnvironment) bodyHeap ∧
      SourceExecutionSize.ForItemsExecute program p context evidence source environment bodyHeap post postContext postEnvironment postHeap ∧
      SourceExecutionSize.ForLoopFaults program n context evidence source environment postHeap condition post body reason after := by
  obtain ⟨c, conditionTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size conditionTrace
  obtain ⟨b, bodyTrace⟩ := SourceExecutionSize.StatementsExecute.has_size bodyTrace
  obtain ⟨p, postTrace⟩ := SourceExecutionSize.ForItemsExecute.has_size postTrace
  obtain ⟨n, nextTrace⟩ := SourceExecutionSize.ForLoopFaults.has_size nextTrace
  exact ⟨_, c, b, p, n, .nextFallthrough conditionTrace bodyTrace postTrace nextTrace,
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp),
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp),
    conditionTrace, bodyTrace, postTrace, nextTrace⟩

/-- While body effects and its later fault also use the same measure. -/
theorem while_later_fault_children
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : Dynamic.StatementsExecute program context evidence source environment
      conditionHeap body bodyContext (.fallthrough bodyEnvironment) bodyHeap)
    (nextTrace : Dynamic.WhileFaults program context evidence source environment
      bodyHeap condition body reason after) :
    ∃ total c b n,
      SourceExecutionSize.WhileFaults program total context evidence source environment before condition body reason after ∧
      SourceExecutionSize.ExpressionEvaluates program c context evidence source environment before condition (.bool true) conditionHeap ∧
      SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap body bodyContext
        (.fallthrough bodyEnvironment) bodyHeap ∧
      SourceExecutionSize.WhileFaults program n context evidence source environment bodyHeap condition body reason after ∧
      c < total ∧ b < total ∧ n < total := by
  obtain ⟨c, conditionTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size conditionTrace
  obtain ⟨b, bodyTrace⟩ := SourceExecutionSize.StatementsExecute.has_size bodyTrace
  obtain ⟨n, nextTrace⟩ := SourceExecutionSize.WhileFaults.has_size nextTrace
  exact ⟨_, c, b, n, .nextFallthrough conditionTrace bodyTrace nextTrace,
    conditionTrace, bodyTrace, nextTrace, SourceExecutionSize.child_lt_stepSize (by simp),
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩
end Loops

end Tests.SourceCoreRecursiveNamedTraceBounds

namespace Tests.SourceCoreRecursiveNamedTraceBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof

section SourceBoundary
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {size : Nat}
  {context callContext : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {caller : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
  {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}

/-- Both original source call and original function-statement sizes survive
dispatch and parameter allocation; no body execution is an extra premise. -/
theorem actual_source_function_below
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types callContext)
    (arity : function.parameters.length = arguments.length)
    (called : RecursiveNamedCallBounds.CallOutcome program size context caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after) :
    ∃ bodySize traceSize environment bound,
      RecursiveNamedCallBounds.BodyOutcome program bodySize body function.evidence before arguments outcome after ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program traceSize function callContext environment bound outcome after ∧
      traceSize < bodySize ∧ bodySize < size := by
  obtain ⟨bodySize, invoked, bodyLess⟩ := RecursiveNamedCallBounds.source_call_body unique frame arity called
  obtain ⟨traceSize, environment, bound, allocated, traced, traceLess⟩ :=
    RecursiveNamedCallBounds.body_trace frame extended arity invoked
  exact ⟨bodySize, traceSize, environment, bound, invoked, allocated, traced, traceLess, bodyLess⟩
end SourceBoundary

private def traceBody (reason : Word) : Expr :=
  .letE (.storeCell (.var 1) (.word (Word.ofNatModulo 7))) (.inLeft .word (.word reason))
private def traceClosure (reason : Word) : Value :=
  .closure .unit (LanguageResult.resultType .word) (traceBody reason) [.cellRef .word 0]
private def traceBefore (reason : Word) : Store := [.word Word.zero, .inRight .unit (traceClosure reason)]
private def traceAfter (reason : Word) : Store := [.word (Word.ofNatModulo 7), .inRight .unit (traceClosure reason)]
private def traceCellType : Ty := OptionalCell.cellType (.function .unit (LanguageResult.resultType .word))

/-- An actual finite call writes through its saved capture and faults. The
smaller saved-body trace comes from that exact original completion. -/
theorem captured_fault_original_child (key : SourceSpecialization.SpecializationKey) (reason : Word) :
    ∃ total child,
      EvaluationSize total [.cellRef traceCellType 1] (traceBefore reason)
        (SourceCoreCalls.call ⟨key, .unit, .word⟩ 0 (LanguageResult.success .unit) Word.zero)
        (.inLeft .word (.word reason)) (traceAfter reason) ∧
      EvaluationSize child [.unit, .cellRef .word 0] (traceBefore reason)
        (traceBody reason) (.inLeft .word (.word reason)) (traceAfter reason) ∧ child < total := by
  have executed : Evaluates [.cellRef traceCellType 1] (traceBefore reason)
      (SourceCoreCalls.call ⟨key, .unit, .word⟩ 0 (LanguageResult.success .unit) Word.zero)
      (.inLeft .word (.word reason)) (traceAfter reason) := by
    exact .caseRight (.inRight .unit) (.caseRight
      (.caseRight (.loadCell (.var rfl) rfl) (.inRight (.var rfl)))
      (.apply (.var rfl) (.var rfl)
        (.letE (.storeCell (.var rfl) rfl .word (by simp [traceBefore, traceAfter, Store.write?])) (.inLeft .word))))
  obtain ⟨total, completed⟩ := evaluation_has_size executed
  obtain ⟨child, smaller, bodyTrace⟩ := RecursiveNamedCallBounds.call_body
    (show Evaluates _ _ (LanguageResult.success .unit) (.inRight .word .unit) _ from .inRight .unit)
    (show ([.cellRef traceCellType 1] : Environment)[0]? = some (.cellRef traceCellType 1) from rfl)
    (show (traceBefore reason).read? 1 = some (.inRight .unit (traceClosure reason)) from rfl) completed
  exact ⟨total, child, completed, bodyTrace, smaller⟩

/-- The actual frame wrapper restores its administrative cell after a body
fault, while retaining the separate captured write. Both real subtraces are
strict children of the original wrapper trace. -/
theorem frame_fault_restores_original_child (reason : Word) :
    ∃ total nextSize bodySize bodyStore,
      EvaluationSize total [.cellRef .integer 0, .cellRef .word 1]
        [.integer 12, .word Word.zero]
        (SourceCoreCallableContextFrames.withFrame (.var 0) (.integer 33) (traceBody reason))
        (.inLeft .word (.word reason)) [.integer 12, .word (Word.ofNatModulo 7)] ∧
      EvaluationSize nextSize (.integer 12 :: [.cellRef .integer 0, .cellRef .word 1])
        [.integer 12, .word Word.zero] ((Expr.integer 33).weakenAt 0) (.integer 33)
        [.integer 12, .word Word.zero] ∧
      EvaluationSize bodySize (.unit :: .integer 12 :: [.cellRef .integer 0, .cellRef .word 1])
        [.integer 33, .word Word.zero] (((traceBody reason).weakenAt 0).weakenAt 0)
        (.inLeft .word (.word reason)) bodyStore ∧
      nextSize < total ∧ bodySize < total ∧
      [.integer 12, .word (Word.ofNatModulo 7)] = bodyStore.set 0 (.integer 12) := by
  have bodyEval : Evaluates (.unit :: .integer 12 :: [.cellRef .integer 0, .cellRef .word 1])
      [.integer 33, .word Word.zero] (((traceBody reason).weakenAt 0).weakenAt 0)
      (.inLeft .word (.word reason)) [.integer 33, .word (Word.ofNatModulo 7)] := by
    simp [traceBody, Expr.weakenAt]
    exact .letE (bodyStore := [.integer 33, .word (Word.ofNatModulo 7)])
      (.storeCell (initialStore := [.integer 33, .word Word.zero])
        (referenceStore := [.integer 33, .word Word.zero]) (valueStore := [.integer 33, .word Word.zero])
        (location := 1) (oldValue := .word Word.zero) (.var rfl) rfl .word (by simp [Store.write?])) (.inLeft .word)
  have executed := CallableContextFrames.withFrame_evaluates
    (show DataEquality.Selects [.cellRef .integer 0, .cellRef .word 1] (.var 0) (.cellRef .integer 0) from .var rfl)
    (show Store.read? [.integer 12, .word Word.zero] 0 = some (.integer 12) from rfl)
    (show Evaluates (.integer 12 :: [.cellRef .integer 0, .cellRef .word 1])
      [.integer 12, .word Word.zero] ((Expr.integer 33).weakenAt 0) (.integer 33)
      [.integer 12, .word Word.zero] from by simpa only [Expr.weakenAt] using (Evaluates.integer (environment := .integer 12 :: [.cellRef .integer 0, .cellRef .word 1]) (store := [.integer 12, .word Word.zero]) (value := 33))) bodyEval
  obtain ⟨total, completed⟩ := evaluation_has_size executed
  obtain ⟨nextSize, bodySize, installed, nextStore, bodyStore, nextTrace, bodyTrace, nextLess, bodyLess, restored⟩ :=
    RecursiveNamedCallBounds.with_frame (.var rfl) rfl completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextTrace.sound
    (show Evaluates _ _ ((Expr.integer 33).weakenAt 0) (.integer 33) _ from by simpa only [Expr.weakenAt] using (Evaluates.integer (value := 33)))
  exact ⟨total, nextSize, bodySize, bodyStore, completed, nextTrace, bodyTrace, nextLess, bodyLess, restored⟩

/-- A callback limited to this original outer trace is consumed only for its
actual smaller child. No unrestricted body contract is reconstructed. -/
theorem actual_child_callback {contract : Nat → Prop}
    {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {total : Nat} {environment : Environment} {store finalStore : Store} {value : Value}
    (callbacks : RecursiveNamedBoundedContracts.Below total contract)
    (completed : EvaluationSize total environment store (SourceCoreCalls.call signature index arguments reason) value finalStore) :
    ∃ child argumentValue argumentStore,
      contract child ∧ child < total ∧ EvaluationSize child environment store arguments argumentValue argumentStore := by
  obtain ⟨child, argumentValue, argumentStore, smaller, trace⟩ := RecursiveNamedCallBounds.call_arguments completed
  exact ⟨child, argumentValue, argumentStore, callbacks.child smaller, smaller, trace⟩

end Tests.SourceCoreRecursiveNamedTraceBounds

namespace Tests.SourceCoreRecursiveNamedTraceBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

/-- Actual accepted parameter compilation and its original completion supply
both the final environment typing and the smaller body derivation. The caller
supplies only typing of the initial actual environment. -/
theorem accepted_parameters_typed_child {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {output : Ty} {body code : Expr}
    {scope : Scope} {bindings : List Binding}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      source scope bindings output SourceCoreFunctions.argumentProjection body = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
    {canonical logical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[0]? = some (DataPatternValues.packValues values))
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) result afterStore) :
    ∃ finalActual finalStore finalWorld finalEmbedding child,
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (CallableIndexedParameterTyped.prefixContext bindings actualContext) nativeDefinitions ∧
      EvaluationSize child finalActual finalStore (body.rename finalEmbedding) result afterStore ∧
      child ≤ size ∧ (bindings ≠ [] → child < size) := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, child, allocated, finalEnvironments, finalHeaps, maps, worlds,
    frame, finalLayout, finalAgrees, spine, finalTyped, childTrace, weak, strict⟩ :=
    RecursiveNamedCallBounds.parameter_prefix tree definitions registered represented environments heaps
      sourceLayout actualLayout actualTyped bundleSlot
      (allTypes := bindings.map Prod.snd) (by simp)
      (by simpa only [List.length_map] using represented.length.2)
      (fun found => by simpa using found) kinds reference read unmapped completed
  exact ⟨finalActual, finalStore, finalWorld, finalEmbedding, child, finalTyped, childTrace, weak, strict⟩

end Tests.SourceCoreRecursiveNamedTraceBounds


namespace Tests.SourceCoreRecursiveNamedTraceBounds
open Solcore Core Frontend

def runBounds : IO Unit := do
  let reason := Word.ofNatModulo 19
  let artifact ← SourceCoreUnifiedCorpusSupport.prepare "original native helper bounds"
    "function helper() returns (Word) { return 19; }" ["helper"]
  let key ← match artifact.indexed.base.functions with
    | function :: _ => pure function.signature.key
    | [] => throw (IO.userError "original native helper bounds missing checked key")
  let signature : SourceCoreCalls.Signature := ⟨key, .unit, .word⟩
  let cases := [
    (State.initial (SourceCoreCalls.call signature 0 (LanguageResult.success .unit) Word.zero)
      [.cellRef traceCellType 1] (traceBefore reason), traceAfter reason),
    (State.initial (SourceCoreCallableContextFrames.withFrame (.var 0) (.integer 33) (traceBody reason))
      [.cellRef .integer 0, .cellRef .word 1] [.integer 12, .word Word.zero],
      [.integer 12, .word (Word.ofNatModulo 7)])]
  for (initial, expected) in cases do
    for fuel in [0, 1, 7, 31] do
      let completed := match runStateful fuel initial with
        | .outOfFuel checkpoint => runStateful 1000 checkpoint
        | result => result
      SourceCoreUnifiedCorpusSupport.assertTrue
        (LanguageResult.observeResult completed == .failed reason expected)
        "original call/frame trace lost a captured fault write or frame restoration on resume"
  IO.println "recursive named trace bounds: all 40 source judgment bridges; actual source call/body children, original Core call/frame/parameter/finish sizes, typed parameter continuation, guarded pointwise budgets, captured faults and resume GREEN"

def run : IO Unit := do
  Tests.SourceCoreRecursiveNamedCatalog.run
  runBounds

end Tests.SourceCoreRecursiveNamedTraceBounds
