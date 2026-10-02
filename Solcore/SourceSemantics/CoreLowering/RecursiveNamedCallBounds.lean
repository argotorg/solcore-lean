import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
import Solcore.SourceSemantics.CoreLowering.NamedCallArgumentMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped
import Solcore.SourceSemantics.CoreLowering.ImperativeFunctionFinish
import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning

/-! Bounds carried by the original finite source and Core derivations.
Outcome wrappers retain the size of their underlying judgment. Actual helper
inversion keeps the original child witness, including its emitted renaming,
store and retained captures. Source and Core sizes have separate roles. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly DataEquality
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedAllocationCompletion
open CallableIndexedParameterMeaning CallableIndexedParameterTyped

inductive ExpressionOutcome (program : Program) (size : Nat) :
    SourceSemantics.Context → Dynamic.EvidenceEnvironment → TypedSource → Dynamic.Environment →
      Dynamic.Heap → ExpressionId → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {context evidence source environment before after id value}
      (trace : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id value after) :
      ExpressionOutcome program size context evidence source environment before id (.value value) after
  | fault {context evidence source environment before after id reason}
      (trace : SourceExecutionSize.ExpressionFaults program size context evidence source environment before id reason after) :
      ExpressionOutcome program size context evidence source environment before id (.fault reason) after

inductive CallOutcome (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (function : Dynamic.Value) (arguments : List Dynamic.Value) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {result after}
      (trace : SourceExecutionSize.CallableApplies program size context caller invocation before function arguments result after) :
      CallOutcome program size context caller invocation before function arguments (.value result) after
  | fault {reason after}
      (trace : SourceExecutionSize.CallableFaults program size context caller invocation before function arguments reason after) :
      CallOutcome program size context caller invocation before function arguments (.fault reason) after

inductive BodyOutcome (program : Program) (size : Nat) (body : Dynamic.BodyInstance)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap) (arguments : List Dynamic.Value) :
      Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {result after} (trace : SourceExecutionSize.BodyInvokes program size body evidence before arguments result after) :
      BodyOutcome program size body evidence before arguments (.value result) after
  | fault {reason after} (trace : SourceExecutionSize.BodyFaults program size body evidence before arguments reason after) :
      BodyOutcome program size body evidence before arguments (.fault reason) after

inductive StatementsOutcome (program : Program) (size : Nat) :
    SourceSemantics.Context → Dynamic.EvidenceEnvironment → TypedSource → Dynamic.Environment → Dynamic.Heap →
      List StatementId → SourceSemantics.Context → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {context finalContext evidence source environment before after statements outcome}
      (trace : SourceExecutionSize.StatementsExecute program size context evidence source environment before statements finalContext outcome after) :
      StatementsOutcome program size context evidence source environment before statements finalContext outcome after
  | fault {context finalContext evidence source environment before after statements reason}
      (trace : SourceExecutionSize.StatementsFault program size context evidence source environment before statements finalContext reason after) :
      StatementsOutcome program size context evidence source environment before statements finalContext (.fault reason) after

inductive FunctionOutcome (program : Program) (size : Nat) :
    SourceSemantics.Context → Dynamic.EvidenceEnvironment → TypedSource → Dynamic.Environment → Dynamic.Heap →
      List StatementId → SourceSemantics.Context → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {context finalContext evidence source environment before after statements outcome}
      (trace : SourceExecutionSize.FunctionStatementsExecute program size context evidence source environment before statements finalContext outcome after) :
      FunctionOutcome program size context evidence source environment before statements finalContext outcome after
  | fault {context finalContext evidence source environment before after statements reason}
      (trace : SourceExecutionSize.FunctionStatementsFault program size context evidence source environment before statements finalContext reason after) :
      FunctionOutcome program size context evidence source environment before statements finalContext (.fault reason) after

inductive BodyTrace (program : Program) (size : Nat) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap) :
      Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | returned {finalContext result after}
      (trace : SourceExecutionSize.FunctionStatementsExecute program size context function.evidence function.source
        environment before function.body finalContext (.returned result) after) :
      BodyTrace program size function context environment before (.value result) after
  | unit {finalContext finalEnvironment after} (same : function.resultType = .unit)
      (trace : SourceExecutionSize.FunctionStatementsExecute program size context function.evidence function.source
        environment before function.body finalContext (.fallthrough finalEnvironment) after) :
      BodyTrace program size function context environment before (.value .unit) after
  | fault {finalContext reason after}
      (trace : SourceExecutionSize.FunctionStatementsFault program size context function.evidence function.source
        environment before function.body finalContext reason after) :
      BodyTrace program size function context environment before (.fault reason) after
  | escaped {finalContext control after}
      (trace : SourceExecutionSize.FunctionStatementsExecute program size context function.evidence function.source
        environment before function.body finalContext control after)
      (escape : (∃ environment, control = .breaking environment) ∨ (∃ environment, control = .continuing environment)) :
      BodyTrace program size function context environment before (.fault .controlEscapedFunction) after

theorem ExpressionOutcome.sound {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {id : ExpressionId} {outcome : Dynamic.ExpressionOutcome}
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | value trace => exact .value trace.sound
  | fault trace => exact .fault trace.sound

theorem ExpressionOutcome.has_size {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {id : ExpressionId} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) : ∃ size, ExpressionOutcome program size context evidence source environment before id outcome after := by
  cases trace with
  | value trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size trace
    exact ⟨size, .value trace⟩
  | fault trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.ExpressionFaults.has_size trace
    exact ⟨size, .fault trace⟩

theorem ExpressionOutcome.positive {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {id : ExpressionId} {outcome : Dynamic.ExpressionOutcome}
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) : 0 < size := by
  cases trace with
  | value trace => exact trace.positive
  | fault trace => exact trace.positive

theorem ExpressionOutcome.iff_size {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {id : ExpressionId} {outcome : Dynamic.ExpressionOutcome} :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ↔ ∃ size, ExpressionOutcome program size context evidence source environment before id outcome after :=
  ⟨ExpressionOutcome.has_size, fun ⟨_, trace⟩ => trace.sound⟩

theorem CallOutcome.sound {program : Program} {size : Nat} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {function : Dynamic.Value} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : CallOutcome program size context caller invocation before function arguments outcome after) : FunctionCallBody.Outcome program context caller invocation before function arguments outcome after := by
  cases trace with
  | value trace => exact .value trace.sound
  | fault trace => exact .fault trace.sound

theorem CallOutcome.has_size {program : Program} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {function : Dynamic.Value} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : FunctionCallBody.Outcome program context caller invocation before function arguments outcome after) : ∃ size, CallOutcome program size context caller invocation before function arguments outcome after := by
  cases trace with
  | value trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.CallableApplies.has_size trace
    exact ⟨size, .value trace⟩
  | fault trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.CallableFaults.has_size trace
    exact ⟨size, .fault trace⟩

theorem CallOutcome.positive {program : Program} {size : Nat} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {function : Dynamic.Value} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : CallOutcome program size context caller invocation before function arguments outcome after) : 0 < size := by
  cases trace with
  | value trace => exact trace.positive
  | fault trace => exact trace.positive

theorem CallOutcome.iff_size {program : Program} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {function : Dynamic.Value} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} :
    FunctionCallBody.Outcome program context caller invocation before function arguments outcome after ↔ ∃ size, CallOutcome program size context caller invocation before function arguments outcome after :=
  ⟨CallOutcome.has_size, fun ⟨_, trace⟩ => trace.sound⟩

theorem BodyOutcome.sound {program : Program} {size : Nat} {body : Dynamic.BodyInstance} {evidence : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : BodyOutcome program size body evidence before arguments outcome after) : NamedCalls.BodyOutcome program body evidence before arguments outcome after := by
  cases trace with
  | value trace => exact .value trace.sound
  | fault trace => exact .fault trace.sound

theorem BodyOutcome.has_size {program : Program} {body : Dynamic.BodyInstance} {evidence : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : NamedCalls.BodyOutcome program body evidence before arguments outcome after) : ∃ size, BodyOutcome program size body evidence before arguments outcome after := by
  cases trace with
  | value trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.BodyInvokes.has_size trace
    exact ⟨size, .value trace⟩
  | fault trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.BodyFaults.has_size trace
    exact ⟨size, .fault trace⟩

theorem BodyOutcome.positive {program : Program} {size : Nat} {body : Dynamic.BodyInstance} {evidence : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : BodyOutcome program size body evidence before arguments outcome after) : 0 < size := by
  cases trace with
  | value trace => exact trace.positive
  | fault trace => exact trace.positive

theorem BodyOutcome.iff_size {program : Program} {body : Dynamic.BodyInstance} {evidence : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} :
    NamedCalls.BodyOutcome program body evidence before arguments outcome after ↔ ∃ size, BodyOutcome program size body evidence before arguments outcome after :=
  ⟨BodyOutcome.has_size, fun ⟨_, trace⟩ => trace.sound⟩

theorem StatementsOutcome.sound {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : StatementsOutcome program size context evidence source environment before statements finalContext outcome after) : Dynamic.StatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after := by
  cases trace with
  | control trace => exact .control trace.sound
  | fault trace => exact .fault trace.sound

theorem StatementsOutcome.has_size {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.StatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after) : ∃ size, StatementsOutcome program size context evidence source environment before statements finalContext outcome after := by
  cases trace with
  | control trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.StatementsExecute.has_size trace
    exact ⟨size, .control trace⟩
  | fault trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.StatementsFault.has_size trace
    exact ⟨size, .fault trace⟩

theorem StatementsOutcome.positive {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : StatementsOutcome program size context evidence source environment before statements finalContext outcome after) : 0 < size := by
  cases trace with
  | control trace => exact trace.positive
  | fault trace => exact trace.positive

theorem StatementsOutcome.iff_size {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome} :
    Dynamic.StatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after ↔ ∃ size, StatementsOutcome program size context evidence source environment before statements finalContext outcome after :=
  ⟨StatementsOutcome.has_size, fun ⟨_, trace⟩ => trace.sound⟩

theorem FunctionOutcome.sound {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : FunctionOutcome program size context evidence source environment before statements finalContext outcome after) : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after := by
  cases trace with
  | control trace => exact .control trace.sound
  | fault trace => exact .fault trace.sound

theorem FunctionOutcome.has_size {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after) : ∃ size, FunctionOutcome program size context evidence source environment before statements finalContext outcome after := by
  cases trace with
  | control trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size trace
    exact ⟨size, .control trace⟩
  | fault trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.FunctionStatementsFault.has_size trace
    exact ⟨size, .fault trace⟩

theorem FunctionOutcome.positive {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : FunctionOutcome program size context evidence source environment before statements finalContext outcome after) : 0 < size := by
  cases trace with
  | control trace => exact trace.positive
  | fault trace => exact trace.positive

theorem FunctionOutcome.iff_size {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {statements : List StatementId} {outcome : Dynamic.ControlOutcome} :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after ↔ ∃ size, FunctionOutcome program size context evidence source environment before statements finalContext outcome after :=
  ⟨FunctionOutcome.has_size, fun ⟨_, trace⟩ => trace.sound⟩

theorem BodyTrace.sound {program : Program} {size : Nat} {function : Dynamic.Closure} {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : BodyTrace program size function context environment before outcome after) : FunctionCallBody.Trace program function context environment before outcome after := by
  cases trace with
  | returned trace => exact .returned trace.sound
  | unit same trace => exact .unit same trace.sound
  | fault trace => exact .fault trace.sound
  | escaped trace escape => exact .escaped trace.sound escape

theorem BodyTrace.has_size {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : FunctionCallBody.Trace program function context environment before outcome after) : ∃ size, BodyTrace program size function context environment before outcome after := by
  cases trace with
  | returned trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size trace
    exact ⟨size, .returned trace⟩
  | unit same trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size trace
    exact ⟨size, .unit same trace⟩
  | fault trace =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.FunctionStatementsFault.has_size trace
    exact ⟨size, .fault trace⟩
  | escaped trace escape =>
    obtain ⟨size, trace⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size trace
    exact ⟨size, .escaped trace escape⟩

theorem BodyTrace.positive {program : Program} {size : Nat} {function : Dynamic.Closure} {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : BodyTrace program size function context environment before outcome after) : 0 < size := by
  cases trace with
  | returned trace => exact trace.positive
  | unit _ trace => exact trace.positive
  | fault trace => exact trace.positive
  | escaped trace _ => exact trace.positive

theorem BodyTrace.iff_size {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} :
    FunctionCallBody.Trace program function context environment before outcome after ↔ ∃ size, BodyTrace program size function context environment before outcome after :=
  ⟨BodyTrace.has_size, fun ⟨_, trace⟩ => trace.sound⟩

/-- Real completion exposes its first argument computation below the original
call derivation, regardless of the language-result branch. -/
theorem call_arguments {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {size : Nat} {environment : Environment} {store finalStore : Store} {value : Value}
    (completed : EvaluationSize size environment store (SourceCoreCalls.call signature index arguments reason) value finalStore) :
    ∃ child argumentValue argumentStore, child < size ∧
      EvaluationSize child environment store arguments argumentValue argumentStore := by
  obtain ⟨child, middle, value, bound, evaluated⟩ := completed.bind_computation
  exact ⟨child, value, middle, bound, evaluated⟩

/-- The retained global read and actual argument result fix the exact body and
captured environment. All three strict bounds come from the original trace. -/
theorem call_body {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {size : Nat} {environment captured : Environment} {store middle finalStore : Store} {value argument : Value}
    {location : Location} {body : Expr}
    (argumentsEvaluated : Evaluates environment store arguments (.inRight .word argument) middle)
    (reference : environment[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : middle.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (completed : EvaluationSize size environment store (SourceCoreCalls.call signature index arguments reason) value finalStore) :
    ∃ child, child < size ∧ EvaluationSize child (argument :: captured) middle body value finalStore := by
  have selected := OptionalCell.read_success reason
    (show Evaluates (argument :: environment) middle (.var (index + 1))
      (.cellRef (OptionalCell.cellType signature.functionType) location) middle from .var reference) read
  obtain ⟨first, firstLess, following⟩ := completed.bind_success argumentsEvaluated
  obtain ⟨second, secondLess, applied⟩ := following.bind_success selected
  obtain ⟨child, childLess, evaluated⟩ := applied.apply_body (.var rfl) (.var rfl)
  exact ⟨child, Nat.lt_trans childLess (Nat.lt_trans secondLess firstLess), evaluated⟩

/-- The actual save/install/body/restore envelope yields its own next and body
subderivations. Restoration is exactly the real final write. -/
theorem with_frame {environment : Environment} {before finalStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location} {saved result : Value} {size : Nat}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (evaluation : EvaluationSize size environment before
      (SourceCoreCallableContextFrames.withFrame reference next body) result finalStore) :
    ∃ nextSize bodySize installedValue nextStore bodyStore,
      EvaluationSize nextSize (saved :: environment) before (next.weakenAt 0) installedValue nextStore ∧
      EvaluationSize bodySize (.unit :: saved :: environment) (nextStore.set location installedValue)
        ((body.weakenAt 0).weakenAt 0) result bodyStore ∧
      nextSize < size ∧ bodySize < size ∧ finalStore = bodyStore.set location saved := by
  cases evaluation with
  | letE save remaining =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic save.sound (.loadCell (referenceSelected.evaluates before) savedRead)
    cases remaining with
    | letE install remaining =>
      cases install with
      | storeCell referenceEvaluation _ nextEvaluation written =>
        obtain ⟨referenceEqual, storeEqual⟩ := evaluation_deterministic referenceEvaluation.sound ((referenceSelected.weaken _).evaluates _)
        cases storeEqual
        cases referenceEqual
        obtain ⟨_, rfl⟩ := Store.write?_eq_some_iff.mp written
        cases remaining with
        | letE bodyEvaluation restore =>
          cases restore with
          | letE restored returned =>
            cases restored with
            | storeCell selected _ oldEvaluation written =>
              obtain ⟨referenceEqual, storeEqual⟩ := evaluation_deterministic selected.sound
                ((((referenceSelected.weaken _).weaken .unit).weaken _).evaluates _)
              cases storeEqual
              cases referenceEqual
              cases oldEvaluation with
              | var found =>
                simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
                cases found
                cases returned with
                | var found =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
                  cases found
                  exact ⟨_, _, _, _, _, nextEvaluation, bodyEvaluation, by omega, by omega,
                    (Store.write?_eq_some_iff.mp written).2⟩

/-- The real finish helper contains the flow as an actual strict child, for
returned values, language faults and all loop-control exits. -/
theorem finish_flow {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {value : Value} {size : Nat}
    (evaluated : EvaluationSize size environment before
      (CompatibleStatements.finish type flow fellThrough escaped) value after) :
    ∃ child result middle, child < size ∧ EvaluationSize child environment before flow result middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, _, by omega, input⟩

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var found => exact .var (agrees found)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index selected found
  exact agrees found


/-- Invert the accepted parameter Tree directly. Projection and marked
allocation are certified by their real receipts; every subsequent sized
witness is a child of the supplied completion. All lexical, heap, world and
actual-environment typing outputs accompany that witness. An empty prefix
retains its size; every nonempty prefix gives a strict decrease. -/
theorem parameter_prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {total : Nat} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source total output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion start) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (total_eq : total = allTypes.length)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) result afterStore) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding child,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.insertion start))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (prefixContext bindings actualContext) nativeDefinitions ∧
      EvaluationSize child finalActual finalStore (body.rename finalEmbedding) result afterStore ∧
      child ≤ size ∧ (bindings ≠ [] → child < size) := by
  induction tree generalizing mapping world environment canonical logical actual heap store ξ sources values actualContext size result afterStore with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ, size,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, sourceLayout, actualLayout, ⟨[], rfl, rfl, rfl⟩, actualTyped, completed, Nat.le_refl _, by simp⟩
  | @cons scope start binder payload bindings next allocation annotation same tail ih =>
    cases represented with
    | @cons _ _ sourceValue value _ sourceValues nativeValues head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projection := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      rw [← FunctionArguments.argumentProjection_eq, ← total_eq] at projection
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreFunctions.argumentProjection start total (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projection actualLayout).evaluates store)
      have canonicalLayout : EnvironmentsAgree (request source scope start (binder, payload)).references
          canonical (value :: logical) := agree_insert sourceLayout value
      have referenceAt : (value :: logical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
          (request source scope start (binder, payload))]? = some (.cellRef layout.type contextLocation) := by
        have found := canonicalLayout reference
        have kind := kinds (binder, payload) (by simp)
        change source.inputs.any (fun input => decide (input.id = binder.id)) = named at kind
        have isNamed : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope start (binder, payload)) = named := kind
        simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, isNamed]
        exact found
      obtain ⟨captured, allocationEval, nextHeaps, nextReference, frame⟩ :=
        CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments
          canonicalLayout heaps referenceAt read (.initialized rfl rfl) (.initialized head) Dynamic.Heap.Allocates.append
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      have nextEnvironments := CallableIndexedOrdinaryAllocation.bind_environment (id := binder.id) environments nextReference
      have nextSourceLayout : EnvironmentsAgree (Renaming.insertion (start + 1))
          (nextRef :: canonical) (nextRef :: logical) := by
        intro index selectedValue found
        have selected := sourceLayout.lift nextRef found
        simpa only [Renaming.lift_insertion] using selected
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (nextRef :: logical) (nextRef :: value :: actual) := by
        have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) := agree_insert actualLayout value
        intro index selectedValue found
        exact inserted.lift nextRef found
      have renamedAllocation := CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
        allocationEval (actualLayout.lift value)
      have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped bound
      have nextRead := stillRead.trans read
      have nextSelected : ∀ {index selectedValue}, nativeValues[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      have whole : EvaluationSize size actual store
          (LanguageResult.bind output
            ((LanguageResult.success (SourceCoreFunctions.argumentProjection start total (.var start))).rename ξ)
            ((Expr.letE annotation.expression (next.weakenAt 1)).rename ξ.lift)) result afterStore := by
        simpa only [LanguageResult.bind, Expr.rename, Renaming.lift] using completed
      obtain ⟨firstSize, firstLess, following⟩ := whole.bind_success initializer
      simp only [Expr.rename] at following
      obtain ⟨remainingSize, remainingLess, remaining⟩ := following.let_body renamedAllocation
      have actualRemaining : EvaluationSize remainingSize (nextRef :: value :: actual)
          (store ++ [SourceCoreCallableIndexedFrames.encode layout native,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, optionalValue payload (some value)])
          (next.rename (Renaming.comp (Renaming.insertion 0) ξ).lift) result afterStore := by
        simpa only [LoopStatements.rename_insert_lift, LoopRenaming.weakenOne, nextRef, request] using remaining
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, child, allocated, finalEnvironments, finalHeaps, maps, worlds,
        finalFrame, finalSourceLayout, finalActualLayout, spine, finalTyped, bodyTrace, childLe, _⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
          (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩))
          nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show RuntimeEnvironmentHasTypes
              (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
              (nextRef :: value :: actual) (OptionalCell.referenceType payload :: payload :: actualContext) nativeDefinitions from
            .cons (.cellRef nextReference.typed)
              (.cons ((model.runtime_hasType head).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)))
          (show (nextRef :: logical)[start + 1]? = some (DataPatternValues.packValues allValues) from bundleSlot)
          nextSelected (fun binding member => kinds binding (List.mem_cons_of_mem _ member))
          (show (nextRef :: canonical)[(((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals)]? =
            some (.cellRef layout.type contextLocation) from by
              have nextIndex : (((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals) =
                  (scope.length + (if named then 0 else 1) + globals) + 1 := by simp only [List.length_cons]; omega
              rw [nextIndex]
              exact reference)
          nextRead stillUnmapped actualRemaining
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, child, .cons .append allocated, finalEnvironments, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        frame.trans finalFrame, ?_, finalActualLayout, ?_, finalTyped, bodyTrace,
        Nat.le_trans childLe (Nat.le_of_lt (Nat.lt_trans remainingLess firstLess)), ?_⟩
      · intro index selectedValue found
        simpa only [List.length_cons, DataMatchCoreAllocation.liftMany, Renaming.lift_insertion] using finalSourceLayout found
      · obtain ⟨added, length, canonicalEq, logicalEq⟩ := spine
        exact ⟨added ++ [nextRef], by simp [length], by simpa [List.append_assoc, nextRef, request] using canonicalEq,
          by simpa [List.append_assoc, nextRef, request] using logicalEq⟩
      · intro _
        exact Nat.lt_of_le_of_lt childLe (Nat.lt_trans remainingLess firstLess)



/-- A retained source body supplies the actual named call child; declaration
and evidence attribution are exactly the independent SourceFrame fields. -/
theorem call_of_body {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {size : Nat}
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (trace : BodyOutcome program size body function.evidence before arguments outcome after) :
    CallOutcome program (SourceExecutionSize.stepSize [size]) context caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after := by
  cases trace with
  | value trace => exact .value (.global frame.instantiated rfl frame.covers trace)
  | fault trace => exact .fault (.globalBody frame.instantiated rfl trace)

private theorem roots_functional {nodes : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots nodes left) (second : Dynamic.StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons id nodes left first ih => cases second with
    | cons remaining => exact congrArg (List.cons id) (ih remaining)

/-- Actual body outcome inversion exposes the original strictly smaller
function-statement derivation at the statically retained call context. Arity
rejects the distinct pre-allocation body fault. -/
theorem body_trace {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {size : Nat}
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program size body function.evidence before arguments outcome after) :
    ∃ child environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      BodyTrace program child function context environment bound outcome after ∧ child < size := by
  have rootsUnique : ∀ {roots}, Dynamic.StatementRoots body.source.roots roots → roots = function.body := by
    intro roots selected
    exact roots_functional selected frame.roots
  have contextUnique : ∀ {inputTypes actualContext},
      MonoBindersExtend body.source.owner body.context body.source.inputs inputTypes actualContext →
      actualContext = context := by
    intro inputTypes actualContext extension
    have actual : MonoBindersExtend function.source.owner function.context function.parameters inputTypes actualContext := by
      simpa only [frame.source, frame.context, frame.parameters] using extension
    have same : types = inputTypes := extended.bodyTypes_eq.symm.trans actual.bodyTypes_eq
    subst inputTypes
    exact (extended.functional actual).symm
  cases executed with
  | value invokes =>
    cases invokes with
    | returned covers roots extension allocated execution returned =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, _, frame.parameters.symm ▸ allocated, .returned (frame.source.symm ▸ execution),
        SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | unit covers same roots extension allocated execution fellThrough =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      obtain ⟨_, rfl⟩ := fellThrough
      subst_vars
      exact ⟨_, _, _, frame.parameters.symm ▸ allocated,
        .unit (frame.result.symm ▸ same) (frame.source.symm ▸ execution),
        SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | fault fails =>
    cases fails with
    | arity mismatch => exact False.elim (mismatch (by simpa only [frame.parameters] using arity))
    | statements roots extension allocated failed =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, _, frame.parameters.symm ▸ allocated, .fault (frame.source.symm ▸ failed),
        SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | controlEscape roots extension allocated executed escape =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, _, frame.parameters.symm ▸ allocated, .escaped (frame.source.symm ▸ executed) escape,
        SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- Actual named-hook acceptance fixes the installed frame literal. The
original completion supplies its body child under the real two hidden slots;
the observed saved frame is restored after that same body trace. -/
theorem named_hook_body {checked : SourceCoreCallableIndexedAncestry.Checked} {base : SourceCoreCallableIndexedAncestry.Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {function : SourceCoreGeneralFunctions.Function} {body code : Expr}
    (accepted : SourceCoreCallableIndexedAncestry.namedBody prepared function body = .ok code)
    {size : Nat} {actual : Environment} {before finalStore : Store} {ξ : Renaming}
    {location : Location} {saved result : Value}
    (reference : actual[ξ (base.globals.length + 1)]? =
      some (.cellRef prepared.layout.frame.type location))
    (savedRead : before.read? location = some saved)
    (completed : EvaluationSize size actual before (code.rename ξ) result finalStore) :
    ∃ origin index child bodyStore,
      prepared.graph.inputs.callable.table.idAt? (.named function.signature.key) = some origin ∧
      SourceCoreCallableIndexedDispatch.namedFrame prepared.graph.table origin = .state index ∧
      EvaluationSize child (.unit :: saved :: actual)
        (before.set location (SourceCoreCallableIndexedFrames.encode prepared.layout.frame (.state index)))
        (((body.rename ξ).weakenAt 0).weakenAt 0) result bodyStore ∧
      child < size ∧ finalStore = bodyStore.set location saved := by
  obtain ⟨origin, index, owned, selected, emitted⟩ :=
    CallableIndexedFormation.namedBody_receipt prepared accepted
  rw [emitted, NamedCalls.withFrame_rename] at completed
  obtain ⟨nextSize, child, installed, nextStore, bodyStore, nextTrace, bodyTrace, _, smaller, restored⟩ :=
    with_frame (.var reference) savedRead completed
  have expected : Evaluates (saved :: actual) before
      (((SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)).rename ξ).weakenAt 0)
      (SourceCoreCallableIndexedFrames.encode prepared.layout.frame (.state index)) before := by
    rw [CallableIndexedRenaming.literal, ← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates _ _ _ _
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextTrace.sound expected
  exact ⟨origin, index, child, bodyStore, owned, selected, bodyTrace, smaller, restored⟩

/-- Retained declaration ownership and argument arity select the actual
source body child of named dispatch. Missing-entry and arity rejection branches
are excluded by these independent static facts. -/
theorem source_call_body {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (frame : NamedCalls.SourceFrame program instantiation body function)
    {size : Nat} {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (called : CallOutcome program size context caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after) :
    ∃ child, BodyOutcome program child body function.evidence before arguments outcome after ∧ child < size := by
  cases called with
  | value evaluated =>
    cases evaluated with
    | global actual invocation covers invoked =>
      have same := BuiltinNamedCalls.instantiation_unique unique frame.instantiated actual
      cases same
      exact ⟨_, .value invoked, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | globalSignatureMissing missing =>
      cases frame.instantiated with
      | intro signatureMem definitionMem declaration owner valid source result context =>
        exact False.elim (missing _ signatureMem declaration.symm)
    | globalBodyMissing missing =>
      cases frame.instantiated with
      | intro signatureMem definitionMem declaration owner valid source result context =>
        exact False.elim (missing _ definitionMem (owner.trans declaration.symm))
    | globalArity actual mismatch =>
      have same := BuiltinNamedCalls.instantiation_unique unique frame.instantiated actual
      cases same
      exact False.elim (mismatch (by simpa only [frame.parameters] using arity))
    | globalBody actual invocation failed =>
      have same := BuiltinNamedCalls.instantiation_unique unique frame.instantiated actual
      cases same
      exact ⟨_, .fault failed, SourceExecutionSize.child_lt_stepSize (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
