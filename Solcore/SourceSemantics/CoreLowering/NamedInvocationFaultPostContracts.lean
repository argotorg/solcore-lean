import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration

/-! An actual named body post remains at its completed body store. The caller
restoration is a separate receipt at that same body state and selected frame. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedInvocationFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState

abbrev BodyFaultPost := Program → Dynamic.Closure → SourceSemantics.Context →
  Dynamic.Environment → Dynamic.Heap → Environment → Store → Expr →
  Dynamic.SemanticFault → Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

/-- Successful bodies impose no primitive fault attribution. -/
def OutcomePost (post : BodyFaultPost) (program : Program) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (actual : Environment) (initialStore : Store) (body : Expr) (type : Ty)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .value _ => True
  | .fault reason => ∃ token, value = .inLeft type (.word token) ∧
      post program function context environment before actual initialStore body reason after token mapping world store

def Trivial : BodyFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True

theorem trivial_of_result {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {actual : Environment} {initialStore store : Store} {body : Expr} {type : Ty}
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (result : FunctionCalls.ResultRepresents model mapping world function.resultType type faults outcome value) :
    OutcomePost Trivial program function context environment before actual initialStore body type
      outcome after value mapping world store := by
  cases result with
  | value represented => trivial
  | @fault reason token represented => exact ⟨token, rfl, trivial⟩

/-- Reflection retains the measured parameter prefix and its actual body child.
Preservation does not invent a native grade. -/
def Measured (budget : Option Nat) (actual : Environment) (initialStore : Store) (parameters : Expr)
    (bodyActual : Environment) (bodyInitial : Store) (body : Expr) (value : Value) (bodyStore : Store) : Prop :=
  match budget with
  | none => ContinuationAgreement actual initialStore parameters bodyActual bodyInitial body
  | some bound => ∃ prefixSize child,
      EvaluationSize prefixSize actual initialStore parameters value bodyStore ∧
      EvaluationSize child bodyActual bodyInitial body value bodyStore ∧
      child ≤ prefixSize ∧ prefixSize < bound

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}

/-- The selected invocation keeps the one actual parameter entry, body trace,
body post, and original restore producer. Its post is at bodyStore throughout. -/
def ReturnedAt (post : BodyFaultPost) (sourceParent : Nat) (nativeBudget : Option Nat)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (arguments : List Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalMap : LocationMap) (finalWorld : StoreTyping) (finalStore : Store) : Prop :=
  ∃ origin index metadata administrative actualContext actual ξ,
    ∃ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
      (store.set (caller.rows owner.position).authority.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ (caller.rows owner.position).authority.frameLocation
      (.state index) (.named origin),
    ∃ parameterState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    ∃ sourceSize bodyStore,
    ∃ bodyState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, bodyStore, entry.canonical⟩,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode ∧
      Relates caller parameterState ∧ Relates parameterState bodyState ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        entry.environment entry.heap outcome after ∧
      sourceSize < sourceParent ∧
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value bodyStore ∧
      OutcomePost post program header.function header.context entry.environment entry.heap
        entry.actualBody entry.store (header.body.rename entry.embedding) header.output
        outcome after value finalMap finalWorld bodyStore ∧
      Measured nativeBudget actual
        (store.set (caller.rows owner.position).authority.frameLocation
          (encode compiled.indexed.ancestry.layout.frame (.state index)))
        (header.parameterCode.rename ξ) entry.actualBody entry.store (header.body.rename entry.embedding) value bodyStore ∧
      Relates caller bodyState ∧
      finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex caller owner.position
        (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, bodyStore, entry.canonical⟩)).store ∧
      CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame keys[owner.position.val].frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost finalStore ∧
      Relates bodyState (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      Relates caller (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      records (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) = records bodyState

/-- A retained body fact is indexed by the original parameter entry and its
same two actual pools. It is independent of the meaning of that fact, and its
seed locations and capture prefix remain arbitrary. -/
abbrev BodyExtra :=
  ∀ {locations : Locations} {capturePrefix : Nat}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping}
    {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame},
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) →
    (parameterState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) →
    (outcome : Dynamic.ExpressionOutcome) → (after : Dynamic.Heap) → (value : Value) →
    (finalMap : LocationMap) → (finalWorld : StoreTyping) → (bodyStore : Store) →
    (bodyState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, bodyStore, entry.canonical⟩) → Prop

/-- Legacy body callbacks can retain the same witness with no additional fact. -/
def TrivialExtra : BodyExtra (compiled := compiled) (program := program) (headers := headers)
    (keys := keys) (functions := functions) (registry := registry) (header := header) :=
  fun {_locations} {_capturePrefix} {_arguments} {_before} {_initialStore} {_initialMap} {_initialWorld}
    {_administrative} {_actualContext} {_actual} {_ξ} {_frameLocation} {_current} {_ghost}
    _entry _parameterState _outcome _after _value _finalMap _finalWorld _bodyStore _bodyState => True

/-- The extra and the actual restored frame share the entire original causal
spine. The body entry, parameter pool and completed body pool are bound once. -/
def ReturnedAtWithExtra (post : BodyFaultPost)
    (extra : BodyExtra (compiled := compiled) (program := program) (headers := headers)
      (keys := keys) (functions := functions) (registry := registry) (header := header))
    (sourceParent : Nat) (nativeBudget : Option Nat)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (arguments : List Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalMap : LocationMap) (finalWorld : StoreTyping) (finalStore : Store) : Prop :=
  ∃ origin index metadata administrative actualContext actual ξ,
    ∃ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
      (store.set (caller.rows owner.position).authority.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ (caller.rows owner.position).authority.frameLocation
      (.state index) (.named origin),
    ∃ parameterState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    ∃ sourceSize bodyStore,
    ∃ bodyState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, bodyStore, entry.canonical⟩,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode ∧
      Relates caller parameterState ∧ Relates parameterState bodyState ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        entry.environment entry.heap outcome after ∧
      sourceSize < sourceParent ∧
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value bodyStore ∧
      OutcomePost post program header.function header.context entry.environment entry.heap
        entry.actualBody entry.store (header.body.rename entry.embedding) header.output
        outcome after value finalMap finalWorld bodyStore ∧
      Measured nativeBudget actual
        (store.set (caller.rows owner.position).authority.frameLocation
          (encode compiled.indexed.ancestry.layout.frame (.state index)))
        (header.parameterCode.rename ξ) entry.actualBody entry.store (header.body.rename entry.embedding) value bodyStore ∧
      Relates caller bodyState ∧
      finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex caller owner.position
        (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, bodyStore, entry.canonical⟩)).store ∧
      CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame keys[owner.position.val].frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost finalStore ∧
      Relates bodyState (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      Relates caller (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      records (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) = records bodyState ∧
      extra entry parameterState outcome after value finalMap finalWorld bodyStore bodyState ∧
      AdministrativePreserved mapping store finalMap
        (CallableIndexedOwnedBodyRestoration.finalIndex caller owner.position
          (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, bodyStore, entry.canonical⟩)).store

/-- Forget only the extra fact and restored-frame proof from the same witnesses. -/
theorem ReturnedAtWithExtra.forget {post : BodyFaultPost}
    {extra : BodyExtra (compiled := compiled) (program := program) (headers := headers)
      (keys := keys) (functions := functions) (registry := registry) (header := header)}
    {sourceParent : Nat} {nativeBudget : Option Nat}
    {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
    {caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}
    (receipt : ReturnedAtWithExtra post extra sourceParent nativeBudget owner caller arguments
      outcome after value finalMap finalWorld finalStore) :
    ReturnedAt (functions := functions) (registry := registry) (header := header) post sourceParent nativeBudget
      owner caller arguments outcome after value finalMap finalWorld finalStore := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, owned, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords, _extra, _restoredFrame⟩ := receipt
  exact ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, owned, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords⟩

end Solcore.SourceSemantics.CoreLowering.NamedInvocationFaultPostContracts
