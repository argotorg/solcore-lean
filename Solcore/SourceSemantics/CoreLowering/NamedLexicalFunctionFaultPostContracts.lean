import Solcore.SourceSemantics.CoreLowering.NamedLexicalFlowFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeControl
import Solcore.SourceSemantics.CoreLowering.ImperativeFunctionFinish

/-! The lexical post embeds into the actual five-way flow tuple and remains
at the same fault token and store through the existing function finish. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLexicalFunctionFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored)
open TypedLexicalControl (LexicalResult)
open RecursiveNamedLoopContracts (ExecutesAt)
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
open NamedLexicalFlowFaultPostContracts
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (readiness : Readiness protocol) (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}

def PreservesAtWith (post : FlowFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      FlowOutcomePost post program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore

def ReflectsAtWith (post : FlowFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      FlowOutcomePost post program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore


theorem PreservesAtWith.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code) :
    PreservesAtWith (post := TrivialFlow) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, readyPost⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, readyPost⟩, by cases represented <;> simp [FlowOutcomePost, TrivialFlow]⟩

theorem PreservesAtWith.forget {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : PreservesAtWith (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, readyPost⟩, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, readyPost⟩

theorem PreservesAtWith.of_lexical {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : NamedLexicalFlowFaultPostContracts.PreservesAtFor (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    PreservesAtWith (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, origin⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, TypedLexicalWhile.FlowRep.of_lexical represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, origin⟩

theorem ReflectsAtWith.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code) :
    ReflectsAtWith (post := TrivialFlow) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, readyPost⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, readyPost⟩, by cases represented <;> simp [FlowOutcomePost, TrivialFlow]⟩

theorem ReflectsAtWith.forget {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ReflectsAtWith (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, readyPost⟩, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, readyPost⟩

theorem ReflectsAtWith.of_lexical {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    ReflectsAtWith (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, origin⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, TypedLexicalWhile.FlowRep.of_lexical represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, origin⟩

/-- A finished post keeps the actual flow witness and exit. Direct transfer
exits carry no assertion about a primitive fault origin. -/
def FinishedPost (post : FlowFaultPost) (program : Program) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (size : Nat) (type : Ty) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Value) (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  ∃ finalContext control,
    RecursiveNamedLoopContracts.ExecutesAt size true program context function.evidence function.source
      environment before function.body finalContext control after ∧
    CompatibleNamedBody.Exit function.resultType control outcome ∧
    match control with
    | .fault reason => ∃ token, result = .inLeft type (.word token) ∧
        post program context function.evidence function.source environment before true function.body reason after token mapping world store
    | _ => True

theorem finished_post {post : FlowFaultPost} {program : Program} {function : Dynamic.Closure}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {type : Ty} {control : Dynamic.ControlOutcome} {outcome : Dynamic.ExpressionOutcome}
    {input result : Value} {mapping : LocationMap} {world : StoreTyping} {initialStore finalStore : Store}
    {actual : Environment} {flow : Expr} {fellThrough escaped : Word}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size true program context function.evidence function.source
      environment before function.body finalContext control after)
    (exit : CompatibleNamedBody.Exit function.resultType control outcome)
    (origin : FlowOutcomePost post program context function.evidence function.source environment before true function.body
      type control after input mapping world finalStore)
    (evaluated : Evaluates actual initialStore flow input finalStore)
    (completed : Evaluates actual initialStore (CompatibleStatements.finish type flow fellThrough escaped) result finalStore) :
    FinishedPost post program function context environment before size type outcome after result mapping world finalStore := by
  refine ⟨finalContext, control, trace, exit, ?_⟩
  cases control <;> try trivial
  obtain ⟨token, rfl, retained⟩ := origin
  obtain ⟨same, _⟩ := evaluation_deterministic completed
    (LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated))
  exact ⟨token, same, retained⟩

end Solcore.SourceSemantics.CoreLowering.NamedLexicalFunctionFaultPostContracts
