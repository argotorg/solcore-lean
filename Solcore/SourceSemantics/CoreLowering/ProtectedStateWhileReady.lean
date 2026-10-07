import Solcore.SourceSemantics.CoreLowering.ProtectedStateWhile
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalGate
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeControl

/-! Readiness travels beside the actual reached loop state. Static condition
and body receipts remain separate from the protocol and its records. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open ProtectedStateTransition
open RecursiveNamedLoopContracts (ExecutesAt)
open TypedLexicalControl (LexicalResult)
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)

/-- The activation facet is restricted to the real self-cell store and world.
It consumes the actual retained activation witness and its original effects. -/
structure ActivationTransfers (readiness : Readiness protocol) where
  ready : ∀ {context : SourceSemantics.Context} {scope : Scope} {mapping : LocationMap}
    {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {type : Ty} {condition body : Expr} {reason : Word},
    ∀ (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
      (reached : protocol.State ⟨scope, mapping, TypedLexicalWhile.installedWorld world type, heap,
        TypedLexicalWhile.installedStore store type condition body (LocalLoop.fallthrough type) reason actual, canonical⟩),
      AdministrativePreserved mapping store mapping
        (TypedLexicalWhile.installedStore store type condition body (LocalLoop.fallthrough type) reason actual) →
      protocol.Relates initial reached → protocol.records reached = protocol.records initial →
      readiness.Ready context initial → readiness.Ready context reached

theorem ActivationTransfers.trivial : ActivationTransfers protocol (Readiness.trivial protocol) where
  ready := fun _ _ _ _ _ _ => True.intro

/-- The constant readiness specialization keeps the exact original expression
post and adds only proof receipts. -/
theorem expression_preserves_trivial
    {source : TypedSource} {context : SourceSemantics.Context} {program : Program}
    {evidence : Dynamic.EvidenceEnvironment} {faults : FunctionCalls.FaultRep}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {certificate : GenericExpressionMeaning.Certificate} {size : Nat}
    (meaning : ProtectedStateTransition.PreservesAt protocol model program context evidence source certificate faults size) :
    ExpressionPreservesAt protocol (Readiness.trivial protocol) (context := context) (source := source)
      (faults := faults) program evidence model (fun _ _ _ => True) certificate size := by
  intro scope id lowered tree node found _facts mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial _ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ :=
    meaning tree found environments heaps locals agrees typed initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, by cases outcome <;> simp only [ExpressionPost, Readiness.trivial] <;> trivial⟩

theorem expression_reflects_trivial
    {source : TypedSource} {context : SourceSemantics.Context} {program : Program}
    {evidence : Dynamic.EvidenceEnvironment} {faults : FunctionCalls.FaultRep}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {certificate : GenericExpressionMeaning.Certificate} {size : Nat}
    (meaning : ProtectedStateTransition.ReflectsAt protocol model program context evidence source certificate faults size) :
    ExpressionReflectsAt protocol (Readiness.trivial protocol) (context := context) (source := source)
      (faults := faults) program evidence model (fun _ _ _ => True) certificate size := by
  intro scope id lowered tree node found _facts mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial _ready completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ :=
    meaning tree found environments heaps locals agrees typed initial completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, by cases outcome <;> simp only [ExpressionPost, Readiness.trivial] <;> trivial⟩

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

variable {administrative : Core.Context}

/-- Constant facets preserve every field of the original actual body result. -/
theorem body_preserves_trivial (validity : SourceSemantics.Context → Prop)
    {scope : Scope} {size : Nat} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol (Readiness.trivial protocol) guard (fun _ _ _ _ => True) functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code := by
  intro valid _facts mapping world actualContext environment canonical actual before after store ξ contextLocation native
    outcome finalContext environments heaps locals agrees typed reference read unmapped initial guarded _ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, lexical, transition⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, lexical, Reached.of_trivial transition⟩

/-- Constant facets preserve every field of the original actual body result. -/
theorem body_reflects_trivial (validity : SourceSemantics.Context → Prop)
    {scope : Scope} {size : Nat} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol (Readiness.trivial protocol) guard (fun _ _ _ _ => True) functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code := by
  intro valid _facts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native
    value environments heaps locals agrees typed reference read unmapped initial guarded _ready completed
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, lexical, transition⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded completed
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, lexical, Reached.of_trivial transition⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady
