import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLeaves
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource

/-! Bidirectional source correspondence for accepted compatible local reads.
The independent source trace supplies only the forward direction; every
completed Core execution reconstructs a source trace in the reverse direction.
All child evaluation is derived, including lazy mapping initialization. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

theorem Certificate.preserves {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason)
    (unique : NodeOccurrencesUnique source)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after) :
    ∃ value finalStore,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨actualOutcome, actualHeap, value, finalStore, sourceTrace, evaluated, represented, finalHeaps, frame, metadata⟩ :=
    certificate.evaluates functions extension program sourceContext evidence binding environments heaps locals agrees uninitialized
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  obtain ⟨_, selected, _, _, _, selectedRead, _, cellRep⟩ :=
    GenericHeap.lookup_visible environments heaps lookup certificate.slot
  have sameCell := read.functional selectedRead
  subst selected
  obtain ⟨rfl, rfl⟩ := source_outcome_unique unique (lookupExpression?_sound certificate.metadata.found)
    certificate.form certificate.metadata.coercions lookup read cellRep.ordinary sourceTrace trace
  exact ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩

theorem Certificate.reflects {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨outcome, after, native, nativeStore, sourceTrace, evaluated, represented, finalHeaps, frame, metadata⟩ :=
    certificate.evaluates functions extension program sourceContext evidence binding environments heaps locals agrees uninitialized
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated evaluation
  exact ⟨outcome, after, sourceTrace, represented, finalHeaps, frame, metadata⟩

/-- A static occurrence receipt for the universal child-expression interface.
The receipt contains compiler and source typing facts, never a child run. -/
def LoweredRead (fuel : Nat) (context : ValuesContext) (source : TypedSource)
    (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ certificate : Certificate fuel context source scope id (reasonAt id) lowered.expression,
    certificate.type = lowered.type ∧ StaticBinding certificate sourceContext

/-- Lexical declarations are checked independently of native projection. Only
binders actually visible in the compiler scope are required in this context. -/
def ScopeDeclarations (source : TypedSource) (scope : Scope) (context : SourceSemantics.Context) : Prop :=
  ∀ binder declared index type,
    SourceCoreLocalCell.lookup? scope binder = some (index, type) →
    SourceCoreDataPlaces.rootBinder source binder = .ok declared →
    Resolved.LocalScope.Lookup context.locals binder declared.scheme

theorem loweredRead_of_accepted {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel context source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression context.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source)
    (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) :
    LoweredRead fuel context source sourceContext reasonAt scope id lowered := by
  obtain ⟨certificate⟩ := of_accepted accepted
  have metadata := metadata_of_read read
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans metadata.found)
  have projection := certificate.metadata.projected
  rw [nodeEq] at projection
  have typeEq := Except.ok.inj (projection.symm.trans metadata.projected)
  refine ⟨certificate, typeEq, StaticBinding.of_expression_type certificate unique
    (declarations _ _ _ _ certificate.slot certificate.declaration) ?_⟩
  simpa only [nodeEq] using typed

/-- The forward universal interface is discharged for every certified read. -/
theorem loweredRead_preserves {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (unique : NodeOccurrencesUnique source) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel context.checked registry functions)
      program sourceContext evidence source (LoweredRead fuel context source sourceContext reasonAt) faults := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩ :=
    certificate.preserves functions extension program sourceContext evidence binding environments heaps locals agrees
      (uninitialized id) unique trace
  refine ⟨value, finalStore, mapping, world, evaluated, ?_, finalHeaps, .refl _, .refl _, frame, metadata⟩
  simpa only [nodeEq, typeEq] using represented

/-- Every completed Core read reconstructs its finite source outcome. -/
theorem loweredRead_reflects {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id)) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel context.checked registry functions)
      program sourceContext evidence source (LoweredRead fuel context source sourceContext reasonAt) faults := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluation
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, frame, metadata⟩ :=
    certificate.reflects functions extension program sourceContext evidence binding environments heaps locals agrees
      (uninitialized id) evaluation
  refine ⟨outcome, after, mapping, world, sourceTrace, ?_, finalHeaps, .refl _, .refl _, frame, metadata⟩
  simpa only [nodeEq, typeEq] using represented

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
