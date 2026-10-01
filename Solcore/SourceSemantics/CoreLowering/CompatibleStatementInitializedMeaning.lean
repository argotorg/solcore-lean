import Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedCertificates
import Solcore.SourceSemantics.CoreLowering.LoopStatementLayout

/-! Initialization runs in the old scope before any binder allocation. Its
failure keeps that context and its exact heap effects. Success creates the real
indexed marker/snapshot/payload prefix and then runs the certified tail. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof

private theorem extended_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

private theorem prepend {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment nextEnvironment : Dynamic.Environment}
    {before middle after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {initializer : ExpressionId} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (head : Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough nextEnvironment) middle)
    (tail : Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source nextEnvironment middle rest finalContext outcome after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after := by
  cases rest with
  | nil => cases tail with
    | control executed => cases executed; exact .control (.singleton (lookupStatement?_sound found) (by intro expression; simp [form]) head)
    | fault failed => cases failed
  | cons => cases tail with
    | control executed => exact .control (.cons head executed)
    | fault failed => exact .fault (.tail head failed)

private theorem fault_intro {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    (rest : List StatementId) {reason : Dynamic.SemanticFault}
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = [])
    (failed : Dynamic.ExpressionFaults program context evidence source environment before initializer reason after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) context (.fault reason) after := by
  have head := Dynamic.StatementFaults.letInitializer (lookupStatement?_sound found) form mono failed
  cases rest with
  | nil => exact .fault (.singleton head)
  | cons => exact .fault (.head head)

private theorem source_view {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {initializer : ExpressionId} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧
      Dynamic.ExpressionFaults program context evidence source environment before initializer reason after) ∨
    (∃ value location middle allocatedHeap,
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location allocatedHeap ∧
      Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source ((binder.id, location) :: environment)
        allocatedHeap rest finalContext outcome after) := by
  have contains := lookupStatement?_sound found
  have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨extension, location, value, middle, same, initial, allocated⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases extended_eq extended extension
      cases same
      exact .inr ⟨value, location, middle, _, initial, allocated, .control tail⟩
    · obtain ⟨_, _, _, _, same, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases same; cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view true unique contains notTail failed with ⟨same, head⟩ | ⟨_, _, _, head, tail⟩
    · exact .inl ⟨_, same, rfl, ScalarStatementViews.letInitialized_fault unique contains form mono head⟩
    · obtain ⟨extension, location, value, middle, same, initial, allocated⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases extended_eq extended extension
      cases same
      exact .inr ⟨value, location, middle, _, initial, allocated, .fault tail⟩

private theorem sequence_rename (type : Ty) (initializer allocation body : Expr) (ξ : Renaming) :
    (sequence type initializer allocation body).rename ξ =
      LanguageResult.bind (LocalLoop.controlType type) (initializer.rename ξ)
        (.letE (allocation.rename ξ.lift) (body.rename (Renaming.comp (Renaming.insertion 0) ξ).lift)) := by
  rw [LoopStatements.rename_insert_lift]
  simp [sequence, LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne]

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context nextContext finalContext : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

include definitions registered in
private theorem allocate {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (request source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep values.checked registry functions mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) ambient.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore := by
  have canonicalLayout : EnvironmentsAgree (request source scope binder payload).references canonical (value :: canonical) := fun found => found
  have referenceAt : (value :: canonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (request source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope binder payload) = false := ordinary
    change (value :: canonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope binder payload) then 0 else 1) + globals)]? = _
    rw [named]
    exact reference
  obtain ⟨captured, evaluated, nextHeaps, nextReference, preservation⟩ :=
    CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments
      canonicalLayout heaps referenceAt read (.initialized rfl rfl) (.initialized represented) allocated
  have nextLocals : Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
    cases extended
    exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))
  have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := fun found => agrees found
  refine ⟨captured, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl) evaluated (agrees.lift value),
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference, nextHeaps, nextLocals, inserted.lift _,
    .cons (.cellRef nextReference.typed) (.cons (represented.runtime_hasType.weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)), ?_, ?_, preservation⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (initialValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (finalValid : CompatibleExpressionLiterals.ContextValid solved finalContext evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include definitions registered extension initialValid finalValid uninitialized in
/-- Initialization failure preserves its exact old-context effects. Success
allocates only afterward, then uses the concrete remaining binding tree. -/
theorem Tree.preserves {scope : Scope} {id : StatementId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code) (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) resultContext outcome after) :
    (resultContext = context ∨ resultContext = finalContext) ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases tree with
  | @initialized node binder initializer initializerNode lowered body found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining =>
    rw [sequence_rename]
    rcases source_view unique found form mono extended trace with ⟨reason, rfl, rfl, failed⟩ |
        ⟨sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        CompatibleExpressionConstructors.preserves functions extension program evidence initialValid unique uninitialized initial initialFound
          environments heaps locals agrees (.fault failed)
      cases represented with
      | fault matched => exact ⟨.inl rfl, _, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        CompatibleExpressionConstructors.preserves functions extension program evidence initialValid unique uninitialized initial initialFound
          environments heaps locals agrees (.value initialTrace)
      cases represented with
      | value payload =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
        obtain ⟨sameContext, result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata⟩ :=
          remaining.preserves functions definitions registered extension program evidence finalValid uninitialized unique
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead tailTrace
        exact ⟨.inr sameContext, result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata)⟩

include definitions registered extension initialValid finalValid uninitialized in
/-- Every completed generated expression determines whether initialization
failed in the old scope or the allocated binding's tail ran in the new scope. -/
theorem Tree.reflects {scope : Scope} {id : StatementId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      (resultContext = context ∨ resultContext = finalContext) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) resultContext outcome after ∧
      CompatibleStatements.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases tree with
  | @initialized node binder initializer initializerNode lowered body found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining =>
    rw [sequence_rename] at evaluated
    have input : ∃ input middle, Evaluates actual store (lowered.expression.rename ξ) input middle := by
      cases evaluated with
      | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, initial⟩
    obtain ⟨input, middleStore, initialEval⟩ := input
    obtain ⟨sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
      CompatibleExpressionConstructors.reflects functions extension program evidence initialValid uninitialized initial initialFound
        environments heaps locals agrees initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LanguageResult.bind_failure _ initialEval)
        exact ⟨context, _, middle, middleMap, middleWorld, .inl rfl, fault_intro rest found form mono failed,
          .fault matched, middleHeaps, maps, worlds, preservation, metadata⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append
        have tailEval := (ContinuationAgreement.letE allocationEval).unwrap ((ContinuationAgreement.bind initialEval).unwrap evaluated)
        obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata⟩ :=
          remaining.reflects functions definitions registered extension program evidence finalValid uninitialized
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead tailEval
        exact ⟨finalContext, outcome, after, finalMap, finalWorld, .inr rfl,
          prepend found form (.letInitialized (lookupStatement?_sound found) form initialTrace mono extended .append) trace,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata)⟩
private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ = CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

private theorem finish_from_flow {mapping : LocationMap} {world : StoreTyping}
    {environment : Environment} {before after : Store} {expected : TypeSystem.Ty} {type : Ty}
    {outcome : Dynamic.ControlOutcome} {flow : Expr} {value : Value}
    (fellThrough escaped : Word)
    (represented : CompatibleStatements.FlowRep (registry := registry) functions mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      CompatibleStatements.BodyRep (registry := registry) functions mapping world faults expected type outcome result := by
  cases represented with
  | fallthrough sourceEnvironment =>
    exact ⟨_, LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated) (by simpa [LanguageResult.success, Expr.weakenAt] using (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)) ,
      .fallthrough sourceEnvironment⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _ (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩

private theorem finish_input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {result : Value}
    (evaluated : Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after) :
    ∃ value middle, Evaluates environment before flow value middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

include definitions registered extension initialValid finalValid uninitialized in
/-- Initialization failure preserves its exact old-context effects. Success
allocates only afterward, then uses the concrete remaining binding tree. -/
theorem Tree.body_preserves {scope : Scope} {id : StatementId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code) (fellThrough escaped : Word) (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) resultContext outcome after) :
    (resultContext = context ∨ resultContext = finalContext) ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨reached, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    tree.preserves functions definitions registered extension program evidence initialValid finalValid uninitialized unique
      environments heaps locals agrees actualTyped reference read unmapped trace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented evaluated
  exact ⟨reached, result, finalStore, finalMap, finalWorld, by rw [finish_rename]; exact completed,
    related, finalHeaps, maps, worlds, frame, metadata⟩

include definitions registered extension initialValid finalValid uninitialized in
/-- Every completed generated expression determines whether initialization
failed in the old scope or the allocated binding's tail ran in the new scope. -/
theorem Tree.body_reflects {scope : Scope} {id : StatementId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code) (fellThrough escaped : Word)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      (resultContext = context ∨ resultContext = finalContext) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) resultContext outcome after ∧
      CompatibleStatements.BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  rw [finish_rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEvaluation⟩ := finish_input evaluated
  obtain ⟨resultContext, outcome, after, finalMap, finalWorld, reached, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    tree.reflects functions definitions registered extension program evidence initialValid finalValid uninitialized
      environments heaps locals agrees actualTyped reference read unmapped flowEvaluation
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented flowEvaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  exact ⟨resultContext, outcome, after, finalMap, finalWorld, reached, trace, related, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
