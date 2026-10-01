import Solcore.SourceSemantics.CoreLowering.NamedCallSource
import Solcore.SourceSemantics.CoreLowering.NamedCallCertificates
import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedParameterIndexed

/-! Concrete named-call bodies beneath their actual installed template
renaming. Parameter and body meaning is derived from the concrete lexical
certificate. Native references, source declaration evidence and protected snapshot
history are explicit independent facts, never inferred from a function type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

private theorem rename_front (expression : Expr) (ξ : Renaming) :
    (expression.weakenAt 0).rename ξ.lift = (expression.rename ξ).weakenAt 0 := by
  simp only [← Expr.rename_insertion, Expr.rename_comp, Renaming.lift_comp_insertion_zero]

/-- Installation weakens the entire wrapper, including its frame reference.
This is a syntax law, not equality of closure values across environments. -/
theorem withFrame_rename (reference next body : Expr) (ξ : Renaming) :
    (SourceCoreCallableIndexedFrames.withFrame reference next body).rename ξ =
      SourceCoreCallableIndexedFrames.withFrame (reference.rename ξ) (next.rename ξ) (body.rename ξ) := by
  simp only [SourceCoreCallableIndexedFrames.withFrame, SourceCoreCallableContextFrames.withFrame,
    Expr.rename, rename_front, Renaming.lift]

private theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

/-- The actual general callable profile wraps this named reference with its
owned descriptor. The closure code remains the global cell's exact payload. -/
theorem reference_decoration (native : SourceCoreGeneralFunctions.CallableContext)
    (active : TypeSystem.Substitution) (compilation : SourceCoreFunctions.Context)
    (source : TypedSource) (node : ExpressionNode) (signature : SourceCoreCalls.Signature)
    (index : Nat) (identity : Word)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named signature.key))
    (accepted : SourceCoreCallableContracts.descriptor native.table (.named signature.key) = .ok descriptor) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).decorateCallable compilation source node
      (.named signature.key) signature.parameterType signature.resultType
      (SourceCoreFunctions.namedReference signature index identity compilation.internalReason) =
      .ok (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
        (SourceCoreFunctions.namedReference signature index identity compilation.internalReason)
        (LanguageResult.success (descriptor.wrap (.var 0)))) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, accepted, Except.mapError,
    bind, Except.bind, pure, Except.pure]
  rfl

theorem native_reference {environment captured : Environment} {store : Store}
    {signature : SourceCoreCalls.Signature} {index : Nat} {location : Location}
    {identity internalReason : Word} {body : Expr}
    {table : SourceCoreStageCodebook.Table}
    (descriptor : SourceCoreCallableContracts.Descriptor table (.named signature.key))
    (reference : environment[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) :
    Evaluates environment store
      (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
        (SourceCoreFunctions.namedReference signature index identity internalReason)
        (LanguageResult.success (descriptor.wrap (.var 0))))
      (.inRight .word (.pair (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))
        (.word descriptor.id))) store := by
  have selected := OptionalCell.read_success internalReason (Evaluates.var reference) read
  have tagged : Evaluates environment store (SourceCoreFunctions.namedReference signature index identity internalReason)
      (.inRight .word (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) store :=
    LanguageResult.bind_success
    (TaggedFunction.functionType signature.parameterType signature.resultType) selected
    (Evaluates.inRight (Evaluates.pair (Evaluates.inRight Evaluates.word) (Evaluates.var rfl)))
  exact LanguageResult.bind_success _ tagged (.inRight (.pair (.var rfl) .word))

/-- Completed formation recovers exactly the owned cell payload and descriptor
and leaves the shared store unchanged. It does not authenticate arbitrary
externally supplied closure bodies merely from their function type. -/
theorem native_reference_reflects {environment captured : Environment} {store finalStore : Store}
    {signature : SourceCoreCalls.Signature} {index : Nat} {location : Location}
    {identity internalReason : Word} {body : Expr} {value : Value}
    {table : SourceCoreStageCodebook.Table}
    (descriptor : SourceCoreCallableContracts.Descriptor table (.named signature.key))
    (reference : environment[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (executed : Evaluates environment store
      (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
        (SourceCoreFunctions.namedReference signature index identity internalReason)
        (LanguageResult.success (descriptor.wrap (.var 0)))) value finalStore) :
    value = .inRight .word (.pair (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))
        (.word descriptor.id)) ∧ finalStore = store :=
  evaluation_deterministic executed (native_reference descriptor reference read)


/-- Actual reference lowering simultaneously constructs the independent source
global value and the owned native descriptor paired with the exact installed
cell payload. Completed formation recovers that same value/store. -/
theorem accepted_named_reference
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {index : Nat} {signature : SourceCoreCalls.Signature} {identity : Word}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature policy compilation source node instantiation true = .ok (index, signature))
    (identified : Word.ofNat? (index + 1) = some identity)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named signature.key))
    (descriptorAccepted : SourceCoreCallableContracts.descriptor native.table (.named signature.key) = .ok descriptor)
    {program : Program} {context : SourceSemantics.Context} {evidence produced : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {heap : Dynamic.Heap}
    (coercions : node.coercions = [])
    (requirements : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (closed : Dynamic.RequirementsProduceEnvironment context evidence [] instantiation.predicates produced)
    {environment captured : Environment} {store : Store} {location : Location} {body : Expr}
    (globalReference : environment[scope.length + compilation.administrativePrefix + index]? =
      some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (globalPayload : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) :
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[index]? = some signature ∧
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment heap id (.global ⟨instantiation, produced⟩) heap ∧
    Evaluates environment store lowered.expression
      (.inRight .word (.pair (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))
        (.word descriptor.id))) store ∧
    (∀ value finalStore, Evaluates environment store lowered.expression value finalStore →
      value = .inRight .word (.pair (.pair (.inRight .unit (.word identity))
        (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))
        (.word descriptor.id)) ∧ finalStore = store) := by
  obtain ⟨selectedIndex, selectedSignature, selectedIdentity, selected, identifiedAction, decorated, _⟩ :=
    reference_of_accepted owner found read form special accepted
  have same := Except.ok.inj (selected.symm.trans selection)
  cases same
  have sameIdentity := Option.some.inj (identifiedAction.symm.trans identified)
  cases sameIdentity
  rw [profile, reference_decoration native active compilation source node signature _ identity descriptor descriptorAccepted] at decorated
  have emitted := Except.ok.inj decorated
  have sourceEvaluation := reference (program := program) (environment := sourceEnvironment) (heap := heap)
    found form coercions requirements valid closed
  obtain ⟨target, global⟩ := selected_signature_target selection
  rw [← emitted]
  exact ⟨target, global, sourceEvaluation, native_reference descriptor globalReference globalPayload,
    fun _ _ evaluated => native_reference_reflects descriptor globalReference globalPayload evaluated⟩


variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (certificate : TypedLexicalNamedBody.Certificate layouts owner active prepared.layout.frame allocationGlobals onError readFuel values function.source context solved reasonAt
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
    policy fuel fellThrough escaped body)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped in
/-- A source allocation and its finite body trace execute the real full named
hook. Parameters are compared with the independently constructed allocation. -/
theorem hook_preserves {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := TypedMixedNamedParameters.entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    TypedLexicalNamedParameters.preserves functions extension definitions registered program contextValid unique uninitialized missing entry certificate trace
  rw [rename_prefix] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var actualReference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    renamed.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame, by simpa only [sameEnvironment, sameHeap] using reached⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped in
/-- Completed actual native execution constructs both source parameter
allocation and the independent body trace from the installed call context with its actual lexical stopping context. -/
theorem hook_reflects {value : Value} {finalStore : Store}
    (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ origin index metadata environment bound outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := TypedMixedNamedParameters.entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  rw [renamed] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var actualReference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_prefix] at bodyEvaluation
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    TypedLexicalNamedParameters.reflects functions extension definitions registered program contextValid unique uninitialized missing entry certificate bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, entry.environment, entry.heap, outcome, after, finalMap, finalWorld, owned, history,
    entry.allocation, trace, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame, reached⟩

/-- The installed global read is pure; after the concrete nil pack, the real
call helper enters exactly the retained closure body. Reflection uses native
evaluation inversion, with no child body evaluation supplied. -/
theorem installed_call_agreement {signature : SourceCoreCalls.Signature}
    {caller captured : Environment} {store : Store} {index : Nat} {location : Location} {body : Expr} {reason : Word}
    (reference : caller[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) :
    ContinuationAgreement caller store
      (SourceCoreCalls.call signature index (SourceCoreCalls.packArguments []).expression reason)
      (.unit :: captured) store body := by
  have arguments := nil_arguments_evaluates caller store
  have selected := OptionalCell.read_success reason
    (show Evaluates (.unit :: caller) store (.var (index + 1))
      (.cellRef (OptionalCell.cellType signature.functionType) location) store from .var reference) read
  constructor
  · intro value finalStore executed
    exact SourceCoreCalls.call_success arguments selected executed
  · intro value finalStore executed
    obtain ⟨_, sized⟩ := evaluation_has_size executed
    obtain ⟨_, _, following⟩ := sized.bind_success arguments
    obtain ⟨_, _, applied⟩ := following.bind_success selected
    obtain ⟨_, _, bodyEvaluation⟩ := applied.apply_body (.var rfl) (.var rfl)
    exact bodyEvaluation.sound


/-- Compiler success and its accepted plan selection enter the exact installed
body. This closes call formation/inversion without any child body evaluation. -/
theorem accepted_nil_agreement
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {type : Ty} {index : Nat} {signature : SourceCoreCalls.Signature}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {environment captured : Environment} {store : Store} {location : Location} {body : Expr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee [] (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature))
    (reference : environment[scope.length + compilation.administrativePrefix + index]? =
      some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (payload : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured))) :
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[index]? = some signature ∧ lowered.type = type ∧
    ContinuationAgreement environment store lowered.expression (.unit :: captured) store body := by
  obtain ⟨selectedIndex, selectedSignature, selected, emitted, typed⟩ :=
    nil_call_of_accepted owner found read form special accepted
  have same := Except.ok.inj (selected.symm.trans selection)
  cases same
  obtain ⟨target, global⟩ := selected_signature_target selection
  exact ⟨target, global, typed, emitted.symm ▸ installed_call_agreement reference payload⟩


variable {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance}
  (sourceFrame : SourceFrame program instantiation bodyInstance function)
  (agreement : CompatibleNamedBody.NamedAgreement named function)
  (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
  {signature : SourceCoreCalls.Signature} {callerEnvironment captured : Environment}
  {globalIndex slot : Nat} {globalLocation : Location}
  {compiledRepresentation : SourceCoreGeneralFunctions.Representation} {compiledFuel : Nat}
  (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base compiledRepresentation compiledFuel)
  (selected : base.functions[slot]? = some named)
  (cached : compiled.closures[slot]? = some
    (.lambda signature.parameterType (LanguageResult.resultType signature.resultType) code))
  (signatureOwned : signature = named.signature)
  (parameterUnit : signature.parameterType = .unit) (resultType : signature.resultType = output)
  (bodyEnvironment : actual = .unit :: captured)
  (globalReference : callerEnvironment[globalIndex]? = some (.cellRef (OptionalCell.cellType signature.functionType) globalLocation))
  (globalRead : store.read? globalLocation = some (.inRight .unit
    (.closure signature.parameterType (LanguageResult.resultType signature.resultType) (code.rename ξ) captured)))

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- A finite independent named-body trace executes the actual installed
global-cell call. Its nil argument pack is derived, and the concrete body
certificate closes all body meaning beneath the real indexed frame wrapper. -/
theorem nil_call_preserves
    (nativeNil : nativeArguments = [])
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after)
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      base.functions[slot]? = some named ∧
      compiled.closures[slot]? = some (.lambda signature.parameterType
        (LanguageResult.resultType signature.resultType) code) ∧
      signature = named.signature ∧ signature.parameterType = .unit ∧ signature.resultType = output ∧
      CompatibleNamedBody.NamedAgreement named function ∧
      SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before
        (.global ⟨instantiation, function.evidence⟩) [] outcome after ∧
      Evaluates callerEnvironment store (SourceCoreCalls.call signature globalIndex
        (SourceCoreCalls.packArguments []).expression Word.zero) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, value, finalStore, finalMap, finalWorld, owned, history,
    evaluated, result, finalHeap, maps, worlds, frame, extendedMetadata, restored, preservedSnapshots, _⟩ :=
    hook_preserves prepared functions extension program onError certificate parameters inputs extended contextValid unique
      uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments heaps initialLocals
      actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots allocated trace
  have nilSource : arguments = [] := List.eq_nil_of_length_eq_zero (by
    rw [← represented.length.1, represented.length.2, nativeNil]
    rfl)
  have source := sourceFrame.call (callerContext := callerContext) (caller := callerEvidence) (sourceFrame.body_of_trace extended allocated trace)
  have applied : Evaluates (.unit :: captured) store (code.rename ξ) value finalStore := bodyEnvironment ▸ evaluated
  have argumentsEvaluation := nil_arguments_evaluates callerEnvironment store
  have read := OptionalCell.read_success Word.zero
    (show Evaluates (.unit :: callerEnvironment) store (.var (globalIndex + 1))
      (.cellRef (OptionalCell.cellType signature.functionType) globalLocation) store from .var globalReference) globalRead
  have invocation := SourceCoreCalls.call_success argumentsEvaluation read applied
  exact ⟨origin, index, metadata, value, finalStore, finalMap, finalWorld, owned, history,
    selected, cached, signatureOwned, parameterUnit, resultType, agreement, target, nilSource ▸ source, invocation, result, finalHeap, maps, worlds, frame, extendedMetadata, restored, preservedSnapshots⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- Every completed installed nil-argument call constructs an independent
source global application, including body faults and exact shared-heap writes.
The parameter prefix and lexical body are derived from their static receipts. -/
theorem nil_call_reflects (nativeNil : nativeArguments = [])
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates callerEnvironment store (SourceCoreCalls.call signature globalIndex
      (SourceCoreCalls.packArguments []).expression Word.zero) value finalStore) :
    ∃ origin index metadata outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      base.functions[slot]? = some named ∧
      compiled.closures[slot]? = some (.lambda signature.parameterType
        (LanguageResult.resultType signature.resultType) code) ∧
      signature = named.signature ∧ signature.parameterType = .unit ∧ signature.resultType = output ∧
      CompatibleNamedBody.NamedAgreement named function ∧
      SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before
        (.global ⟨instantiation, function.evidence⟩) [] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  have bodyEvaluation := (installed_call_agreement globalReference globalRead).unwrap evaluated
  rw [← bodyEnvironment] at bodyEvaluation
  obtain ⟨origin, index, metadata, environment, bound, outcome, after, finalMap, finalWorld, owned, history,
    allocated, trace, result, finalHeap, maps, worlds, frame, extendedMetadata, restored, preservedSnapshots, _⟩ :=
    hook_reflects prepared functions extension program onError certificate parameters inputs extended contextValid unique
      uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments heaps initialLocals
      actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots bodyEvaluation
  have nilSource : arguments = [] := List.eq_nil_of_length_eq_zero (by
    rw [← represented.length.1, represented.length.2, nativeNil]
    rfl)
  have source := sourceFrame.call (callerContext := callerContext) (caller := callerEvidence)
    (sourceFrame.body_of_trace extended allocated trace)
  exact ⟨origin, index, metadata, outcome, after, finalMap, finalWorld, owned, history,
    selected, cached, signatureOwned, parameterUnit, resultType, agreement, target, nilSource ▸ source, result, finalHeap,
    maps, worlds, frame, extendedMetadata, restored, preservedSnapshots⟩


include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- Preservation starts with the independent instantiated declaration body's
outcome. Its real parameter allocation and trace are extracted at the concrete
certified context, rather than supplied as a semantic body hypothesis. -/
theorem nil_body_preserves (nativeNil : nativeArguments = [])
    {after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (execution : BodyOutcome program bodyInstance function.evidence before arguments outcome after)
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      base.functions[slot]? = some named ∧
      compiled.closures[slot]? = some (.lambda signature.parameterType
        (LanguageResult.resultType signature.resultType) code) ∧
      signature = named.signature ∧ signature.parameterType = .unit ∧ signature.resultType = output ∧
      CompatibleNamedBody.NamedAgreement named function ∧
      SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before
        (.global ⟨instantiation, function.evidence⟩) [] outcome after ∧
      Evaluates callerEnvironment store (SourceCoreCalls.call signature globalIndex
        (SourceCoreCalls.packArguments []).expression Word.zero) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  have arity : function.parameters.length = arguments.length := by
    rw [parameters, List.length_map]
    exact represented.length.1
  obtain ⟨environment, bound, allocated, trace⟩ := sourceFrame.trace_of_body extended arity execution
  exact nil_call_preserves prepared functions extension program onError certificate parameters inputs extended
    contextValid unique uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments
    heaps initialLocals actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots
    sourceFrame agreement target compiled selected cached signatureOwned parameterUnit resultType bodyEnvironment globalReference globalRead
    nativeNil allocated trace callerContext callerEvidence


include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- The final ordinary expression boundary consumes actual lowering success,
canonical selected-key attribution and the concrete body tree. Every completed
Core result reconstructs the independent source direct call, with the exact
callee instantiation/evidence and restored indexed administration. -/
theorem nil_expression_reflects
    (nativeNil : nativeArguments = [])
    {expressionPolicy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {expressionFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {name : String} {type : Ty}
    {expressionReason : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : expressionPolicy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee [] (.declaration instantiation))
    (special : (match expressionPolicy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy lowerBody (min budget expressionFuel)
              compilation childSource childScope childId childReasonAt)
          (expressionFuel + 1) source scope id expressionReason) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy lowerBody (expressionFuel + 1)
      compilation source scope id expressionReason = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature expressionPolicy compilation source node instantiation false = .ok (slot, signature))
    (offset : globalIndex = scope.length + compilation.administrativePrefix + slot)
    (internal : compilation.internalReason = Word.zero)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : node.coercions = [])
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence node.requirements node.coercions
      instantiation.predicates function.evidence)
    (sourceEnvironment : Dynamic.Environment)
    {value : Value} {finalStore : Store}
    (evaluation : Evaluates callerEnvironment store lowered.expression value finalStore) :
    ∃ origin index metadata outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence source sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨selectedIndex, selectedSignature, selectedAction, emitted, _⟩ :=
    nil_call_of_accepted owner found read form special accepted
  have same := Except.ok.inj (selectedAction.symm.trans selection)
  cases same
  rw [emitted, ← offset, internal] at evaluation
  obtain ⟨origin, index, metadata, outcome, after, finalMap, finalWorld, owned, history, _, _, _, _, _, _, _,
    called, represented, finalHeaps, maps, worlds, admin, metadataExtended, frameRestored, savedSnapshots⟩ :=
    nil_call_reflects prepared functions extension program onError certificate parameters inputs extended
      contextValid unique uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments
      heaps initialLocals actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots
      sourceFrame agreement target compiled selected cached signatureOwned parameterUnit resultType bodyEnvironment globalReference globalRead
      nativeNil callerContext callerEvidence evaluation
  have sourceEvaluation := direct_nil (environment := sourceEnvironment) found form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed called
  exact ⟨origin, index, metadata, outcome, after, finalMap, finalWorld, owned, history,
    sourceEvaluation, represented, finalHeaps, maps, worlds, admin, metadataExtended, frameRestored, savedSnapshots⟩


include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped sourceFrame agreement target compiled selected cached signatureOwned
  parameterUnit resultType bodyEnvironment globalReference globalRead in
/-- Preservation of the actual lowered expression starts with the independent
instantiated declaration body. The concrete certificate constructs body/prefix
meaning and preserves the exact source declaration and caller evidence. -/
theorem nil_expression_preserves
    (nativeNil : nativeArguments = [])
    {expressionPolicy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {expressionFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {name : String} {type : Ty}
    {expressionReason : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : expressionPolicy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee [] (.declaration instantiation))
    (special : (match expressionPolicy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy lowerBody (min budget expressionFuel)
              compilation childSource childScope childId childReasonAt)
          (expressionFuel + 1) source scope id expressionReason) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy expressionPolicy lowerBody (expressionFuel + 1)
      compilation source scope id expressionReason = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature expressionPolicy compilation source node instantiation false = .ok (slot, signature))
    (offset : globalIndex = scope.length + compilation.administrativePrefix + slot)
    (internal : compilation.internalReason = Word.zero)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : node.coercions = [])
    (callerContext : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence node.requirements node.coercions
      instantiation.predicates function.evidence)
    (sourceEnvironment : Dynamic.Environment)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (execution : BodyOutcome program bodyInstance function.evidence before arguments outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence source sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store lowered.expression value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨selectedIndex, selectedSignature, selectedAction, emitted, _⟩ :=
    nil_call_of_accepted owner found read form special accepted
  have same := Except.ok.inj (selectedAction.symm.trans selection)
  cases same
  obtain ⟨origin, index, metadata, value, finalStore, finalMap, finalWorld, owned, history, _, _, _, _, _, _, _,
    called, evaluation, represented, finalHeaps, maps, worlds, admin, metadataExtended, frameRestored, savedSnapshots⟩ :=
    nil_body_preserves prepared functions extension program onError certificate parameters inputs extended
      contextValid unique uninitialized missing acceptedPrefix definitions registered acceptedHook represented environments
      heaps initialLocals actualLayout actualTyped canonicalReference actualReference unmapped typed caller snapshots
      sourceFrame agreement target compiled selected cached signatureOwned parameterUnit resultType bodyEnvironment globalReference globalRead
      nativeNil execution callerContext callerEvidence
  have sourceEvaluation := direct_nil (environment := sourceEnvironment) found form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed called
  rw [emitted, ← offset, internal]
  exact ⟨origin, index, metadata, value, finalStore, finalMap, finalWorld, owned, history,
    sourceEvaluation, evaluation, represented, finalHeaps, maps, worlds, admin, metadataExtended, frameRestored, savedSnapshots⟩

end Solcore.SourceSemantics.CoreLowering.NamedCalls
