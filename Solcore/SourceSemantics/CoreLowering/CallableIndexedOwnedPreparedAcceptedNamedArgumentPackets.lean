import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAcceptedIndirectPhysicalArity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment

/-! Accepted named application retains the actual positive named association.
Its Source frame fixes the raw signature and ordered binders. The selected
second gate fixes physical arity separately, while the compiler fixes the
native bundle. Static body profiles remain independent of execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {calleeHeap : Dynamic.Heap} {store : Store}
  {function : Dynamic.GlobalFunction} {native : Value} {canonical : Environment}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {unknown : Word} {sourceType : TypeSystem.Ty}

local notation "positive" => functions qualification headers keys bodyRegistry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry positive

/-- These are finite static compiler profiles for the actual owned headers.
They contain no Source trace, native execution or body meaning premise. -/
structure StaticBodies where
  layouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts
  profiles : ∀ (origin : Owner (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (profile := profile))
      (header : Header compiled (Program.ofChecked compiled.sourceProgram)), header ∈ headers →
    CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      positive origin.owner (header := header)
  syntaxTree : ∀ header, header ∈ headers →
    GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType

include bridge compiler in
/-- Construct the named application packet once at the actual argument state.
The positive association supplies the same complete Source dictionary and
capture; neither is reconstructed from an erased function relation. -/
theorem at_arguments
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (static : StaticBodies (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (profile := profile)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (faults := faults))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata
      compiler.original dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none)
    {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
    (admitted : Admission bridge context initial)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter result sourceResultType : TypeSystem.Ty} {packed : Dynamic.Value}
    (calleeRelated : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      index.mapping index.world sourceType (.global function) native compiler.calleeCode.type)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
    (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
    (represented : DataExpressionSequence.Values model index.mapping index.world
      sourceTypes (compiler.codes.map (·.type)) arguments payloads)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (rawArguments : Dynamic.ValuesHaveTypes context index.heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (rawBundle : TypeSystem.Ty.productMany types = parameter)
    (resultSame : sourceResultType = result) :
    ∃ actualSourceResult,
      SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult ∧
      CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.Receipt
        (qualification := qualification) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax)
        (mapping := index.mapping) (world := index.world) (before := index.heap)
        (arguments := arguments) (payloads := payloads)
        positive (.global function) function.evidence native actualSourceResult compiler.resultType := by
  obtain ⟨actualType, _sameType, ⟨packet⟩⟩ := global_member calleeRelated function rfl
  generalize compilerType : compiler.calleeCode.type = nativeType at packet
  cases packet with
  | @named header rawD source identity origin member sourceAt capture installed number projection descriptor typed =>
    rcases calleeTyped.global_inv with ordinary | staged
    · obtain ⟨typeEq, _valid, _evidence⟩ := ordinary
      obtain ⟨facts, certified⟩ :=
        CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
      have signature := TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)
      have bindingTypes : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
        have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
        rw [header.parameters] at bodyTypes
        simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
      have nativeSignature : compiler.parameterType = header.named.signature.parameterType ∧
          compiler.resultType = header.named.signature.resultType := by
        have acceptedType := compiler.callableType
        rw [actualFunctionType] at acceptedType
        exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (acceptedType.trans compilerType)
      have physical := CallableIndexedOwnedAcceptedIndirectPhysicalArity.named_count sourceAt caller dispatch selected accepted
      have ordered := compiler.ordered_children.1
      have representedCount : compiler.codes.length = arguments.length := by
        simpa only [List.length_map] using represented.length.1
      have actualCount : arguments.length = header.bindings.length := by
        have parameterCount : header.function.parameters.length = header.bindings.length := by
          simpa only [List.length_map] using congrArg List.length header.parameters
        exact representedCount.symm.trans (ordered.symm.trans (physical.symm.trans parameterCount))
      have sourcePacked := sourceBundle.trans (signature.1.trans (congrArg TypeSystem.Ty.productMany bindingTypes))
      have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
          SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :=
        (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
          (compiler.packedType.symm.trans (nativeSignature.1.trans header.parameterType))
      have binderArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
        header.bindings represented actualCount sourcePacked nativePacked
      refine ⟨header.function.resultType,
        congrArg SourceCoreRawMetadata.runtimeType (resultSame.trans (signature.2.trans sourceAt.frame.result.symm)), ?_⟩
      rw [nativeSignature.2, header.resultType]
      simpa only [CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.carrier, header.resultType] using
        (CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts.named positive bridge initial admitted runtime
        extension rawArguments packing rawBundle origin.owner member origin.capture_zero (origin.globals member)
        sourceAt capture identity descriptor.id (static.layouts header member) wellFormed calleeTyped
        binderArguments (static.profiles origin header member) (static.syntaxTree header member))
    · obtain ⟨inner, impossible, _innerTyped⟩ := staged
      cases impossible

include bridge compiler in
/-- Original Source typing and the actual accepted selected row construct the
full named argument factory with the original invocation and result indices. -/
theorem packets
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (static : StaticBodies (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (profile := profile)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (faults := faults))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) calleeNode.type)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType (.global function) native compiler.calleeCode.type)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata
      compiler.original dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none) :
    CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := function.evidence) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .global function) (calleeNative := native) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := by
  obtain ⟨sourceParameter, sourceResult, calleeType, _typedRows, sourceBundle, resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler parent tree unique parentTyped calleeFound
  rw [calleeType] at calleeTyped
  rcases calleeTyped.global_inv with ordinary | staged
  · obtain ⟨originalType, _valid, _evidence⟩ := ordinary
    intro middleMap middleWorld middle middleStore arguments payloads types parameter result packed
      argumentState admitted maps worlds _frame _metadata actualTyped extension rows _heaps rawArguments packing rawBundle
    rcases actualTyped.global_inv with actual | staged
    · obtain ⟨actualType, _actualValid, _actualEvidence⟩ := actual
      have signature := TypeSystem.Ty.function.inj (originalType.trans actualType.symm)
      exact at_arguments bridge compiler actualFunctionType static wellFormed caller dispatch selected accepted
        argumentState admitted runtime
        (represented.extend (SourceCoreRawMetadata.Extends.refl registry) maps worlds) actualTyped extension rows
        (sourceBundle.trans signature.1) rawArguments packing rawBundle (resultType.trans signature.2)
    · obtain ⟨inner, impossible, _innerTyped⟩ := staged
      cases impossible
  · obtain ⟨inner, impossible, _innerTyped⟩ := staged
    cases impossible

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets
