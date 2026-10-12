import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectNativePrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows

/-! The actual staged callee post constructs its original scoped boundary.
The first gate either constructs the exact staged rejection, retaining the
selected original row and exact token, or exposes the real argument helper.
That helper uses the ordered staged argument producer at the same reached
caller state. Application and diagnostic receiver transport follow separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open GenericExpressionMeaning (agree_prefix rename_prefix)

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

include sourceEq found sourceParent tree unique parentTyped in
/-- Original parent typing and the actual ordered compiler tree determine the
raw callee and argument rows. The SourceParent requirements, output coercions
and physical-count cuts remain explicit for this exact compiler receipt. -/
theorem source_rows :
    ∃ rawParameter rawResult,
      calleeNode.type = .function rawParameter rawResult ∧
      ExpressionsHaveTypes invocation.source context ids sourceTypes ∧
      TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
      compiler.original.type = rawResult := by
  have rawTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have rawUnique : NodeOccurrencesUnique source := by
    simpa only [sourceEq] using unique
  have rawParentTyped : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent rawTree rawUnique rawParentTyped found
  exact ⟨rawParameter, rawResult, calleeFunction,
    by simpa only [sourceEq] using argumentsTyped, bundle, originalResult⟩

private theorem foldlApplication_ne_function
    (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty)
    (head_ne : ∀ parameter result, head ≠ .function parameter result)
    (parameter result : TypeSystem.Ty) :
    arguments.foldl TypeSystem.Ty.application head ≠ .function parameter result := by
  induction arguments generalizing head with
  | nil => exact head_ne parameter result
  | cons argument arguments induction =>
      exact induction (.application head argument)
        (by intro candidateParameter candidateResult equality; cases equality)

private theorem nominal_ne_function
    (declaration : Resolved.DeclarationId) (arguments : List TypeSystem.Ty)
    (parameter result : TypeSystem.Ty) :
    TypeSystem.Ty.nominal declaration arguments ≠ .function parameter result :=
  foldlApplication_ne_function (.constructor (.declaration declaration)) arguments
    (by intro candidateParameter candidateResult equality; cases equality) parameter result

private theorem value_is_function {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap value (.function parameter result)) : IsFunction value := by
  cases value with
  | closure function => exact .closure function
  | global function => exact .global function
  | builtin function => exact .builtin function
  | constructed instantiation arguments =>
    rcases Dynamic.ValueHasType.constructed_inv typed with
      ⟨same, valid, _⟩ | ⟨_inner, impossible, _⟩
    · cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner constructor_eq
          substitution_exact substitution_range payloadTypes_eq resultType_eq =>
        have impossible := same.trans resultType_eq
        exact False.elim ((nominal_ne_function dataType.id
          (ParameterSubstitution.orderedArguments instantiation.parameterSubstitution dataType.parameters)
          parameter result) impossible.symm)
    · cases impossible
  | unit | bool | word | integer | product | proxy | mapping => cases typed

include caller view originalUnique sourceEq found sourceParent tree unique parentTyped in
/-- The actual callee payload comes from the positive receiving model. Its
Source function type and reached admission supply genuine callable shape;
the original scoped boundary factory then runs at that same payload. -/
theorem scoped_boundary {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue after carrier calleeStore finalMap finalWorld) :
    ∃ before originalMetadata, ContainsExpression sidecar.source prepared.site.call before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallView before compiler.original originalMetadata metadata ∧
      BoundaryAt sidecar prepared.site callee ids originalMetadata before sourceValue carrier := by
  obtain ⟨_rawParameter, _rawResult, calleeFunction, _argumentsTyped, _bundle, _originalResult⟩ :=
    source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  obtain ⟨reached, _related, admitted⟩ := post.2.2.2.2.2.2.2
  have typedSource := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value admitted |>.1
  rw [calleeFunction] at typedSource
  have positive := CallableIndexedOwnedContextualCalleeOriginReadReceipts.callable_at profile post.2.1
    (value_is_function typedSource)
  exact CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.boundary_at_source_view compiler prepared
    caller view originalUnique (CallableIndexedOwnedContextualCalleeStageReceipts.callee_origin positive)

/-- The stage branch retains its actual invocation and occurrence, exact
selected original row/metadata and native word. Its diagnostic representation
is identified later by the receiving codebook, not by changing the failure. -/
def StageRejectedPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld originalNode originalMetadata reason,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.value sourceValue) after ∧
    CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
      CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row ∧
      Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
        (Staging.Recursive.Size.stepSize [sourceSize]) invocation context environment before id
        (.fault (.stage invocation id reason)) after ∧
      value = .inLeft lowered.type (.word (dispatch.reason reason)) ∧ finalStore = calleeStore

/-- A real argument failure retains the cumulative reached state and full
receiving-model relation, with neither semantic nor nested stage tag changed. -/
def ArgumentFaultPrefix (value : Value) (finalStore : Store) : Prop :=
  ∃ calleeSize argumentsSize sourceValue calleeHeap failure after token finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.fault failure) after ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
      (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
      bridge functions compiler initial failure after token finalStore finalMap finalWorld

/-- Successful arguments retain their independent Source grade and actual
packed payload, raw callee/bundle/original-result rows, reached caller state
and strict original second-gate/application computation. No application trace
or body result is asserted here. -/
def ApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
    compiler.original.type = rawResult ∧
  ∃ calleeSize argumentsSize sourceValue calleeHeap sources values carrier argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    ∃ size, EvaluationSize size (DataPatternValues.packValues values :: .unit :: carrier :: actual) argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ size < budget

private theorem argument_fault_post {failure : Staging.Recursive.Failure} {type : TypeSystem.Ty}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : CallableIndexedOwnedAdmittedStagedExpressionSequence.PostAdmission bridge
      (context := context) (.fault failure) reached) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context type (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨post.rows, by intro _ impossible; cases impossible⟩
  | stage origin call reason => exact post.rows

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Whole-parent native reflection uses the strict staged callee IH once and
the actual scoped boundary. An accepted gate then invokes the concrete staged
argument fold at its genuine callee endpoint, preserving all transient effects. -/
theorem reflects_arguments (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CallableIndexedOwnedPreparedStagedIndirectNativePrefix.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge functions compiler initial budget value finalStore ∨
    StageRejectedPrefix (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore ∨
    ArgumentFaultPrefix (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge profile compiler initial value finalStore ∨
    ApplicationPrefix (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  cases CallableIndexedOwnedPreparedStagedIndirectNativePrefix.reflects_prefix bridge functions compiler prepared
      sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed initial admitted
      budget children completed within with
  | inl fault => exact .inl fault
  | inr positive =>
    obtain ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
      calleeNative, calleeStrict, calleeTrace, calleePost, gate⟩ := positive
    obtain ⟨original, originalMetadata, _contained, _form, callView, boundary⟩ :=
      scoped_boundary (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
        (tree := tree) (unique := unique) (parentTyped := parentTyped)
        bridge profile compiler prepared initial caller view originalUnique calleePost
    have gateResult :
        (∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
          ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
            CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata original dispatch.row ∧
            value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧ finalStore = calleeStore) ∨
        (Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
          ∃ suffixSize, EvaluationSize suffixSize (.unit :: carrier :: actual) calleeStore
            (CallableIndexedOwnedStoredIndirectNativePrefix.suffix prepared.site
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore ∧ suffixSize < budget) := by
      cases boundary with
      | user dispatch selected =>
          cases gate.resolve dispatch with
          | inl rejected =>
              obtain ⟨reason, rejected, valueEq, storeEq, _represented⟩ := rejected
              left
              refine ⟨reason, ?_, dispatch, selected, valueEq, storeEq⟩
              simpa only [guardFrame, prepared.call] using rejected
          | inr accepted =>
              right
              simpa only [guardFrame, prepared.call] using accepted
      | builtin receipt =>
          right
          simpa only [guardFrame, prepared.call] using receipt.resolve_prefix gate
    cases gateResult with
    | inl rejected =>
        obtain ⟨reason, rejected, dispatch, selected, valueEq, storeEq⟩ := rejected
        right; left
        refine ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
          original, originalMetadata, reason, calleeNative, calleeStrict, calleeTrace, calleePost, callView,
          dispatch, selected, rejected, .rejected occurrence calleeTrace rejected, ?_, storeEq⟩
        simpa only [loweredType] using valueEq
    | inr accepted =>
        obtain ⟨accepted, suffixSize, suffixTrace, suffixStrict⟩ := accepted
        obtain ⟨_calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ := calleePost
        have argumentLayout : EnvironmentsAgree
            (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
            canonical (Value.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
        have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
          (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
        cases CallableIndirectCallBounds.bind_completed suffixTrace (Nat.le_of_lt suffixStrict) with
        | failed arguments argumentsStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @fault failure token matched =>
                right; right; left
                refine ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after, token, finalMap, finalWorld,
                  calleeTrace, accepted, argumentsTrace, .argumentsFault occurrence calleeTrace accepted argumentsTrace,
                  ?_, (by simpa only [loweredType] using completed.sound), .fault matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
                  calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
                  reached, callerProtocol.trans calleeRelated related, argument_fault_post bridge post⟩
                simp only [loweredType]
        | continued arguments remaining argumentsStrict remainingStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @values sources values relatedValues =>
                right; right; right
                exact ⟨rawParameter, rawResult, calleeFunction, bundle, originalResult,
                  calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier, after, _, finalMap, finalWorld,
                  original, originalMetadata, calleeTrace, accepted, argumentsTrace, relatedValues,
                  GenericHeap.PayloadModel.extend model payload maps worlds, callView, boundary, finalHeaps,
                  calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
                  calleeMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans calleeRelated related, post.at_values⟩,
                  _, remaining, remainingStrict⟩

end Calls
/-- Source function typing excludes data-valued callees before direct dispatch. -/
theorem callable_shape {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap value (.function parameter result)) : IsFunction value :=
  value_is_function typed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix
