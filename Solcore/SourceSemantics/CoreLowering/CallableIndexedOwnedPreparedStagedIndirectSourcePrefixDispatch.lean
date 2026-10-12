import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectValuesPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds

/-! The original recursively staged indirect parent selects its actual executed
prefix. Faults construct full native parent results from strict child hypotheses;
successful arguments retain the original application trace and real native
prefix. No application execution law is supplied to the classifier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSourcePrefixDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

private inductive SourcePrefix (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (call callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution) :
    Nat → Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | calleeFault {childSize failure after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault failure) after
  | notCallable {childSize value after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (invalid : ¬ Dynamic.CallableValue value) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.semantic .notCallable)) after
  | rejected {childSize value after reason}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (rejected : Staging.CallBoundary.GuardRejects invocation.guards call ids value reason) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.stage invocation call reason)) after
  | argumentsFault {childSize argumentsSize value middle after failure}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize]) (.fault failure) after
  | sourceArity {childSize argumentsSize value middle after values}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.values values) after)
      (mismatch : ids.length ≠ metadata.argumentCount) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize])
        (.fault (.semantic (.argumentArityMismatch metadata.argumentCount ids.length))) after
  | applied {childSize argumentsSize applicationSize value calleeHeap argumentsHeap after values outcome}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) calleeHeap)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment calleeHeap ids (.values values) argumentsHeap)
      (called : Staging.Recursive.Size.Applies program stages applicationSize invocation context
        argumentsHeap value values outcome after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize, applicationSize]) outcome after

private theorem source_prefix
    {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {size : Nat} {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (trace : Staging.Recursive.Size.Expression program stages size invocation context
      environment before id outcome after) :
    SourcePrefix program stages invocation context environment before id callee ids metadata size outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm}, Staging.Recursive.Occurrence invocation id actualForm →
      actualForm = .call callee ids (.indirect metadata) := by
    intro actualForm occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | calleeFault occurrence child =>
      cases occurrence_form occurrence
      exact .calleeFault child
  | notCallable occurrence child invalid =>
      cases occurrence_form occurrence
      exact .notCallable child invalid
  | rejected occurrence child rejected =>
      cases occurrence_form occurrence
      exact .rejected child rejected
  | argumentsFault occurrence child accepted arguments =>
      cases occurrence_form occurrence
      exact .argumentsFault child accepted arguments
  | sourceArity occurrence child accepted arguments mismatch =>
      cases occurrence_form occurrence
      exact .sourceArity child accepted arguments mismatch
  | applied occurrence _uncoerced child accepted arguments _arity called =>
      cases occurrence_form occurrence
      exact .applied child accepted arguments called
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _ => cases occurrence_form occurrence

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
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
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

/-- The actual failed Source parent already supplies its original grade,
outcome and heap. This is the native result and complete caller post at that
same endpoint, constructed by strict child preservation. -/
def NativeResultAt (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ value finalStore finalMap finalWorld,
    Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type
      lowered.type callFaults outcome value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type outcome reached

/-- The successful prefix keeps the actual Source application and its strict
grade, together with the constructed original native callee/arguments and
complete reached admission. It contains no native application law. -/
def ApplicationAt (budget size : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources,
    size = Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize] ∧
    applicationSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after ∧
    CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.ValuesPrefix
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial
      sourceValue calleeHeap argumentsHeap sources

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver in
/-- The literal original Source trace selects a branch once. Its three prefix
failure constructors produce the complete native parent. The actual successful
argument endpoint is retained for the independent application producer. -/
theorem preserves_fault_or_application (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    NativeResultAt (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after ∨
    ApplicationAt (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget size outcome after := by
  have parentFound : invocation.source.lookupExpression? id = some compiler.original := by
    rw [sourceEq]
    exact compiler.found
  have selected := source_prefix unique parentFound compiler.originalForm trace
  cases selected with
  | calleeFault child =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.preserves_callee_fault
        bridge functions compiler prepared sourceEq occurrence certified found sourceTyped
        environments heaps locals agrees typed initial admitted budget children child within
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | @notCallable childSize sourceValue after child invalid =>
    have smaller : childSize < budget := Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize
      (child := childSize) (children := [childSize]) (by simp)) within
    have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
    have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
      children _ smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | value payload =>
      obtain ⟨_originalNode, _originalMetadata, _contains, _form, _view, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique
          ⟨evaluated, payload, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
      cases boundary with
      | user dispatch _ =>
        have callable := (CallableLedger.frame sidecar).userCallable dispatch.bound
        cases callable <;> exact False.elim (invalid trivial)
      | builtin _ => exact False.elim (invalid trivial)
  | rejected child rejected =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds.preserves_rejected
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame
        profile certified found sourceTyped environments heaps locals agrees typed admitted
        caller originalUnique sourceParent tree unique parentTyped budget children child within rejected
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | argumentsFault child accepted arguments =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds.preserves_argument_fault
        bridge profile compiler prepared sourceEq occurrence certified found sourceTyped environments heaps locals
        agrees typed initial admitted caller view originalUnique guardFrame sourceParent tree unique parentTyped
        budget children child accepted arguments within
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | sourceArity _ _ _ mismatch => exact False.elim (mismatch sourceParent.arity)
  | @applied calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap after sources outcome child accepted arguments called =>
    have prefixBound : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget := by
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within ⊢
      omega
    have strict : applicationSize < budget := Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize
      (child := applicationSize) (children := [calleeSize, argumentsSize, applicationSize]) (by simp)) within
    have constructedPrefix := CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.preserves_values
      bridge profile compiler prepared sourceEq certified found sourceTyped environments heaps locals agrees
      typed initial admitted caller view originalUnique guardFrame sourceParent tree unique parentTyped
      budget children child accepted arguments prefixBound
    exact .inr ⟨_, _, _, _, _, _, _, rfl, strict, child, accepted, arguments, called, constructedPrefix⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectSourcePrefixDispatch
