import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredMemberCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds

/-! A selected initialized local call supplies the admitted expression head
from its original whole Source trace or native completion. The original Source
children retain their own grades. Positive live cells are required separately
at every input state; argument execution only extends the already-read callable
association. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedStoredClosureArgumentReceipts
open CallableIndexedOwnedContextualStoredMemberCallBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section Source
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {location : Dynamic.Location}
  {function : Dynamic.Closure} {native : Core.Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
  {readFuel : Nat} {readReason : Word} {readCode : Expr}
  (read : CompatibleExpressionReads.Certificate readFuel (.initial compiled.compatible.checked)
    source scope callee readReason readCode)
  (stored : CallableIndexedOwnedContextualInitializedClosureReceipts.StoredAt headers keys registry faults
    mapping world heap store location function native bindings parameter result)
  (lookup : Dynamic.Environment.LooksUp environment read.binder location)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (heapTyped : Dynamic.HeapWellTyped context heap)
  (parentTyped : ExpressionHasType source context id compiler.original.type)

include parent read stored lookup unique wellFormed runtime covers locals heapTyped parentTyped in
/-- A finite inversion keeps the original measured children. The initialized
Source read is constructed directly from its actual cell; no diagnostic read
producer or body execution is called to identify these children. -/
theorem suffix_of_source {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment heap id outcome after) :
    ∃ calleeSize argumentsSize callSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
        context evidence source environment heap callee (.closure function) heap ∧
      SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment heap ids function
        argumentsSize callSize outcome after ∧
      calleeSize < size ∧ argumentsSize < size ∧ callSize ≤ size := by
  have known : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap callee (.closure function) heap := by
    have formTrace : Dynamic.ExpressionFormEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
        source environment heap read.node.form [] [] (.closure function) heap :=
      read.form ▸ Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup
        stored.2.choose_spec.2.1 rfl rfl
    exact .intro (lookupExpression?_sound read.metadata.found)
      (by rw [read.metadata.requirements, read.metadata.coercions]; exact formTrace)
      (by rw [read.metadata.coercions]; exact .nil)
  have align : ∀ {childOutcome childHeap},
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence source
        environment heap callee childOutcome childHeap →
      childOutcome = .value (.closure function) ∧ childHeap = heap := by
    intro childOutcome childHeap child
    exact CompatibleExpressionReads.source_outcome_unique unique
      (lookupExpression?_sound read.metadata.found) read.form read.metadata.coercions
      lookup stored.2.choose_spec.2.1 rfl child (.value known)
  obtain ⟨_parameter, _result, types, _calleeTyped, argumentsTyped, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  have count : types.length = metadata.argumentCount := by
    cases application with
    | intro count _ _ _ => exact count.symm
  have independent := CallableIndirectCallSourceBounds.indirect_inv_sized
    compiler.found compiler.originalForm parent.coercions unique trace
  cases independent with
  | calleeFault child smaller =>
    obtain ⟨same, _⟩ := align (.fault child.sound)
    cases same
  | notCallable child invalid smaller =>
    obtain ⟨same, _⟩ := align (.value child.sound)
    cases same
    exact False.elim (invalid trivial)
  | argumentsFault first callable children firstSmall childrenSmall =>
    obtain ⟨same, sameHeap⟩ := align (.value first.sound)
    cases same; cases sameHeap
    exact ⟨_, _, 0, first, .argumentFault children, firstSmall, childrenSmall, Nat.zero_le _⟩
  | sourceArity first children mismatch firstSmall childrenSmall =>
    exact False.elim (mismatch parent.arity.symm)
  | argumentCoercionFault first children sameArity pack failed firstSmall childrenSmall coercionSmall =>
    rw [compiler.argumentCoercions] at failed
    cases failed
  | applied layout first children packed converted unpacked sameArity appliedArity called firstSmall childrenSmall coercionSmall callSmall =>
    obtain ⟨same, sameHeap⟩ := align (.value first.sound)
    cases same; cases sameHeap
    rw [compiler.argumentCoercions] at converted
    cases converted
    have sameArguments := Dynamic.ValuesPack.injective_of_length_eq packed unpacked
      ((arguments_count_of_source_admission wellFormed runtime covers locals heapTyped
        argumentsTyped count children).trans appliedArity.symm)
    cases sameArguments
    exact ⟨_, _, _, first, SourceSuffix.of_call children (.value called),
      firstSmall, childrenSmall, Nat.le_of_lt callSmall⟩
  | applicationFault first children packed converted unpacked sameArity appliedArity called firstSmall childrenSmall coercionSmall callSmall =>
    obtain ⟨same, sameHeap⟩ := align (.value first.sound)
    cases same; cases sameHeap
    rw [compiler.argumentCoercions] at converted
    cases converted
    have sameArguments := Dynamic.ValuesPack.injective_of_length_eq packed unpacked
      ((arguments_count_of_source_admission wellFormed runtime covers locals heapTyped
        argumentsTyped count children).trans appliedArity.symm)
    cases sameArguments
    exact ⟨_, _, _, first, SourceSuffix.of_call children (.fault called),
      firstSmall, childrenSmall, Nat.le_of_lt callSmall⟩
end Source

/-- A static call head retains its actual lowering, caller sidecar and local
read certificates. It stores no callee, argument or body execution law. -/
structure Receipt (context : SourceSemantics.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  policy : SourceCoreFunctions.Policy
  body : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  compilation : SourceCoreFunctions.Context
  callee : ExpressionId
  ids : List ExpressionId
  metadata : IndirectCallResolution
  reasonAt : ExpressionId → Word
  compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered
  prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable
  parent : SourceParent compiler
  readFuel : Nat
  readReason : Word
  readCode : Expr
  read : CompatibleExpressionReads.Certificate readFuel (.initial compiled.compatible.checked)
    source scope callee readReason readCode
  sameCode : compiler.calleeCode.expression = readCode
  sameType : compiler.calleeCode.type = read.type
  binding : CompatibleExpressionReads.StaticBinding read context
  sidecar : SourceCoreStageContracts.Sidecar
  caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar
  sidecarSource : sidecar.source = source

def Head (context : SourceSemantics.Context) (source : TypedSource) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (Receipt (compiled := compiled) context source scope id lowered)

/-- This positive input witness is indexed by the actual current heap/store.
The selected external Code shares binder and result indices with the retained
member. Its descriptor word may align without identifying hidden Codes. -/
structure LiveAt {context : SourceSemantics.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Receipt (compiled := compiled) context source scope id lowered)
    (certificate : GenericExpressionMeaning.Certificate)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (environment : Dynamic.Environment) where
  function : Dynamic.Closure
  captureScope : SourceCoreLocalCell.Scope
  capturedActual : Environment
  captured : Captures compiled.indexed mapping world captureScope function.captured capturedActual
  code : Code compiled.indexed function captureScope captured.administrative
  history : History code
  selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) head.compiler head.prepared code
  location : Dynamic.Location
  stored : CallableIndexedOwnedContextualInitializedClosureReceipts.StoredAt headers keys registry faults
    mapping world heap store location function
    (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
    code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore
  lookup : Dynamic.Environment.LooksUp environment head.read.binder location

section Meaning
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- Availability of a retained live member is a state invariant, independent
of execution meaning. Every instance must supply its own real cell reads.
Administrative map/frame extension alone does not establish this invariant. -/
def LiveFor : Prop :=
  ∀ {scope id lowered}, (head : Receipt (compiled := compiled) context source scope id lowered) →
  ∀ {mapping world administrative environment canonical heap store},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store →
    Dynamic.EnvironmentAgrees heap context.locals environment →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
    Admission bridge context initial →
    Nonempty (LiveAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      head certificate mapping world heap store environment)

include extension unique wellFormed runtime covers in
/-- Original full Source inversion constructs the suffix internally. The
single common producer then returns exactly the admitted head spine at the
same caller witness, preserving argument faults and strict child grades. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (live : LiveFor (registry := registry) (faults := faults) (context := context)
      (source := source) (certificate := certificate) bridge profile)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults child)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source
      (Head (compiled := compiled) context source) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    heap store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨head⟩ := certified
  have sameNode : node = head.compiler.original := Option.some.inj (found.symm.trans head.compiler.found)
  subst node
  obtain ⟨current⟩ := live head environments heaps locals initial admitted
  obtain ⟨_calleeSize, argumentsSize, callSize, _originalCallee, suffix,
      _calleeSmaller, argumentsSmaller, callWithin⟩ := suffix_of_source
    (compiler := head.compiler) (parent := head.parent) (read := head.read)
    (stored := current.stored) (lookup := current.lookup) (unique := unique)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (locals := locals) (heapTyped := admitted.heap) (parentTyped := sourceTyped) trace
  obtain ⟨_constructedSourceSize, value, finalStore, finalMap, finalWorld, _constructedSource,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedContextualStoredMemberCallBounds.preserves_at_stored
      (bridge := bridge) (profile := profile) (compiler := head.compiler) (prepared := head.prepared)
      (captured := current.captured) (code := current.code) (history := current.history)
      (selected := current.selected) (stored := current.stored) (read := head.read)
      (sameCode := head.sameCode) (sameType := head.sameType) (extension := extension)
      (binding := head.binding) (unique := unique) (parentTyped := sourceTyped)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (lookup := current.lookup) (initial := initial) (admitted := admitted)
      (parent := head.parent) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      (typed := typed) (caller := head.caller) (sidecarSource := head.sidecarSource)
      budget children below suffix (Nat.le_trans (Nat.le_of_lt argumentsSmaller) within)
      (Nat.le_trans callWithin within)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩

include extension unique wellFormed runtime covers in
/-- Native reflection calls the same common producer once. Its independently
measured Source grade and exact reached admission are the head result. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (live : LiveFor (registry := registry) (faults := faults) (context := context)
      (source := source) (certificate := certificate) bridge profile)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults child)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source
      (Head (compiled := compiled) context source) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    heap store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨head⟩ := certified
  have sameNode : node = head.compiler.original := Option.some.inj (found.symm.trans head.compiler.found)
  subst node
  obtain ⟨current⟩ := live head environments heaps locals initial admitted
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
      represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedContextualStoredMemberCallBounds.reflects_at_stored
      (bridge := bridge) (profile := profile) (compiler := head.compiler) (prepared := head.prepared)
      (captured := current.captured) (code := current.code) (history := current.history)
      (selected := current.selected) (stored := current.stored) (read := head.read)
      (sameCode := head.sameCode) (sameType := head.sameType) (extension := extension)
      (binding := head.binding) (unique := unique) (parentTyped := sourceTyped)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (lookup := current.lookup) (initial := initial) (admitted := admitted)
      (parent := head.parent) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      (typed := typed) (caller := head.caller) (sidecarSource := head.sidecarSource)
      budget children below completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
end Meaning
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredExpressionHeads
