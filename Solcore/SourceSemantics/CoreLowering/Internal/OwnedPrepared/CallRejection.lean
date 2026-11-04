import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LexicalBodyFaults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectApplication
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts

/-!
# Prepared callables: call rejection

Rejection at the first and second call gates, its diagnostics and posts, and finite named inventories.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
/-! Finite named inventories are built from actual prepared rows. Each Header
uses the selected diagnostic issuer and keeps its full resolved dictionary and
ordered Source record. The remaining selection coverage premise mentions only
prepared compiler rows; it never supplies Headers or execution outcomes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
open Core Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning

abbrev Header (compiled : SourceCoreUnifiedCompilation.Compiled) :=
  CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)

/-- Static compiler receipts for one admitted ordinary named body. The slot
is the real singleton lookup, independently of parameter representation. -/
structure Input (compiled : SourceCoreUnifiedCompilation.Compiled) where
  row : SourceSpecialization.SpecializedFunction
  prepared : Prepared compiled row
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution
  ordinaryReturn : row.function.returnComptime = false
  ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
    (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key
  slot : CallableNamedMetadata.Slot compiled.indexed.base.globals prepared.index prepared.named.signature

/-- An accepted ordinary selection supplies both the exact target and the
singleton physical slot. Neither fact is guessed from the native type. -/
def Input.of_selected {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode}
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node
      (CallableNamedCanonicalOrder.retainedInstantiation row) false =
      .ok (prepared.index, prepared.named.signature)) : Input compiled :=
  { row := row
    prepared := prepared
    range := range
    ordinaryReturn := ordinaryReturn
    ordinaryParameters := ordinaryParameters
    target := by simpa only [plan] using (NamedCalls.selected_signature_target selected).1
    slot := by simpa only [globals] using CallableNamedMetadata.slot_of_selected_signature selected }

/-- The Header, its issuer and its Source provenance are produced together.
No body execution law, heap or runtime ownership is needed here. -/
structure Issued {compiled : SourceCoreUnifiedCompilation.Compiled} (input : Input compiled) where
  selected : CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.SelectedReceipt
    compiled input.prepared.named input.prepared.index
  header : Header compiled
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt
    (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared selected)
    (CallableNamedCanonicalOrder.retainedInstantiation input.row) header
  function : header.function = input.prepared.view
  reason : header.reasonAt = CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies.reasonAt selected
  sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header input.prepared.available
    (CallableNamedReversal.global (CallableNamedMetadata.global header.named.specialized input.prepared.available))

theorem exists_issued {compiled : SourceCoreUnifiedCompilation.Compiled}
    (input : Input compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (Issued input) := by
  obtain ⟨selected, header, aligned, function, reason⟩ :=
    CallableIndexedOwnedSelectedNamedHeaderReceipts.retained_at_prepared input.prepared
      wellFormed input.range input.ordinaryReturn input.ordinaryParameters input.target
  have named : header.named = input.prepared.named := aligned.named
  have slot : header.slot = input.prepared.index := aligned.slot
  have specialized : header.named.specialized = input.row :=
    (congrArg (·.specialized) named).trans input.prepared.same
  have metadata : header.instantiation =
      CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation header.named.specialized) := by
    rw [aligned.metadata, specialized]
    rfl
  have target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation header.named.specialized) = .ok header.named.signature.key := by
    rw [← CallableNamedReversal.target_reverse, ← metadata]
    exact header.target
  have resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      compiled.indexed.base.sourceProgram header.named.signature.key header.named.specialized.assumptions =
      .ok input.prepared.available := by
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1, named,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key input.prepared, input.prepared.same]
    exact input.prepared.resolved
  have row : CallableIndexedNamedValues.Row compiled.indexed header.slot header.named.signature
      header.named.specialized input.prepared.available :=
    ⟨by simpa only [slot, named] using input.slot,
      CallableIndexedActualNamedSourceReceipts.header_record compiled header, target, resolved⟩
  have dictionary : header.function.evidence =
      (CallableNamedMetadata.global header.named.specialized input.prepared.available).evidence := by
    rw [function]
    rfl
  exact ⟨⟨selected, header, aligned, function, reason,
    CallableIndexedOwnedFunctionValues.NamedSourceAt.of_retained_header row metadata dictionary⟩⟩

/-- The genuine issuer produces a witness inside Prop. A later consumer
retains that exact packet instead of selecting a Type-valued witness again. -/
theorem issue {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (input : Input compiled) : Nonempty (Issued input) :=
  exists_issued input wellFormed

/-- Each physical input position retains its actual issued packet. Repeated
inputs remain repeated positions, and Header construction follows this order. -/
inductive Inventory {compiled : SourceCoreUnifiedCompilation.Compiled} :
    List (Input compiled) → Type where
  | nil : Inventory []
  | cons {input : Input compiled} {inputs : List (Input compiled)}
      (packet : Issued input) (rest : Inventory inputs) : Inventory (input :: inputs)

/-- Membership identifies a literal packet in this exact retained inventory. -/
inductive Inventory.HasRow {compiled : SourceCoreUnifiedCompilation.Compiled}
    {input : Input compiled} (packet : Issued input) :
    {inputs : List (Input compiled)} → Inventory inputs → Prop where
  | here {inputs : List (Input compiled)} (rest : Inventory inputs) :
      HasRow packet (.cons packet rest)
  | tail {first : Input compiled} {inputs : List (Input compiled)}
      (head : Issued first) {rest : Inventory inputs} (member : HasRow packet rest) :
      HasRow packet (.cons head rest)

/-- This finite producer invokes the existing issuer once for each retained
position. Elimination of its witnesses stays inside the Nonempty conclusion. -/
theorem inventory {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (inputs : List (Input compiled)) : Nonempty (Inventory inputs) := by
  induction inputs with
  | nil => exact ⟨.nil⟩
  | cons input inputs tail =>
      obtain ⟨packet⟩ := issue wellFormed input
      obtain ⟨rest⟩ := tail
      exact ⟨.cons packet rest⟩

def headers {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} : Inventory inputs → List (Header compiled)
  | .nil => []
  | .cons packet rest => packet.header :: headers rest

theorem Inventory.input_member {compiled : SourceCoreUnifiedCompilation.Compiled}
    {input : Input compiled} {packet : Issued input} {inputs : List (Input compiled)}
    {rows : Inventory inputs} (member : Inventory.HasRow packet rows) : input ∈ inputs := by
  induction member with
  | here rest => exact List.mem_cons_self
  | tail head member previous => exact List.mem_cons_of_mem _ previous

theorem Inventory.header_member {compiled : SourceCoreUnifiedCompilation.Compiled}
    {input : Input compiled} {packet : Issued input} {inputs : List (Input compiled)}
    {rows : Inventory inputs} (member : Inventory.HasRow packet rows) :
    packet.header ∈ headers rows := by
  induction member with
  | here rest => exact List.mem_cons.mpr (Or.inl rfl)
  | tail head member previous => exact List.mem_cons.mpr (Or.inr previous)

theorem Inventory.row_at {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs) :
    ∀ input, input ∈ inputs → ∃ packet : Issued input, Inventory.HasRow packet rows := by
  induction rows with
  | nil => intro input member; cases member
  | cons packet rest previous =>
      intro input member
      rcases List.mem_cons.mp member with same | member
      · subst input
        exact ⟨packet, .here rest⟩
      · obtain ⟨actual, retained⟩ := previous input member
        exact ⟨actual, .tail packet retained⟩

theorem Inventory.mem_headers {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs) :
    ∀ header, header ∈ headers rows →
      ∃ input, ∃ packet : Issued input, Inventory.HasRow packet rows ∧ packet.header = header := by
  induction rows with
  | nil => intro header member; cases member
  | cons packet rest previous =>
      intro header member
      rcases List.mem_cons.mp member with same | member
      · exact ⟨_, packet, .here rest, same.symm⟩
      · obtain ⟨input, actual, retained, same⟩ := previous header member
        exact ⟨input, actual, .tail packet retained, same⟩

theorem globals {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs) :
    ∀ header, header ∈ headers rows →
      header.globals = compiled.indexed.base.globals.length := by
  intro header member
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact packet.aligned.globals

theorem source_receipts {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs) :
    CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts.SourceReceiptCover
      (headers := headers rows) := by
  refine ⟨?_⟩
  intro header member
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact ⟨input.prepared.available, _, packet.sourceAt⟩

theorem ordered {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs) :
    ∀ header, header ∈ headers rows →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse := by
  intro header member
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  have aligned := packet.aligned
  have named : packet.header.named = input.prepared.named := aligned.named
  rw [aligned.metadata, named, input.prepared.same]
  simp only [CallableNamedCanonicalOrder.retainedInstantiation, List.map_reverse]

/-- Reached coverage before Header construction. It refers to the exact
compiler context and source occurrence, and retains each complete prepared row.
Producing these inputs from all public compiler branches remains separate. -/
structure ReachedInputs {compiled : SourceCoreUnifiedCompilation.Compiled}
    (inputs : List (Input compiled)) (compilation : SourceCoreFunctions.Context)
    (source : TypedSource) (admitted : ExpressionId → Prop) : Prop where
  plan : compilation.plan = compiled.indexed.base.plan
  slots : ∀ policy id node callee arguments instantiation index signature specialized,
    admitted id → source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) →
    SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature) →
    SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized →
    ∃ input, input ∈ inputs ∧ input.prepared.index = index ∧
      input.prepared.named.signature = signature ∧ input.row = specialized

theorem reached_coverage {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {admitted : ExpressionId → Prop}
    (reached : ReachedInputs inputs compilation source admitted) :
    RecursiveNamedCallSelectionCertificates.ReachedCoverage
      (headers rows) compilation source admitted := by
  refine ⟨reached.plan, ?_, ordered rows⟩
  intro policy id node callee arguments instantiation index signature specialized allowed found form selected record
  obtain ⟨input, member, slot, signatureEq, specializedEq⟩ :=
    reached.slots policy id node callee arguments instantiation index signature specialized
      allowed found form selected record
  obtain ⟨issued, retained⟩ := rows.row_at input member
  exact ⟨issued.header, Inventory.header_member retained,
    issued.aligned.slot.trans slot,
    (congrArg (·.signature) issued.aligned.named).trans signatureEq,
    (congrArg (·.specialized) issued.aligned.named).trans (input.prepared.same.trans specializedEq)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSecondCallGateRejection
/-! After-arguments rejection ports. The existing recursive staged
grammar already has physical closure, named and builtin arity failures. These
are its semantic failure constructors, and retain the actual argument heap.
The first-stage guard failure keeps its separate stage failure constructor.

Original selected metadata identifies each physical count and the exact second
gate word. No count is inferred from a packed type. Native completion keeps an
earlier argument failure separate from a successful argument computation and
pure arity rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSecondCallGateRejection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)

section Selected
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {row : SourceCoreStageCodebook.Decision}

/-- The retained generated request fixes the actual physical argument count. -/
theorem rejected_row (selected : Selected sidecar site callee ids metadata node row)
    (different : row.entry.parameterCount ≠ ids.length) :
    row.afterArguments = .error (.argumentArityMismatch row.entry.parameterCount ids.length) := by
  have mismatch : row.entry.parameterCount ≠ row.argumentCount := by
    rw [selected.argument_count]
    exact different
  simpa only [selected.argument_count] using row.afterArguments_mismatch mismatch

/-- The word retains the same caller, call, descriptor, phase and runtime error. -/
theorem rejected_gate (selected : Selected sidecar site callee ids metadata node row)
    {tag : Word} (found : site.rowAt? tag = some row)
    (different : row.entry.parameterCount ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown tag =
      some (site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length)) := by
  rw [site.decision_known .beforeApplication unknown tag row found]
  exact SourceCoreCallableContracts.reason_rejected row site.reasonAt .beforeApplication _
    (rejected_row selected different)

theorem closure_gate {function : Dynamic.Closure} {native : Value}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.closure function) native)
    (selected : Selected sidecar site callee ids metadata node dispatch.row)
    (different : function.parameters.length ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown dispatch.contract =
      some (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
        (.argumentArityMismatch function.parameters.length ids.length)) :=
  CallableIndexedOwnedStoredClosureArityBoundary.rejected_gate dispatch selected different unknown

theorem named_gate {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {function : Dynamic.GlobalFunction} {native : Value}
    (sourceAt : NamedSourceAt header rawD function)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : Selected sidecar site callee ids metadata node dispatch.row)
    (different : header.function.parameters.length ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown dispatch.contract =
      some (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
        (.argumentArityMismatch header.function.parameters.length ids.length)) := by
  have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
    sourceAt caller dispatch selected
  have mismatch : dispatch.row.entry.parameterCount ≠ ids.length := by
    rw [physical]
    exact different
  simpa only [physical] using rejected_gate selected dispatch.found mismatch unknown

theorem builtin_gate {function : Dynamic.BuiltinFunction} {native : Value}
    (builtin : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids metadata node function native row)
    (different : function.id.parameterTypes.length ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown row.entry.id =
      some (site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch function.id.parameterTypes.length ids.length)) := by
  have physical := builtin.parameter_count
  have mismatch : row.entry.parameterCount ≠ ids.length := by
    rw [physical]
    exact different
  simpa only [physical] using rejected_gate builtin.selected builtin.selected.found mismatch unknown
end Selected

section Source
variable {program : Program} {registry : Staging.Recursive.Registry}
  {scope : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {calleeSize argumentsSize : Nat} {values : List Dynamic.Value}

/-- The actual ordered staged trace preserves its list length by constructor
inversion, independently of packed Source or native product types. -/
theorem values_count {size : Nat} {first last : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expressions program registry size scope context environment
      first ids (.values values) last) : values.length = ids.length := by
  induction ids generalizing size first last values with
  | nil => cases trace with | nil => rfl
  | cons id ids ih =>
    cases trace with
    | cons head tail =>
      have count := ih tail
      simpa only [List.length_cons] using congrArg Nat.succ count

variable (occurrence : Staging.Recursive.Occurrence scope call (.call callee ids (.indirect metadata)))
  (uncoerced : metadata.argumentCoercions = [])
  (sourceArity : ids.length = metadata.argumentCount)
  (arguments : Staging.Recursive.Size.Expressions program registry argumentsSize scope context environment
    middle ids (.values values) after)

include occurrence uncoerced sourceArity arguments in
/-- Physical closure rejection happens at the existing application rule, after
the actual successful argument trace, and invokes no closure body. -/
theorem closure_source {function : Dynamic.Closure}
    (child : Staging.Recursive.Size.Expression program registry calleeSize scope context environment
      before callee (.value (.closure function)) middle)
    (accepted : Staging.CallBoundary.GuardAccepts scope.guards call ids (.closure function))
    (different : function.parameters.length ≠ ids.length) :
    Staging.Recursive.Size.Expression program registry
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []])
      scope context environment before call
      (.fault (.semantic (.argumentArityMismatch function.parameters.length ids.length))) after := by
  have count := values_count arguments
  have mismatch : function.parameters.length ≠ values.length := by
    rw [count]
    exact different
  have invocation : Staging.Recursive.Size.Applies program registry
      (Staging.Recursive.Size.stepSize []) scope context after (.closure function) values
      (.fault (.semantic (.argumentArityMismatch function.parameters.length ids.length))) after := by
    simpa only [count] using (Staging.Recursive.Size.Applies.closureArity
      (program := program) (registry := registry) (scope := scope) (context := context) (heap := after) mismatch)
  exact .applied occurrence uncoerced child accepted arguments sourceArity invocation

include occurrence uncoerced sourceArity arguments in
/-- Genuine NamedSourceAt retains the same original BodyInstance and ordered
parameters. The staged global arity constructor uses that exact instantiation. -/
theorem named_source {compiled : SourceCoreUnifiedCompilation.Compiled}
    {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {function : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD function)
    (child : Staging.Recursive.Size.Expression program registry calleeSize scope context environment
      before callee (.value (.global function)) middle)
    (accepted : Staging.CallBoundary.GuardAccepts scope.guards call ids (.global function))
    (different : header.function.parameters.length ≠ ids.length) :
    Staging.Recursive.Size.Expression program registry
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []])
      scope context environment before call
      (.fault (.semantic (.argumentArityMismatch header.function.parameters.length ids.length))) after := by
  have count := values_count arguments
  have mismatch : header.sourceBody.source.inputs.length ≠ values.length := by
    rw [← sourceAt.frame.parameters, count]
    exact different
  have invocation : Staging.Recursive.Size.Applies program registry
      (Staging.Recursive.Size.stepSize []) scope context after (.global function) values
      (.fault (.semantic (.argumentArityMismatch header.function.parameters.length ids.length))) after := by
    simpa only [← sourceAt.frame.parameters, count] using
      (Staging.Recursive.Size.Applies.globalArity (registry := registry) (scope := scope)
        (context := context) (heap := after) sourceAt.frame.instantiated mismatch)
  exact .applied occurrence uncoerced child accepted arguments sourceArity invocation

include occurrence uncoerced sourceArity arguments in
/-- Builtin physical arity uses its original parameter list. It needs no user
stage acceptance premise because the existing grammar bypasses that guard. -/
theorem builtin_source {function : Dynamic.BuiltinFunction}
    (child : Staging.Recursive.Size.Expression program registry calleeSize scope context environment
      before callee (.value (.builtin function)) middle)
    (different : function.id.parameterTypes.length ≠ ids.length) :
    Staging.Recursive.Size.Expression program registry
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []])
      scope context environment before call
      (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length ids.length))) after := by
  have count := values_count arguments
  have mismatch : function.id.parameterTypes.length ≠ values.length := by
    rw [count]
    exact different
  have invocation : Staging.Recursive.Size.Applies program registry
      (Staging.Recursive.Size.stepSize []) scope context after (.builtin function) values
      (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length ids.length))) after := by
    simpa only [count] using (Staging.Recursive.Size.Applies.builtinArity
      (program := program) (registry := registry) (scope := scope) (context := context) (heap := after) mismatch)
  exact .applied occurrence uncoerced child (.builtin function) arguments sourceArity invocation
end Source

section Native
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {sourceValue : Dynamic.Value} {native : Value}
  {actual : Environment} {before middle after : Store}
  {result : Ty} {calleeCode argumentCode : Expr} {argument : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids sourceValue native)
  (selected : Selected sidecar site callee ids metadata node dispatch.row)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids sourceValue)
  (different : dispatch.row.entry.parameterCount ≠ ids.length)
  (unknown : Word)

include selected accepted different in
/-- Both effectful prefixes are the actual traces. The pure second gate keeps
the argument's final store; the real Source first guard derives its gate. -/
theorem user_native_preserves
    (calleeTrace : Evaluates actual before calleeCode (.inRight .word native) middle)
    (argumentsTrace : Evaluates (.unit :: native :: actual) middle
      ((argumentCode.weakenAt 0).weakenAt 0) (.inRight .word argument) after) :
    Evaluates actual before (site.lower unknown result calleeCode argumentCode)
      (.inLeft result (.word (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
        .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))) after := by
  rw [dispatch.shape] at calleeTrace argumentsTrace
  exact site.lower_arity_failure unknown dispatch.row _ dispatch.found
    (dispatch.accepted accepted) (rejected_row selected different) calleeTrace argumentsTrace

include selected accepted different in
/-- The original finite bind inversion retains either an earlier argument
failure or the successful argument trace at the exact arity-rejection store.
No application trace or called-body hypothesis is consumed. -/
theorem user_native_completion {budget size : Nat} {value : Value} {last : Store}
    (calleeTrace : Evaluates actual before calleeCode (.inRight .word native) middle)
    (completed : EvaluationSize size actual before (site.lower unknown result calleeCode argumentCode) value last)
    (within : size ≤ budget) :
    CallableIndexedOwnedStoredClosureArityBoundary.Completion
      (actual := actual) (calleeStore := middle) (native := native)
      (token := site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
        (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))
      budget result argumentCode value last := by
  have stage : CallableContract.decision site.gates .beforeArguments unknown dispatch.contract = none := by
    rw [site.decision_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found]
    exact SourceCoreCallableContracts.reason_accepted dispatch.row site.reasonAt .beforeArguments
      (dispatch.accepted accepted)
  exact CallableIndexedOwnedStoredClosureArityBoundary.completed dispatch.shape calleeTrace stage
    (rejected_gate selected dispatch.found different unknown) completed within

theorem builtin_native_preserves {function : Dynamic.BuiltinFunction} {row : SourceCoreStageCodebook.Decision}
    (builtin : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids metadata node function native row)
    (mismatch : function.id.parameterTypes.length ≠ ids.length)
    (calleeTrace : Evaluates actual before calleeCode (.inRight .word native) middle)
    (argumentsTrace : Evaluates (.unit :: native :: actual) middle
      ((argumentCode.weakenAt 0).weakenAt 0) (.inRight .word argument) after) :
    Evaluates actual before (site.lower unknown result calleeCode argumentCode)
      (.inLeft result (.word (site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length)))) after := by
  have physical : row.entry.parameterCount ≠ ids.length := by
    rw [builtin.parameter_count]
    exact mismatch
  have passed : row.beforeArguments = .ok () := by
    simp only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      builtin.unguarded]
  obtain ⟨raw, shape⟩ := builtin.shape
  rw [shape] at calleeTrace argumentsTrace
  exact site.lower_arity_failure unknown row _ builtin.selected.found passed
    (rejected_row builtin.selected physical) calleeTrace argumentsTrace

theorem builtin_native_completion {function : Dynamic.BuiltinFunction} {row : SourceCoreStageCodebook.Decision}
    (builtin : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids metadata node function native row)
    (mismatch : function.id.parameterTypes.length ≠ ids.length)
    {budget size : Nat} {value : Value} {last : Store}
    (calleeTrace : Evaluates actual before calleeCode (.inRight .word native) middle)
    (completed : EvaluationSize size actual before (site.lower unknown result calleeCode argumentCode) value last)
    (within : size ≤ budget) :
    CallableIndexedOwnedStoredClosureArityBoundary.Completion
      (actual := actual) (calleeStore := middle) (native := native)
      (token := site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length))
      budget result argumentCode value last := by
  have physical : row.entry.parameterCount ≠ ids.length := by
    rw [builtin.parameter_count]
    exact mismatch
  have passed : row.beforeArguments = .ok () := by
    simp only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      builtin.unguarded]
  have stage : CallableContract.decision site.gates .beforeArguments unknown row.entry.id = none := by
    rw [site.decision_known .beforeArguments unknown row.entry.id row builtin.selected.found]
    exact SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeArguments passed
  obtain ⟨raw, shape⟩ := builtin.shape
  exact CallableIndexedOwnedStoredClosureArityBoundary.completed shape calleeTrace stage
    (rejected_gate builtin.selected builtin.selected.found physical unknown) completed within
end Native

section Diagnostic
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}
  (selected : Selected sidecar prepared.site callee ids metadata compiler.original row)

/-- The concrete relation decodes only the actual physical arity category.
It cannot represent a first-stage Failure.stage or an unrelated child fault. -/
def arityFaults (table : SourceCoreFaultSites.Table) : FunctionCalls.FaultRep :=
  fun reason token => ∃ expected actual diagnostic,
    reason = .argumentArityMismatch expected actual ∧
    table.diagnostic? token = some diagnostic ∧
    diagnostic.error = .argumentArityMismatch expected actual

/-- Only the original semantic arity constructor is represented here. The
first guard's stage failure remains a separate Source rule and relation. -/
def stagedArityFaults (table : SourceCoreFaultSites.Table) : RecursiveStageMeaning.FaultRep :=
  fun failure token => match failure with
    | .semantic reason => arityFaults table reason token
    | .stage .. => False

private theorem issued_reason {table : SourceCoreStageCodebook.Table}
    {caller : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {actualReason : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table caller call actualReason = .ok site) :
    site.reasonAt = actualReason := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

include stages selected in
/-- The sealed public compiler supplies the factory. The actual selected row
supplies membership; neither decoder success nor a FaultRep inclusion is given. -/
theorem public_diagnostic (different : row.entry.parameterCount ≠ ids.length) :
    ∃ diagnostic,
      native.diagnostics.rootTable.diagnostic?
        (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
          (.argumentArityMismatch row.entry.parameterCount ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch row.entry.parameterCount ids.length := by
  have member := List.mem_of_find?_eq_some selected.found
  change row ∈ prepared.site.table.casesAt prepared.site.caller prepared.site.call at member
  have contained := (List.mem_filter.mp member).1
  rw [prepared.table] at contained
  obtain ⟨_issuer, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have decoded := CallableFaultDiagnosticPreparation.prepared_after_arguments allocated contained
    (rejected_row selected different)
  rw [issued_reason prepared.prepared]
  exact decoded

include stages selected in
/-- A pure word rejection returns the argument's actual state and complete
heap relation unchanged, with its concrete same-table fault representation.
Transport to a later rebuilt Session table is a separate indexed obligation. -/
theorem public_argument_post
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    {registry : SourceCoreRawMetadata.Registry}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (argumentState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (different : row.entry.parameterCount ≠ ids.length) :
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world sourceResult resultCore (arityFaults native.diagnostics.rootTable)
      (.fault (.argumentArityMismatch row.entry.parameterCount ids.length))
      (.inLeft resultCore (.word (prepared.site.reasonAt row.caller row.call row.entry.id
        .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = argumentState := by
  obtain ⟨diagnostic, decoded, error⟩ := public_diagnostic compiler prepared stages selected different
  exact ⟨.fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩,
    heaps, argumentState, rfl⟩

include stages selected in
/-- The same concrete word also represents the exact staged semantic failure,
at the same argument heap/store and the same dependent caller state. -/
theorem public_staged_argument_post
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    {registry : SourceCoreRawMetadata.Registry}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (argumentState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (different : row.entry.parameterCount ≠ ids.length) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world sourceResult resultCore (stagedArityFaults native.diagnostics.rootTable)
      (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)))
      (.inLeft resultCore (.word (prepared.site.reasonAt row.caller row.call row.entry.id
        .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = argumentState := by
  obtain ⟨diagnostic, decoded, error⟩ := public_diagnostic compiler prepared stages selected different
  exact ⟨.fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩,
    heaps, argumentState, rfl⟩
end Diagnostic

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSecondCallGateRejection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics
/-! An original selected call row keeps its diagnostic through the actual
receiving-registry rebuild and the public callable append. The preappend table
decodes only below the real issuer endpoint; callable rejection tokens lie at
or above the later allocator boundary. Original and substituted call metadata
remain separate. No decoder inclusion or execution law is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics
open Core Frontend SourceInference SourceTypedRuntime GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPreparedSecondCallGateRejection
open CallableIndexedOwnedPublicFaultReceiverTables

/-- Every reason selected from this actual inventory is at or above the
allocator boundary, including its authentic unknown-descriptor fallback. -/
theorem reason_at_lower_bound {contracts : SourceCoreStageCodebook.Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat}
    {program : SourceCoreCallableFaultSites.Program}
    (receipt : CallableFaultDiagnosticPreparation.Receipt contracts base minimum program)
    (caller : SourceSpecialization.SpecializationKey) (call : ExpressionId)
    (descriptor : Word) (phase : SourceCoreCallableFaultSites.Phase) (error : RuntimeError) :
    program.unknown.val ≤ (program.reasonAt caller call descriptor phase error).val := by
  unfold SourceCoreCallableFaultSites.Program.reasonAt
  split
  · rename_i site found
    have member := List.mem_of_find?_eq_some found
    have high := (receipt.inventory.bounds site member).1
    rw [receipt.unknown]
    omega
  · exact Nat.le_refl _

private theorem filtered_find {rows : List (Word × SourceCoreFaultSites.Diagnostic)}
    {unknown token : Word} (high : unknown.val ≤ token.val) :
    (rows.filter (fun item => unknown.val ≤ item.1.val)).find?
        (fun item => decide (item.1 = token)) =
      rows.find? (fun item => decide (item.1 = token)) := by
  rw [List.find?_filter]
  congr 1
  funext item
  by_cases same : item.1 = token
  · simp [same, high]
  · simp [same]

/-- The actual receiving base has no lookup at a high callable token. The
literal filter retains the same first matching callable row. -/
theorem receiver_lookup (compiled : SourceCoreUnifiedCompilation.Compiled)
    {native : SourceCoreGeneralFunctions.CallableContext}
    (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (high : native.diagnostics.unknown.val ≤ token.val)
    (decoded : native.diagnostics.rootTable.diagnostic? token = some diagnostic) :
    completion.result.diagnostics.diagnostic? token = some diagnostic := by
  obtain ⟨issued, present, callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have allocatedReceipt := CallableFaultDiagnosticPreparation.prepare_receipt allocated
  have boundary : issued.nextReason ≤ native.diagnostics.unknown.val := by
    rw [allocatedReceipt.unknown]
    exact Nat.le_max_right _ _
  obtain ⟨root, sources, accepted⟩ :=
    CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨actual, rebuilt, sameReceiver⟩ := receiver
  rw [present] at rebuilt
  have absent : actual.diagnostic? token = none := by
    cases found : actual.diagnostic? token with
    | none => rfl
    | some original =>
        have below := CallableIndexedOwnedReceivingPreparedShapeInterpretations.decoded_token_below
          accepted rebuilt found
        omega
  obtain ⟨extra, _expanded, sameBase, _origins⟩ := issued.tableForRegistry_receipt rebuilt
  have sameEscaped : actual.escapedReason = native.diagnostics.rootTable.escapedReason := by
    rw [sameBase, allocatedReceipt.table]
  have sameReads : actual.reads = native.diagnostics.rootTable.reads := by
    rw [sameBase, allocatedReceipt.table]
  have nonzero : token ≠ Word.zero := by
    intro zero
    simp [zero, SourceCoreFaultSites.Table.diagnostic?] at absent
  have notEscaped : token ≠ actual.escapedReason := by
    intro escaped
    have escapedNonzero : actual.escapedReason ≠ Word.zero := by
      rw [← escaped]
      exact nonzero
    simp [SourceCoreFaultSites.Table.diagnostic?, escaped, escapedNonzero] at absent
  have additionalAbsent : actual.additional.find? (fun item => decide (item.1 = token)) = none := by
    cases found : actual.additional.find? (fun item => decide (item.1 = token)) with
    | none => rfl
    | some pair =>
        simp [SourceCoreFaultSites.Table.diagnostic?, nonzero, notEscaped, found] at absent
  have originalNotEscaped : token ≠ native.diagnostics.rootTable.escapedReason := by
    rwa [sameEscaped] at notEscaped
  rw [sameReceiver, appendCallable, callablePresent]
  simp only [SourceCoreFaultSites.Table.diagnostic?, nonzero, notEscaped,
    originalNotEscaped, if_false, List.find?_append, additionalAbsent,
    Option.none_or, filtered_find high, sameReads] at decoded ⊢
  exact decoded

private theorem issued_reason {table : SourceCoreStageCodebook.Table}
    {caller : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {actualReason : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table caller call actualReason = .ok site) :
    site.reasonAt = actualReason := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

section OriginalRow
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : Prepared compiler native)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode row)

include stages selected in
/-- The original selected metadata, same actual site and sealed allocation
construct the raw arity diagnostic. No equality to the substituted node is used. -/
theorem original_diagnostic (different : row.entry.parameterCount ≠ ids.length) :
    ∃ diagnostic,
      native.diagnostics.rootTable.diagnostic?
        (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
          (.argumentArityMismatch row.entry.parameterCount ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch row.entry.parameterCount ids.length := by
  have member := List.mem_of_find?_eq_some selected.found
  change row ∈ prepared.site.table.casesAt prepared.site.caller prepared.site.call at member
  have contained := (List.mem_filter.mp member).1
  rw [prepared.table] at contained
  obtain ⟨_issuer, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have decoded := CallableFaultDiagnosticPreparation.prepared_after_arguments allocated contained
    (rejected_row selected different)
  rw [issued_reason prepared.prepared]
  exact decoded

include stages selected in
/-- The original row's concrete second-gate reason reaches the actual public
receiving table through its genuine rebuild and filtered callable append. -/
theorem receiving_diagnostic
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    (different : row.entry.parameterCount ≠ ids.length) :
    ∃ diagnostic,
      completion.result.diagnostics.diagnostic?
        (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
          (.argumentArityMismatch row.entry.parameterCount ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch row.entry.parameterCount ids.length := by
  obtain ⟨diagnostic, decoded, error⟩ := original_diagnostic compiler prepared stages selected different
  obtain ⟨_issued, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have high := reason_at_lower_bound (CallableFaultDiagnosticPreparation.prepare_receipt allocated)
    row.caller row.call row.entry.id .beforeApplication
    (.argumentArityMismatch row.entry.parameterCount ids.length)
  rw [← issued_reason prepared.prepared] at high
  exact ⟨diagnostic, receiver_lookup compiled stages receiver high decoded, error⟩

end OriginalRow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts
/-! A genuine contextual Source view preserves the original indirect call's
callee and ordered argument identities. The original node and metadata remain
attached to the original selected codebook row; substituted metadata are kept
separately. The static boundary factory uses the same actual Prepared site,
caller and table. These receipts concern static source and artifact provenance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)

/-- The actual node is either the original node or its actual substitution.
This retains the embedded argument types and coercion metadata explicitly. -/
def CallView (before actual : ExpressionNode)
    (originalMetadata metadata : IndirectCallResolution) : Prop :=
  (actual = before ∧ metadata = originalMetadata) ∨
    ∃ active, actual = before.applySubstitution active ∧
      metadata = originalMetadata.applySubstitution active

/-- Type substitution leaves the physical argument count unchanged. -/
theorem CallView.argument_count {before actual : ExpressionNode}
    {originalMetadata metadata : IndirectCallResolution}
    (view : CallView before actual originalMetadata metadata) :
    metadata.argumentCount = originalMetadata.argumentCount := by
  rcases view with ⟨_, same⟩ | ⟨active, _, same⟩
  · rw [same]
  · rw [same]; rfl

/-- Recover the original indirect metadata from an actual substituted form.
The callee and ordered IDs remain literal; embedded types are not equated. -/
theorem substituted_indirect_origin (active : TypeSystem.Substitution)
    (node : ExpressionNode) {callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution}
    (form : (node.applySubstitution active).form = .call callee ids (.indirect metadata)) :
    ∃ originalMetadata, node.form = .call callee ids (.indirect originalMetadata) ∧
      metadata = originalMetadata.applySubstitution active := by
  cases originalForm : node.form <;>
    simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, originalForm] at form <;>
    try cases form
  case call actualCallee actualIds resolution =>
    cases resolution with
    | indirect originalMetadata =>
        simp only [CallResolution.applySubstitution] at form
        obtain ⟨sameCallee, sameIds, sameMetadata⟩ := ExpressionForm.call.inj form
        cases sameCallee
        cases sameIds
        exact ⟨originalMetadata, rfl, (CallResolution.indirect.inj sameMetadata).symm⟩
    | declaration instantiation => cases form
    | builtinFunction function => cases form

/-- One actual contextual Source occurrence recovers its original call node
and retains the exact forward relation between both metadata records. -/
theorem indirect_origin {original actual : TypedSource}
    (view : SourceView original actual) {id : ExpressionId} {node : ExpressionNode}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    (contains : ContainsExpression actual id node)
    (form : node.form = .call callee ids (.indirect metadata)) :
    ∃ before originalMetadata, ContainsExpression original id before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallView before node originalMetadata metadata := by
  rcases view with same | ⟨active, same⟩
  · subst actual
    exact ⟨node, metadata, contains, form, .inl ⟨rfl, rfl⟩⟩
  · subst actual
    obtain ⟨before, retained, sameNode⟩ :=
      CallableIndexedOwnedContextualDiagnosticSources.substituted_contains contains
    subst node
    obtain ⟨originalMetadata, originalForm, sameMetadata⟩ :=
      substituted_indirect_origin active before form
    exact ⟨before, originalMetadata, retained, originalForm,
      .inr ⟨active, rfl, sameMetadata⟩⟩

section Caller
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {sidecar : SourceCoreStageContracts.Sidecar}

include compiler prepared in
/-- The existing finite static factory runs at the actual original call node.
Its selected row is tied to this original metadata and the same native site. -/
theorem boundary_at_original {before : ExpressionNode} {originalMetadata : IndirectCallResolution}
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source prepared.site.call before)
    (form : before.form = .call callee ids (.indirect originalMetadata))
    (unique : NodeOccurrencesUnique sidecar.source)
    {sourceValue : Dynamic.Value} {carrier : Value}
    (actualOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier) :
    BoundaryAt sidecar prepared.site callee ids originalMetadata before sourceValue carrier := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  have atSite := stages.accepted
  rw [← prepared.table] at atSite
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection atSite caller contains form
  have origin : CallableLedger.OriginRep sidecar.plan prepared.site.table sourceValue carrier := by
    have plan := (CallContractCertificates.sidecar_of_accepted caller).1
    rw [plan, prepared.table]
    exact actualOrigin
  cases origin with
  | @closure function raw entry owner occurrence active contract member entryOrigin retained provenance =>
      obtain ⟨dispatch⟩ := CallableLedger.dispatch rows
        (CallableLedger.OriginRep.closure member entryOrigin retained provenance) provenance.binds
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains form unique dispatch.found
      exact .user dispatch selected
  | @named function raw entry key contract member entryOrigin retained target contractPrepared =>
      obtain ⟨dispatch⟩ := CallableLedger.dispatch rows
        (CallableLedger.OriginRep.named member entryOrigin retained target contractPrepared)
        (CallableLedger.Binds.named target contractPrepared)
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains form unique dispatch.found
      exact .user dispatch selected
  | @builtin function raw entry member entryOrigin retained =>
      obtain ⟨ledger⟩ := rows entry member
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains form unique ledger.found
      refine .builtin ⟨selected, ?_, ?_, ?_, ledger.builtin retained⟩
      · rw [ledger.entry_eq]; exact entryOrigin
      · rw [ledger.entry_eq]; exact retained
      · refine ⟨raw, ?_⟩
        rw [ledger.entry_eq]

include compiler prepared in
/-- The actual compiler occurrence and authentic Source view supply the
original static factory. No equality between the whole Sources is required. -/
theorem boundary_at_source_view
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (view : SourceView sidecar.source source)
    (unique : NodeOccurrencesUnique sidecar.source)
    {sourceValue : Dynamic.Value} {carrier : Value}
    (actualOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier) :
    ∃ before originalMetadata, ContainsExpression sidecar.source prepared.site.call before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallView before compiler.original originalMetadata metadata ∧
      BoundaryAt sidecar prepared.site callee ids originalMetadata before sourceValue carrier := by
  have actualContains : ContainsExpression source prepared.site.call compiler.original := by
    rw [prepared.call]
    exact lookupExpression?_sound compiler.found
  obtain ⟨before, originalMetadata, contains, form, callView⟩ :=
    indirect_origin view actualContains compiler.originalForm
  exact ⟨before, originalMetadata, contains, form, callView,
    boundary_at_original compiler prepared caller contains form unique actualOrigin⟩

end Caller
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingFirstCallGateRejection
/-! A rejected first guard keeps its actual failing invocation and original
selected call row. The sealed before-arguments diagnostic reaches the literal
receiving table through its real rebuild and callable append. Its stage tag,
Source view, guard frame and callee endpoint remain attached to that lookup. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingFirstCallGateRejection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)

/-- The view retains the actual failing scope and the forward relation to the
original row. A raw diagnostic alone cannot supply those Source coordinates. -/
inductive StageErrorView : Staging.Recursive.Scope → ExpressionId → Staging.CallGuard.Fault →
    SourceTypedRuntime.RuntimeError → Prop where
  | selected {invocation : Staging.Recursive.Scope} {sidecar : SourceCoreStageContracts.Sidecar}
      {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId} {ids : List ExpressionId}
      {originalNode actualNode : ExpressionNode} {originalMetadata metadata : IndirectCallResolution}
      {sourceValue : Dynamic.Value} {carrier : Value} {reason : Staging.CallGuard.Fault}
      (sourceView : SourceView sidecar.source invocation.source)
      (actualContains : ContainsExpression invocation.source site.call actualNode)
      (actualForm : actualNode.form = .call callee ids (.indirect metadata))
      (callView : CallView originalNode actualNode originalMetadata metadata)
      (guardFrame : invocation.guards = CallableLedger.frame sidecar)
      (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
        site site.call ids sourceValue carrier)
      (selected : Selected sidecar site callee ids originalMetadata originalNode dispatch.row)
      (rejected : Staging.CallBoundary.GuardRejects invocation.guards site.call ids sourceValue reason) :
      StageErrorView invocation site.call reason
        (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node
          dispatch.guard.contract.owner reason)

/-- This first-gate relation keeps the complete stage failure. In particular,
the guard's arity fault still has its stage tag even when its raw error uses the
same count category as the semantic second-gate rejection. -/
def stagedFaults (table : SourceCoreFaultSites.Table) : RecursiveStageMeaning.FaultRep :=
  fun failure token => match failure with
    | .semantic _ => False
    | .stage invocation call reason => ∃ diagnostic,
        table.diagnostic? token = some diagnostic ∧ StageErrorView invocation call reason diagnostic.error

section OriginalRow
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : Prepared compiler native)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {sidecar : SourceCoreStageContracts.Sidecar} {sourceValue : Dynamic.Value} {carrier : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
    prepared.site prepared.site.call ids sourceValue carrier)
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  {reason : Staging.CallGuard.Fault}

private theorem issued_reason {table : SourceCoreStageCodebook.Table}
    {caller : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {actualReason : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table caller call actualReason = .ok site) :
    site.reasonAt = actualReason := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

include stages selected in
/-- The original selected row and authentic rejection supply the sealed
before-arguments diagnostic at this exact prepared site. -/
theorem original_diagnostic
    (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason) :
    ∃ diagnostic, native.diagnostics.rootTable.diagnostic? (dispatch.reason reason) = some diagnostic ∧
      diagnostic.error = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node
        dispatch.guard.contract.owner reason := by
  have member := List.mem_of_find?_eq_some selected.found
  change dispatch.row ∈ prepared.site.table.casesAt prepared.site.caller prepared.site.call at member
  have contained := (List.mem_filter.mp member).1
  rw [prepared.table] at contained
  obtain ⟨_issuer, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have decoded := CallableFaultDiagnosticPreparation.prepared_before_arguments allocated contained
    (dispatch.rejected rejected)
  simpa only [CallStageBoundary.Dispatch.reason, issued_reason prepared.prepared] using decoded

include stages selected in
/-- The same first-gate word is decoded in the actual public receiving table. -/
theorem receiving_diagnostic
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason) :
    ∃ diagnostic, completion.result.diagnostics.diagnostic? (dispatch.reason reason) = some diagnostic ∧
      diagnostic.error = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node
        dispatch.guard.contract.owner reason := by
  obtain ⟨diagnostic, decoded, error⟩ :=
    original_diagnostic compiler prepared stages dispatch selected rejected
  obtain ⟨_issued, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have high := CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.reason_at_lower_bound
    (CallableFaultDiagnosticPreparation.prepare_receipt allocated)
    dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeArguments
    (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason)
  rw [← issued_reason prepared.prepared] at high
  exact ⟨diagnostic,
    CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiver_lookup
      compiled stages receiver high decoded, error⟩

include stages selected in
/-- The actual invocation and its reached callee state remain unchanged while
the original first-gate diagnostic is observed in the receiving table. -/
theorem receiving_staged_post
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {invocation : Staging.Recursive.Scope}
    (sourceEq : invocation.source = source)
    (view : SourceView sidecar.source source)
    (callView : CallView originalNode compiler.original originalMetadata metadata)
    (guardFrame : invocation.guards = CallableLedger.frame sidecar)
    (rejected : Staging.CallBoundary.GuardRejects invocation.guards prepared.site.call ids sourceValue reason)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (calleeState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (related : protocol.Relates initial calleeState)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked
        completion.result.context.registry functions)
      mapping world sourceResult resultCore (stagedFaults completion.result.diagnostics)
      (.fault (.stage invocation prepared.site.call reason))
      (.inLeft resultCore (.word (dispatch.reason reason))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = calleeState ∧ protocol.Relates initial reached := by
  have actualRejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason := by
    rw [← guardFrame]
    exact rejected
  obtain ⟨diagnostic, decoded, error⟩ :=
    receiving_diagnostic compiler prepared stages dispatch selected receiver actualRejected
  have scopeView : SourceView sidecar.source invocation.source := by
    rw [sourceEq]
    exact view
  have actualContains : ContainsExpression invocation.source prepared.site.call compiler.original := by
    rw [sourceEq, prepared.call]
    exact lookupExpression?_sound compiler.found
  have errorView : StageErrorView invocation prepared.site.call reason diagnostic.error := by
    rw [error]
    exact .selected scopeView actualContains compiler.originalForm callView guardFrame dispatch selected rejected
  exact ⟨.fault ⟨diagnostic, decoded, errorView⟩, heaps, calleeState, rfl, related⟩

end OriginalRow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingFirstCallGateRejection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionPosts
/-! The original selected call row represents second-gate rejection against
the actual public receiving table. Original and substituted call metadata stay
distinct. A pure rejection retains the argument computation's exact dependent
caller state, record relation, heap and store. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedSecondCallGateRejection (arityFaults stagedArityFaults)

/-- Each actual boundary retains its original generated request. -/
theorem selected_row {sidecar : SourceCoreStageContracts.Sidecar}
    {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
    {ids : List ExpressionId} {originalMetadata : IndirectCallResolution}
    {originalNode : ExpressionNode} {sourceValue : Dynamic.Value} {carrier : Value}
    (boundary : BoundaryAt sidecar site callee ids originalMetadata originalNode sourceValue carrier) :
    ∃ row, Selected sidecar site callee ids originalMetadata originalNode row := by
  cases boundary with
  | user dispatch selected => exact ⟨dispatch.row, selected⟩
  | builtin receipt => exact ⟨_, receipt.selected⟩

section OriginalRow
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : Prepared compiler native)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode row)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)

include stages selected receiver in
theorem receiving_argument_post
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (argumentState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (related : protocol.Relates initial argumentState)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store)
    (different : row.entry.parameterCount ≠ ids.length) :
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked
        completion.result.context.registry functions)
      mapping world sourceResult resultCore (arityFaults completion.result.diagnostics)
      (.fault (.argumentArityMismatch row.entry.parameterCount ids.length))
      (.inLeft resultCore (.word (prepared.site.reasonAt row.caller row.call row.entry.id
        .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = argumentState ∧ protocol.Relates initial reached := by
  obtain ⟨diagnostic, decoded, error⟩ :=
    CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
      compiler prepared stages selected receiver different
  exact ⟨.fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩,
    heaps, argumentState, rfl, related⟩

include stages selected receiver in
theorem receiving_staged_argument_post
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical : Environment} {sourceResult : TypeSystem.Ty} {resultCore : Ty}
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (argumentState : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (related : protocol.Relates initial argumentState)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store)
    (different : row.entry.parameterCount ≠ ids.length) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked
        completion.result.context.registry functions)
      mapping world sourceResult resultCore (stagedArityFaults completion.result.diagnostics)
      (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)))
      (.inLeft resultCore (.word (prepared.site.reasonAt row.caller row.call row.entry.id
        .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      completion.result.context.registry functions mapping world heap store ∧
    ∃ reached : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
      reached = argumentState ∧ protocol.Relates initial reached := by
  obtain ⟨diagnostic, decoded, error⟩ :=
    CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
      compiler prepared stages selected receiver different
  exact ⟨.fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩,
    heaps, argumentState, rfl, related⟩

end OriginalRow

section ScopedRow
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {sidecar : SourceCoreStageContracts.Sidecar}

include compiler prepared in
/-- The actual Source view constructs the original selected row at the same
prepared site; both metadata records remain in the output. -/
theorem row_at_source_view
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
    (unique : NodeOccurrencesUnique sidecar.source)
    {sourceValue : Dynamic.Value} {carrier : Value}
    (actualOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier) :
    ∃ before originalMetadata row, ContainsExpression sidecar.source prepared.site.call before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.CallView
        before compiler.original originalMetadata metadata ∧
      Selected sidecar prepared.site callee ids originalMetadata before row := by
  obtain ⟨before, originalMetadata, contains, form, callView, boundary⟩ :=
    CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.boundary_at_source_view
      compiler prepared caller view unique actualOrigin
  obtain ⟨row, selected⟩ := selected_row boundary
  exact ⟨before, originalMetadata, row, contains, form, callView, selected⟩

end ScopedRow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionPosts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveCalleeBoundaryReceipts
/-! The receiving positive function model retains enough actual provenance to
construct the original selected call boundary. Compatible raw views preserve
that same callee. User dispatch and builtin rows remain independent of guard
acceptance, physical arity and body execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveCalleeBoundaryReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}

/-- Only original retained Source, Code and descriptor constructors are used.
No legacy closure support or semantic diagnostic law is manufactured. -/
theorem function_origin
    (positive : FunctionOrigins qualification headers keys bodyRegistry faults profile
      mapping world raw sourceValue carrier type) :
    CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  cases positive with
  | closure member =>
    obtain ⟨packet⟩ := member
    cases packet.association with
    | ordinary owner captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
      exact CompatibleAmbientStageOrigins.actual_lambda_origin stages.accepted code.descriptor
        support.source_receipt code.viewOfSource support.unique code.found
        (code.form.trans code.sourceForm) _
    | principal owner captured code history support origin prepared qualified globals leading referenceIndex typed =>
      exact CompatibleAmbientStageOrigins.actual_lambda_origin stages.accepted code.descriptor
        support.source_receipt code.viewOfSource support.body.unique code.found
        (code.form.trans code.sourceForm) _
  | global member =>
    obtain ⟨packet⟩ := member
    cases packet with
    | named origin member sourceAt capture installed number projection descriptor typed =>
      apply RecursiveStageProjection.named_origin stages.accepted descriptor
      rw [sourceAt.retained]
      simpa only [CallableNamedReversal.global, CallableNamedReversal.target_reverse,
        CallableNamedMetadata.global] using sourceAt.row.target
  | builtin related =>
    cases related with
    | prior prior =>
      cases prior with
      | prior original =>
        cases original with
        | builtin builtin =>
          cases builtin with
          | builtin selected number descriptor typed =>
            exact RecursiveStageProjection.builtin_origin stages.accepted descriptor _

/-- Compatible type views are projected forward from the genuine positive
payload. The Source callable shape remains a separate raw typing fact. -/
theorem payload_origin
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world raw sourceValue carrier type) :
    IsFunction sourceValue → CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function positive => intro _; exact function_origin positive
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro callable; cases callable
  | nil | cons | empty | entry | absent | present => trivial

section Caller
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {sidecar : SourceCoreStageContracts.Sidecar}

include compiler prepared in
/-- The original same-caller row factory runs once at the actual positive
callee. Its user or builtin alternative retains the authentic selected row. -/
theorem boundary_at_payload
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (sidecarSource : sidecar.source = source)
    (unique : NodeOccurrencesUnique source)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world raw sourceValue carrier type)
    (shape : IsFunction sourceValue) :
    CallableIndexedOwnedContextualCalleeStageReceipts.BoundaryAt
      sidecar prepared.site callee ids metadata compiler.original sourceValue carrier :=
  CallableIndexedOwnedContextualCalleeStageReceipts.boundary_at_origin compiler prepared caller sidecarSource unique
    (payload_origin represented shape)

end Caller
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveCalleeBoundaryReceipts
end
