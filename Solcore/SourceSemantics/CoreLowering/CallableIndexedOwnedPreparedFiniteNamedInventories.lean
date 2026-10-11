import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedNamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence

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
