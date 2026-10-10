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

noncomputable def issue {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (input : Input compiled) :
    Issued input := Classical.choice (exists_issued input wellFormed)

noncomputable def headers {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (inputs : List (Input compiled)) : List (Header compiled) :=
  inputs.map (fun input => (issue wellFormed input).header)

theorem globals {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (inputs : List (Input compiled)) :
    ∀ header, header ∈ headers wellFormed inputs →
      header.globals = compiled.indexed.base.globals.length := by
  intro header member
  obtain ⟨input, _member, same⟩ := List.mem_map.mp member
  subst header
  exact (issue wellFormed input).aligned.globals

theorem source_receipts {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (inputs : List (Input compiled)) :
    CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts.SourceReceiptCover
      (headers := headers wellFormed inputs) := by
  refine ⟨?_⟩
  intro header member
  obtain ⟨input, _member, same⟩ := List.mem_map.mp member
  subst header
  exact ⟨input.prepared.available, _, (issue wellFormed input).sourceAt⟩

theorem ordered {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (inputs : List (Input compiled)) :
    ∀ header, header ∈ headers wellFormed inputs →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse := by
  intro header member
  obtain ⟨input, _member, same⟩ := List.mem_map.mp member
  subst header
  have aligned := (issue wellFormed input).aligned
  have named : (issue wellFormed input).header.named = input.prepared.named := aligned.named
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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {inputs : List (Input compiled)} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {admitted : ExpressionId → Prop}
    (reached : ReachedInputs inputs compilation source admitted) :
    RecursiveNamedCallSelectionCertificates.ReachedCoverage
      (headers wellFormed inputs) compilation source admitted := by
  refine ⟨reached.plan, ?_, ordered wellFormed inputs⟩
  intro policy id node callee arguments instantiation index signature specialized allowed found form selected record
  obtain ⟨input, member, slot, signatureEq, specializedEq⟩ :=
    reached.slots policy id node callee arguments instantiation index signature specialized
      allowed found form selected record
  let issued := issue wellFormed input
  exact ⟨issued.header, List.mem_map.mpr ⟨input, member, rfl⟩,
    issued.aligned.slot.trans slot,
    (congrArg (·.signature) issued.aligned.named).trans signatureEq,
    (congrArg (·.specialized) issued.aligned.named).trans (input.prepared.same.trans specializedEq)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
