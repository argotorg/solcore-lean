import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfiles
import Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder

/-! Successful selection fixes the complete global signature and plan record.
The finite header inventory still needs coverage of those real slots. Exact
source instantiation equality additionally uses the retained domain order;
native types and specialization keys do not determine that ordered record.
These receipts contain only source metadata and compiler actions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallSelectionCertificates
open Core Frontend SourceInference CallableAncestryPairedLookup RecursiveNamedCatalog

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {definitions : DataEnvironment} {program : Program}
  {headers : Inventory prepared values definitions program} {compilation : SourceCoreFunctions.Context}

/-- Coverage refers to each actual ordered global slot and the entire selected
specialization. It does not reconstruct a source header from a native type. -/
structure Coverage (headers : Inventory prepared values definitions program)
    (compilation : SourceCoreFunctions.Context) : Prop where
  plan : compilation.plan = base.plan
  slots : ∀ index signature specialized,
    compilation.globals[index]? = some signature →
    SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized →
    ∃ header, header ∈ headers ∧ header.slot = index ∧
      header.named.signature = signature ∧ header.named.specialized = specialized
  ordered : ∀ header, header ∈ headers →
    header.instantiation.parameterSubstitution.map Prod.fst =
      (header.named.specialized.parameterSubstitution.map Prod.fst).reverse

/-- The admitted occurrence uses the same domain order actually retained by
source inference. All remaining fields come from the accepted matcher. -/
def Ordered (plan : SourceCompilationPlan.Plan) (instantiation : DeclarationInstantiation) : Prop :=
  ∀ key specialized, SourceCompilationPlan.exactInstantiationKey plan instantiation = .ok key →
    SourceCompilationPlan.exactSpecialization plan key = .ok specialized →
    instantiation.parameterSubstitution.map Prod.fst =
      (specialized.parameterSubstitution.map Prod.fst).reverse

theorem selected {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation} {index : Nat}
    {signature : SourceCoreCalls.Signature}
    (coverage : Coverage headers compilation) (ordered : Ordered compilation.plan instantiation)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false =
      .ok (index, signature)) :
    ∃ header, header ∈ headers ∧ header.slot = index ∧ header.named.signature = signature ∧
      instantiation = header.instantiation ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok header.named.specialized := by
  obtain ⟨specialized, exactRecord, matched, _, _⟩ :=
    CallableNamedMetadata.metadata_of_selected_signature accepted
  have target := NamedCalls.selected_signature_target accepted
  obtain ⟨header, member, slot, signatureEq, specializationEq⟩ :=
    coverage.slots index signature specialized target.2 exactRecord
  have headerTarget : SourceCompilationPlan.exactInstantiationKey compilation.plan header.instantiation =
      .ok signature.key := by rw [coverage.plan, ← signatureEq]; exact header.target
  have headerMatch := CallableNamedMetadata.matches_of_exact headerTarget exactRecord
  have occurrenceEq := matched.retained_canonical (ordered _ _ target.1 exactRecord)
  have headerEq := headerMatch.retained_canonical (by simpa [← specializationEq] using coverage.ordered header member)
  exact ⟨header, member, slot, signatureEq, occurrenceEq.trans headerEq.symm,
    specializationEq.symm ▸ exactRecord⟩

/-- Empty actual domains are one concrete way to close the order condition.
No permutation-sensitive equality is inferred merely from the selected key. -/
theorem ordered_monomorphic {plan : SourceCompilationPlan.Plan} {instantiation : DeclarationInstantiation}
    (empty : instantiation.parameterSubstitution = [])
    (domains : ∀ key specialized, SourceCompilationPlan.exactInstantiationKey plan instantiation = .ok key →
      SourceCompilationPlan.exactSpecialization plan key = .ok specialized → specialized.parameterSubstitution = []) :
    Ordered plan instantiation := by
  intro key specialized target exactRecord
  simp [empty, domains key specialized target exactRecord]

/-- Actual inference and specialization supply the retained domain order. -/
theorem ordered_inferred {plan : SourceCompilationPlan.Plan} {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : TypeSystem.ParameterSubstitution}
    (unique : signature.scheme.parameters.Nodup) (next : Nat)
    (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (records : ∀ key specialized,
      SourceCompilationPlan.exactInstantiationKey plan
        (CallableNamedCanonicalOrder.inferredInstantiation signature next final caller) = .ok key →
      SourceCompilationPlan.exactSpecialization plan key = .ok specialized →
      SourceSpecialization.specializeFunction signature function supplied = .ok specialized) :
    Ordered plan (CallableNamedCanonicalOrder.inferredInstantiation signature next final caller) := by
  intro key specialized target exactRecord
  rw [CallableNamedCanonicalOrder.inferred_parameterDomain signature next final caller unique,
    SourceSpecialization.specializeFunction_parameterDomain (records key specialized target exactRecord)]

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallSelectionCertificates
