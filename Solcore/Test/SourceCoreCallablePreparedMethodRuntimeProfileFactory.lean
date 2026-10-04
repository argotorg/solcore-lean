import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory

/-! Formal consumers retain actual selection, the same dictionary, cache and
returned diagnostic receipt. Existing operator suites supply the runtime checks. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodRuntimeProfileFactory
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CallablePreparedMethodSelection CallableCoercionMethodInstantiation
open CallablePreparedMethodCatalogHookMeaning CallablePreparedMethodRuntimeProfileFactory

abbrev actual_source := @source_at
abbrev actual_parameters := @parameter_pack
abbrev actual_cached_body := @cached_body_native
abbrev actual_extraction := @extract_cached
abbrev good_profile := @profile_of_interpreted

section Formal
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  (source : SourceAt compilation values sourceBody dictionary)
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {administrative : Core.Context}
  (receipt : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative))
  (catalog : SignatureCatalogWellFormed values.checked.signatures)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (interpreted : receipt.extracted.diagnostics registry faults)

include catalog definitions registered interpreted in
theorem actual_profile :
    ∃ profile : ProfileFor compilation values ambient sourceBody dictionary administrative registry faults
      expressionSyntax certificates
      (fun context => CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)
      diagnosticPolicy,
      profile.context = source.context ∧ profile.body.flow = receipt.flow ∧
      HEq profile.body.tree receipt.extracted.tree ∧
      HEq profile.body.initialValid source.valid ∧
      profile.parameters = source.parameters := by
  exact ⟨receipt.profile source catalog definitions registered interpreted, rfl, rfl, HEq.rfl, HEq.rfl, rfl⟩

theorem actual_source_frame :
    (receipt.profile source catalog definitions registered interpreted).sourceFrame = source.frame := rfl

theorem full_unused_ledger :
    (receipt.profile source catalog definitions registered interpreted).context.solvedRequirements =
      named.specialized.function.solvedRequirements := source.valid.ledger

include source in
theorem ordered_parameters :
    sourceBody.source.inputs.map (fun binder => (binder.id, binder.scheme, binder.comptime)) =
      named.inputs.map (fun binding => (binding.1.id, binding.1.scheme, binding.1.comptime)) := by
  rw [source.parameters]
  simp only [List.map_map, Function.comp_def]

/-- A receipt can carry an impossible interpretation while retaining the same Tree. -/
def blocked : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) :=
  { receipt with extracted := {
      tree := receipt.extracted.tree
      diagnostics := fun _ _ => False
      materialize := fun _ _ impossible => impossible.elim } }

theorem blocked_same_tree : HEq (blocked source receipt).extracted.tree receipt.extracted.tree := HEq.rfl

theorem blocked_uninterpreted : ¬ (blocked source receipt).extracted.diagnostics registry faults := fun impossible => impossible

include receipt interpreted in
theorem good_is_not_all :
    (∃ result : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative),
      result.extracted.diagnostics registry faults) ∧
    ¬ (∀ result : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative),
      result.extracted.diagnostics registry faults) := by
  exact ⟨⟨receipt, interpreted⟩, fun every => blocked_uninterpreted source receipt (every _)⟩

end Formal

/-- Packing alone does not identify the source arity. -/
theorem pack_not_arity : SourceCoreCompatibleCatalog.packTypes [] =
    SourceCoreCompatibleCatalog.packTypes [.unit] ∧ ([] : List Core.Ty) ≠ [.unit] := ⟨rfl, by simp⟩

/-- Ordered duplicate evidence is retained; neither set equality nor length
is sufficient to identify the actual selected dictionary. -/
theorem dictionary_order {α : Type} (a b : α) (different : a ≠ b) :
    [a, a, b] ≠ [a, b, a] := by simp [different]

#check_failure CallablePreparedMethodCatalogHookMeaning.ProfileFor.with_evidence
#check_failure CallablePreparedMethodRuntimeProfileFactory.SourceAt.ordinary

end Tests.SourceCoreCallablePreparedMethodRuntimeProfileFactory
