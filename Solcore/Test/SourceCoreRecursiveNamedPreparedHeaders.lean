import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders

/-! Actual compiler receipts assemble the Header without input Header/native
projection callbacks. Independent raw source typing and ordinary admission stay
visible. These consumers do not supply a runtime Entry or semantic profile. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedHeaders
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedPreparedHeaders RecursiveNamedCatalog

section Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {values : SourceCoreCompatibleValues.Context}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (range : ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
  (closed : row.assumptions = []) (ordinaryReturn : row.function.returnComptime = false)
  (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)

include prepared wellFormed range closed ordinaryReturn ordinaryParameters in
theorem actual_canonical
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared (CallableNamedMetadata.instantiation row) header :=
  RecursiveNamedPreparedHeaders.Prepared.canonical_header prepared wellFormed range closed ordinaryReturn ordinaryParameters target

include prepared wellFormed range closed ordinaryReturn ordinaryParameters in
theorem actual_retained
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header :=
  RecursiveNamedPreparedHeaders.Prepared.retained_header prepared wellFormed range closed ordinaryReturn ordinaryParameters target

include prepared wellFormed range in
theorem source_shape_before_native_pack : prepared.named.signature.parameterType =
    SourceCoreCompatibleCatalog.packTypes (prepared.named.inputs.map Prod.snd) :=
  RecursiveNamedPreparedHeaders.Prepared.parameter_pack prepared wellFormed range

variable {instantiation : DeclarationInstantiation}
  {header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
    (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include prepared aligned in
theorem actual_full_cache :
    header.named.specialized = row ∧ header.slot = prepared.index ∧
    header.bindings = prepared.named.inputs ∧
    HEq header.compiled compiled.indexed.secondPass ∧
    header.compiled.closures[header.slot]? = some prepared.code := by
  refine ⟨aligned.named ▸ prepared.same, aligned.slot, aligned.bindings, aligned.secondPass, ?_⟩
  rw [header.cached]
  have emitted := prepared.compilation.emitted
  rw [aligned.named, aligned.code]
  exact congrArg some emitted.symm

include prepared aligned in
theorem exact_policy_and_body :
    header.policy = RecursiveNamedPreparedHeaders.Prepared.policy prepared ∧
    SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body ∧
    (∃ facts, BodyHasType header.function.source header.context header.function.resultType facts) :=
  ⟨aligned.policy, aligned.accepted, aligned.bodyTyped⟩

include prepared aligned in
theorem actual_runtime_context : CompatibleRuntimeContextValidity.Valid
    prepared.named.specialized.function.solvedRequirements header.context prepared.view.evidence := by
  have valid := header.valid
  rw [aligned.solved, aligned.function] at valid
  exact valid

include prepared aligned closed in
theorem actual_closed_dictionary : header.function.evidence = [] := by
  rw [aligned.function]
  exact RecursiveNamedPreparedHeaders.Prepared.evidence_empty prepared closed

include prepared aligned in
theorem full_parameter_order :
    header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      prepared.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)) := by
  rw [aligned.bindings]

include prepared in
theorem constrained_not_empty_header (constrained : row.assumptions ≠ []) :
    ¬ ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header ∧
        header.named.specialized.assumptions = [] := by
  rintro ⟨header, aligned, closed⟩
  apply constrained
  rw [aligned.named, prepared.same] at closed
  exact closed

include prepared in
theorem staged_return_not_header (staged : row.function.returnComptime = true) :
    ¬ ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header := by
  rintro ⟨header, aligned⟩
  have ordinary := header.ordinaryReturn
  rw [aligned.named, prepared.same, staged] at ordinary
  cases ordinary
end Prepared

/-- The actual public compiler, original retained row and full target lookup
supply the row-to-Header bridge in one application. -/
abbrev actual_public := @RecursiveNamedPreparedHeaders.of_public_compile

/-- Packing alone cannot recover the raw binder count. The real preparation
and source certificate are necessary even for Unit. -/
theorem packed_unit_does_not_identify_inputs :
    SourceCoreCompatibleCatalog.packTypes ([] : List Core.Ty) =
      SourceCoreCompatibleCatalog.packTypes [.unit] ∧ ([] : List Core.Ty) ≠ [.unit] := by
  exact ⟨rfl, by intro equal; cases equal⟩

end Tests.SourceCoreRecursiveNamedPreparedHeaders
