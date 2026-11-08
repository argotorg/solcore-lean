import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions
import Solcore.SourceSemantics.Internal.Substitution.TraitLaws
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeControl
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchPrefixes
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.Core.Correspondence
import Solcore.SourceSemantics.Dynamic.Program

/-!
# Recursive named rows: headers and programs

Prepared headers and their parameters, catalog initialization and mutual meaning, finite completion, and the meaning of a whole program's entry and outcome.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts
/-! Independent whole-program typing authenticates the source parameters and
result of each actual named body. Signature identity and complete substitution
are retained. Native projection and invocation evidence are separate receipts;
neither is inferred from packed native types or source body typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts
open Frontend SourceInference RecursiveNamedCatalog

theorem instance_shape {program : Program} {instantiation : SourceInference.DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {signature : ProgramFunctionSignature}
    (programTyped : ProgramWellFormed program)
    (member : signature ∈ program.signatures.functions)
    (selected : instantiation.declaration = signature.id)
    (instantiated : Dynamic.FunctionInstantiates program instantiation body) :
    body.source.inputs.map (fun binder => binder.scheme.body) =
      signature.parameterTypes.map instantiation.parameterSubstitution.apply ∧
    body.resultType = instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) := by
  cases instantiated with
  | @intro actual definition _ actualMember definitionMember actualSelected owner valid sourceEq resultEq contextEq =>
    have actualEq : actual = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
      programTyped.signatures.function_ids actualMember member (actualSelected.symm.trans selected)
    subst actual
    cases programTyped.functions_valid definition definitionMember with
    | @intro declared facts declaredMember declaredOwner bodyTyped =>
      have declaredEq : declared = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
        programTyped.signatures.function_ids declaredMember member (declaredOwner.symm.trans owner)
      subst declared
      cases bodyTyped with
      | intro _ _ _ _ _ declaredResult _ _ _ extended _ _ _ _ _ _ =>
        refine ⟨?_, resultEq.trans (congrArg instantiation.parameterSubstitution.apply declaredResult)⟩
        have inputs := congrArg (List.map instantiation.parameterSubstitution.apply) extended.bodyTypes_eq
        simpa only [sourceEq, StructuralSubstitution.applyTypedSource, StructuralSubstitution.applyBinder,
          StructuralSubstitution.applyScheme, List.map_map, Function.comp_def] using inputs

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : Core.DataEnvironment} {program : Program}

/-- The actual source-frame parameters and result are authenticated separately
from their native carriers. All binder positions remain in source order. -/
theorem header_shape (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
      header.bindings.map (fun binding => binding.1.scheme.body) ∧
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
      header.function.resultType := by
  have shape := instance_shape programTyped member selected header.frame.instantiated
  have inputs : header.bindings.map (fun binding => binding.1.scheme.body) =
      header.sourceBody.source.inputs.map (fun binder => binder.scheme.body) := by
    have parameters := congrArg (List.map (fun binder => binder.scheme.body))
      (header.parameters.symm.trans header.frame.parameters)
    simpa only [List.map_map, Function.comp_def] using parameters
  exact ⟨shape.1.symm.trans inputs.symm, shape.2.symm.trans header.frame.result.symm⟩

/-- Build the existing source-shape receipt from independent program typing.
Actual native projections and the exact invocation dictionary remain explicit. -/
theorem source_types {ambient : Core.AmbientDefinitions values.checked.catalog.definitions}
    {headers : Inventory prepared values ambient.definitions program} {context : Context}
    (programTyped : ProgramWellFormed program)
    (sameSignatures : context.signatures = program.signatures)
    (projections : ∀ header, header ∈ headers →
      (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
        .ok (header.bindings.map Prod.snd))
    (evidence : ∀ header, header ∈ headers → header.function.evidence = []) :
    RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context := by
  refine ⟨?_, ?_, projections, evidence⟩
  · intro header _ signature member selected
    exact (header_shape header programTyped (sameSignatures ▸ member) selected).1
  · intro header _ signature member selected
    exact (header_shape header programTyped (sameSignatures ▸ member) selected).2

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedParameterPackingFacts
/-! Packed native argument types determine the ordered row only after its
arity is fixed independently. Source binder identity comes from the actual
header agreement. Parameter preparation and its packed signature agreement
remain separate receipts; a native type never authenticates source binders. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedParameterPackingFacts
open Core Frontend SourceInference RecursiveNamedCatalog

/-- Zero and one arguments, or one tuple and several arguments, can have the
same packed type. With equal arity the complete ordered native row is unique. -/
theorem packed_eq_of_length {left right : List Core.Ty}
    (arity : left.length = right.length)
    (packed : SourceCoreCompatibleCatalog.packTypes left =
      SourceCoreCompatibleCatalog.packTypes right) : left = right := by
  induction left generalizing right with
  | nil =>
    have empty : right = [] := List.eq_nil_of_length_eq_zero arity.symm
    exact empty.symm
  | cons head tail ih =>
    cases right with
    | nil => simp at arity
    | cons other rest =>
      have sameLength : tail.length = rest.length := Nat.succ.inj arity
      cases tail with
      | nil =>
        have empty : rest = [] := List.eq_nil_of_length_eq_zero sameLength.symm
        subst rest
        simp only [SourceCoreCompatibleCatalog.packTypes] at packed
        cases packed
        rfl
      | cons next suffix =>
        cases rest with
        | nil => simp at sameLength
        | cons otherNext otherSuffix =>
          simp only [SourceCoreCompatibleCatalog.packTypes] at packed
          have components := Ty.product.inj packed
          have sameHead := components.1
          subst other
          exact congrArg (List.cons head) (ih sameLength components.2)

variable {checked : CallableAncestryPairedLookup.Checked}
  {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The full source parameter agreement supplies arity independently of the
native carrier. The packed agreement is required for the actual prepared row. -/
theorem header_native_types (header : Header prepared values definitions program)
    (parameterPack : header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd)) :
    header.bindings.map Prod.snd = header.named.inputs.map Prod.snd := by
  have binders := header.parameters.symm.trans header.agreement.parameters
  have arity : (header.bindings.map Prod.snd).length =
      (header.named.inputs.map Prod.snd).length := by
    simpa only [List.length_map] using congrArg List.length binders
  exact packed_eq_of_length arity (header.parameterType.symm.trans parameterPack)

/-- Transport real preparation projections along the original ordered source
binders and independently authenticated native row. No source shape or evidence
dictionary is inferred from this native projection receipt. -/
theorem header_projections (header : Header prepared values definitions program)
    (parameterPack : header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd))
    (preparedProjections :
      (header.named.inputs.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
        .ok (header.named.inputs.map Prod.snd)) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := by
  have binders := header.parameters.symm.trans header.agreement.parameters
  have raw : header.bindings.map (fun binding => binding.1.scheme.body) =
      header.named.inputs.map (fun binding => binding.1.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) binders
  rw [raw, header_native_types header parameterPack]
  exact preparedProjections

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedParameterPackingFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
/-! Actual named preparation and independent source signature typing determine
both ordered parameter vectors. Packed equality is proved from raw source shape
and real projection, then used only after source binder identity fixes arity.
Invocation evidence and exact source/native catalog identity remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
open Core Frontend SourceInference RecursiveNamedCatalog

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- Only the outer function preparation is inverted. Its input fold is consumed
as the actual success witness and does not need to be exposed again. -/
theorem prepared_parameter {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    {parameter result : TypeSystem.Ty}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (shape : specialized.function.type = .function parameter result) :
    representation.expressions.projectType (.declaration specialized.key.declaration) parameter =
      .ok named.signature.parameterType := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (specialized.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged, shape, pure, Except.pure, bind, Except.bind] at accepted
    by_cases mismatch : result ≠ specialized.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨parameterType, projected, accepted⟩ := bind_ok accepted
      obtain ⟨resultType, _, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact mapError_ok projected

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : SourceSemantics.Program}

/-- Source program typing and the actual source frame identify raw argument
shape. Neither the argument count nor its source types come from a Core carrier. -/
theorem header_type (header : Header compiled.indexed.ancestry values definitions program)
    (programTyped : ProgramWellFormed program) :
    header.instantiation.type = .function
      (TypeSystem.Ty.productMany (header.bindings.map (fun binding => binding.1.scheme.body)))
      header.function.resultType := by
  have instantiated := header.frame.instantiated
  have valid : DeclarationInstantiation.Valid (SourceSemantics.Context.ofSignatures program.signatures)
      header.instantiation := by
    cases instantiated with
    | intro _ _ _ _ valid _ _ _ => exact valid
  cases valid with
  | intro signature member selected _ _ typeEq _ _ _ =>
    have shape := RecursiveNamedSourceSignatureFacts.header_shape header programTyped member selected
    have declared := (programTyped.signatures.functions_semantic signature member).scheme_body
    rw [typeEq, declared]
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [StructuralSubstitution.apply_productMany, shape.1, shape.2]

private theorem project_productMany {catalog : SourceCoreCompatibleCatalog.Catalog}
    {types : List TypeSystem.Ty} {native : List Core.Ty}
    (projected : types.mapM catalog.project = .ok native) :
    catalog.project (TypeSystem.Ty.productMany types) = .ok (SourceCoreCompatibleCatalog.packTypes native) := by
  induction types generalizing native with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
    subst native
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at projected
    obtain ⟨first, projectedHead, projected⟩ := bind_ok projected
    obtain ⟨rest, projectedTail, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projectedTail
      subst rest
      exact projectedHead
    | cons next suffix =>
      have remaining := ih projectedTail
      rw [List.mapM_cons] at projectedTail
      obtain ⟨nextNative, _, projectedTail⟩ := bind_ok projectedTail
      obtain ⟨suffixNative, _, projectedTail⟩ := bind_ok projectedTail
      cases projectedTail
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [projectedHead, remaining]
      rfl

/-- The real prepared parameter projection agrees with the complete ordered
input vector, using independent source shape for the packed parameter type. -/
theorem parameter_pack (header : Header compiled.indexed.ancestry values definitions program)
    (programTyped : ProgramWellFormed program)
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    header.named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd) := by
  have binders := header.parameters.symm.trans header.agreement.parameters
  have raw : header.bindings.map (fun binding => binding.1.scheme.body) =
      header.named.inputs.map (fun binding => binding.1.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) binders
  have shape := matched.type.trans (header_type header programTyped)
  rw [raw] at shape
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled header.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have sourceShape := same ▸ shape
  have projected := prepared_parameter accepted sourceShape
  have realProjected := CompatibleExpressionReads.projectType_of_accepted projected
  have vector := project_productMany (RecursiveNamedPreparedParameterProjections.cached_projected compiled header.selected)
  exact Except.ok.inj (realProjected.symm.trans vector)

/-- The Header's native projection callback is now supplied by actual compiler
receipts; the source and compiler catalogs must still be the same catalog. -/
theorem projections (header : Header compiled.indexed.ancestry values definitions program)
    (sameChecked : values.checked = compiled.compatible.checked)
    (programTyped : ProgramWellFormed program)
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := by
  apply RecursiveNamedParameterPackingFacts.header_projections header (parameter_pack header programTyped matched)
  rw [sameChecked]
  exact RecursiveNamedPreparedParameterProjections.cached_projected compiled header.selected

/-- Complete exact plan selection supplies the metadata match without a
separate Matches assumption. A key alone is deliberately insufficient. -/
theorem projections_of_record (header : Header compiled.indexed.ancestry values definitions program)
    (sameChecked : values.checked = compiled.compatible.checked)
    (programTyped : ProgramWellFormed program)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan header.named.signature.key =
      .ok header.named.specialized) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) :=
  projections header sameChecked programTyped (CallableNamedMetadata.matches_of_exact header.target record)

/-- Raw parameter/result facts and native parameter projections are internal.
The invocation dictionary remains an independent source condition. -/
theorem source_types {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {headers : Inventory compiled.indexed.ancestry values ambient.definitions program} {context : SourceSemantics.Context}
    (sameChecked : values.checked = compiled.compatible.checked)
    (programTyped : ProgramWellFormed program) (sameSignatures : context.signatures = program.signatures)
    (records : ∀ header, header ∈ headers →
      SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan header.named.signature.key = .ok header.named.specialized)
    (evidence : ∀ header, header ∈ headers → header.function.evidence = []) :
    RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context :=
  RecursiveNamedSourceSignatureFacts.source_types programTyped sameSignatures
    (fun header member => projections_of_record header sameChecked programTyped (records header member)) evidence

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
/-! Independent program typing and the Header's actual source instantiation
give body typing in its real parameter context. The two parameter extensions
have the same source binders, so functionality identifies their contexts.
Native types, decoding, and runtime completion do not authenticate source data.
Syntax admission, compiler policies, and runtime frames remain separate facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The complete source invocation package uses the Header's actual raw input
types and lexical context, rather than a separately supplied body judgment. -/
theorem certificate (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, Dynamic.FunctionInstanceTypingCertificate program header.instantiation header.sourceBody
      header.types header.context facts := by
  obtain ⟨types, lexical, facts, certified⟩ := header.frame.instantiated.certificate programTyped
  have extended := header.extended
  rw [header.frame.source, header.frame.context, header.frame.parameters] at extended
  have contextEq := Dynamic.MonoBindersExtend.functional certified.typing.inputs_extend extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certified.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ certified⟩

/-- Source typing is transported along real frame attribution only. -/
theorem body (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, BodyHasType header.function.source header.context header.function.resultType facts := by
  obtain ⟨facts, certified⟩ := certificate header programTyped
  rw [header.frame.source, header.frame.result]
  exact ⟨facts, certified.typing.body_typed⟩

/-- The same body belongs to the complete prepared specialization. -/
theorem prepared_body (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, BodyHasType header.named.specialized.function.typedBody header.context
      header.named.specialized.function.inferredBodyType facts := by
  obtain ⟨facts, typed⟩ := body header programTyped
  exact ⟨facts, by simpa only [header.agreement.source, header.agreement.result] using typed⟩

/-- The normative statement judgment is for the actual invocation roots.
This does not manufacture a lowerer's more restricted Syntax certificate. -/
theorem statements (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ final facts, StatementsHaveType header.function.source
      {returnType := header.function.resultType} header.context header.function.body final facts ∧
      BodyCompletes header.function.resultType facts := by
  obtain ⟨facts, final, typed, _, completes⟩ := body header programTyped
  refine ⟨final, facts, ?_, completes⟩
  simpa [header.agreement.roots, List.filterMap_map, Function.comp_def] using typed

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
/-! An actual public specialization and its second-pass receipts determine an
ordinary named Header. Source typing and the complete substitution range remain
independent inputs. Closed assumptions, ordinary staging flags and exact full
plan selection are explicit admission conditions. No inventory completeness,
runtime Entry, body execution or source Syntax is obtained from native types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
open Core Frontend SourceInference RecursiveNamedCatalog
open RecursiveNamedPublicSpecializationMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem project_productMany {catalog : SourceCoreCompatibleCatalog.Catalog}
    {types : List TypeSystem.Ty} {native : List Core.Ty}
    (projected : types.mapM catalog.project = .ok native) :
    catalog.project (TypeSystem.Ty.productMany types) = .ok (SourceCoreCompatibleCatalog.packTypes native) := by
  induction types generalizing native with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
    subst native
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at projected
    obtain ⟨first, projectedHead, projected⟩ := bind_ok projected
    obtain ⟨rest, projectedTail, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projectedTail
      subst rest
      exact projectedHead
    | cons next suffix =>
      have remaining := ih projectedTail
      rw [List.mapM_cons] at projectedTail
      obtain ⟨nextNative, _, projectedTail⟩ := bind_ok projectedTail
      obtain ⟨suffixNative, _, projectedTail⟩ := bind_ok projectedTail
      cases projectedTail
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [projectedHead, remaining]
      rfl

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem prepared_outputs {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named) :
    named.signature.key = specialized.key ∧
      representation.expressions.projectType (.declaration specialized.key.declaration)
        specialized.function.inferredBodyType = .ok named.signature.resultType := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (specialized.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : specialized.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ specialized.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨parameterType, _, accepted⟩ := bind_ok accepted
      obtain ⟨resultType, projected, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      cases accepted
      have resultEq : result = specialized.function.inferredBodyType := Classical.byContradiction mismatch
      exact ⟨rfl, by simpa only [resultEq] using mapError_ok projected⟩

namespace Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)

/-- Raw source shape comes from the independent invocation certificate. The
packed native parameter is then fixed by its actual preparation and projections. -/
theorem parameter_pack (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    prepared.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (prepared.named.inputs.map Prod.snd) := by
  obtain ⟨types, lexical, facts, certified⟩ := (prepared.instantiated wellFormed range).certificate wellFormed
  have raw := Dynamic.MonoBindersExtend.bodyTypes_eq certified.typing.inputs_extend
  have binders := prepared.agreement.parameters
  have sameInputs : row.function.typedBody.inputs = prepared.named.inputs.map Prod.fst := by
    simpa only [RecursiveNamedPublicSpecializationMeaning.Prepared.view,
      RecursiveNamedPreparedSourceFrames.view, prepared.same] using binders
  change row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = types at raw
  rw [sameInputs] at raw
  simp only [List.map_map, Function.comp_def] at raw
  have shape := certified.callable_type
  change row.function.type = .function (TypeSystem.Ty.productMany types) row.function.inferredBodyType at shape
  rw [← raw] at shape
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have sourceShape : specialized.function.type = .function
      (TypeSystem.Ty.productMany (prepared.named.inputs.map (fun binding => binding.1.scheme.body)))
      specialized.function.inferredBodyType := by
    rw [same.symm.trans prepared.same]
    exact shape
  have projected := RecursiveNamedHeaderParameterProjections.prepared_parameter accepted sourceShape
  have realProjected := CompatibleExpressionReads.projectType_of_accepted projected
  have vector := project_productMany
    (RecursiveNamedPreparedParameterProjections.cached_projected compiled prepared.selected)
  exact Except.ok.inj (realProjected.symm.trans vector)

/-- The actual resolver's complete dictionary is empty precisely here because
its complete ordered predicate list is empty. -/
theorem evidence_empty (closed : row.assumptions = []) : prepared.view.evidence = [] := by
  have keys := prepared.dictionary.2.trans closed
  exact List.map_eq_nil_iff.mp keys

private theorem outputs : prepared.named.signature.key = row.key ∧
    compiled.compatible.checked.catalog.project prepared.view.resultType = .ok prepared.named.signature.resultType := by
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  obtain ⟨key, result⟩ := prepared_outputs accepted
  have projected := CompatibleExpressionReads.projectType_of_accepted result
  refine ⟨key.trans (congrArg (·.key) (same.symm.trans prepared.same)), ?_⟩
  change compiled.compatible.checked.catalog.project prepared.named.specialized.function.inferredBodyType = _
  rw [same]
  exact projected

/-- Exactly the policy used by the original named body callback. -/
def policy : SourceCoreLoops.Policy :=
  let indexed := compiled.indexed
  let named := prepared.named
  let actual := (CallableIndexedNamedGeneration.representation indexed).atContext named.signature.key []
  let expression := SourceCoreGeneralFunctions.lowerContextualExpression indexed.base.sourceProgram actual
    indexed.base.sourceProgram.signatures indexed.base.locals prepared.compilation.parents
    prepared.compilation.own.assignments prepared.diagnostics
    (CallableIndexedNamedGeneration.context indexed named) indexed.base.callableContext none none
  { actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
      prepared.compilation.own.assignments prepared.diagnostics named.signature.key expression with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual indexed.base.locals named.signature.key [] }

/-- All fields refer to this prepared row and second pass. The policy and its
acceptance retain the original callback, not an independently chosen lowering. -/
structure HeaderAt {values : SourceCoreCompatibleValues.Context} (instantiation : DeclarationInstantiation)
    (header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram)) : Prop where
  function : header.function = prepared.view
  metadata : header.instantiation = instantiation
  sourceBody : header.sourceBody = RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row
  named : header.named = prepared.named
  bindings : header.bindings = prepared.named.inputs
  slot : header.slot = prepared.index
  body : header.body = prepared.compilation.body
  parameterCode : header.parameterCode = prepared.compilation.parameterCode
  code : header.code = prepared.compilation.output
  representation : header.representation = CallableIndexedNamedGeneration.representation compiled.indexed
  compiledFuel : header.compiledFuel = compiled.indexed.fuel
  secondPass : HEq header.compiled compiled.indexed.secondPass
  layouts : header.layouts = compiled.indexed.layouts
  owner : header.owner = prepared.named.signature.key
  active : header.active = []
  globals : header.globals = compiled.indexed.base.globals.length
  onError : header.onError = fun error => .sourceAllocation (reprStr error)
  policy : header.policy = policy prepared
  fuel : header.fuel = compiled.indexed.fuel
  readFuel : header.readFuel = compiled.indexed.fuel
  solved : header.solved = prepared.named.specialized.function.solvedRequirements
  output : header.output = prepared.named.signature.resultType
  reasonAt : header.reasonAt = prepared.diagnostics.reasonAt prepared.named.signature.key
  fellThrough : header.fellThrough = prepared.compilation.own.fellThroughReason
  escaped : header.escaped = prepared.compilation.own.table.escapedReason
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  bodyTyped : ∃ facts, BodyHasType header.function.source header.context header.function.resultType facts
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output

private theorem header_of_frame_with_evidence {values : SourceCoreCompatibleValues.Context}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {instantiation : DeclarationInstantiation}
    (frame : NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) instantiation
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
      .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram), HeaderAt prepared instantiation header := by
  obtain ⟨types, context, facts, certified⟩ := frame.instantiated.certificate wellFormed
  have extended : MonoBindersExtend prepared.view.source.owner prepared.view.context
      prepared.view.parameters types context := by
    rw [frame.source, frame.context, frame.parameters]
    exact certified.typing.inputs_extend
  have unique : NodeOccurrencesUnique prepared.view.source := by
    rw [frame.source]
    exact certified.graph_closed.wellFormed.nodeOccurrencesUnique
  have bodyTyped : BodyHasType prepared.view.source context prepared.view.resultType facts := by
    rw [frame.source, frame.result]
    exact certified.typing.body_typed
  have ordinary : ∀ binder, binder ∈ prepared.view.parameters → binder.comptime = false := by
    simpa only [RecursiveNamedPublicSpecializationMeaning.Prepared.view,
      RecursiveNamedPreparedSourceFrames.view, prepared.same] using ordinaryParameters
  let header := Header.of_dictionary_frame
    (values := values)
    (function := prepared.view) (instantiation := instantiation)
    (sourceBody := RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
    (frame := frame) (named := prepared.named) (agreement := prepared.agreement)
    (ordinaryReturn := by simpa only [prepared.same] using ordinaryReturn)
    (ordinaryParameters := ordinary) (target := target)
    (context := context) (types := types) (bindings := prepared.named.inputs)
    (parameters := prepared.agreement.parameters) (inputs := prepared.agreement.parameters)
    (extended := extended) (solved := prepared.named.specialized.function.solvedRequirements)
    (reasonAt := prepared.diagnostics.reasonAt prepared.named.signature.key)
    (readFuel := compiled.indexed.fuel) (output := prepared.named.signature.resultType)
    (policy := policy prepared) (fuel := compiled.indexed.fuel)
    (fellThrough := prepared.compilation.own.fellThroughReason)
    (escaped := prepared.compilation.own.table.escapedReason)
    (body := prepared.compilation.body) (parameterCode := prepared.compilation.parameterCode)
    (code := prepared.compilation.output) (layouts := compiled.indexed.layouts)
    (owner := prepared.named.signature.key) (active := []) (globals := compiled.indexed.base.globals.length)
    (onError := fun error => .sourceAllocation (reprStr error))
    (acceptedPrefix := prepared.compilation.parametersCompiled) (hook := prepared.compilation.hook)
    (definitions_eq := rfl) (registered := CallableIndexedAmbient.frame_registered compiled.indexed)
    (unique := unique) (parameterType := parameter_pack prepared wellFormed range)
    (resultType := rfl) (representation := CallableIndexedNamedGeneration.representation compiled.indexed)
    (compiledFuel := compiled.indexed.fuel) (compiled := compiled.indexed.secondPass)
    (slot := prepared.index) (selected := prepared.selected)
    (cached := prepared.cached.trans (congrArg some prepared.compilation.emitted))
    (programTyped := wellFormed) (sameLedger := rfl)
  refine ⟨header, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    prepared.compilation.bodyCompiled, ⟨facts, bodyTyped⟩, (outputs prepared).2⟩

private theorem header_of_frame {values : SourceCoreCompatibleValues.Context}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {instantiation : DeclarationInstantiation}
    (frame : NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) instantiation
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view)
    (closed : row.assumptions = []) (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
      .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram), HeaderAt prepared instantiation header :=
  let _ := closed
  header_of_frame_with_evidence prepared wellFormed range frame ordinaryReturn ordinaryParameters target

/-- Canonical source metadata and the actual second pass supply a Header.
Complete inventory membership and runtime authority are separate obligations. -/
theorem canonical_header_with_evidence {values : SourceCoreCompatibleValues.Context}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram), HeaderAt prepared (CallableNamedMetadata.instantiation row) header :=
  header_of_frame_with_evidence prepared wellFormed range (prepared.source_frame wellFormed range)
    ordinaryReturn ordinaryParameters target


theorem canonical_header {values : SourceCoreCompatibleValues.Context}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (closed : row.assumptions = []) (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram), HeaderAt prepared (CallableNamedMetadata.instantiation row) header :=
  let _ := closed
  canonical_header_with_evidence prepared wellFormed range ordinaryReturn ordinaryParameters target
/-- Retained metadata keeps its reversed full substitution order; it uses the
same source body and compilation through the same common Header constructor. -/
theorem retained_header_with_evidence {values : SourceCoreCompatibleValues.Context}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram), HeaderAt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header :=
  header_of_frame_with_evidence prepared wellFormed range (prepared.retained_frame wellFormed range)
    ordinaryReturn ordinaryParameters target

theorem retained_header {values : SourceCoreCompatibleValues.Context}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (closed : row.assumptions = []) (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram), HeaderAt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header :=
  let _ := closed
  retained_header_with_evidence prepared wellFormed range ordinaryReturn ordinaryParameters target

end Prepared

/-- The public compiler's retained original worklist row supplies the complete
preparation witness. No dictionary-bearing row is silently made ordinary. -/
theorem of_public_compile_with_evidence {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    {values : SourceCoreCompatibleValues.Context}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures recipe.compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key) :
    ∃ (prepared : Prepared recipe.compiled row)
      (header : Header recipe.compiled.indexed.ancestry values recipe.compiled.indexed.layouts.definitions
        (Program.ofChecked recipe.compiled.sourceProgram)),
      Prepared.HeaderAt prepared (CallableNamedMetadata.instantiation row) header := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile accepted issued member
  obtain ⟨header, aligned⟩ := Prepared.canonical_header_with_evidence prepared wellFormed range ordinaryReturn ordinaryParameters
    (target.trans (congrArg Except.ok (Prepared.outputs prepared).1.symm))
  exact ⟨prepared, header, aligned⟩

theorem of_public_compile {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    {values : SourceCoreCompatibleValues.Context}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures recipe.compiled.sourceProgram.signatures) row.parameterSubstitution)
    (closed : row.assumptions = []) (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key) :
    ∃ (prepared : Prepared recipe.compiled row)
      (header : Header recipe.compiled.indexed.ancestry values recipe.compiled.indexed.layouts.definitions
        (Program.ofChecked recipe.compiled.sourceProgram)),
      Prepared.HeaderAt prepared (CallableNamedMetadata.instantiation row) header :=
  let _ := closed
  of_public_compile_with_evidence accepted issued member wellFormed range ordinaryReturn ordinaryParameters target

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization
/-! Actual preparation supplies the complete ordered lambda cache and global
signatures to the closed initialization proof. Source headers, their cached
ledger and empty source lexical contexts remain independent static receipts.
This factory does not attribute a source body from a native cache or decoder. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

def store (compiled : SourceCoreUnifiedCompilation.Compiled) : Store :=
  initialStore compiled.indexed.base.globals (RecursiveNamedCachedRows.rows compiled)
    compiled.indexed.ancestry.layout.frame

def environment (compiled : SourceCoreUnifiedCompilation.Compiled) : Environment :=
  initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame

theorem evaluates (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Evaluates [] [] (SourceCoreCallableIndexedFrames.allocate compiled.indexed.ancestry.layout.frame
      (SourceCoreRecursiveEntry.allocateGlobals compiled.indexed.base.globals.reverse
        (SourceCoreRecursiveEntry.installFunctions compiled.indexed.secondPass.closures (LanguageResult.success .unit))))
      (.inRight .word .unit) (store compiled) := by
  rw [RecursiveNamedCachedRows.exact_cache compiled]
  exact framed_bootstrap _ _ _ (RecursiveNamedCachedRows.ordered compiled)

theorem typed {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe) :
    ∃ world, RuntimeStoreHasTypes world (store compiled) compiled.indexed.layouts.definitions :=
  stored accepted (RecursiveNamedCachedRows.rows compiled) (RecursiveNamedCachedRows.exact_cache compiled)
    (RecursiveNamedCachedRows.ordered compiled)

theorem supported_cached {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {slot : Nat} {code : Expr} (cached : compiled.indexed.secondPass.closures[slot]? = some code) :
    NativeExpressionContextSupport.supported code (compiled.indexed.base.globals.length + 1) = true := by
  obtain ⟨_, _, _, ⟨receipt⟩⟩ := RecursiveNamedCachedRows.cached_at compiled cached
  rw [receipt.emitted] at cached ⊢
  exact RecursiveNamedCachedSupport.cached_supported accepted (RecursiveNamedCachedRows.rows compiled)
    (RecursiveNamedCachedRows.exact_cache compiled) (RecursiveNamedCachedRows.ordered compiled) cached

/-- Completed original machines expose the same actual bootstrap result and
store, with no source execution or source catalog as a premise. -/
theorem completed_store {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ finalStore = store compiled := by
  obtain ⟨_, emitted⟩ := recipe_emitted accepted
  have expected := evaluates compiled
  rw [← emitted] at expected
  exact evaluation_deterministic (runStateful_evaluation_sound completed) expected

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])

include ledger sizes locals in
theorem authority {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions) :
    ∃ world, Nonempty (Authority headers
      (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
      0 [] world ⟨[]⟩ (store compiled)) :=
  RecursiveNamedCatalogInitialization.of_recipe compiled headers
    (RecursiveNamedCachedRows.rows compiled) (RecursiveNamedCachedRows.exact_cache compiled)
    (RecursiveNamedCachedRows.ordered compiled) ledger
    (fun header _ => CallableIndexedPreparedInventories.cached_global_at compiled header.selected)
    sizes locals accepted definitions

include ledger sizes locals in
theorem entry {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ (store compiled) ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ (store compiled) (environment compiled)) :=
  RecursiveNamedCatalogInitialization.initial_entry compiled headers
    (RecursiveNamedCachedRows.rows compiled) (RecursiveNamedCachedRows.exact_cache compiled)
    (RecursiveNamedCachedRows.ordered compiled) ledger
    (fun header _ => CallableIndexedPreparedInventories.cached_global_at compiled header.selected)
    sizes locals accepted definitions functions registry

include ledger sizes locals in
theorem completed_entry {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ finalStore ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ finalStore (environment compiled)) := by
  obtain ⟨result, storeEq⟩ := completed_store accepted completed
  rw [storeEq]
  exact ⟨result, entry compiled headers ledger sizes locals accepted definitions functions registry⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
/-! Strong induction closes the finite catalog's body obligations. Static
profiles retain actual compiler equations at each reachable body entry;
they require no profiles for arbitrary unreachable contexts and contain no execution law. Source and native sizes use separate inductions.
An actual call selects a strictly smaller body; structural expression children
may have the same size. Initial catalog authority remains an independent input
to the resulting invocation contracts. Whole compiler extraction and arbitrary
qualified/lambda expressions remain separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds


/-- Selects the static context condition, without changing runtime code. -/
def ContextFor (runtime : Bool) (solved : List SolvedRequirement)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) : Prop :=
  match runtime with
  | false => CompatibleExpressionLiterals.ContextValid solved context evidence
  | true => CompatibleRuntimeContextValidity.Valid solved context evidence

theorem context_extend {runtime : Bool} {solved : List SolvedRequirement}
    {context next : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (valid : ContextFor runtime solved context evidence)
    (extended : BinderExtends owner context binder next) : ContextFor runtime solved next evidence := by
  cases runtime with
  | false => exact TypedLexicalControl.valid_extend valid extended
  | true => exact valid.extend extended

theorem context_runtime {runtime : Bool} {solved : List SolvedRequirement}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : ContextFor runtime solved context evidence) :
    CompatibleRuntimeContextValidity.Valid solved context evidence := by
  cases runtime with
  | false => exact CompatibleRuntimeContextValidity.of_ordinary valid
  | true => exact valid

section Families
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

/-- The ordinary tree and the same tree with actual numeric receipts are kept
as separate static cases. No ordinary receipt is cast to a selected receipt. -/
abbrev ExpressionsFor (runtime : Bool) (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  match runtime with
  | false => Expressions headers compilation fuel source context solved reasonAt
  | true => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation fuel source context solved reasonAt

abbrev MatchProfileForMode (runtime : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program) (compilation : SourceCoreFunctions.Context)
    (fuel : Nat) (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence)
    (fun context => ExpressionsFor runtime headers compilation fuel header.function.source context header.solved header.reasonAt)
    diagnosticPolicy header expressionSyntax administrative registry faults
/-- The ordinary tree and the same tree with actual numeric receipts are kept
as separate static cases. No ordinary receipt is cast to a selected receipt. -/
abbrev ExpressionsForWith (authenticated runtime : Bool) (evidence : Dynamic.EvidenceEnvironment) (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  match runtime with
  | false => Expressions headers compilation fuel source context solved reasonAt
  | true => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some evidence else none) headers compilation fuel source context solved reasonAt

abbrev MatchProfileForModeWith (authenticated runtime : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program) (compilation : SourceCoreFunctions.Context)
    (fuel : Nat) (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence)
    (fun context => ExpressionsForWith authenticated runtime header.function.evidence headers compilation fuel header.function.source context header.solved header.reasonAt)
    diagnosticPolicy header expressionSyntax administrative registry faults
end Families

/-- A stronger body entry is required only at the actual parameter result.
An arbitrary BodyState remains unchanged and cannot construct this condition. -/
def BodyEntryCondition {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (P : Header prepared values ambient.definitions program → ProtectedExpressionMeaning.Entry)
    (header : Header prepared values ambient.definitions program) :
    BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _} entry =>
    P header (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.mapping entry.world entry.heap entry.store entry.canonical

section EvidenceCommon

variable (authenticated runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileForModeWith authenticated runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

namespace NamedFamily

/-- The real named profile supplies the neutral kernel fields directly. -/
def origin (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P) (binders : ProtectedExpressionMeaning.Binds P)
    {header : Header prepared values ambient.definitions program}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    (profile : MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence)
      certificates diagnosticPolicy header expressionSyntax administrative registry faults)
    (escapedFault : faults .controlEscapedFunction header.escaped) :
    CallableRuntimeBodyOrigins.Origin values ambient registry faults :=
  { layouts := header.layouts, owner := header.owner, active := header.active
    frameLayout := prepared.layout.frame, globals := header.globals, onError := header.onError
    function := header.function, expressionSyntax := expressionSyntax, certificates := certificates
    validity := fun context => ContextFor runtime header.solved context header.function.evidence
    diagnosticPolicy := diagnosticPolicy, administrative := administrative, context := header.context
    scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))
    output := header.output, code := header.body, fellThrough := header.fellThrough, escaped := header.escaped
    solved := header.solved, protectedEntry := P
    body := { flow := profile.flow, tree := profile.tree, sites := profile.errors, initialValid := profile.initialValid
              projection := profile.projection, unique := header.unique, emitted := profile.emitted }
    definitions := header.definitions_eq, registered := header.registered, escapedFault := escapedFault
    transport := transport, binders := binders, extend := fun valid extended => context_extend valid extended
    runtimeOf := fun valid => context_runtime valid }

/-- The actual parameter result supplies the full state, including its physical
frame reference. No authority is recovered from a native type. -/
def entry (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P) (binders : ProtectedExpressionMeaning.Binds P)
    {header : Header prepared values ambient.definitions program}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {expressionSyntax : ExpressionId → Prop}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location}
    {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
    (profile : MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence)
      certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (escapedFault : faults .controlEscapedFunction header.escaped)
    (state : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (aligned : P (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      state.mapping state.world state.heap state.store state.canonical) :
    CallableRuntimeBodyOrigins.Entry (origin runtime P transport binders profile escapedFault) functions :=
  { mapping := state.mapping, world := state.world, environment := state.environment
    canonical := state.canonical, actual := state.actualBody, heap := state.heap, store := state.store
    embedding := state.embedding, actualContext := CallableIndexedParameterTyped.prefixContext header.bindings actualContext
    frameLocation := frameLocation, native := current
    environments := state.environments, heaps := state.heaps, locals := state.locals, lookups := state.lookups
    actualTyped := state.actualTyped, reference := by simpa only [origin, List.length_map, List.length_reverse] using state.reference
    read := state.state.read
    unmapped := Eq.mp (congrArg (fun location => location ∉ state.mapping) state.catalog_frame) state.catalog.authority.unmapped
    installed := aligned }

end NamedFamily

include extension faithful observations escaped in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_with_family
    (P : Header prepared values ambient.definitions program → ProtectedExpressionMeaning.Entry)
    (transports : ∀ header, ProtectedExpressionMeaning.Transport (P header))
    (binders : ∀ header, ProtectedExpressionMeaning.Binds (P header))
    (certificates : Header prepared values ambient.definitions program → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
  (profileProvider : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      BodyEntryCondition functions registry P header entry →
      MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence) (certificates header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      ContextFor runtime header.solved context header.function.evidence → ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          functions registry callee faults (BodyEntryCondition functions registry P callee))) →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults (P header))
    (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAtWith
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (BodyEntryCondition functions registry P header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (fun context => ContextFor runtime header.val.solved context header.val.function.evidence)
      (certificates header.val) diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.Origin values ambient registry faults := fun index =>
    NamedFamily.origin runtime (P index.1.val) (transports index.1.val) (binders index.1.val) index.2.2 (escaped index.1.val index.1.property)
  have bodies := CallableRuntimeBodyMutualMeaning.preserves_at origins functions extension program faithful observations
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, profile⟩
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after aligned trace
      let actualProfile := profileProvider callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := NamedFamily.entry runtime functions (P callee) (transports callee) (binders callee)
        actualProfile (escaped callee calleeMember) entry aligned
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
        meaning actualEntry trace
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after aligned trace
  let profile := profileProvider header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, profile⟩
  let actualEntry := NamedFamily.entry runtime functions (P header) (transports header) (binders header)
    profile (escaped header member) entry aligned
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    bodies index actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata⟩

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_with_evidence (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  have bodies := preserves_at_with_family runtime functions extension faithful observations escaped
    (fun _ => protectedEntry headers locations capturePrefix (capturePrefix + 1))
    (fun _ => entry_transport) (fun _ => entry_binds)
    (fun header context => ExpressionsForWith authenticated runtime header.function.evidence headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact profiles header member entry)
    (by
      intro header member context valid budget child within below
      have oldBodies : ∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
          (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry callee faults) := by
        intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after trace
        exact below callee calleeMember smaller strict entry ⟨entry.catalog⟩ trace
      have meaning : RecursiveNamedBoundedContracts.PreservesAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context header.function.evidence header.function.source
          (ExpressionsForWith authenticated runtime header.function.evidence headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt) faults
          (protectedEntry headers locations capturePrefix (compilation header).administrativePrefix) := by
        cases runtime with
        | false =>
          exact RecursiveNamedExpressionTreeBounds.preserves_at functions extension faithful observations runtimeViews
            header.function.evidence valid header.unique owners (uninitialized header member) (missing header member) budget child within oldBodies
        | true =>
          exact RecursiveNamedExpressionTreeBounds.preserves_at_runtime_with functions extension faithful observations runtimeViews
            header.function.evidence header.unique owners (uninitialized header member) (missing header member) authenticated valid.ledger valid.runtime budget child within oldBodies
      rw [prefixMatches header member] at meaning
      exact @meaning) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after trace
  exact bodies header member entry ⟨entry.catalog⟩ trace

include extension faithful observations runtimeViews escaped in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_with_family
    (P : Header prepared values ambient.definitions program → ProtectedExpressionMeaning.Entry)
    (transports : ∀ header, ProtectedExpressionMeaning.Transport (P header))
    (binders : ∀ header, ProtectedExpressionMeaning.Binds (P header))
    (certificates : Header prepared values ambient.definitions program → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
  (profileProvider : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      BodyEntryCondition functions registry P header entry →
      MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence) (certificates header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      ContextFor runtime header.solved context header.function.evidence → ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          functions registry callee faults (BodyEntryCondition functions registry P callee))) →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults (P header))
    (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAtWith
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (BodyEntryCondition functions registry P header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (fun context => ContextFor runtime header.val.solved context header.val.function.evidence)
      (certificates header.val) diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.Origin values ambient registry faults := fun index =>
    NamedFamily.origin runtime (P index.1.val) (transports index.1.val) (binders index.1.val) index.2.2 (escaped index.1.val index.1.property)
  have bodies := CallableRuntimeBodyMutualMeaning.reflects_at origins functions extension program faithful observations runtimeViews
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, profile⟩
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore aligned completed
      let actualProfile := profileProvider callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := NamedFamily.entry runtime functions (P callee) (transports callee) (binders callee)
        actualProfile (escaped callee calleeMember) entry aligned
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
        meaning actualEntry completed
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore aligned completed
  let profile := profileProvider header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, profile⟩
  let actualEntry := NamedFamily.entry runtime functions (P header) (transports header) (binders header)
    profile (escaped header member) entry aligned
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    bodies index actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_with_evidence (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  have bodies := reflects_at_with_family runtime functions extension faithful observations runtimeViews escaped
    (fun _ => protectedEntry headers locations capturePrefix (capturePrefix + 1))
    (fun _ => entry_transport) (fun _ => entry_binds)
    (fun header context => ExpressionsForWith authenticated runtime header.function.evidence headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact profiles header member entry)
    (by
      intro header member context valid budget child within below
      have oldBodies : ∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
          (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry callee faults) := by
        intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore completed
        exact below callee calleeMember smaller strict entry ⟨entry.catalog⟩ completed
      have meaning : RecursiveNamedBoundedContracts.ReflectsAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context header.function.evidence header.function.source
          (ExpressionsForWith authenticated runtime header.function.evidence headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt) faults
          (protectedEntry headers locations capturePrefix (compilation header).administrativePrefix) := by
        cases runtime with
        | false =>
          exact RecursiveNamedExpressionTreeBounds.reflects_at functions extension faithful observations runtimeViews
            header.function.evidence valid (uninitialized header member) (missing header member) budget child within oldBodies
        | true =>
          exact RecursiveNamedExpressionTreeBounds.reflects_at_runtime_with functions extension faithful observations runtimeViews
            header.function.evidence (uninitialized header member) (missing header member) authenticated valid.ledger valid.runtime budget child within oldBodies
      rw [prefixMatches header member] at meaning
      exact @meaning) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore completed
  exact bodies header member entry ⟨entry.catalog⟩ completed

variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : ContextFor runtime solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_with_evidence (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (ExpressionsForWith authenticated runtime evidence headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  cases runtime with
  | false =>
    exact RecursiveNamedExpressionTreeBounds.preserves_at functions extension faithful observations runtimeViews
      evidence valid sourceUnique owners callerUninitialized callerMissing size size (Nat.le_refl size)
      (fun header member child _ => preserves_at_with_evidence authenticated false functions extension faithful observations runtimeViews owners
        uninitialized missing escaped prefixMatches profiles child header member)
  | true =>
    exact RecursiveNamedExpressionTreeBounds.preserves_at_runtime_with functions extension faithful observations runtimeViews
      evidence sourceUnique owners callerUninitialized callerMissing authenticated valid.ledger valid.runtime size size (Nat.le_refl size)
      (fun header member child _ => preserves_at_with_evidence authenticated true functions extension faithful observations runtimeViews owners
        uninitialized missing escaped prefixMatches profiles child header member)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_with_evidence (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (ExpressionsForWith authenticated runtime evidence headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  cases runtime with
  | false =>
    exact RecursiveNamedExpressionTreeBounds.reflects_at functions extension faithful observations runtimeViews
      evidence valid callerUninitialized callerMissing size size (Nat.le_refl size)
      (fun header member child _ => reflects_at_with_evidence authenticated false functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles child header member)
  | true =>
    exact RecursiveNamedExpressionTreeBounds.reflects_at_runtime_with functions extension faithful observations runtimeViews
      evidence callerUninitialized callerMissing authenticated valid.ledger valid.runtime size size (Nat.le_refl size)
      (fun header member child _ => reflects_at_with_evidence authenticated true functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles child header member)


end EvidenceCommon

section Common

variable (runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileForMode runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_with (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact preserves_at_with_evidence false runtime functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles size

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_with (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles size

variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : ContextFor runtime solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_with (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (ExpressionsFor runtime headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_preserves_at_with_evidence false runtime functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles evidence valid sourceUnique callerUninitialized callerMissing size

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_with (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (ExpressionsFor runtime headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing size


end Common

section Ordinary

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_match (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact preserves_at_with false functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_match (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_with false functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) size


variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_match (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Expressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_preserves_at_with false functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) evidence valid sourceUnique callerUninitialized callerMissing size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_match (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Expressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_with false functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) evidence valid callerUninitialized callerMissing size


end Ordinary

section Runtime

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_runtime (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact preserves_at_with true functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_runtime (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_with true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles size


variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_runtime (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_preserves_at_with true functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles evidence valid sourceUnique callerUninitialized callerMissing size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_runtime (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_with true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing size


end Runtime

section RuntimeEvidence

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith true diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_runtime_evidence (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact preserves_at_with_evidence true true functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_runtime_evidence (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_with_evidence true true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles size


variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_runtime_evidence (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (some evidence) headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_preserves_at_with_evidence true true functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles evidence valid sourceUnique callerUninitialized callerMissing size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_runtime_evidence (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (some evidence) headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_with_evidence true true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing size


end RuntimeEvidence

section Legacy
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
theorem preserves_at (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact preserves_at_match functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches
    (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) size

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
theorem reflects_at (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_match functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches
    (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) size

variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
theorem expression_preserves_at (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Expressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_preserves_at_match functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches
    (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) evidence valid sourceUnique callerUninitialized callerMissing size

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
theorem expression_reflects_at (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Expressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_match functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches
    (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) evidence valid callerUninitialized callerMissing size

end Legacy

section Formation
variable {values : SourceCoreCompatibleValues.Context}
  {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program} {locations : Locations}
  {expressionSyntax : Header indexed.ancestry values indexed.layouts.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : values.checked.catalog.callableContracts = true)


abbrev FormationExpressions (authenticated : Bool)
    (header : Header indexed.ancestry values indexed.layouts.definitions program)
    (context : SourceSemantics.Context) :=
  RecursiveNamedLambdaFormationTreeMeaning.Expressions (caller := header) (headers := headers)
    (context := context) (evidence := header.function.evidence) (registry := registry) (faults := faults)
    (fuel := header.readFuel) (solved := header.solved) (reasonAt := header.reasonAt) authenticated

abbrev FormationProfile (authenticated : Bool)
    (header : Header indexed.ancestry values indexed.layouts.definitions program) (administrative : Core.Context) :=
  MatchProfileWith (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (fun context => CompatibleRuntimeContextValidity.Valid header.solved context header.function.evidence)
    (FormationExpressions (headers := headers) (registry := registry) (faults := faults) authenticated header)
    diagnosticPolicy header (expressionSyntax header) administrative registry faults

variable (authenticated : Bool)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (alignments : ∀ header, header ∈ headers → RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header
    (CallableIndexedNamedGeneration.context indexed header.named) 0)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers locations 0 (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry header
        arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost) →
      RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry entry →
      FormationProfile (headers := headers) (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) authenticated header
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))

include complete alignments extension owners uninitialized missing escaped profiles in
/-- The same strong induction closes formation inside every actual named callee.
Its static provider is restricted to independently aligned parameter states. -/
theorem preserves_at_formation (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAtWith
      (headers := headers) (locations := locations) (capturePrefix := 0) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry header faults
      (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry) size := by
  apply preserves_at_with_family (locations := locations) (capturePrefix := 0) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) true (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) extension (CallableIndexedLambdaValues.identity_faithful indexed)
    (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile) escaped
    (fun header => RecursiveNamedLambdaFormationEntries.protectedEntry
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header headers locations 0 1)
    (fun _ => RecursiveNamedLambdaFormationEntries.transport) (fun _ => RecursiveNamedLambdaFormationEntries.binds)
    (FormationExpressions (headers := headers) (registry := registry) (faults := faults) authenticated)
    profiles _ size
  intro header member context valid budget child within bodies
  exact RecursiveNamedLambdaFormationTreeMeaning.preserves_at profile complete alignments (alignments header member) extension
    header.unique owners (uninitialized header member) (missing header member) authenticated valid.ledger valid.runtime budget child within bodies

include complete alignments extension uninitialized missing escaped profiles in
/-- Reflection consumes original strict body children and returns independent
source grades. No body preservation or source trace is an input. -/
theorem reflects_at_formation (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAtWith
      (headers := headers) (locations := locations) (capturePrefix := 0) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry header faults
      (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry) size := by
  apply reflects_at_with_family (locations := locations) (capturePrefix := 0) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) true (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) extension (CallableIndexedLambdaValues.identity_faithful indexed)
    (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) escaped
    (fun header => RecursiveNamedLambdaFormationEntries.protectedEntry
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header headers locations 0 1)
    (fun _ => RecursiveNamedLambdaFormationEntries.transport) (fun _ => RecursiveNamedLambdaFormationEntries.binds)
    (FormationExpressions (headers := headers) (registry := registry) (faults := faults) authenticated)
    profiles _ size
  intro header member context valid budget child within bodies
  exact RecursiveNamedLambdaFormationTreeMeaning.reflects_at profile complete alignments (alignments header member) extension
    (uninitialized header member) (missing header member) authenticated valid.ledger valid.runtime budget child within bodies

variable {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {fuel : Nat} {reasonAt : ExpressionId → Word}
  (callerAligned : RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
    (CallableIndexedNamedGeneration.context indexed caller.named) 0)
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include complete alignments extension owners uninitialized missing escaped profiles callerAligned valid callerUninitialized callerMissing in
/-- Whole expressions use the same closed named-callee induction. Formation
receipts stay in the fixed model through both arguments and full heaps. -/
theorem expression_preserves_at_formation (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source
      (RecursiveNamedLambdaFormationTreeMeaning.Expressions (caller := caller) (headers := headers)
        (context := context) (evidence := evidence) (registry := registry) (faults := faults)
        (fuel := fuel) (solved := solved) (reasonAt := reasonAt) authenticated) faults
      (RecursiveNamedLambdaFormationEntries.protectedEntry
        (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  exact RecursiveNamedLambdaFormationTreeMeaning.preserves_at profile complete alignments callerAligned extension
    caller.unique owners callerUninitialized callerMissing authenticated valid.ledger valid.runtime size size (Nat.le_refl _)
    (fun header member child _ => preserves_at_formation profile authenticated complete alignments extension owners
      uninitialized missing escaped profiles child header member)

include complete alignments extension uninitialized missing escaped profiles callerAligned valid callerUninitialized callerMissing in
/-- Original native completion returns source evaluation through that same
closed family; no source trace or body law is supplied. -/
theorem expression_reflects_at_formation (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source
      (RecursiveNamedLambdaFormationTreeMeaning.Expressions (caller := caller) (headers := headers)
        (context := context) (evidence := evidence) (registry := registry) (faults := faults)
        (fuel := fuel) (solved := solved) (reasonAt := reasonAt) authenticated) faults
      (RecursiveNamedLambdaFormationEntries.protectedEntry
        (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  exact RecursiveNamedLambdaFormationTreeMeaning.reflects_at profile complete alignments callerAligned extension
    callerUninitialized callerMissing authenticated valid.ledger valid.runtime size size (Nat.le_refl _)
    (fun header member child _ => reflects_at_formation profile authenticated complete alignments extension
      uninitialized missing escaped profiles child header member)

end Formation

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
/-! The initial named body scope retains the original source parameter schemes.
A successful declaration lookup is authenticated against the actual inputs;
no success is invented for duplicate or qualified declarations. Native payload
types do not determine source types, and no runtime authority is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
open Core Frontend SourceInference
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts

/-- An actual successful declaration lookup must return this entire input
binder, including its raw scheme and requirement metadata. -/
theorem input_identifies {source : TypedSource} {binder declared : TypedBinder}
    (member : binder ∈ source.inputs)
    (accepted : SourceCoreDataPlaces.rootBinder source binder.id = .ok declared) :
    declared = binder :=
  CompatibleMatchArmScopes.rootBinder_identifies
    (List.mem_append_left _ member) accepted

/-- Installing a real source binder keeps lookup correspondence even if an
unrelated declared binder would make a future compiler lookup fail. -/
theorem scope_bind {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context next : SourceSemantics.Context} {binder : TypedBinder} (payload : Core.Ty)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (extended : BinderExtends source.owner context binder next) :
    CompatibleExpressionReads.ScopeDeclarations source ((binder.id, payload) :: scope) next := by
  cases extended
  intro id declared index type selected authentic
  by_cases same : binder.id = id
  · subst id
    have identified := CompatibleMatchArmScopes.rootBinder_identifies member authentic
    subst declared
    exact .head
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact .tail same (declarations _ _ _ _ previous authentic)

/-- Source-order installation and the compiler's reversed scope agree. The
native payload vector is arbitrary; only original binder identities matter. -/
theorem parameters {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context final : SourceSemantics.Context} {bindings : List (TypedBinder × Core.Ty)} {types : List TypeSystem.Ty}
    (member : ∀ binding, binding ∈ bindings → binding.1 ∈ SourceCoreDataPlaces.declaredBinders source)
    (extended : MonoBindersExtend source.owner context (bindings.map Prod.fst) types final)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations source
      (bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope) final := by
  induction bindings generalizing context scope types with
  | nil => cases extended; exact declarations
  | cons binding rest ih =>
    cases extended with
    | cons _ head tail =>
      exact ih (fun candidate present => member candidate (List.mem_cons_of_mem _ present)) tail
        (scope_bind binding.2 (member binding List.mem_cons_self) declarations head)

private theorem reversed_scope (bindings : List (TypedBinder × Core.Ty)) (scope : SourceCoreLocalCell.Scope) :
    bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope =
      bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih => simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Every real named Header supplies its initial body's source declaration
correspondence. Residual flags, source schemes and the complete input order
are unchanged. This does not claim that every rootBinder call succeeds. -/
theorem header_scope {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} (header : Header prepared values ambient.definitions program) :
    CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context := by
  have members : ∀ binding, binding ∈ header.bindings →
      binding.1 ∈ SourceCoreDataPlaces.declaredBinders header.function.source := by
    intro binding member
    have input : binding.1 ∈ header.function.source.inputs := by
      rw [header.inputs]
      exact List.mem_map.mpr ⟨binding, member, rfl⟩
    exact List.mem_append_left _ input
  have extended := header.extended
  rw [header.parameters] at extended
  have initial : CompatibleExpressionReads.ScopeDeclarations header.function.source [] header.function.context := by
    intro _ _ _ _ selected _
    cases selected
  have final := parameters members extended initial
  simpa only [reversed_scope, List.append_nil, bodyScope] using final

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins
/-! Ordinary callees discovered while preparing implementation methods retain
actual Source provenance and their final physical slot. The accepted complete
preparation pass supplies their full runtime evidence environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins
open Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning (Origin Prepared)

/-- A cached row belongs to the final preparation plan, including helpers
that were absent from the original specialization worklist. -/
theorem final_member (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) :
    row ∈ compiled.indexed.base.plan.specializations := by
  obtain ⟨actual, present, generated⟩ :=
    RecursiveNamedPreparedParameterProjections.cached_preparation compiled selected
  have actualEq : actual = row :=
    (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs generated).1.symm.trans same
  subst actual
  rw [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared]
  exact List.mem_reverse.mp (List.mem_of_getElem? present)

/-- Exact Source origin and an installed final row supply a prepared ordinary
caller. Its dictionary follows from the actual complete preparation receipt. -/
theorem of_cached_origin (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (origin : Origin compiled.sourceProgram row) :
    Nonempty (Prepared compiled row) := by
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ :=
    CallableIndexedNamedGeneration.compiled_at compiled.indexed selected
  have preparation := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled
  obtain ⟨_growth, covered⟩ := CallableCoercionPreparation.of_accepted preparation
  obtain ⟨available, resolved, _sites⟩ := covered row (final_member compiled selected same)
  exact ⟨⟨index, named, diagnostics, code, compilation, available,
    selected, same, cached, origin, resolved⟩⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStagedCalls
/-! Actual named specialization views select the global body's own staging
scope. This connects independent recursively staged body runs to independent
global applications. Original source instantiation, full evidence and ordered
allocation stay explicit. Native body meaning and full expression admission
are separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStagedCalls
open Frontend SourceInference SourceCoreStageContracts
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedPreparedStageScopes
open Staging.Recursive

namespace Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)

theorem global_view : prepared.view = globalView
    (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
    prepared.view.evidence prepared.compilation.statements := by
  dsimp only [RecursiveNamedPublicSpecializationMeaning.Prepared.view, RecursiveNamedPreparedSourceFrames.view,
    globalView, RecursiveNamedSpecializationBodyFacts.bodyInstance]
  rw [prepared.same]

variable {native : SourceCoreGeneralFunctions.CallableContext}
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan row.key = .ok row)

include prepared actual record in
/-- The same descriptor-authenticated sidecar selects the actual global view.
No dictionary is emptied and no stage marker is copied from the caller. -/
theorem selected_global
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named row.key)) :
    ∃ sidecar : Sidecar,
      prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar ∧ sidecar.caller = row ∧
      (registry actual).Closure
        (globalView (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
          prepared.view.evidence prepared.compilation.statements)
        (RecursiveStageRegistry.scope sidecar [] prepared.view) := by
  obtain ⟨sidecar, issued, same, selected⟩ := selected_of_descriptor actual prepared record descriptor
  refine ⟨sidecar, issued, same, ?_⟩
  rw [← global_view prepared]
  exact selected

include prepared actual record in
/-- A real source body run enters the named callee's original scope and
ordered parameter allocation. Its entire heap and failure scope are retained. -/
theorem applies
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {sidecar : Sidecar} (issued : prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar)
    {caller : Scope} {context bodyContext finalContext : Context}
    {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    {types : List TypeSystem.Ty} {outcome : BodyOutcome} {result : Outcome}
    (parameters : MonoBindersExtend row.function.typedBody.owner
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context
      row.function.typedBody.inputs types bodyContext)
    (allocate : Dynamic.BindersAllocate [] before row.function.typedBody.inputs arguments environment bound)
    (body : Statements (Program.ofChecked compiled.sourceProgram) (registry actual)
      (RecursiveStageRegistry.scope sidecar [] prepared.view) bodyContext environment bound
      prepared.compilation.statements finalContext outcome after)
    (converted : BodyResult row.function.inferredBodyType outcome result) :
    Applies (Program.ofChecked compiled.sourceProgram) (registry actual) caller context before
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments result after := by
  have frame := prepared.source_frame wellFormed range
  have same := sidecar_caller issued record
  have selected : (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) :=
    .named prepared sidecar issued same
  refine Applies.global (function := ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩)
    frame.instantiated frame.covers frame.roots ?_ parameters allocate body converted
  change (registry actual).Closure
    (globalView (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      prepared.view.evidence prepared.compilation.statements)
    (RecursiveStageRegistry.scope sidecar [] prepared.view)
  rw [← global_view prepared]
  exact selected

include prepared actual in
/-- Arity failure is independent of body staging and changes no heap. It
requires the actual source instantiation rather than native packed arity. -/
theorem arity_failure
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {caller : Scope} {context : Context} {heap : Dynamic.Heap} {arguments : List Dynamic.Value}
    (mismatch : row.function.typedBody.inputs.length ≠ arguments.length) :
    Applies (Program.ofChecked compiled.sourceProgram) (registry actual) caller context heap
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments
      (.fault (.semantic (.argumentArityMismatch row.function.typedBody.inputs.length arguments.length))) heap :=
  Applies.globalArity (function := ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩)
    (bodyInstance := RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
    (prepared.instantiated wellFormed range) mismatch
end Prepared
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStagedCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts
/-! Static annotation and continuation facts from the independent source
judgments. A returned annotation uses the actual control return type. Universal
stopping keeps an actual return/default/branch/prefix receipt; BodyCompletes is
never used to manufacture that receipt. Exhaustive no-default stopping remains
at its existing typed pointwise boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts
open Frontend SourceInference
open ReachableStatementContinuations

/-- The legacy returned annotation follows the actual source typing derivation,
including ordered match facts and lexical context changes. -/
theorem returned_type {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {statements : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts)
    (returns : facts.sawReturn = true) : facts.type = control.returnType := by
  have result : facts.sawReturn = true → facts.type = control.returnType := by
    apply StatementsHaveType.rec (source := source) (t := typed)
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ => True)
      (motive_6 := fun _ _ _ _ _ => True)
      (motive_7 := fun _ _ _ => True)
      (motive_8 := fun control _ _ _ facts _ => facts.sawReturn = true → facts.type = control.returnType)
      (motive_9 := fun control _ _ _ facts _ => facts.sawReturn = true → facts.type = control.returnType)
      (motive_10 := fun _ _ _ _ _ => True)
      (motive_11 := fun _ _ _ _ _ => True)
      (motive_12 := fun control _ _ _ facts _ => facts.sawReturn = true → facts.type = control.returnType)
      (motive_13 := fun control _ _ _ facts _ => ∀ fact ∈ facts, fact.sawReturn = true → fact.type = control.returnType)
    all_goals try { intros; exact True.intro }
    all_goals try { intros; simp_all }
    case singleton =>
      intro control context final id facts head ih returns
      have r : facts.sawReturn = true := returns
      simpa [BodyFacts.singleton, r] using ih r
    case cons =>
      intro control context middle final id next rest headFacts tailFacts head tail headIH tailIH returns
      cases h : tailFacts.sawReturn with
      | true => simpa [BodyFacts.cons, h] using tailIH h
      | false =>
        have r : headFacts.sawReturn = true := by simpa [BodyFacts.cons, h] using returns
        simpa [BodyFacts.cons, h, r] using headIH r
    case nil => simp [BodyFacts.empty]
    case cons =>
      intro control context type arm arms fact facts head tail headIH tailIH candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact headIH
      · exact tailIH candidate member
  exact result returns

/-- Prefixing a statically typed ordinary-or-terminal head preserves the actual
stopping selection in the tail. It does not require the head to fall through. -/
theorem prefix_stopped {source : TypedSource} {control : ControlContext}
    {context next : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {facts : StatementFacts} {rest : List StatementId} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node)
    (head : StatementHasType source control context id next facts)
    (tail : StoppingStatements source rest summary) :
    StoppingStatements source (id :: rest) (facts.control.sequence summary) :=
  .prefix found head tail

private theorem same_form {source : TypedSource} {id : StatementId} {node other : StatementNode}
    (first : source.lookupStatement? id = some node)
    (second : source.lookupStatement? id = some other) : other.form = node.form := by
  cases Option.some.inj (second.symm.trans first)
  rfl

/-- Only the actual block stopping constructor can match this source form. -/
theorem stopped_block {source : TypedSource} {id : StatementId} {node : StatementNode}
    {body : List StatementId} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node) (form : node.form = .block body)
    (stopped : StoppingStatement source id summary) :
    ∃ inner, StoppingStatements source body inner := by
  cases stopped <;> have eq := same_form found (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

/-- Universal conditional stopping retains both actual branch selections. -/
theorem stopped_if {source : TypedSource} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {left right : List StatementId} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition left (some right))
    (stopped : StoppingStatement source id summary) :
    (∃ l, StoppingStatements source left l) ∧ (∃ r, StoppingStatements source right r) := by
  cases stopped <;> have eq := same_form found (by assumption) <;> simp_all
  exact ⟨⟨_, by assumption⟩, ⟨_, by assumption⟩⟩

/-- Static arm facts retain the compiler's full ordered case count. -/
theorem cases_length {source : TypedSource} {control : ControlContext} {context : SourceSemantics.Context}
    {type : TypeSystem.Ty} {cases : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type cases facts) : cases.length = facts.length := by
  apply MatchCasesHaveType.rec (source := source) (t := typed)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ cases facts _ => cases.length = facts.length)
  all_goals intros; first | exact True.intro | simp_all

private theorem zip_fact {cases : List TypedMatchCase} {facts : List BodyFacts} {arm : TypedMatchCase}
    (length : cases.length = facts.length) (member : arm ∈ cases) :
    ∃ fact, (arm, fact) ∈ cases.zip facts := by
  induction cases generalizing facts with
  | nil => cases member
  | cons head tail ih =>
    cases facts with
    | nil => simp at length
    | cons fact rest =>
      have sizes : tail.length = rest.length := Nat.succ.inj length
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨fact, List.mem_cons_self⟩
      · obtain ⟨chosen, present⟩ := ih sizes member
        exact ⟨chosen, List.mem_cons_of_mem _ present⟩

/-- A stopping match view comes only from the actual present-default receipt.
No no-default exhaustiveness certificate is cast to this universal boundary. -/
theorem stopped_match {source : TypedSource} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (stopped : StoppingStatement source id summary) :
    ReachableMatchContinuations.DefaultStopped source id resolution := by
  cases stopped <;> have eq := same_form found (by assumption) <;> simp_all
  case matchDefault =>
    subst_vars
    rename_i actualNode resolution fallback control context type facts defaultFinal defaultFacts summary present casesTyped defaultTyped merged arms defaultStops originalFound
    refine ReachableMatchContinuations.DefaultStopped.of_source originalFound form present ⟨?_, ?_⟩
    · intro arm member
      have length := cases_length casesTyped
      obtain ⟨fact, zipped⟩ := zip_fact length member
      exact GenericLexicalStatements.Stopped.of_source (arms arm fact zipped)
    · intro body same
      cases Option.some.inj (present.symm.trans same)
      exact GenericLexicalStatements.Stopped.of_source defaultStops

private theorem sequence_stopped {head tail : ControlSummary} (stops : head.fallthrough = none) :
    head.sequence tail = head := by
  cases head
  simp_all [ControlSummary.sequence, ControlSummary.canFallthrough]

/-- Static input for one binding actually retained in a source body/header. -/
def BinderReceipt (source : TypedSource) (binder : TypedBinder) : Prop :=
  SourceCoreDataPlaces.rootBinder source binder.id = .ok binder ∧ binder.scheme.quantified = [] ∧
    source.inputs.any (fun input => decide (input.id = binder.id)) = false

/-- The actual finite assignment children and source root correspondence.
These are source typing/admission receipts, with no runtime law. -/
structure AssignmentReceipt (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) : Prop where
  projections : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
    SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type
  writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body
  right : ExpressionHasType source context rhs assignment.target.type
  profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false
  children : ∀ id, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
    expressionSyntax id ∧ ∃ node, source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type

structure UnaryReceipt (source : TypedSource) (context : SourceSemantics.Context)
    (assignment : AssignmentResolution) : Prop where
  writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body
  bare : assignment.target.projections = []
  profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer

/- Support is indexed by the original independent typing proof, rather than a
new source grammar. Its Bool index records availability of a universal stopping
receipt. No-default cases retain false; an actual later stopper can still make
the complete sequence true. Only the static children actually present in the
typing derivation occur here. -/
mutual
  inductive StatementReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {id : StatementId} →
      {final : SourceSemantics.Context} → {facts : StatementFacts} →
      StatementHasType source control context id final facts → Bool → Prop where
    | letUninitialized {control context final id node binder contains form mono generalizes extension annotation}
        (binderReceipt : BinderReceipt source binder) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.letUninitialized source control context final id node binder contains form mono generalizes extension annotation) false
    | letInitialized {control context final id node binder initializer contains form initial mono generalizes extension annotation}
        (binderReceipt : BinderReceipt source binder) (value : expressionSyntax initializer) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.letInitialized source control context final id node binder initializer contains form initial mono generalizes extension annotation) false
    | returnUnit {control context id node contains form unit annotation} :
        StatementReceipts source expressionSyntax
          (@StatementHasType.returnUnit source control context id node contains form unit annotation) true
    | returnValue {control context id node value contains form typed annotation}
        (expression : expressionSyntax value) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.returnValue source control context id node value contains form typed annotation) true
    | expressionValue {control context id node expression type contains form typed annotation}
        (value : expressionSyntax expression) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.expressionValue source control context id node expression type contains form typed annotation) false
    | expressionDiscard {control context id node expression type contains form typed annotation}
        (value : expressionSyntax expression) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.expressionDiscard source control context id node expression type contains form typed annotation) false
    | assignValue {control context id node assignment operator rhs contains form typed annotation}
        (receipt : AssignmentReceipt source expressionSyntax context assignment operator rhs) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.assignValue source control context id node assignment operator rhs contains form typed annotation) false
    | assignBitNot {control context id node assignment contains form typed annotation}
        (receipt : UnaryReceipt source context assignment) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.assignBitNot source control context id node assignment contains form typed annotation) false
    | ifWithoutElse {control context thenFinal id node condition body facts contains form conditionTyped bodyTyped annotation ready}
        (conditionSyntax : expressionSyntax condition)
        (bodyReceipt : BodyReceipts source expressionSyntax bodyTyped ready) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.ifWithoutElse source control context thenFinal id node condition body facts contains form conditionTyped bodyTyped annotation) false
    | ifWithElse {control context leftFinal rightFinal id node condition left right leftFacts rightFacts
        contains form conditionTyped leftTyped rightTyped annotation leftReady rightReady}
        (conditionSyntax : expressionSyntax condition)
        (leftReceipt : BodyReceipts source expressionSyntax leftTyped leftReady)
        (rightReceipt : BodyReceipts source expressionSyntax rightTyped rightReady)
        (admitted : control.returnType = .unit ∨ (leftFacts.sawReturn && rightFacts.sawReturn) = false ∨
          (leftReady = true ∧ rightReady = true)) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.ifWithElse source control context leftFinal rightFinal id node condition left right leftFacts rightFacts
            contains form conditionTyped leftTyped rightTyped annotation) (leftReady && rightReady)
    | block {control context innerFinal id node statements facts contains form typed annotation ready}
        (inner : BodyReceipts source expressionSyntax typed ready) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.block source control context innerFinal id node statements facts contains form typed annotation) ready
    | matchWithoutDefault {control context id node resolution type facts summary
        contains form absent scrutineeTyped casesTyped requirements exhaustive merged annotation ready}
        (scrutinee : expressionSyntax resolution.scrutinee)
        (cases : CasesReceipts source expressionSyntax casesTyped ready)
        (hidden : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
        (ordinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
          source.inputs.any (fun input => decide (input.id = binder)) = false) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.matchWithoutDefault source control context id node resolution type facts summary
            contains form absent scrutineeTyped casesTyped requirements exhaustive merged annotation) false
    | matchWithDefault {control context defaultFinal id node resolution fallback type facts defaultFacts summary
        contains form present scrutineeTyped casesTyped defaultTyped requirements merged annotation ready defaultReady}
        (scrutinee : expressionSyntax resolution.scrutinee)
        (cases : CasesReceipts source expressionSyntax casesTyped ready)
        (fallbackReceipt : BodyReceipts source expressionSyntax defaultTyped defaultReady)
        (hidden : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
        (ordinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
          source.inputs.any (fun input => decide (input.id = binder)) = false) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.matchWithDefault source control context defaultFinal id node resolution fallback type facts defaultFacts summary
            contains form present scrutineeTyped casesTyped defaultTyped requirements merged annotation) (ready && defaultReady)
    | forLoop {control context loopContext postContext bodyFinal id node initializer condition post statements facts
        contains form initializerTyped conditionTyped bodyTyped postTyped annotation ready}
        (initial : ItemsReceipts source expressionSyntax initializerTyped)
        (conditionSyntax : expressionSyntax condition)
        (bodyReceipt : BodyReceipts source expressionSyntax bodyTyped ready)
        (postReceipt : ItemsReceipts source expressionSyntax postTyped) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.forLoop source control context loopContext postContext bodyFinal id node initializer post condition statements facts
            contains form initializerTyped conditionTyped bodyTyped postTyped annotation) false
    | whileLoop {control context final id node condition statements facts contains form conditionTyped bodyTyped annotation ready}
        (conditionSyntax : expressionSyntax condition)
        (bodyReceipt : BodyReceipts source expressionSyntax bodyTyped ready) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.whileLoop source control context final id node condition statements facts
            contains form conditionTyped bodyTyped annotation) false
    | breakStmt {control context id node contains form allowed annotation} :
        StatementReceipts source expressionSyntax
          (@StatementHasType.breakStmt source control context id node contains form allowed annotation) true
    | continueStmt {control context id node contains form allowed annotation} :
        StatementReceipts source expressionSyntax
          (@StatementHasType.continueStmt source control context id node contains form allowed annotation) true

  inductive BodyReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {statements : List StatementId} →
      {final : SourceSemantics.Context} → {facts : BodyFacts} →
      StatementsHaveType source control context statements final facts → Bool → Prop where
    | nil (control context) : BodyReceipts source expressionSyntax (StatementsHaveType.nil control context) false
    | singleton {control context final id facts head ready}
        (headReceipt : StatementReceipts source expressionSyntax head ready)
        (admitted : (BodyFacts.singleton facts).type = control.returnType →
          control.returnType = .unit ∨ facts.sawReturn = false ∨ ready = true) :
        BodyReceipts source expressionSyntax (@StatementsHaveType.singleton source control context final id facts head) ready
    | cons {control context middle final id next rest headFacts tailFacts head tail headReady tailReady}
        (headReceipt : StatementReceipts source expressionSyntax head headReady)
        (tailReceipt : BodyReceipts source expressionSyntax tail tailReady)
        (admitted : (BodyFacts.cons headFacts tailFacts).type = control.returnType →
          tailFacts.type = control.returnType ∨ (headFacts.sawReturn = true ∧ headReady = true)) :
        BodyReceipts source expressionSyntax
          (@StatementsHaveType.cons source control context middle final id next rest headFacts tailFacts head tail) (headReady || tailReady)

  inductive ItemReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {item : ForItemForm} →
      {final : SourceSemantics.Context} → ForItemHasType source control context item final → Prop where
    | letUninitialized {control context final binder mono generalizes extension}
        (receipt : BinderReceipt source binder) : ItemReceipts source expressionSyntax
          (@ForItemHasType.letUninitialized source control context final binder mono generalizes extension)
    | letInitialized {control context final binder expression typed mono generalizes extension}
        (receipt : BinderReceipt source binder) (value : expressionSyntax expression) : ItemReceipts source expressionSyntax
          (@ForItemHasType.letInitialized source control context final binder expression typed mono generalizes extension)
    | expression {control context expression type typed} (value : expressionSyntax expression) :
        ItemReceipts source expressionSyntax (@ForItemHasType.expression source control context expression type typed)
    | assignValue {control context assignment operator expression typed}
        (receipt : AssignmentReceipt source expressionSyntax context assignment operator expression) :
        ItemReceipts source expressionSyntax (@ForItemHasType.assignValue source control context assignment operator expression typed)
    | assignBitNot {control context assignment typed} (receipt : UnaryReceipt source context assignment) :
        ItemReceipts source expressionSyntax (@ForItemHasType.assignBitNot source control context assignment typed)

  inductive ItemsReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {items : List ForItemForm} →
      {final : SourceSemantics.Context} → ForItemsHaveType source control context items final → Prop where
    | nil (control context) : ItemsReceipts source expressionSyntax (ForItemsHaveType.nil control context)
    | cons {control context middle final item items head tail}
        (headReceipt : ItemReceipts source expressionSyntax head)
        (tailReceipt : ItemsReceipts source expressionSyntax tail) : ItemsReceipts source expressionSyntax
          (@ForItemsHaveType.cons source control context middle final item items head tail)

  inductive CaseReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {type : TypeSystem.Ty} →
      {arm : TypedMatchCase} → {facts : BodyFacts} →
      MatchCaseHasType source control context type arm facts → Bool → Prop where
    | intro {control context type arm binders arity armContext final facts pattern extended typed ready}
        (body : BodyReceipts source expressionSyntax typed ready) : CaseReceipts source expressionSyntax
          (@MatchCaseHasType.intro source control context type arm binders arity armContext final facts pattern extended typed) ready

  inductive CasesReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {type : TypeSystem.Ty} →
      {arms : List TypedMatchCase} → {facts : List BodyFacts} →
      MatchCasesHaveType source control context type arms facts → Bool → Prop where
    | nil (control context type) : CasesReceipts source expressionSyntax (MatchCasesHaveType.nil control context type) true
    | cons {control context type arm arms fact facts head tail headReady tailReady}
        (headReceipt : CaseReceipts source expressionSyntax head headReady)
        (tailReceipt : CasesReceipts source expressionSyntax tail tailReady) : CasesReceipts source expressionSyntax
          (@MatchCasesHaveType.cons source control context type arm arms fact facts head tail) (headReady && tailReady)
end

/-- Universal stopping is constructed from the selected default/return/block/
if and typed prefix support, at the original typing contexts and source. -/
theorem BodyReceipts.stopping {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {control : ControlContext} {context final : SourceSemantics.Context}
    {statements : List StatementId} {facts : BodyFacts} {typed : StatementsHaveType source control context statements final facts}
    {ready : Bool} (unique : NodeOccurrencesUnique source)
    (receipt : BodyReceipts source expressionSyntax typed ready) (available : ready = true) :
    StoppingStatements source statements facts.control := by
  have result : ready = true → StoppingStatements source statements facts.control := by
    apply BodyReceipts.rec (t := receipt)
      (motive_1 := fun {control context id final facts} _ ready _ => ready = true → StoppingStatement source id facts.control)
      (motive_2 := fun {control context ids final facts} _ ready _ => ready = true → StoppingStatements source ids facts.control)
      (motive_3 := fun {control context item final} _ _ => True)
      (motive_4 := fun {control context items final} _ _ => True)
      (motive_5 := fun {control context type arm facts} _ ready _ => ready = true → StoppingStatements source arm.body facts.control)
      (motive_6 := fun {control context type arms facts} _ ready _ => ready = true → ∀ arm fact,
        (arm, fact) ∈ arms.zip facts → StoppingStatements source arm.body fact.control)
    all_goals try { intros; exact True.intro }
    all_goals try { intros; contradiction }
    case returnUnit => intros; exact .returnUnit (lookupStatement?_complete unique (by assumption)) (by assumption)
    case returnValue => intros; exact .returnValue (lookupStatement?_complete unique (by assumption)) (by assumption)
    case breakStmt => intros; exact .breaking (lookupStatement?_complete unique (by assumption)) (by assumption)
    case continueStmt => intros; exact .continuing (lookupStatement?_complete unique (by assumption)) (by assumption)
    case ifWithElse =>
      intros
      rename_i leftIH rightIH available
      rcases Bool.and_eq_true_iff.mp available with ⟨leftReady, rightReady⟩
      exact .conditional (lookupStatement?_complete unique (by assumption)) (by assumption) (leftIH leftReady) (rightIH rightReady)
    case block =>
      intros
      rename_i bodyIH available
      exact .block (lookupStatement?_complete unique (by assumption)) (by assumption) (bodyIH available)
    case matchWithDefault =>
      intros
      rename_i casesIH defaultIH available
      rcases Bool.and_eq_true_iff.mp available with ⟨caseReady, defaultReady⟩
      exact .matchDefault (lookupStatement?_complete unique (by assumption)) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (casesIH caseReady) (defaultIH defaultReady)
    case singleton =>
      intros
      rename_i headIH available
      exact .stop (headIH available)
    case cons =>
      intros
      rename_i actualControl initial middle final id next rest headFacts tailFacts headTyped tailTyped headReady tailReady headReceipt tailReceipt admitted headIH tailIH available
      rcases Bool.or_eq_true_iff.mp available with headReady | tailReady
      · have head := headIH headReady
        change StoppingStatements source (id :: next :: rest) (headFacts.control.sequence tailFacts.control)
        rw [sequence_stopped head.no_fallthrough]
        exact .stop head
      · obtain ⟨node, present, _⟩ := Dynamic.StatementHasType.controlFormTyping headTyped
        exact .prefix (lookupStatement?_complete unique present) headTyped (tailIH tailReady)
    case intro =>
      intros
      rename_i bodyIH available
      exact bodyIH available
    case cons =>
      intros
      rename_i headIH tailIH available arm fact member
      rcases Bool.and_eq_true_iff.mp available with ⟨headReady, tailReady⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact headIH headReady
      · exact tailIH tailReady arm fact member
  exact result available

private theorem singleton_stopping {source : TypedSource} {id : StatementId} {summary : ControlSummary}
    (stops : StoppingStatements source [id] summary) : StoppingStatement source id summary := by
  cases stops with
  | stop head => exact head
  | «prefix» _ _ tail => exact False.elim (tail.nonempty rfl)

/-- The statement receipt uses the same universal stopping proof as its
one-statement body; no completion-to-stopping implication is assumed. -/
theorem StatementReceipts.stopping {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {control : ControlContext} {context final : SourceSemantics.Context}
    {id : StatementId} {facts : StatementFacts} {typed : StatementHasType source control context id final facts}
    {ready : Bool} (unique : NodeOccurrencesUnique source)
    (receipt : StatementReceipts source expressionSyntax typed ready) (available : ready = true) :
    StoppingStatement source id facts.control := by
  have body : BodyReceipts source expressionSyntax (StatementsHaveType.singleton typed) ready :=
    .singleton receipt (fun _ => .inr (.inr available))
  exact singleton_stopping (body.stopping unique available)

/-- A fixed ordered source binder extension fixes the complete lexical context. -/
theorem binders_context_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binders : List TypedBinder} (one : BindersExtend owner context binders left)
    (two : BindersExtend owner context binders right) : left = right := by
  induction one generalizing right with
  | nil => cases two; rfl
  | cons first rest ih =>
    cases two with
    | cons other tail =>
      cases first
      cases other
      exact ih tail

/-- Typed pattern binders retain their full source order before context transport. -/
theorem pattern_context_eq {source : TypedSource} {context left right : SourceSemantics.Context}
    {pattern : TypedMatchPattern} {type : TypeSystem.Ty} {one two : List TypedBinder} {a b : Nat}
    (first : TypedMatchPatternHasType context pattern type one a)
    (second : TypedMatchPatternHasType context pattern type two b)
    (leftExtension : BindersExtend source.owner context one left)
    (rightExtension : BindersExtend source.owner context two right) : left = right := by
  have same : one = two := (CompatiblePatternSourceBinders.pattern_binders first).symm.trans
    (CompatiblePatternSourceBinders.pattern_binders second)
  subst two
  exact binders_context_eq leftExtension rightExtension

/-- Every ordered typed case keeps its own actual body stopping receipt. -/
theorem CasesReceipts.stopping {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {control : ControlContext} {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {arms : List TypedMatchCase} {facts : List BodyFacts}
    {typed : MatchCasesHaveType source control context type arms facts} {ready : Bool}
    (unique : NodeOccurrencesUnique source) (receipt : CasesReceipts source expressionSyntax typed ready)
    (available : ready = true) :
    ∀ arm fact, (arm, fact) ∈ arms.zip facts → StoppingStatements source arm.body fact.control := by
  cases receipt with
  | nil => intro arm fact member; cases member
  | @cons _ _ _ arm arms fact facts head tail headReady tailReady first rest =>
    rcases Bool.and_eq_true_iff.mp available with ⟨headAvailable, tailAvailable⟩
    intro selected selectedFacts member
    rcases List.mem_cons.mp member with same | member
    · cases same
      cases first with
      | intro body => exact body.stopping unique headAvailable
    · exact rest.stopping unique tailAvailable selected selectedFacts member
termination_by arms.length

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogFiniteCompletion
/-! All finite derivation grades have already been closed by catalog mutual
induction. Erasing independent Source/Core grades gives invocation meaning and
connects it to the actual machine. A finite source derivation supplies sufficient
native fuel; a completed native run supplies a source derivation. Fuel exhaustion
is not completion, and no source termination claim follows from static typing.
Initial catalog authority and real-entry static profiles remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogFiniteCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

section Evidence
variable (authenticated runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith authenticated runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The source derivation chooses its own grade. All callee meaning is
provided by the catalog theorem for every grade, rather than a fixed budget. -/
theorem preserves_with_evidence {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨size, measured⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size trace
  exact invocation_preserves_bounded (functions := functions) (registry := registry) (faults := faults) size
    (fun child _ => RecursiveNamedCatalogMutualMeaning.preserves_at_with_evidence authenticated runtime functions extension faithful observations runtimeViews owners
      uninitialized missing escaped prefixMatches profiles child header member)
    caller member represented heaps measured (Nat.le_refl size)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_sized_with_evidence (budget size : Nat) (within : size ≤ budget)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (measured : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨_, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    invocation_reflects_bounded (functions := functions) (registry := registry) (faults := faults) budget
      (fun child _ => RecursiveNamedCatalogMutualMeaning.reflects_at_with_evidence authenticated runtime functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles child header member)
      caller member represented heaps capture measured within
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_with_evidence
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨size, measured⟩ := evaluation_has_size completed
  exact reflects_sized_with_evidence authenticated runtime functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller member represented heaps size size (Nat.le_refl size) capture measured

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Sufficient fuel follows from a finite independent source execution,
including language faults represented by the normal result carrier. -/
theorem has_sufficient_fuel_with_evidence {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    preserves_with_evidence authenticated runtime functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles
      caller member represented heaps trace
  obtain ⟨required, run⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨capture, value, finalStore, finalMap, finalWorld, required, run, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every machine completion reflects. No relation between source and
native fuel, and no assumption of source termination, enters this consumer. -/
theorem completed_run_reflects_with_evidence
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_with_evidence authenticated runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
    caller member represented heaps capture (runStateful_evaluation_sound completed)

end Evidence

section Common
variable (runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForMode runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The source derivation chooses its own grade. All callee meaning is
provided by the catalog theorem for every grade, rather than a fixed budget. -/
theorem preserves_with {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact preserves_with_evidence false runtime functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_sized_with (budget size : Nat) (within : size ≤ budget)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (measured : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_sized_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps budget size within capture measured

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_with
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps capture completed

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Sufficient fuel follows from a finite independent source execution,
including language faults represented by the normal result carrier. -/
theorem has_sufficient_fuel_with {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact has_sufficient_fuel_with_evidence false runtime functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every machine completion reflects. No relation between source and
native fuel, and no assumption of source termination, enters this consumer. -/
theorem completed_run_reflects_with
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_run_reflects_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps capture completed

end Common

section Match
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The source derivation chooses its own grade. All callee meaning is
provided by the catalog theorem for every grade, rather than a fixed budget. -/
theorem preserves_match {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact preserves_with false functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_sized_match (budget size : Nat) (within : size ≤ budget)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (measured : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_sized_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps budget size within capture measured

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_match
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps capture completed

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Sufficient fuel follows from a finite independent source execution,
including language faults represented by the normal result carrier. -/
theorem has_sufficient_fuel_match {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact has_sufficient_fuel_with false functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every machine completion reflects. No relation between source and
native fuel, and no assumption of source termination, enters this consumer. -/
theorem completed_run_reflects_match
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_run_reflects_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps capture completed

end Match

section Legacy
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The source derivation chooses its own grade. All callee meaning is
provided by the catalog theorem for every grade, rather than a fixed budget. -/
theorem preserves {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact preserves_match functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps capture completed

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Sufficient fuel follows from a finite independent source execution,
including language faults represented by the normal result carrier. -/
theorem has_sufficient_fuel {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact has_sufficient_fuel_match functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every machine completion reflects. No relation between source and
native fuel, and no assumption of source termination, enters this consumer. -/
theorem completed_run_reflects
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_run_reflects_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps capture completed

end Legacy
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogFiniteCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramEntrySource
/-! The independent whole-program entry selects the Header's exact body.
Admission, raw argument typing and initial heap typing remain source facts.
This connects ProgramEvaluates to the body relation used by Core meaning;
the actual completed body machine is connected below. Public session
preparation remains a separate connection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramEntrySource
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

def entry (header : Header prepared values definitions program) (arguments : List Dynamic.Value) :
    Dynamic.ProgramEntry := ⟨header.instantiation, header.function.evidence, arguments⟩

/-- The real input binders determine argument types. Source heap validity and
argument validity are independent of native representation or decoding. -/
theorem entry_valid (header : Header prepared values definitions program)
    {before : Dynamic.Heap} {arguments : List Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    Dynamic.ProgramEntryValid program (entry header arguments) before header.sourceBody := by
  have extended := header.extended
  rw [header.frame.source, header.frame.context, header.frame.parameters] at extended
  have typesEq := Dynamic.MonoBindersExtend.bodyTypes_eq extended
  refine ⟨header.frame.instantiated, header.frame.covers, ?_, ?_⟩
  · simpa only [header.frame.context] using heapTyped
  · simpa only [entry, typesEq, header.frame.context] using argumentsTyped

/-- A whole-program source execution carries its own admission and entry
validation. Body uniqueness identifies its hidden instance with the Header. -/
theorem invokes_from_program (header : Header prepared values definitions program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {value : Dynamic.Value}
    (evaluated : Dynamic.ProgramEvaluates program (entry header arguments) before value after) :
    Dynamic.BodyInvokes program header.sourceBody header.function.evidence before arguments value after := by
  cases evaluated with
  | run admitted valid invoked =>
    have same := BuiltinNamedCalls.instantiation_unique_of_wellFormed admitted.staticallyValid
      valid.instantiates header.frame.instantiated
    cases same
    exact invoked

/-- A body execution becomes a whole-program execution only after genuine
source staging admission and raw external-input validity have been supplied. -/
theorem program_from_invokes (header : Header prepared values definitions program)
    (admitted : Staging.ProgramHasStages program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {value : Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (invoked : Dynamic.BodyInvokes program header.sourceBody header.function.evidence before arguments value after) :
    Dynamic.ProgramEvaluates program (entry header arguments) before value after :=
  .run admitted (entry_valid header heapTyped argumentsTyped) invoked

/-- The successful whole-program observation is exactly the real Header body
observation under the independent entry conditions. Faults retain BodyFaults;
they are not encoded as successful ProgramEvaluates. -/
theorem program_iff_body_value (header : Header prepared values definitions program)
    (admitted : Staging.ProgramHasStages program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {value : Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    Dynamic.ProgramEvaluates program (entry header arguments) before value after ↔
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments (.value value) after := by
  constructor
  · intro evaluated
    exact .value (invokes_from_program header evaluated)
  · intro outcome
    cases outcome with
    | value invoked => exact program_from_invokes header admitted heapTyped argumentsTyped invoked

section Evidence
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (authenticated runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith authenticated runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
theorem program_has_sufficient_native_fuel_evidence {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (evaluated : Dynamic.ProgramEvaluates program (RecursiveNamedProgramEntrySource.entry header arguments) before sourceValue after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults (.value sourceValue) value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  have invoked := RecursiveNamedProgramEntrySource.invokes_from_program header evaluated
  exact RecursiveNamedCatalogFiniteCompletion.has_sufficient_fuel_with_evidence authenticated runtime functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles caller member represented heaps (.value invoked)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- A native success reconstructs an independent whole-program source run.
Source staging and raw initial-input validity are separate entry conditions. -/
theorem native_success_reflects_program_evidence
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {payload : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done (.inRight .word payload) finalStore) :
    ∃ sourceValue after finalMap finalWorld,
      Dynamic.ProgramEvaluates program (RecursiveNamedProgramEntrySource.entry header arguments) before sourceValue after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry functions).Represents
        finalMap finalWorld header.function.resultType sourceValue payload header.output ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨outcome, after, finalMap, finalWorld, traced, result, finalHeaps, maps, worlds, administrative, metadata, finalEntry⟩ :=
    RecursiveNamedCatalogFiniteCompletion.completed_run_reflects_with_evidence authenticated runtime functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles caller member represented heaps capture completed
  cases result with
  | value representedResult =>
    cases traced with
    | value invoked =>
      exact ⟨_, after, finalMap, finalWorld,
        RecursiveNamedProgramEntrySource.program_from_invokes header admitted heapTyped argumentsTyped invoked,
        representedResult, finalHeaps, maps, worlds, administrative, metadata, finalEntry⟩

end Evidence

section Native
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
theorem program_has_sufficient_native_fuel {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (evaluated : Dynamic.ProgramEvaluates program (RecursiveNamedProgramEntrySource.entry header arguments) before sourceValue after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults (.value sourceValue) value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact program_has_sufficient_native_fuel_evidence false false functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match.toMatchProfileWith) caller member represented heaps evaluated

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- A native success reconstructs an independent whole-program source run.
Source staging and raw initial-input validity are separate entry conditions. -/
theorem native_success_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {payload : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done (.inRight .word payload) finalStore) :
    ∃ sourceValue after finalMap finalWorld,
      Dynamic.ProgramEvaluates program (RecursiveNamedProgramEntrySource.entry header arguments) before sourceValue after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry functions).Represents
        finalMap finalWorld header.function.resultType sourceValue payload header.output ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact native_success_reflects_program_evidence false false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match.toMatchProfileWith) caller member represented heaps admitted heapTyped argumentsTyped capture completed

end Native

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramEntrySource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramOutcomeMeaning
/-! Whole-program successes and failures correspond to the exact retained
Header body and finite native result. Source admission and raw input validity
stay independent of native typing and decoding. Failure heaps are preserved. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramOutcomeMeaning
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

open RecursiveNamedProgramEntrySource

theorem faults_from_program (header : Header prepared values definitions program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {reason : Dynamic.SemanticFault}
    (faulted : Dynamic.ProgramFaults program (entry header arguments) before reason after) :
    Dynamic.BodyFaults program header.sourceBody header.function.evidence before arguments reason after := by
  cases faulted with
  | run admitted valid failed =>
    have same := BuiltinNamedCalls.instantiation_unique_of_wellFormed admitted.staticallyValid
      valid.instantiates header.frame.instantiated
    cases same
    exact failed

theorem program_from_faults (header : Header prepared values definitions program)
    (admitted : Staging.ProgramHasStages program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {reason : Dynamic.SemanticFault}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (failed : Dynamic.BodyFaults program header.sourceBody header.function.evidence before arguments reason after) :
    Dynamic.ProgramFaults program (entry header arguments) before reason after :=
  .run admitted (entry_valid header heapTyped argumentsTyped) failed

theorem body_from_program (header : Header prepared values definitions program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (executed : Dynamic.ProgramOutcome program (entry header arguments) before outcome after) :
    NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after := by
  cases executed with
  | value evaluated => exact .value (invokes_from_program header evaluated)
  | fault failed => exact .fault (faults_from_program header failed)

theorem program_from_body (header : Header prepared values definitions program)
    (admitted : Staging.ProgramHasStages program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (traced : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    Dynamic.ProgramOutcome program (entry header arguments) before outcome after := by
  cases traced with
  | value invoked => exact .value (program_from_invokes header admitted heapTyped argumentsTyped invoked)
  | fault failed => exact .fault (program_from_faults header admitted heapTyped argumentsTyped failed)

theorem program_iff_body (header : Header prepared values definitions program)
    (admitted : Staging.ProgramHasStages program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    Dynamic.ProgramOutcome program (entry header arguments) before outcome after ↔
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after :=
  ⟨body_from_program header, program_from_body header admitted heapTyped argumentsTyped⟩

section Evidence
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (authenticated runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith authenticated runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
theorem program_has_sufficient_native_fuel_with_evidence {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (entry header arguments) before outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  have traced := body_from_program header executed
  have owners := executed.program_well_formed.function_ids
  exact RecursiveNamedCatalogFiniteCompletion.has_sufficient_fuel_with_evidence authenticated runtime functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles caller member represented heaps traced

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every native result, including a language fault, reconstructs an admitted
source outcome with the same final heap correspondence. Fuel exhaustion is a
separate machine result and is not an input to this theorem. -/
theorem completed_run_reflects_program_with_evidence
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨outcome, after, finalMap, finalWorld, traced, result, finalHeaps, maps, worlds, administrative, metadata, finalEntry⟩ :=
    RecursiveNamedCatalogFiniteCompletion.completed_run_reflects_with_evidence authenticated runtime functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles caller member represented heaps capture completed
  exact ⟨outcome, after, finalMap, finalWorld,
    program_from_body header admitted heapTyped argumentsTyped traced,
    result, finalHeaps, maps, worlds, administrative, metadata, finalEntry⟩

end Evidence

section Common
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForMode runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
theorem program_has_sufficient_native_fuel_with {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (entry header arguments) before outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact program_has_sufficient_native_fuel_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every native result, including a language fault, reconstructs an admitted
source outcome with the same final heap correspondence. Fuel exhaustion is a
separate machine result and is not an input to this theorem. -/
theorem completed_run_reflects_program_with
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_run_reflects_program_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps admitted heapTyped argumentsTyped capture completed

end Common

section Match
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
theorem program_has_sufficient_native_fuel_match {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (entry header arguments) before outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact program_has_sufficient_native_fuel_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every native result, including a language fault, reconstructs an admitted
source outcome with the same final heap correspondence. Fuel exhaustion is a
separate machine result and is not an input to this theorem. -/
theorem completed_run_reflects_program_match
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_run_reflects_program_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps admitted heapTyped argumentsTyped capture completed

end Match

section Native
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
theorem program_has_sufficient_native_fuel {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (entry header arguments) before outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact program_has_sufficient_native_fuel_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every native result, including a language fault, reconstructs an admitted
source outcome with the same final heap correspondence. Fuel exhaustion is a
separate machine result and is not an input to this theorem. -/
theorem completed_run_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_run_reflects_program_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps admitted heapTyped argumentsTyped capture completed

end Native
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramOutcomeMeaning
end
