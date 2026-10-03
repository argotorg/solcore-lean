import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping

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
