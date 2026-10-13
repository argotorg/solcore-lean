import Solcore.Test.SourceCoreMethodOriginEvidenceMethodCompilerSupport
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins

/-! The original cache supplies finite method observations. Its full parameter
replacement range, evidence-bearing calls, source nodes and local identities
are retained. Genuine final preparation supplies method selection separately. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedScopedMethodAdmission (Excluded RowCase)

/-- This shape signature is obtained from the original implementation's generic
signature and the actual cached replacement list. It supplies only finite shape
observations; method typing is derived from the genuine compiler selector. -/
def methodShapeSignature (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function) :
    ProgramFunctionSignature :=
  let generic := fixture.implementation.functionSignatureOfMethodWithTrait
    fixture.methodShape.trait fixture.methodShape.method
  { generic with
    parameters := generic.parameters.map fun parameter =>
      { parameter with type := named.specialized.parameterSubstitution.apply parameter.type }
    returnTypes := generic.returnTypes.map named.specialized.parameterSubstitution.apply
    scheme := {
      parameters := []
      predicates := named.specialized.assumptions
      body := named.specialized.function.type } }

structure ObservedMethodCompiler (fixture : CompiledFixture)
    (named : SourceCoreGeneralFunctions.Function)
    (rows : List SourceSpecialization.SpecializedFunction) where
  shape : MethodShape named.specialized.function (methodShapeSignature fixture named)
    named.specialized.function.inferredBodyType
  nodes : named.specialized.function.typedBody.nodes = shape.nodeList
  notOrdinary : ∀ signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions,
    named.specialized.function.typedBody.owner ≠ signature.id
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
    named.specialized.parameterSubstitution
  first : DirectSite rows shape.call.instantiation
  loop : DirectSite rows shape.loopCall.instantiation
  last : DirectSite rows shape.finalCall.instantiation

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def site (rows : List SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : IO (PLift (DirectSite rows instantiation)) :=
  match CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? rows instantiation with
  | none => throw (IO.userError "original method direct target missing")
  | some receipt => pure receipt

private def observeMethodCompiler (fixture : CompiledFixture)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) :
    IO (ObservedMethodCompiler fixture named rows) := do
  let ⟨shape, _, _, _⟩ ← observeMethod named.specialized.function (methodShapeSignature fixture named)
    named.specialized.function.inferredBodyType fixture.identitySignature fixture.identityParameter
    (.declaration fixture.mark.id)
  let ⟨nodes⟩ ← observed (named.specialized.function.typedBody.nodes = shape.nodeList)
    "original cached method source nodes"
  let ⟨different⟩ ← observed (fixture.recipe.compiled.sourceProgram.signatures.functions.all
      (fun signature => decide (named.specialized.function.typedBody.owner ≠ signature.id)) = true)
    "method owner belongs to an ordinary signature"
  let some ⟨range⟩ := CallableIndexedOwnedPreparedOrdinarySyntaxTable.range?
      fixture.recipe.compiled.sourceProgram.signatures 64 named.specialized.parameterSubstitution
    | throw (IO.userError "original full method replacement range rejected")
  let ⟨first⟩ ← site rows shape.call.instantiation
  let ⟨loop⟩ ← site rows shape.loopCall.instantiation
  let ⟨last⟩ ← site rows shape.finalCall.instantiation
  pure ⟨shape, nodes, (fun signature member =>
    of_decide_eq_true (List.all_eq_true.mp different signature member)), range, first, loop, last⟩

def MethodCompilerRow (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function)
    (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  Excluded fixture.recipe.compiled named ∨ Nonempty (ObservedMethodCompiler fixture named rows)

private def observeMethodCompilerList (fixture : CompiledFixture)
    (rows : List SourceSpecialization.SpecializedFunction) :
    (items : List SourceCoreGeneralFunctions.Function) →
      IO (PLift (∀ named ∈ items, MethodCompilerRow fixture named rows))
  | [] => pure ⟨by intro named member; cases member⟩
  | named :: rest => do
      let ⟨head⟩ ← (do
        if excluded : (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods.all
            (fun definition => decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
          pure ⟨Or.inl (fun definition member =>
            of_decide_eq_true (List.all_eq_true.mp excluded definition member))⟩
        else
          let source ← observeMethodCompiler fixture named rows
          pure ⟨Or.inr ⟨source⟩⟩ : IO (PLift (MethodCompilerRow fixture named rows)))
      let ⟨tail⟩ ← observeMethodCompilerList fixture rows rest
      pure ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

structure ObservedMethodCompilers (fixture : CompiledFixture)
    (rows : List SourceSpecialization.SpecializedFunction) : Prop where
  rows : ∀ named ∈ fixture.recipe.compiled.indexed.base.functions, MethodCompilerRow fixture named rows

def observeMethodCompilers (fixture : CompiledFixture)
    (rows : List SourceSpecialization.SpecializedFunction) : IO (PLift (ObservedMethodCompilers fixture rows)) := do
  let ⟨all⟩ ← observeMethodCompilerList fixture rows fixture.recipe.compiled.indexed.base.functions
  pure ⟨⟨all⟩⟩

/-- No operator selector is replayed. Actual final-plan provenance authenticates
this same cache row, and its accepted compilation supplies the method body. -/
theorem ObservedMethodCompilers.complete {fixture : CompiledFixture}
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table fixture.recipe.compiled)
    (sources : ObservedMethodCompilers fixture table.rows)
    (catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (index : Nat) (named : SourceCoreGeneralFunctions.Function)
    (found : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    RowCase fixture.recipe.compiled named table.rows := by
  have actual : Excluded fixture.recipe.compiled named ∨ Nonempty (ObservedMethodCompiler fixture named table.rows) :=
    sources.rows named (List.mem_of_getElem? found)
  rcases actual with excluded | original
  · exact .inl excluded
  · obtain ⟨source⟩ := original
    have retained := RecursiveNamedPreparedFinalPlanOrigins.final_member fixture.recipe.compiled found rfl
    have origin := CallablePreparedFinalCatalogOrigins.of_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared fixture.recipe.compiled) named.specialized retained
    generalize sameRow : named.specialized = row at origin
    cases origin with
    | ordinary original =>
        obtain ⟨request, signature, generic, member, _genericMember, _resolved, accepted⟩ := original
        have owner : row.function.typedBody.owner = signature.id := by
          rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1]
          change generic.typedBody.owner = signature.id
          have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
          exact identities.2.1.trans identities.1.symm
        exact False.elim (source.notOrdinary signature member ((congrArg (fun value => value.function.typedBody.owner) sameRow).trans owner))
    | @method method selected =>
        obtain ⟨diagnostics, code, cachedCode, ⟨compilation⟩⟩ :=
          CallableIndexedNamedGeneration.compiled_at fixture.recipe.compiled.indexed found
        let cached : CallablePreparedMethodSelection.Cached fixture.recipe.compiled method.specialized :=
          ⟨index, named, diagnostics, code, found, sameRow, cachedCode, compilation⟩
        have formed := catalog.formed.formed selected.implementation selected.implementationMember
          selected.declaration selected.methodMember
        have checked : CallableMethodBodyCoherence.Checked fixture.recipe.compiled.sourceProgram :=
          fixture.sameProgram.symm ▸ CallableMethodBodyCoherence.of_checked fixture.checked
        have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
            (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
            method.specialized.parameterSubstitution := by
          rw [← sameRow]
          exact source.range
        exact .inr (method_compiler_admission cached checked selected formed.parameters range
          fixture.source_wellFormed table source.shape source.nodes noLocals source.first source.loop source.last)

end Tests.SourceCoreMethodOriginEvidence
