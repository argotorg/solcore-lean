import Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence

/-! Retain bootstrap layout and empty Source lexical capture from the same
authentic Header constructor, together with its existing runtime evidence.
Native installer captures keep their actual globals and frame references. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering Core
open CallableIndexedNamedGeneration
open Tests.SourceCoreChosenOrdinaryAcceptedFixture
open Tests.SourceCoreChosenOrdinaryAcceptedHeader
open Tests.SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence

/-- Bootstrap fields retained by the same authentic Header constructor. -/
structure BootstrapEvidence (fixture : AcceptedFixture) (header : ActualHeader fixture) : Prop
    extends RuntimeEvidence fixture header where
  layouts : header.layouts = fixture.packet.compiled.indexed.layouts
  captured : header.function.captured = []

/-- The genuine selected Compilation is eliminated only into this Prop receipt.
All fields belong to the one original Header constructor. -/
theorem header_exists_with_bootstrap (fixture : AcceptedFixture) (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet) : ∃ header : ActualHeader fixture, BootstrapEvidence fixture header := by
  obtain ⟨compilation⟩ := fixture.packet.named_compilation
  let function := RecursiveNamedPreparedSourceFrames.view fixture.packet.compiled.sourceProgram fixture.packet.named compilation.statements
  have frame := source_frame fixture selected checked compilation
  obtain ⟨row, _, prepared⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation
    fixture.packet.compiled fixture.packet.namedSelected
  have agreement := RecursiveNamedPreparedSourceFrames.agreement prepared compilation
  have namedInputs := checked.named_inputs
  have parameters : function.parameters = [] := checked.inputs
  have sameContext : function.context = runtimeContext fixture.packet := checked.view_context compilation.statements
  have extended : MonoBindersExtend function.source.owner function.context function.parameters [] (runtimeContext fixture.packet) := by
    rw [parameters, sameContext]
    exact .nil _
  have valid : CompatibleRuntimeContextValidity.Valid fixture.packet.named.specialized.function.solvedRequirements
      (runtimeContext fixture.packet) function.evidence := by
    refine ⟨rfl, ?_, ?_⟩
    · exact fixture.runtime.source_runtime.requirements
    · have covers := RecursiveNamedPreparedSourceFrames.empty_covers (program := fixture.packet.compiled.sourceProgram) checked.assumptions
      rw [← sameContext]
      exact covers
  have unique : NodeOccurrencesUnique function.source := fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
  have parameterType : fixture.packet.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (fixture.packet.named.inputs.map Prod.snd) := by
    rw [namedInputs, List.map_nil]
    exact checked.parameter
  let header := RecursiveNamedCatalog.Header.of_dictionary_body
    (values := .initial fixture.packet.compiled.compatible.checked)
    (function := function) (instantiation := CallableNamedMetadata.instantiation fixture.packet.named.specialized)
    (sourceBody := RecursiveNamedSpecializationBodyFacts.bodyInstance fixture.packet.compiled.sourceProgram fixture.packet.named.specialized)
    (frame := frame) (named := fixture.packet.named) (agreement := agreement)
    (ordinaryReturn := checked.ordinary) (ordinaryParameters := by intro binder member; rw [parameters] at member; cases member)
    (target := checked.target) (context := runtimeContext fixture.packet) (types := []) (bindings := fixture.packet.named.inputs)
    (parameters := agreement.parameters) (inputs := agreement.parameters) (extended := extended)
    (solved := fixture.packet.named.specialized.function.solvedRequirements)
    (reasonAt := (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
    (readFuel := fixture.packet.compiled.indexed.fuel) (output := fixture.packet.named.signature.resultType)
    (policy := policy fixture)
    (fuel := fixture.packet.compiled.indexed.fuel) (fellThrough := compilation.own.fellThroughReason)
    (escaped := compilation.own.table.escapedReason) (body := compilation.body) (parameterCode := compilation.parameterCode)
    (code := compilation.output) (layouts := fixture.packet.compiled.indexed.layouts)
    (owner := fixture.packet.named.signature.key) (active := []) (globals := fixture.packet.compiled.indexed.base.globals.length)
    (onError := fun error => .sourceAllocation (reprStr error)) (acceptedPrefix := compilation.parametersCompiled)
    (hook := compilation.hook) (definitions_eq := rfl) (registered := CallableIndexedAmbient.frame_registered fixture.packet.compiled.indexed)
    (valid := valid) (unique := unique) (parameterType := parameterType) (resultType := rfl)
    (representation := representation fixture.packet.compiled.indexed) (compiledFuel := fixture.packet.compiled.indexed.fuel)
    (compiled := fixture.packet.compiled.indexed.secondPass) (slot := 0) (selected := fixture.packet.namedSelected)
    (cached := fixture.packet.cached.trans (congrArg some compilation.emitted))
  obtain ⟨parentsEq, ownEq, statementsEq, bodyEq⟩ := fixture.calls.compilation_alignment compilation
  obtain ⟨parametersEq, outputEq⟩ := fixture.tail.compilation_alignment compilation
  refine ⟨header, ⟨⟨?_, rfl, rfl⟩, rfl, rfl⟩⟩
  refine ⟨rfl, rfl, rfl, sameContext, parameters, rfl, bodyEq, parametersEq, outputEq, rfl, rfl,
    fixture.calls.fuel, fixture.calls.fuel, statementsEq, rfl, ?_⟩
  simpa only [header, function, RecursiveNamedPreparedSourceFrames.view, ownEq, statementsEq, bodyEq,
    CallableIndexedNamedGeneration.source, bodyAction, SourceCoreGeneralFunctions.bodyLowererWithRepresentation,
    policy] using fixture.calls.bodyCompiled

/-- The checked fixture supplies the same authentic Header and runtime facts. -/
theorem header_fixture_with_bootstrap (given : HeaderFixture) :
    ∃ header : ActualHeader given.fixture,
      BootstrapEvidence given.fixture header :=
  header_exists_with_bootstrap given.fixture given.selected given.checked

end Tests.SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
