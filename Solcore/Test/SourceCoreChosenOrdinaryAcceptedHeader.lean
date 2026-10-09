import Solcore.Test.SourceCoreChosenOrdinaryAcceptedFixture
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient

/-! An actual named Header for the accepted fixture. Original worklist selection
and executable-plan growth authenticate the complete specialization. The finite
metadata check and independent graph/ledger receipt supply its Source context;
no program body meaning or native-code provenance is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedHeader
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering Core
open CallableIndexedNamedGeneration
open Tests.SourceCoreChosenOrdinaryAcceptedFixture

/-- The selected row belongs to the original successful worklist action. -/
structure OriginalSelection (packet : Packet) where
  row : SourceSpecialization.SpecializedFunction
  accepted : SourceCompilationPlan.exactSpecialization packet.plan packet.named.signature.key = .ok row

def originalSelection (packet : Packet) : Except String (OriginalSelection packet) :=
  match accepted : SourceCompilationPlan.exactSpecialization packet.plan packet.named.signature.key with
  | .error error => .error s!"original worklist selection: {reprStr error}"
  | .ok row => .ok ⟨row, accepted⟩

/-- The prepared plan preserves the entire original row, not just its key. -/
theorem OriginalSelection.same (packet : Packet) (selected : OriginalSelection packet) :
    selected.row = packet.named.specialized := by
  obtain ⟨programEq, planEq, _⟩ := SourceCoreUnifiedPreparationCertificates.prepare_fields packet.compiledAccepted
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared packet.compiled
  rw [programEq, planEq] at prepared
  obtain ⟨growth, _⟩ := CallableCoercionPreparation.of_accepted prepared
  have retained := growth.selected _ _ selected.accepted
  exact Except.ok.inj (retained.symm.trans packet.named_record)

theorem OriginalSelection.origin (packet : Packet) (selected : OriginalSelection packet) :
    RecursiveNamedPublicSpecializationMeaning.Origin packet.compiled.sourceProgram packet.named.specialized := by
  have member := (CallableNamedMetadata.specialization_of_exact selected.accepted).1
  have origin := RecursiveNamedPublicSpecializationMeaning.worklist_origins packet.worklist selected.row member
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields packet.compiledAccepted).1
  simpa only [programEq, selected.same packet] using origin

/-- Every field is checked on the unchanged selected named row. -/
structure Metadata (packet : Packet) : Prop where
  owner : (source packet.named).owner = packet.named.specialized.declaration
  inputs : (source packet.named).inputs = []
  substitution : packet.named.specialized.parameterSubstitution = []
  assumptions : packet.named.specialized.assumptions = []
  ordinary : packet.named.specialized.function.returnComptime = false
  parameter : packet.named.signature.parameterType = .unit
  target : SourceCompilationPlan.exactInstantiationKey packet.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation packet.named.specialized) = .ok packet.named.signature.key

def metadata (packet : Packet) : Except String (PLift (Metadata packet)) := do
  if owner : (source packet.named).owner = packet.named.specialized.declaration then
    if inputs : (source packet.named).inputs = [] then
      if substitution : packet.named.specialized.parameterSubstitution = [] then
        if assumptions : packet.named.specialized.assumptions = [] then
          if ordinary : packet.named.specialized.function.returnComptime = false then
            if parameter : packet.named.signature.parameterType = .unit then
              match target : SourceCompilationPlan.exactInstantiationKey packet.compiled.indexed.base.plan
                  (CallableNamedMetadata.instantiation packet.named.specialized) with
              | .error error => throw s!"actual instantiation target: {reprStr error}"
              | .ok key =>
                if same : key = packet.named.signature.key then
                  pure ⟨⟨owner, inputs, substitution, assumptions, ordinary, parameter, by simpa only [same] using target⟩⟩
                else throw "actual instantiation target has another named key"
            else throw "actual named parameter type is not unit"
          else throw "actual named return is staged"
        else throw "actual named assumptions are nonempty"
      else throw "actual named substitution is nonempty"
    else throw "actual named inputs are nonempty"
  else throw "actual Source owner disagrees with the specialization"

theorem Metadata.named_inputs {packet : Packet} (checked : Metadata packet) : packet.named.inputs = [] := by
  have same := (RecursiveNamedPreparedParameterProjections.cached_inputs packet.compiled packet.namedSelected).1
  change packet.named.inputs.map Prod.fst = (source packet.named).inputs at same
  rw [checked.inputs] at same
  exact List.map_eq_nil_iff.mp same

/-- The named declaration context is exactly the already validated context. -/
theorem Metadata.view_context {packet : Packet} (checked : Metadata packet) (statements : List StatementId) :
    (RecursiveNamedPreparedSourceFrames.view packet.compiled.sourceProgram packet.named statements).context =
      runtimeContext packet := by
  simp only [RecursiveNamedPreparedSourceFrames.view, RecursiveNamedSpecializationBodyFacts.bodyInstance,
    runtimeContext, checked.assumptions, checked.owner]

abbrev ActualHeader (fixture : AcceptedFixture) :=
  CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled (Program.ofChecked fixture.packet.compiled.sourceProgram)

/-- This is the original named-body callback, with its actual retained fields. -/
def policy (fixture : AcceptedFixture) : SourceCoreLoops.Policy :=
  let packet := fixture.packet
  let actual := (representation packet.compiled.indexed).atContext packet.named.signature.key []
  let diagnostics := effectiveDiagnostics packet.compiled packet.diagnostics
  let expression := SourceCoreGeneralFunctions.lowerContextualExpression packet.compiled.indexed.base.sourceProgram actual
    packet.compiled.indexed.base.sourceProgram.signatures packet.compiled.indexed.base.locals fixture.calls.parents
    fixture.calls.own.assignments diagnostics (context packet.compiled.indexed packet.named)
    packet.compiled.indexed.base.callableContext none none
  { actual.loopsWithSourceCells actual.expressions.sourceCells packet.named.specialized.function.solvedRequirements
      fixture.calls.own.assignments diagnostics packet.named.signature.key expression with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual packet.compiled.indexed.base.locals packet.named.signature.key [] }

/-- The returned Header retains the original accepted body, prefix and hook. -/
structure HeaderAt (fixture : AcceptedFixture) (header : ActualHeader fixture) : Prop where
  named : header.named = fixture.packet.named
  source : header.function.source = source fixture.packet.named
  context : header.context = runtimeContext fixture.packet
  functionContext : header.function.context = runtimeContext fixture.packet
  parameters : header.function.parameters = []
  bindings : header.bindings = fixture.packet.named.inputs
  body : header.body = fixture.calls.body
  parameterCode : header.parameterCode = fixture.tail.parameters
  code : header.code = fixture.tail.output
  slot : header.slot = 0
  ledger : header.solved = fixture.packet.named.specialized.function.solvedRequirements
  fuel : header.fuel = 500
  readFuel : header.readFuel = 500
  statements : header.function.body = [statementId fixture.packet 0, statementId fixture.packet 4]
  policy : header.policy = policy fixture
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map fun binding => (binding.1.id, binding.2)) header.function.body header.output
    header.reasonAt header.fellThrough header.escaped = .ok header.body

/-- The source frame uses original specialization and preparation receipts. -/
theorem source_frame (fixture : AcceptedFixture) (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet)
    (compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode) :
    NamedCalls.SourceFrame (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (CallableNamedMetadata.instantiation fixture.packet.named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance fixture.packet.compiled.sourceProgram fixture.packet.named.specialized)
      (RecursiveNamedPreparedSourceFrames.view fixture.packet.compiled.sourceProgram fixture.packet.named compilation.statements) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, specialized⟩ := selected.origin fixture.packet
  have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
  have catalog := SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked
  rw [← programEq] at catalog
  have unique := (catalog.function_parameters signature signatureMember).1
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.packet.compiled.sourceProgram.signatures)
      fixture.packet.named.specialized.parameterSubstitution := by
    rw [checked.substitution]
    intro entry replacement member
    cases member
  obtain ⟨row, _, prepared⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation
    fixture.packet.compiled fixture.packet.namedSelected
  exact (RecursiveNamedSpecializationValidity.of_compilation signatureMember genericMember specialized unique range
    checked.assumptions prepared compilation).2

/-- Actual accepted compiler receipts and independent finite Source validity
construct the Header. The sealed Compilation is eliminated only into Prop. -/
theorem header_exists (fixture : AcceptedFixture) (selected : OriginalSelection fixture.packet)
    (checked : Metadata fixture.packet) : ∃ header : ActualHeader fixture, HeaderAt fixture header := by
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
  refine ⟨header, ⟨rfl, rfl, rfl, sameContext, parameters, rfl, bodyEq, parametersEq, outputEq, rfl, rfl,
    fixture.calls.fuel, fixture.calls.fuel, statementsEq, rfl, ?_⟩⟩
  simpa only [header, function, RecursiveNamedPreparedSourceFrames.view, ownEq, statementsEq, bodyEq,
    CallableIndexedNamedGeneration.source, bodyAction, SourceCoreGeneralFunctions.bodyLowererWithRepresentation,
    policy] using fixture.calls.bodyCompiled

theorem source_runtime_at_header (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) :
    Dynamic.SourceRuntimeValid (Program.ofChecked fixture.packet.compiled.sourceProgram) header.context header.function.source := by
  rw [atHeader.context, atHeader.source]
  exact fixture.runtime.source_runtime

/-- The executable checks retain original compiler provenance and finite
metadata. The actual Header is constructed by the theorem below. -/
structure HeaderFixture where
  fixture : AcceptedFixture
  selected : OriginalSelection fixture.packet
  checked : Metadata fixture.packet

def acceptedHeaderFixture : Except String HeaderFixture := do
  let fixture ← acceptedFixture
  let selected ← originalSelection fixture.packet
  let checked ← metadata fixture.packet
  pure ⟨fixture, selected, checked.down⟩

theorem HeaderFixture.header (given : HeaderFixture) :
    ∃ header : ActualHeader given.fixture, HeaderAt given.fixture header :=
  header_exists given.fixture given.selected given.checked

theorem HeaderFixture.runtime (given : HeaderFixture) :
    ∃ header : ActualHeader given.fixture, HeaderAt given.fixture header ∧
      Dynamic.SourceRuntimeValid (Program.ofChecked given.fixture.packet.compiled.sourceProgram)
        header.context header.function.source := by
  obtain ⟨header, atHeader⟩ := given.header
  exact ⟨header, atHeader, source_runtime_at_header given.fixture atHeader⟩

theorem Metadata.initial_scope {packet : Packet} (checked : Metadata packet) : initialScope packet = [] := by
  simp only [initialScope, checked.named_inputs, List.reverse_nil, List.map_nil]

def run : IO Unit := do
  match acceptedHeaderFixture with
  | .error error => throw (IO.userError error)
  | .ok _ =>
    IO.println "accepted Header fixture: original worklist row and compiler metadata checks passed; Header and its exact Source runtime context are constructed by the kernel proofs"

end Tests.SourceCoreChosenOrdinaryAcceptedHeader
