import Solcore.Test.SourceCoreSelectedCoercedDirectFixture
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)

structure HeaderFacts {compiled : SourceCoreUnifiedCompilation.Compiled}
    (row : SourceSpecialization.SpecializedFunction) (available : SourceTypedRuntime.RuntimeEvidenceEnvironment)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) : Prop where
  source : header.function.source = row.function.typedBody
  result : header.function.resultType = row.function.inferredBodyType
  metadata : header.instantiation = CallableNamedCanonicalOrder.retainedInstantiation row
  signatures : header.context.signatures = compiled.sourceProgram.signatures
  ledger : header.context.solvedRequirements = row.function.solvedRequirements
  assumptions : header.context.assumptions = row.assumptions
  evidence : header.function.evidence = CallableNamedMetadata.environment available

theorem header_facts {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
    (packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input)
    {row : SourceSpecialization.SpecializedFunction} (sameRow : input.row = row)
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram row.key row.assumptions = .ok available) :
    HeaderFacts row available packet.header := by
  have extension := packet.header.extended
  rw [packet.function] at extension
  have fields := RecursiveNamedPreparedCallEvidence.Prepared.context_fields input.prepared extension
  have evidence : input.prepared.available = available := by
    have actual := input.prepared.resolved
    have actual : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram row.key row.assumptions = .ok input.prepared.available :=
      Eq.mp (congrArg (fun r => SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram r.key r.assumptions = .ok input.prepared.available) sameRow) actual
    exact Except.ok.inj (actual.symm.trans resolved)
  refine ⟨?_, ?_, ?_, fields.1, ?_, ?_, ?_⟩
  · rw [packet.function]
    change input.prepared.named.specialized.function.typedBody = row.function.typedBody
    rw [input.prepared.same, sameRow]
  · rw [packet.function]
    change input.prepared.named.specialized.function.inferredBodyType = row.function.inferredBodyType
    rw [input.prepared.same, sameRow]
  · exact packet.aligned.metadata.trans (congrArg _ sameRow)
  · simpa only [sameRow] using fields.2.1
  · simpa only [sameRow] using fields.2.2
  · rw [packet.function]
    change CallableNamedMetadata.environment input.prepared.available = _
    rw [evidence]

def Fixture.shapeAt (fixture : Fixture) {header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (facts : HeaderFacts fixture.make.named.specialized fixture.available header) : Shape header.function.source where
  binder := fixture.shape.binder
  read := fixture.shape.read.node
  call := fixture.shape.call.node
  inner := fixture.shape.innerReturn
  lambda := fixture.shape.expression.node
  outer := fixture.shape.statement
  inputs := by rw [facts.source]; exact fixture.shape.inputs
  binderType := fixture.makeBinder
  roots := by rw [facts.source]; exact fixture.shape.roots
  readFound := by rw [facts.source]; exact fixture.shape.read.found
  readForm := fixture.shape.read.form
  readRequirements := fixture.shape.read.requirements
  readCoercions := fixture.shape.read.coercions
  innerFound := by rw [facts.source]; exact fixture.shape.innerReturnFound
  innerForm := fixture.shape.innerReturnForm
  lambdaFound := by rw [facts.source]; exact fixture.shape.expression.found
  lambdaForm := fixture.shape.lambda
  lambdaRequirements := fixture.shape.expression.requirements
  lambdaCoercions := fixture.shape.expression.coercions
  outerFound := by rw [facts.source]; exact fixture.shape.statementFound
  outerForm := fixture.shape.statementForm

/-- All semantic selection data are derived before invocation from the actual
checker, selected cache and original evidence actions. -/
theorem Fixture.method_certificate (fixture : Fixture) (issued : Profiled fixture.recipe) :
    ∃ types lexical facts, Dynamic.BodyInstanceTypingCertificate
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (CallableCoercionMethodInstantiation.bodyInstance fixture.recipe.compiled.sourceProgram fixture.method)
      types lexical facts := by
  obtain ⟨receipt⟩ := CallableCoercionSourceSelection.of_accepted fixture.methodSelected
  exact SelectedCompilationRegistryMethodCertificates.of_origin issued.support.bodyTyping fixture.checked
    (SelectedCompilationRegistryMethodCertificates.ranges_of_profile fixture.profile)
    receipt.selected.toSelection fixture.methodMember

def converted (flag : Bool) : Word := if flag then Word.ofNatModulo 41 else Word.ofNatModulo 7

def convertedHeap (flag : Bool) : Dynamic.Heap := appendBool (appendBool (capturedHeap flag) flag) flag

/-- Independently execute the original captured read, generic named call and
complete conversion suffix. No staged or completed native trace is used. -/
theorem Fixture.closure_plain (fixture : Fixture) (issued : Profiled fixture.recipe)
    {makeHeader keepHeader : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available makeHeader)
    (keepFacts : HeaderFacts fixture.keep.named.specialized fixture.dictionary keepHeader)
    {context : SourceSemantics.Context} (invocation : Staging.Recursive.Scope) (flag : Bool)
    (signatures : context.signatures = fixture.recipe.compiled.sourceProgram.signatures)
    (typed : Dynamic.ValueHasType context (capturedHeap flag)
      (.closure (capturedFunction makeHeader (fixture.shapeAt makeFacts))) (.function .unit .word)) :
    Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) context invocation.evidence
      (capturedFunction makeHeader (fixture.shapeAt makeFacts)).evidence (capturedHeap flag)
      (.closure (capturedFunction makeHeader (fixture.shapeAt makeFacts))) []
      (.word (converted flag)) (convertedHeap flag) := by
  obtain ⟨_parameters, _result, sameSignatures, code, covers, _captures⟩ := typed.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (capturedFunction makeHeader (fixture.shapeAt makeFacts)) :=
    ⟨sameSignatures.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  have certified := SelectedCompilationHeaderCertificates.certified issued.support.bodyTyping makeHeader
  have runtime := certified.runtime.transport (RecursiveNamedInitialContextValidity.mono_fields makeHeader.extended)
  have binders : TypeParameterBindersWellFormed makeHeader.context := by
    simp [TypeParameterBindersWellFormed, runtime.closed]
  have metadata : keepHeader.instantiation = fixture.shape.call.instantiation :=
    keepFacts.metadata.trans fixture.target.symm
  have valid : SourceSemantics.DeclarationInstantiation.Valid makeHeader.context fixture.shape.call.instantiation := by
    rw [← metadata]
    have supports := CallableCoercionRawNamedCallAdmission.catalog_supports makeFacts.signatures binders
    cases keepHeader.frame.instantiated with
    | intro _ _ _ _ valid _ _ _ =>
      exact Dynamic.DeclarationInstantiation.Valid.transportContext supports valid
  have produced := CallableCallRequirementLayouts.direct_produces makeFacts.signatures makeFacts.ledger
    (fun goal member => makeFacts.assumptions.symm ▸ member) fixture.resolved fixture.direct fixture.authenticated
  have produced : Dynamic.DirectCallProducesEvidence makeHeader.context makeHeader.function.evidence
      fixture.shape.call.node.requirements fixture.shape.call.node.coercions fixture.shape.call.instantiation.predicates
      keepHeader.function.evidence := by
    rw [makeFacts.evidence, keepFacts.evidence]
    exact produced
  have chosen := SelectedCompilationClosedCoercionSourceSelection.selects
    (CallableMethodBodyCoherence.of_checked fixture.checked) fixture.closed.catalog
    fixture.methodSelected fixture.resolved fixture.materialized makeFacts.signatures makeFacts.ledger
    (fun goal member => makeFacts.assumptions.symm ▸ member)
  have chosen : Dynamic.OperatorMethodSelected (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      makeHeader.context makeHeader.function.evidence "Coerce" "coerce" fixture.shape.call.step.requirements
      (CallableCoercionMethodInstantiation.bodyInstance fixture.recipe.compiled.sourceProgram fixture.method)
      (CallableNamedMetadata.environment fixture.methodDictionary) := by
    rw [makeFacts.evidence]
    exact chosen
  obtain ⟨types, lexical, facts, methodCertificate⟩ := fixture.method_certificate issued
  have methodRuntime := methodCertificate.sourceRuntimeValid.transport
    (RecursiveNamedInitialContextValidity.mono_fields methodCertificate.typing.inputs_extend)
  have ledger : lexical.solvedRequirements = fixture.method.specialized.function.solvedRequirements := by
    exact (RecursiveNamedInitialContextValidity.mono_fields methodCertificate.typing.inputs_extend).solvedRequirements
  have methodCovers : (CallableNamedMetadata.environment fixture.methodDictionary).Covers
      (CallableCoercionMethodInstantiation.bodyInstance fixture.recipe.compiled.sourceProgram fixture.method).context := by
    cases chosen with | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covered => exact covered
  have invoked := method_plain (program := Program.ofChecked fixture.recipe.compiled.sourceProgram) fixture.methodShape rfl methodCertificate.typing.inputs_extend fixture.methodBinder
    ledger methodRuntime.requirements methodCovers (appendBool (capturedHeap flag) flag) flag
  have invoked : Dynamic.BodyInvokes (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (CallableCoercionMethodInstantiation.bodyInstance fixture.recipe.compiled.sourceProgram fixture.method)
      (CallableNamedMetadata.environment fixture.methodDictionary) (appendBool (capturedHeap flag) flag) [.bool flag]
      (.word (converted flag)) (convertedHeap flag) := by
    simpa only [fixture.firstValue, fixture.secondValue, converted, convertedHeap] using invoked
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      makeHeader.context makeHeader.function.evidence makeHeader.function.source
      [(fixture.shape.binder.id, ⟨0⟩)] (capturedHeap flag) fixture.shape.read.node.id (.bool flag) (capturedHeap flag) := by
    rw [makeFacts.source]
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound fixture.shape.read.found)
    · rw [fixture.shape.read.form]
      exact .local (by rw [fixture.shape.read.requirements, fixture.shape.read.coercions]; rfl) .head
        (Dynamic.Heap.Allocates.reads_new (Dynamic.Heap.Allocates.append (heap := ⟨[]⟩)
          (type := .bool) (value := some (.bool flag)))) rfl rfl
    · rw [fixture.shape.read.coercions]; exact .nil
  have called := identity_plain keepHeader fixture.identity keepFacts.source fixture.keepBinder
    (context := makeHeader.context) (evidence := makeHeader.function.evidence) (capturedHeap flag) flag
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      makeHeader.context makeHeader.function.evidence makeHeader.function.source
      [(fixture.shape.binder.id, ⟨0⟩)] (capturedHeap flag) fixture.shape.call.node.id
      (.word (converted flag)) (convertedHeap flag) := by
    apply Dynamic.ExpressionEvaluates.intro (by rw [makeFacts.source]; exact lookupExpression?_sound fixture.shape.call.found)
    · rw [fixture.shape.call.form]
      apply Dynamic.ExpressionFormEvaluates.directCall
        (by rw [makeFacts.source]; exact lookupExpression?_sound fixture.shape.call.callee.found)
        fixture.shape.call.calleeForm fixture.shape.call.callee.requirements fixture.shape.call.callee.coercions
        valid (.cons read .nil) produced
      simpa only [metadata] using called
    · rw [fixture.shape.call.coercions]
      exact .cons (.method chosen invoked) .nil
  have executed : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      makeHeader.context makeHeader.function.evidence makeHeader.function.source
      [(fixture.shape.binder.id, ⟨0⟩)] (capturedHeap flag) [fixture.shape.innerReturn.id] makeHeader.context
      (.returned (.word (converted flag))) (convertedHeap flag) := by
    exact .singleton (by rw [makeFacts.source]; exact lookupStatement?_sound fixture.shape.innerReturnFound)
      (by rw [fixture.shape.innerReturnForm]; intro id impossible; cases impossible)
      (.returnValue (by rw [makeFacts.source]; exact lookupStatement?_sound fixture.shape.innerReturnFound)
        fixture.shape.innerReturnForm expression)
  exact .closure rfl frame (.nil _) (.nil _ _) executed rfl

end Tests.SourceCoreSelectedCoercedDirect
