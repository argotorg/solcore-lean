import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStagedCalls
import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! An actual owned named Source frame and its original prepared Header select
the named body's authenticated staging scope. The global view retains the
original instantiation and complete dictionary. Independently graded staged
body traces then construct global applications without erasing nested stage
failures. Native body execution and caller restoration remain separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedPreparedHeaders
open RecursiveNamedPreparedStageScopes Staging.Recursive

private theorem closure_fields {left right : Dynamic.Closure}
    (parameters : left.parameters = right.parameters) (result : left.resultType = right.resultType)
    (body : left.body = right.body) (source : left.source = right.source)
    (captured : left.captured = right.captured) (context : left.context = right.context)
    (evidence : left.evidence = right.evidence) : left = right := by
  cases left
  cases right
  simp_all

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)

include sourceAt in
/-- This uses the actual retained global instantiation's Source frame. No
canonical substitution order or empty dictionary is substituted for it. -/
theorem global_view : globalView header.sourceBody function.evidence header.function.body = header.function := by
  exact closure_fields sourceAt.frame.parameters.symm sourceAt.frame.result.symm rfl
    sourceAt.frame.source.symm sourceAt.frame.captured.symm sourceAt.frame.context.symm sourceAt.dictionary.symm

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row) {instantiation : DeclarationInstantiation}
  (aligned : Prepared.HeaderAt prepared instantiation header)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))

include aligned in
/-- The full actual cached Header record and preparation identify the selected
row. A key or erased native type does not stand in for that record. -/
theorem record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan row.key = .ok row := by
  have selected := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  rw [aligned.named, prepared.same, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared] at selected
  exact selected

include sourceAt aligned actual descriptor in
/-- The descriptor's authenticated original sidecar selects this exact retained
global view. Declaration substitution, stage analysis and full evidence are
fields of the selected child scope, independent of the caller's stage markers. -/
theorem selected :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar ∧
      sidecar.caller = row ∧
      (registry actual).Closure (globalView header.sourceBody function.evidence header.function.body)
        (RecursiveStageRegistry.scope sidecar [] header.function) ∧
      (RecursiveStageRegistry.scope sidecar [] header.function).origin.declarationSubstitution = row.parameterSubstitution ∧
      (RecursiveStageRegistry.scope sidecar [] header.function).origin.localSubstitution = [] ∧
      (RecursiveStageRegistry.scope sidecar [] header.function).evidence = function.evidence ∧
      (RecursiveStageRegistry.scope sidecar [] header.function).guards.stages.callerReturnComptime = row.function.returnComptime ∧
      SourceStageAnalysis.analyzeFunction row.function = .ok row.stageAnalysis := by
  have actualDescriptor : SourceCoreCallableContracts.Descriptor native.table (.named row.key) := by
    simpa only [aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared] using descriptor
  obtain ⟨sidecar, issued, same, related⟩ := selected_of_descriptor actual prepared (record prepared aligned) actualDescriptor
  refine ⟨sidecar, issued, same, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [global_view sourceAt, aligned.function]
    exact related
  · simp only [RecursiveStageRegistry.scope_declarationSubstitution, same]
  · exact sourceAt.dictionary
  · simp only [RecursiveStageRegistry.scope_returnMarker, same]
  · simpa only [same] using sidecar.analyzed

include sourceAt in
/-- Ordered Source allocation and an independently measured recursively staged
body produce the original global application. The entire heap, outcome and
nested failure scope are retained; no ordinary body trace is used. -/
theorem applies
    {caller child : Scope} {context bodyContext finalContext : Context}
    {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    {types : List TypeSystem.Ty} {outcome : BodyOutcome} {result : Outcome} {bodySize : Nat}
    (selected : (registry actual).Closure header.function child)
    (parameters : MonoBindersExtend header.function.source.owner header.function.context
      header.function.parameters types bodyContext)
    (allocate : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (body : Size.Statements (Program.ofChecked compiled.sourceProgram) (registry actual)
      bodySize child bodyContext environment bound header.function.body finalContext outcome after)
    (converted : BodyResult header.function.resultType outcome result) :
    Size.Applies (Program.ofChecked compiled.sourceProgram) (registry actual) (Size.stepSize [bodySize])
      caller context before (.global function) arguments result after := by
  have actualParameters : MonoBindersExtend header.sourceBody.source.owner header.sourceBody.context
      header.sourceBody.source.inputs types bodyContext := by
    simpa only [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] using parameters
  have actualAllocate : Dynamic.BindersAllocate [] before header.sourceBody.source.inputs arguments environment bound :=
    sourceAt.frame.parameters ▸ allocate
  have actualResult : BodyResult header.sourceBody.resultType outcome result := sourceAt.frame.result ▸ converted
  exact Size.Applies.global sourceAt.frame.instantiated (sourceAt.dictionary ▸ sourceAt.frame.covers)
    sourceAt.frame.roots ((global_view sourceAt).symm ▸ selected) actualParameters actualAllocate body actualResult

include sourceAt in
/-- The authentic Source frame determines named arity failure independently of
packed native parameters. No callee scope or body execution is needed. -/
theorem arity_failure {caller : Scope} {context : Context} {heap : Dynamic.Heap} {arguments : List Dynamic.Value}
    (mismatch : header.function.parameters.length ≠ arguments.length) :
    Size.Applies (Program.ofChecked compiled.sourceProgram) (registry actual) (Size.stepSize [])
      caller context heap (.global function) arguments
      (.fault (.semantic (.argumentArityMismatch header.function.parameters.length arguments.length))) heap := by
  rw [sourceAt.frame.parameters] at mismatch ⊢
  exact Size.Applies.globalArity sourceAt.frame.instantiated mismatch

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
