import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics

/-! Original lambda formation retains actual diagnostic issuer tokens on used
body expressions. The current public receiving table decodes that same issuer;
a captured read keeps the original binder, occurrence and source span. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance
open CallableIndexedOwnedPublicFaultReceiverTables

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}

/-- The real named callback gives its exact token provider before recapture. -/
theorem of_prepared {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (same : code.reasonAt = header.reasonAt) : BodyReasons code header.named := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  apply BodyReasons.of_issued present
  rw [same, aligned.reasonAt, aligned.named, lowered]
  cases compiled.indexed.base.callableContext <;> rfl

/-- An authentic original read token decodes in the actual receiving table. -/
theorem uninitialized
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
    (reasons : BodyReasons code support.caller.named)
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {fuel : Nat} {context : SourceSemantics.Context} {readScope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression id))
    (receipt : CompatibleExpressionReads.LoweredRead fuel
      (.initial compiled.compatible.checked) function.source context code.reasonAt readScope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (code.reasonAt id) := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  obtain ⟨issued, present, token⟩ := reasons id reached
  obtain ⟨actual, namedCode, actualPresent, _cached, compiledCode⟩ :=
    NamedCalls.compiled_at compiled.indexed support.caller.selected
  have sameIssuer : actual = issued := Option.some.inj (actualPresent.symm.trans present)
  subst actual
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed compiledCode
  have ownFound : issued.program.base.find? support.caller.named.signature.key = some compilation.own := by
    have selected := compilation.diagnostic
    have sameBase : (match compiled.indexed.base.callableContext with
        | none => issued.program
        | some native => { issued.program with rootTable := native.diagnostics.rootTable }).base =
        issued.program.base := by cases compiled.indexed.base.callableContext <;> rfl
    exact (congrArg (fun base => base.find? support.caller.named.signature.key) sameBase).symm.trans selected
  have original : function.source = support.caller.named.specialized.function.typedBody := support.source
  have unique : NodeOccurrencesUnique support.caller.named.specialized.function.typedBody := original ▸ support.unique
  have contains : ContainsExpression support.caller.named.specialized.function.typedBody id certificate.node :=
    original ▸ lookupExpression?_sound certificate.metadata.found
  obtain ⟨read, _expression, _binder, _span, readToken, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
      (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)
      unique contains certificate.form ownFound
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (by simpa only [← readToken, ← token] using decoded)
  exact .readUninitialized location certificate.binder

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
