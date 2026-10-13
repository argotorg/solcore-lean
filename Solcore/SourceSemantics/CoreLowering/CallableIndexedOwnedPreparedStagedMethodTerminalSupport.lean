import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads

/-! The real cached method compiler retains its diagnostic issuer. Local-read
roots use that issuer and the current public receiver; the full method Source
and dictionary remain those of the genuine trait principal. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallablePreparedMethodSelection (Cached)
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport (Packet)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}

/-- The complete original program diagnostic table of this exact cache row. -/
structure DiagnosticAt (cached : Cached compiled row) : Prop where
  actual : ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
    compiled.indexed.base.diagnostics = some diagnostics ∧
    cached.diagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}

/-- The actual second pass returns both the method cache and its issuer.
This constructor never identifies methods with ordinary Source declarations. -/
theorem cached_at {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) :
    ∃ cached : Cached compiled row, cached.index = index ∧ cached.named = named ∧ DiagnosticAt cached := by
  obtain ⟨diagnostics, code, actual, found, accepted⟩ := NamedCalls.compiled_at compiled.indexed selected
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed accepted
  let cached : Cached compiled row := ⟨index, named, _, code, selected, same, found, compilation⟩
  exact ⟨cached, rfl, rfl, ⟨diagnostics, actual, rfl⟩⟩

variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method) (diagnostic : DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)

include diagnostic receiver in
/-- The exact actual method row issues the original read occurrence and span. -/
theorem decoded_read
    (unique : NodeOccurrencesUnique principal.sourceBody.source)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : Expr}
    (certificate : CompatibleExpressionReads.Certificate fuel (.initial compiled.compatible.checked)
      principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key id) code) :
    completion.result.diagnostics.diagnostic? (principal.cached.diagnostics.reasonAt principal.named.signature.key id) = some {
      error := .uninitializedLocal certificate.binder
      site := .occurrence id.occurrence
      span := some certificate.node.span } := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  have source : principal.sourceBody.source = principal.named.specialized.function.typedBody := principal.source_eq.symm
  have unique : NodeOccurrencesUnique principal.named.specialized.function.typedBody := source ▸ unique
  have contains : ContainsExpression principal.named.specialized.function.typedBody id certificate.node :=
    source ▸ lookupExpression?_sound certificate.metadata.found
  have sameBase : principal.cached.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  have ownFound := principal.cached.compilation.diagnostic
  rw [sameBase] at ownFound
  have reasonEq : principal.cached.diagnostics.reasonAt principal.named.signature.key id =
      issued.program.reasonAt principal.named.signature.key id := by
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  obtain ⟨_read, _expression, _binder, _span, readToken, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic
      compiled receiver present principal.record unique contains certificate.form ownFound
  simpa only [← readToken, ← reasonEq] using decoded

include diagnostic receiver in
/-- Every actual lowered method read obtains its fault meaning from the real
current receiver, retaining the Source location in the independent trace. -/
theorem uninitialized
    (unique : NodeOccurrencesUnique principal.sourceBody.source)
    {fuel : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (read : CompatibleExpressionReads.LoweredRead fuel (.initial compiled.compatible.checked)
      principal.sourceBody.source context (principal.cached.diagnostics.reasonAt principal.named.signature.key) scope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (principal.cached.diagnostics.reasonAt principal.named.signature.key id) := by
  obtain ⟨certificate, _type, _binding⟩ := read
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  exact CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (decoded_read principal diagnostic receiver unique certificate) (.readUninitialized location certificate.binder)

/-- The finite original method graph contains only local reads. The fixture
proves this from its actual node table, including input occurrences. -/
def ReadOnlySource (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node →
    ∃ name binder, node.form = .reference name (.local binder)

variable (packet : Packet principal)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (reads : ReadOnlySource principal.sourceBody.source)
  {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
  (found : principal.sourceBody.source.lookupExpression? packet.expression = some node)
  (form : node.form = .reference name (.local binder))
  (requirements : node.requirements = []) (coercions : node.coercions = [])
  (ordinary : compiled.indexed.base.locals.bindings.any (fun binding =>
    decide (binding.caller = principal.named.signature.key ∧ binding.binder.id = binder)) = false)
  (notInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = principal.named.signature.key ∧ binding.initializer = packet.expression)) = none)

include diagnostic receiver wellFormed reads found form requirements coercions ordinary notInitializer in
/-- A genuine terminal read supplies the exact physical method root. Every
excluded call is ruled out by original Source lookup, not certificate identity. -/
theorem of_read_child
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child) :
    Nonempty (CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Child principal packet headers stages child
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨actual, childFound, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.child_typed principal packet wellFormed selected
  have same := Option.some.inj (childFound.symm.trans (sourceEq ▸ found))
  subst actual
  have originalTyped : ExpressionHasType principal.sourceBody.source packet.sourceAt.context packet.expression node.type :=
    sourceEq ▸ typed
  have accepted := packet.receipt.generated
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext principal.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    principal.cached.compilation.parents principal.cached.compilation.own.assignments principal.cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
    compiled.indexed.base.callableContext none none packet.receipt.childFuel principal.sourceBody.source
    (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok packet.receipt.child at accepted
  have read := CompatibleExpressionReads.loweredRead_of_contextual found form requirements coercions
    ordinary notInitializer (by rfl) (by rfl) accepted packet.sourceAt.unique packet.sourceAt.declarations originalTyped
  have childRead : CompatibleExpressionReads.LoweredRead compiled.indexed.fuel (.initial compiled.compatible.checked)
      child.source packet.sourceAt.context (principal.cached.diagnostics.reasonAt principal.named.signature.key)
      (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child := by
    simpa only [sourceEq] using read
  obtain ⟨fuel, ⟨policy⟩⟩ := CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.policy_receipt principal packet
  let certificate : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
      policy.selected.policy policy.selected.lowerBody (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) child.source packet.sourceAt.context
      (principal.cached.diagnostics.reasonAt principal.named.signature.key)
      (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child :=
    .leaf ⟨.read childRead, .read childRead⟩
  have childReads : ReadOnlySource child.source := by simpa only [sourceEq] using reads
  have noIndirect : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirect
      (compiled := compiled) (invocation := child) certificate := by
    intro callFuel callScope callId callee ids metadata code compiler _path
    obtain ⟨name, binder, form⟩ := childReads callId compiler.original compiler.found
    have impossible := compiler.originalForm
    simp [form] at impossible
  let root : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.Root compiled headers stages
      policy.selected.policy policy.selected.lowerBody (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
      compiled.indexed.fuel packet.sourceAt.context child (principal.cached.diagnostics.reasonAt principal.named.signature.key)
      (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child
      principal.sourceBody.resultType (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := {
    compilerFuel := fuel + 1
    accepted := by simpa only [sourceEq] using policy.selected.accepted
    certificate := certificate
    node := node
    found := childFound
    rawResult := rawType
    typed := typed
    sameLedger := packet.sourceAt.valid.ledger
    runtimeLedger := packet.sourceAt.valid.runtime
    unique := by simpa only [sourceEq] using packet.sourceAt.unique
    wellFormed := wellFormed
    runtime := by simpa only [sourceEq] using CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.runtime principal packet wellFormed
    covers := by rw [stages.evidence selected]; exact packet.sourceAt.valid.covers
    actualFunctionType := by rw [policy.callables]; rfl
    uninitialized := by
      intro current id code read _reached location
      exact uninitialized principal diagnostic receiver packet.sourceAt.unique (by simpa only [sourceEq] using read) location
    callsReady := by
      intro callFuel callScope callId callee ids metadata code compiler path
      exact False.elim (noIndirect compiler path)
    directReady := by
      intro callFuel callScope callId callee ids instantiation code compiler _path
      obtain ⟨name, binder, form⟩ := childReads callId compiler.node compiler.metadata.found
      have impossible := compiler.form
      simp [form] at impossible
    indexReady := by
      intro indexScope indexId base key node baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _scalar _path
      obtain ⟨name, binder, readForm⟩ := childReads indexId node indexed.metadata.found
      simp [readForm] at form
    methodReady := by
      intro callFuel callScope callId code compiler _path
      obtain ⟨name, binder, readForm⟩ := childReads callId compiler.node compiler.metadata.found
      rcases compiler.operator.form with ⟨op, operand, form, _arguments⟩ | ⟨op, left, right, form, _arguments⟩ <;>
        simp [readForm] at form
    noIndirect := noIndirect }
  exact ⟨⟨CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt.ofRoot root, rfl, rfl, rfl⟩⟩

include diagnostic receiver wellFormed reads found form requirements coercions ordinary notInitializer in
/-- Static support is issued for each authentic staged method scope. -/
theorem of_read
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} :
    CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) :=
  ⟨fun _ selected => of_read_child principal diagnostic receiver packet wellFormed reads
    found form requirements coercions ordinary notInitializer selected⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport
