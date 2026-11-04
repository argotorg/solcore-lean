import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableMethodOriginTable
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableMethodResolverTable
import Solcore.SourceSemantics.CoreLowering.CachedMethodEvidenceCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardTerminals
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndexDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerPolicies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPhysicalCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads

/-!
# Staged bounds: method selection and terminals

Selection of a method by origin and evidence, the general body view's transport, and the terminal support and bounds of method bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport
/-! Static terminal method packets retain the genuine trait principal, exact
parameter context and original accepted body. Whole-program Source typing and
the actual compiler callback provide the used child; no execution law is stored. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallablePreparedMethodRuntimeProfileFactory (SourceAt policy scope)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)

structure Packet where
  sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary
  expression : ExpressionId
  receipt : Receipt (policy principal.cached.compilation) compiled.indexed.fuel principal.sourceBody.source
    (scope (named := principal.named)) expression principal.cached.compilation.statements
    principal.named.signature.resultType (principal.cached.diagnostics.reasonAt principal.named.signature.key)
    principal.cached.compilation.own.fellThroughReason principal.cached.compilation.own.table.escapedReason
    principal.cached.compilation.body

/-- The actual selected Source method determines typing in the same parameter
context retained by SourceAt; native type projection is not used for this step. -/
theorem source_typing (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      principal.sourceBody sourceAt.types sourceAt.context facts := by
  obtain ⟨types, context, facts, typed, _valid⟩ := CallablePreparedMethodSelection.selected_typed principal.selected wellFormed
  have contextEq := Dynamic.MonoBindersExtend.functional typed.typing.inputs_extend sourceAt.extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq typed.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq sourceAt.extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ typed⟩

theorem statements (packet : Packet principal)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ final facts, StatementsHaveType principal.sourceBody.source {returnType := principal.sourceBody.resultType}
      packet.sourceAt.context principal.cached.compilation.statements final facts ∧
      BodyCompletes principal.sourceBody.resultType facts := by
  obtain ⟨facts, typed⟩ := source_typing principal packet.sourceAt wellFormed
  obtain ⟨final, body, _roots, complete⟩ := typed.typing.body_typed
  refine ⟨final, facts, ?_, complete⟩
  have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
      | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
    principal.source_frame.roots.filterMap_eq
  exact roots ▸ body

/-- Original Source typing selects the actual terminal expression and raw result. -/
theorem child_typed (packet : Packet principal)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child) :
    ∃ node, child.source.lookupExpression? packet.expression = some node ∧
      node.type = principal.sourceBody.resultType ∧
      ExpressionHasType child.source packet.sourceAt.context packet.expression node.type := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨final, facts, typed, complete⟩ := statements principal packet wellFormed
  rw [← sourceEq] at typed
  exact CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed
    (sourceEq ▸ packet.sourceAt.unique) (packet.receipt.head child sourceEq) typed complete

/-- Static validity is transported along the genuine method parameter extension. -/
theorem runtime (packet : Packet principal)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      packet.sourceAt.context principal.sourceBody.source := by
  obtain ⟨_facts, typed⟩ := source_typing principal packet.sourceAt wellFormed
  exact typed.sourceRuntimeValid.transport (RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended)

/-- The exact contextual compiler action selects one shared policy for the
method child, preserving the actual specializer row and callback budget. -/
theorem policy_receipt (packet : Packet principal) :
    ∃ fuel, Nonempty (CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      principal.named principal.cached.diagnostics principal.cached.code principal.cached.compilation
      fuel principal.sourceBody.source (scope (named := principal.named)) packet.expression
      (principal.cached.diagnostics.reasonAt principal.named.signature.key) packet.receipt.child) := by
  have accepted := packet.receipt.generated
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext principal.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    principal.cached.compilation.parents principal.cached.compilation.own.assignments principal.cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
    compiled.indexed.base.callableContext none none packet.receipt.childFuel principal.sourceBody.source
    (scope (named := principal.named)) packet.expression
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok packet.receipt.child at accepted
  cases eq : packet.receipt.childFuel with
  | zero =>
    rw [eq, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases accepted
  | succ fuel =>
    exact ⟨fuel, CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      principal.cached.compilation principal.record (by simpa only [eq] using accepted)⟩

/-- Only the actual original terminal syntax is needed in addition to SourceAt. -/
theorem of_terminal
    (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
      principal.sourceBody principal.dictionary)
    (expression : ExpressionId)
    (terminal : Terminal principal.sourceBody.source expression principal.cached.compilation.statements) :
    Nonempty (Packet principal) := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  exact ⟨⟨sourceAt, expression, receipt⟩⟩

/-- The selected root keeps the method result, diagnostic issuer and real
single packed-argument prefix. Called-body meaning is supplied by the numeric IH. -/
structure Child (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)
    (semanticFaults : FunctionCalls.FaultRep) extends
    CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt compiled headers stages
      packet.sourceAt.context child (scope (named := principal.named)) packet.expression
      packet.receipt.child semanticFaults where
  result : rawType = principal.sourceBody.resultType
  reasons : reasonAt = principal.cached.diagnostics.reasonAt principal.named.signature.key
  prefixLength : compilation.administrativePrefix = 1

/-- Every actual selected method scope receives a static expression root. -/
structure Support (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep) : Prop where
  roots : ∀ child, stages.Closure principal.sourceFunction child →
    Nonempty (Child principal packet headers stages child semanticFaults)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport
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
      intro indexScope indexId base key node baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _path
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOriginsMethodSelection
/-! Actual final preparation, retained method dictionaries and original Source
parent typing issue methods using coherence of their actual evidence origins. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOriginsMethodSelection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

structure Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  formed : CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport.Catalog compiled.sourceProgram
  ready : CallableMethodOriginTable.Ready compiled.sourceProgram compiled.indexed.base.plan.specializations

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  (actual : Operator compiled.sourceProgram project caller compilation
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation) (fuel+1)
    source scope id reasonAt policy.callables receipt.node lowered)
  (special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation
        (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation)
        (fuel+1) source scope id reasonAt) = .ok (some lowered))

include receipt actual special in
/-- Complete static evidence is recovered from the actual compiler table.
The public body family supplies no method execution or dictionary equality. -/
theorem of_actual
    (selected : OperatorSource actual)
    (methods : Catalog compiled)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (sourceUnique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
      receipt context callerEvidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  have finalMember : caller ∈ compiled.indexed.base.plan.specializations := samePlan ▸ callerMember
  obtain ⟨evidence⟩ := methods.ready.operator finalMember actual nodeMember
  let authentic := CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.authentic receipt actual special
  have support := CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport.selection_support
    authentic checked wellFormed methods.formed selected evidence.covered
    signatures ledger assumptions sourceUnique unique typed
  have coherent := evidence.at_source_receipt selected.toSourceReceipt
  exact CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.of_actual_with_origins receipt actual special
    selected support coherent (evidence.materialized.for_actual actual.materialized)
    checked wellFormed catalog prepared callerMember nodeMember samePlan globals
    signatures ledger assumptions unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOriginsMethodSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceMethodSelection
/-! Actual final preparation, retained method dictionaries and original Source
parent typing issue methods whose own evidence assumptions may be nonempty. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceMethodSelection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

structure Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  formed : CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport.Catalog compiled.sourceProgram
  ready : CallableMethodResolverTable.Ready compiled.sourceProgram compiled.indexed.base.plan.specializations
  coherent : CachedMethodEvidenceCoherence.Catalog compiled

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  (actual : Operator compiled.sourceProgram project caller compilation
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation) (fuel+1)
    source scope id reasonAt policy.callables receipt.node lowered)
  (special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation
        (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation)
        (fuel+1) source scope id reasonAt) = .ok (some lowered))

include receipt actual special in
/-- Complete static evidence is recovered from the actual compiler table.
The public body family supplies no method execution or dictionary equality. -/
theorem of_actual
    (selected : OperatorSource actual)
    (methods : Catalog compiled)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (sourceUnique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
      receipt context callerEvidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  have finalMember : caller ∈ compiled.indexed.base.plan.specializations := samePlan ▸ callerMember
  obtain ⟨evidence⟩ := methods.ready.operator finalMember actual nodeMember
  let authentic := CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.authentic receipt actual special
  have support := CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport.selection_support
    authentic checked wellFormed methods.formed selected evidence.covered
    signatures ledger assumptions sourceUnique unique typed
  obtain ⟨cached⟩ := actual.cached prepared callerMember nodeMember compiled samePlan
  obtain ⟨definition, _member, _identity, instantiated⟩ :=
    selected.certificate.selected.instantiates checked support.formed.parameters support.range
  have coherent := methods.coherent.of_instantiated cached instantiated
  exact CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.of_actual_with_evidence receipt actual special
    selected support coherent (evidence.materialized.for_actual actual.materialized)
    checked wellFormed catalog prepared callerMember nodeMember samePlan globals
    signatures ledger assumptions unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceMethodSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalSourceInversion
/-! Actual lexical Source steps expose the initializer and the allocated tail.
The tail keeps its extended context and final context; no body execution law
or chosen allocation is supplied separately. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalSourceInversion
open Frontend SourceInference Staging.Recursive

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
  cases nodeEq
  exact same

private theorem extension_unique {owner : Resolved.DeclarationId}
    {context first second : SourceSemantics.Context} {binder : TypedBinder}
    (left : BinderExtends owner context binder first)
    (right : BinderExtends owner context binder second) : first = second := by
  cases left
  cases right
  rfl

theorem absent {program : Program} {registry : Registry} {invocation : Scope}
    {context nextContext finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.Statements program registry size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ tailSize location bound,
      size = Size.stepSize [tailSize] ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      Size.Statements program registry tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | letGeneralized actual same _ _ _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | breaking actual same | continuing actual same
  | blockBreaking actual same _ | blockContinuing actual same _
  | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | bitNotProjected actual same _ _ _ _ _
  | bitNotProjectedRootFault actual same _ _
  | bitNotProjectedKeysFault actual same _ _ _
  | bitNotProjectedGetterFault actual same _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _
  | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _
  | assignProjectedRhsFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | assignBare actual same _ _ _ _ | assignBareOperands actual same _ _ _ _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | expressionFault actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _
  | letInitialized actual same _ _ _ _ _ | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | letUninitialized actual same _ actualExtended allocated remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have contexts := extension_unique extended actualExtended
      cases contexts
      exact ⟨_, _, _, rfl, allocated, remaining⟩

theorem initialized {program : Program} {registry : Registry} {invocation : Scope}
    {context nextContext finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.Statements program registry size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before
        initializer (.fault failure) after) ∨
    (∃ childSize tailSize value location middle bound,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before
        initializer (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      Size.Statements program registry tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after) := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | letGeneralized actual same _ _ polymorphic _ _ _ =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact False.elim (polymorphic monomorphic)
  | breaking actual same | continuing actual same
  | blockBreaking actual same _ | blockContinuing actual same _
  | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | bitNotProjected actual same _ _ _ _ _
  | bitNotProjectedRootFault actual same _ _
  | bitNotProjectedKeysFault actual same _ _ _
  | bitNotProjectedGetterFault actual same _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _
  | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _
  | assignProjectedRhsFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | assignBare actual same _ _ _ _ | assignBareOperands actual same _ _ _ _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | expressionFault actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _
  | letUninitialized actual same _ _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | letInitialized actual same child _ actualExtended allocated remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have contexts := extension_unique extended actualExtended
      cases contexts
      exact .inr ⟨_, _, _, _, _, _, rfl, child, allocated, remaining⟩
  | letFault actual same _ child =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, rfl, rfl, rfl, child⟩

theorem return_unit {program : Program} {registry : Registry} {invocation : Scope}
    {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt none)
    (trace : Size.Statements program registry size invocation context environment before
      (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | letGeneralized actual same _ _ _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | breaking actual same | continuing actual same
  | blockBreaking actual same _ | blockContinuing actual same _
  | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | bitNotProjected actual same _ _ _ _ _
  | bitNotProjectedRootFault actual same _ _
  | bitNotProjectedKeysFault actual same _ _ _
  | bitNotProjectedGetterFault actual same _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _
  | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _
  | assignProjectedRhsFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | assignBare actual same _ _ _ _ | assignBareOperands actual same _ _ _ _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | returnUnit actual same => exact ⟨rfl, rfl, rfl⟩
  | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | expressionFault actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _
  | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport
/-! Actual compiler actions for recursive ordinary and direct calls cross the
retained unchanged body view. Runtime children keep their ordered syntax;
synthetic callees retain real metadata lookups and are not evaluated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport

variable {directSites : DeclarationInstantiation → Prop}

private theorem mapM_eq_of_members {α β ε : Type} {items : List α}
    {left right : α → Except ε β} (same : ∀ item, item ∈ items → left item = right item) :
    items.mapM left = items.mapM right := by
  revert same
  induction items with
  | nil => intro _same; rfl
  | cons item rest ih =>
      intro same
      simp only [List.mapM_cons]
      rw [same item (by simp), ih (fun next member => same next (by simp [member]))]

private inductive FormInFragment : ExpressionForm → Prop where
  | atomic {form} (leaf : CompatibleExpressionLiterals.Atomic form) : FormInFragment form
  | proxy {inner} : FormInFragment (.proxy inner)
  | read {name binder} : FormInFragment (.reference name (.local binder))
  | group {inner} : FormInFragment (.group inner)
  | tuple {ids} : FormInFragment (.tuple ids)
  | constructor {instantiation ids} : FormInFragment (.constructor instantiation ids)
  | direct {callee ids instantiation} : FormInFragment (.call callee ids (.declaration instantiation))
  | builtin {callee ids function} : FormInFragment (.call callee ids (.builtinFunction function))
  | call {callee ids metadata} : FormInFragment (.call callee ids (.indirect metadata))
  | unary {operator operand} : FormInFragment (.unary operator operand)
  | binary {left operator right} : FormInFragment (.binary left operator right)
  | index {base key} : FormInFragment (.index base key)
  | conditional {test yes no} : FormInFragment (.conditional test yes no)

private theorem syntax_form {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax source id directSites) (found : source.lookupExpression? id = some node) :
    FormInFragment node.form := by
  cases tree with
  | leaf finite =>
      cases finite with
      | literal selected atomic =>
          cases Option.some.inj (selected.symm.trans found)
          exact .atomic atomic
      | read selected form =>
          cases Option.some.inj (selected.symm.trans found)
          exact form.symm ▸ FormInFragment.read
      | group selected form _ =>
          cases Option.some.inj (selected.symm.trans found)
          exact form.symm ▸ FormInFragment.group
      | pair selected form _ _ =>
          cases Option.some.inj (selected.symm.trans found)
          exact form.symm ▸ FormInFragment.tuple
  | proxy selected form =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.proxy
  | group selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.group
  | tuple selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.tuple
  | constructor selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.constructor
  | direct selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.direct
  | builtin selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.builtin
  | call selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.call
  | unary selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.unary
  | binary selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.binary
  | index selected form _ _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.index
  | conditional selected form _ _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.conditional

private theorem basic_atomic_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (lookup : source.lookupExpression? id = view.lookupExpression? id)
    (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (reason : Word) :
    SourceCoreBasic.lowerExpression fuel source scope id reason =
      SourceCoreBasic.lowerExpression fuel view scope id reason := by
  have sameRead : SourceCoreBasic.readExpression source id = SourceCoreBasic.readExpression view id := by
    simp only [SourceCoreBasic.readExpression, metadata.owner, lookup]
  cases fuel with
  | zero => rfl
  | succ fuel =>
      conv => lhs; rw [SourceCoreBasic.lowerExpression]
      conv => rhs; rw [SourceCoreBasic.lowerExpression]
      cases reading : SourceCoreBasic.readExpression source id with
      | error error =>
          have viewReading := sameRead.symm.trans reading
          simp only [viewReading, bind, Except.bind]
      | ok output =>
          rcases output with ⟨actualNode, type⟩
          have readFound := (BasicExpressions.readExpression_certificate reading).1
          cases Option.some.inj (readFound.symm.trans found)
          have viewReading := sameRead.symm.trans reading
          generalize formEq : node.form = actualForm at atomic
          cases atomic <;>
            simp only [viewReading, formEq, bind, Except.bind, pure, Except.pure]

/-- Reader and leaf fields shared by ordinary and evidence-aware policies.
The special action is compared at the actual compiler step separately. -/
structure ReadPolicyOn (policy : SourceCoreFunctions.Policy)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (allowed : ExpressionId → Prop) (directSites : DeclarationInstantiation → Prop) : Prop where
  read : ∀ id, allowed id → GeneralSyntax source id directSites → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : ReadPolicyOn
    policy readFuel values source
      (fun id => Reaches source roots (.expression id)) directSites)
  (viewProfile : ReadPolicyOn
    policy readFuel values view
      (fun id => Reaches view roots (.expression id)) directSites)
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
  (readView : ∀ id, Reaches source roots (.expression id) →
    policy.readExpression source id = policy.readExpression view id)
include edited avoids sourceProfile viewProfile

private theorem policy_read_eq {id : ExpressionId} (tree : GeneralSyntax source id directSites)
    (reached : Reaches source roots (.expression id)) :
    policy.readExpression source id = policy.readExpression view id := by
  rw [sourceProfile.read id reached tree,
    viewProfile.read id (reached.metadata edited.metadata) (syntax_view edited avoids tree reached)]
  exact compatible_read_eq edited.metadata (expression_lookup edited avoids reached)

include callables readView in
theorem compiler_step_eq_of_hook (fuel : Nat) {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax source id directSites) (reached : Reaches source roots (.expression id))
    (found : source.lookupExpression? id = some node)
    (children : ∀ child, RuntimeChild node.form child →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt =
        SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt)
    (specialEq :
      (match policy.lowerSpecial? with
        | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
        | some lower => lower compilation
            (fun budget childSource childScope childId childReasonAt =>
              SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                compilation childSource childScope childId childReasonAt)
            (fuel + 1) source scope id reasonAt) =
      (match policy.lowerSpecial? with
        | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
        | some lower => lower compilation
            (fun budget childSource childScope childId childReasonAt =>
              SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                compilation childSource childScope childId childReasonAt)
            (fuel + 1) view scope id reasonAt)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation view scope id reasonAt := by
  have lookup := expression_lookup edited avoids reached
  have viewFound := lookup.symm.trans found
  have sameRead := policy_read_eq edited avoids sourceProfile viewProfile tree reached
  by_cases owner : id.occurrence.owner = source.owner
  · have viewOwner := owner.trans edited.metadata.owner
    conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    have sourceOwned : ¬id.occurrence.owner ≠ source.owner := fun different => different owner
    have viewOwned : ¬id.occurrence.owner ≠ view.owner := fun different => different viewOwner
    simp only [if_neg sourceOwned, if_neg viewOwned,
      found, viewFound, bind, Except.bind, pure, Except.pure]
    cases hook : policy.lowerSpecial? <;> simp only [hook] at specialEq ⊢
    all_goals try
      rename_i lower
      rw [specialEq]
      cases action : lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) view scope id reasonAt
      all_goals try rfl
      all_goals rename_i output
      all_goals cases output
      all_goals try rfl
    all_goals
      try dsimp only [bind, Except.bind, pure, Except.pure]
      cases reading : policy.readExpression source id with
      | error error =>
          have viewReading := sameRead.symm.trans reading
          cases form : node.form <;> try rfl
          all_goals simp only [viewReading]
      | ok output =>
          rcases output with ⟨actualNode, type⟩
          have compatibleReading := (sourceProfile.read id reached tree).symm.trans reading
          have actualMetadata := CompatibleExpressionReads.metadata_of_read compatibleReading
          cases Option.some.inj (actualMetadata.found.symm.trans found)
          have viewReading := sameRead.symm.trans reading
          have viewCompatibleReading :=
            (viewProfile.read id (reached.metadata edited.metadata) (syntax_view edited avoids tree reached)).symm.trans viewReading
          have clipped : min (fuel + 1) fuel = fuel := Nat.min_eq_right (Nat.le_succ fuel)
          have readLower := compatible_lower_read_eq edited.metadata (fuel := readFuel)
            (values := values) (scope := scope) (reason := reasonAt id) lookup
          have hookSame : ∀ result callee arguments,
              policy.callables.callCallable compilation source node result callee arguments =
                policy.callables.callCallable compilation view node result callee arguments := by
            intro result callee arguments
            rw [callables]
            exact production_call_eq native active compilation source view node result callee arguments
          have tupleChildren {ids : List ExpressionId} (form : node.form = .tuple ids) :
              ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                compilation source scope child reasonAt) =
              ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                compilation view scope child reasonAt) := by
            apply mapM_eq_of_members
            intro child member
            exact children child (by simp [RuntimeChild, form, ExpressionForm.references, member])
          have tupleLeaf {ids : List ExpressionId} (form : node.form = .tuple ids) :
              policy.leafLowerer
                  (fun budget childSource childScope childId childReasonAt =>
                    SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                      compilation childSource childScope childId childReasonAt)
                  (fuel + 1) source scope id reasonAt =
              policy.leafLowerer
                  (fun budget childSource childScope childId childReasonAt =>
                    SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                      compilation childSource childScope childId childReasonAt)
                  (fuel + 1) view scope id reasonAt := by
            rw [sourceProfile.leaf]
            simp only [SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading,
              viewCompatibleReading, bind, Except.bind, pure, Except.pure, form, clipped,
              tupleChildren form]
          have fragment := syntax_form tree found
          generalize formEq : node.form = actualForm at fragment
          cases fragment with
          | atomic atomic =>
              have atomicBasic := basic_atomic_eq edited.metadata found lookup (formEq.symm ▸ atomic)
                (fuel + 1) scope (reasonAt id)
              generalize atomicForm : actualForm = leafForm at atomic
              cases atomic with
              | unit =>
                  simp only [formEq, atomicForm, viewReading]
                  exact tupleLeaf (formEq.trans atomicForm)
              | bool name value =>
                  simp only [formEq, atomicForm, viewReading, sourceProfile.leaf,
                    SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading, viewCompatibleReading, bind, Except.bind, atomicBasic]
              | word literal =>
                  simp only [formEq, atomicForm, viewReading, sourceProfile.leaf,
                    SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading, viewCompatibleReading, bind, Except.bind, atomicBasic]
              | integer literal resolution => rfl
          | proxy =>
              simp only [formEq, viewReading, sourceProfile.leaf,
                SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading, viewCompatibleReading,
                SourceCoreCompatibleDataExpressions.lowerWithReasons, bind, Except.bind, pure, Except.pure]
          | read =>
              simp only [formEq, viewReading, sourceProfile.lower, readLower]
          | @group inner =>
              have child := children inner (by simp [RuntimeChild, formEq, ExpressionForm.references])
              simp only [formEq, viewReading, child]
          | @tuple ids =>
              cases ids with
              | nil =>
                  simp only [formEq, viewReading, tupleLeaf formEq]
              | cons first rest =>
                  cases rest with
                  | nil =>
                      simp only [formEq, viewReading, tupleLeaf formEq]
                  | cons second tail =>
                      cases tail with
                      | nil =>
                          have firstSame := children first (by simp [RuntimeChild, formEq, ExpressionForm.references])
                          have secondSame := children second (by simp [RuntimeChild, formEq, ExpressionForm.references])
                          simp only [formEq, viewReading, firstSame, secondSame]
                      | cons third tail =>
                          simp only [formEq, viewReading, tupleLeaf formEq]
          | @constructor instantiation ids =>
              have argumentsSame : (ids.zip instantiation.payloadTypes).mapM (fun (argument, expected) => do
                  let expected ← SourceCoreCompatibleDataExpressions.projectType values.checked
                    (.occurrence id.occurrence) expected
                  let argument ← SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                    compilation source scope argument reasonAt
                  SourceCoreBasic.ensureType (.occurrence id.occurrence) expected argument.type
                  pure argument) =
                (ids.zip instantiation.payloadTypes).mapM (fun (argument, expected) => do
                  let expected ← SourceCoreCompatibleDataExpressions.projectType values.checked
                    (.occurrence id.occurrence) expected
                  let argument ← SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                    compilation view scope argument reasonAt
                  SourceCoreBasic.ensureType (.occurrence id.occurrence) expected argument.type
                  pure argument) := by
                apply mapM_eq_of_members
                intro pair member
                have child := children pair.1 (by
                  simp only [RuntimeChild, formEq, ExpressionForm.references, List.mem_map, NodeId.expression.injEq]
                  exact ⟨pair.1, (List.of_mem_zip member).1, rfl⟩)
                cases pair
                dsimp only at child ⊢
                rw [child]
              simp only [bind, Except.bind] at argumentsSame
              simp only [formEq, viewReading, sourceProfile.leaf,
                SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading,
                viewCompatibleReading, bind, Except.bind]
              simp only [SourceCoreCompatibleDataExpressions.lowerWithReasons, compatibleReading,
                viewCompatibleReading, bind, Except.bind, formEq, Nat.min_self, argumentsSame]
          | @unary operator operand =>
              have child := children operand (by simp [RuntimeChild, formEq, ExpressionForm.references])
              simp only [formEq, viewReading, child]
          | @binary left operator right =>
              have first := children left (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have second := children right (by simp [RuntimeChild, formEq, ExpressionForm.references])
              simp only [formEq, viewReading, first, second]
          | @index base key =>
              have first := children base (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have second := children key (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have baseReached : Reaches source roots (.expression base) :=
                .expression reached found (by simp [formEq, ExpressionForm.references])
              have baseLookup := expression_lookup edited avoids baseReached
              have baseReading : SourceCoreCompatibleDataExpressions.readExpression values.checked source base =
                  SourceCoreCompatibleDataExpressions.readExpression values.checked view base := by
                simp only [SourceCoreCompatibleDataExpressions.readExpression, baseLookup, edited.metadata.owner]
              simp only [formEq, viewReading, sourceProfile.leaf,
                SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading,
                viewCompatibleReading, bind, Except.bind]
              simp only [SourceCoreCompatibleDataExpressions.lowerWithReasons, compatibleReading,
                viewCompatibleReading, bind, Except.bind, formEq, Nat.min_self, baseReading, first, second]
          | @conditional condition yes no =>
              have test := children condition (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have thenBranch := children yes (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have elseBranch := children no (by simp [RuntimeChild, formEq, ExpressionForm.references])
              simp only [formEq, viewReading, test, thenBranch, elseBranch]
          | @direct callee ids instantiation =>
              have calleeReached : Reaches source roots (.expression callee) :=
                .expression reached found (by simp [formEq, ExpressionForm.references])
              have calleeLookup := expression_lookup edited avoids calleeReached
              have calleeRead := readView callee calleeReached
              have validatorSame : SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation =
                  SourceCompilationPlan.validateDirectDeclarationCallee view id callee instantiation := by
                simp only [SourceCompilationPlan.validateDirectDeclarationCallee, calleeLookup]
              have selectedSame : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false =
                  SourceCoreFunctions.selectedSignature policy compilation view node instantiation false := by
                simp only [SourceCoreFunctions.selectedSignature, edited.metadata.owner]
              have argumentsSame : ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
                ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) := by
                apply mapM_eq_of_members
                intro child member
                exact children child (by simp [RuntimeChild, formEq, member])
              simp only [formEq, viewReading, edited.metadata.owner, calleeRead, validatorSame,
                selectedSame, argumentsSame]
          | @builtin callee ids function =>
              have calleeReached : Reaches source roots (.expression callee) :=
                .expression reached found (by simp [formEq, ExpressionForm.references])
              have argumentReached : ∀ child, child ∈ ids → Reaches source roots (.expression child) :=
                fun child member => .expression reached found
                  (by simp [formEq, ExpressionForm.references, member])
              have validatorSame := SourceCoreElaboration.validateBuiltinFunctionCall_congr
                edited.metadata.owner node callee ids function
                (CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy.lookup_node edited.metadata
                  (expression_lookup edited avoids calleeReached))
                (fun child member => CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy.lookup_node edited.metadata
                  (expression_lookup edited avoids (argumentReached child member)))
              have calleeRead := readView callee calleeReached
              have referenceSame : ∀ calleeNode,
                  SourceCoreFunctions.builtinReference policy.callables compilation source calleeNode function.spelling function =
                    SourceCoreFunctions.builtinReference policy.callables compilation view calleeNode function.spelling function := by
                intro calleeNode
                rw [callables]
                cases native <;> rfl
              have argumentsSame : ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
                ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) := by
                apply mapM_eq_of_members
                intro child member
                exact children child (by simp [RuntimeChild, formEq, member])
              simp only [formEq, viewReading, validatorSame, calleeRead, referenceSame, argumentsSame, hookSame]
          | @call callee ids metadata =>
              have calleeReached : Reaches source roots (.expression callee) :=
                .expression reached found (by simp [formEq, ExpressionForm.references])
              have argumentReached : ∀ child, child ∈ ids → Reaches source roots (.expression child) :=
                fun child member => .expression reached found
                  (by simp [formEq, ExpressionForm.references, member])
              have validatorSame := indirect_validator_eq (node := node) (metadata := metadata)
                (expression_lookup edited avoids calleeReached)
                (fun child member => expression_lookup edited avoids (argumentReached child member))
              have calleeRead := policy_read_eq edited avoids sourceProfile viewProfile
                (syntax_child tree found (by simp [RuntimeChild, formEq, ExpressionForm.references])) calleeReached
              have calleeSame := children callee (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have argumentsSame : ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
                ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) := by
                apply mapM_eq_of_members
                intro child member
                exact children child (by simp [RuntimeChild, formEq, ExpressionForm.references, member])
              simp only [formEq, viewReading, validatorSame, calleeRead, calleeSame, argumentsSame, hookSame]
  · have viewOwner : id.occurrence.owner ≠ view.owner :=
      fun same => owner (same.trans edited.metadata.owner.symm)
    conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    simp only [if_pos owner, if_pos viewOwner]
    change Except.error (.ownerMismatch source.owner id.occurrence.owner) =
      (Except.error (.ownerMismatch view.owner id.occurrence.owner) :
        Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr)
    rw [edited.metadata.owner]

end Compiler

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn
    policy compilation readFuel values source scope reasonAt
      (fun id => Reaches source roots (.expression id)) directSites)
  (viewProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn
    policy compilation readFuel values view scope reasonAt
      (fun id => Reaches view roots (.expression id)) directSites)
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
  (readView : ∀ id, Reaches source roots (.expression id) →
    policy.readExpression source id = policy.readExpression view id)
include edited avoids sourceProfile viewProfile

include callables readView in
/-- The actual production compiler returns the same complete action on every
reached node of the supported recursive grammar. Compiler fuel is identical;
child equalities follow its real predecessor recursion, including ordered
vectors. No evaluator, raw-type cast, or arbitrary source-insensitive policy is
assumed. -/
theorem compiler_eq_on (fuel : Nat) {id : ExpressionId} (tree : GeneralSyntax source id directSites)
    (reached : Reaches source roots (.expression id)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope id reasonAt := by
  induction fuel generalizing id with
  | zero => simp only [SourceCoreFunctions.lowerExpressionWithPolicy]
  | succ fuel ih =>
      obtain ⟨node, found⟩ := syntax_found tree
      apply compiler_step_eq_of_hook edited avoids
        ⟨sourceProfile.read, sourceProfile.lower, sourceProfile.leaf⟩
        ⟨viewProfile.read, viewProfile.lower, viewProfile.leaf⟩
        callables readView fuel tree reached found
      · intro child edge
        exact ih (syntax_child tree found edge) (.expression reached found (runtime_child_references edge))
      · exact (sourceProfile.special id reached tree _ _).trans
          (viewProfile.special id (reached.metadata edited.metadata)
            (syntax_view edited avoids tree reached) _ _).symm

include callables readView in
/-- An accepted Code.view action transfers to the original Source through the
same factory action, after its actual recursive syntax has been transported.
Raw typing and declaration authority remain original-source issuer inputs. -/
theorem accepted_original_on (fuel : Nat) {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax view id directSites) (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation view scope id reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation source scope id reasonAt = .ok lowered := by
  exact (compiler_eq_on edited avoids sourceProfile viewProfile callables readView fuel
    (syntax_original edited avoids tree reached) reached).trans accepted
end Compiler

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
    policy compilation readFuel values source scope reasonAt directSites)
  (viewProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
    policy compilation readFuel values view scope reasonAt directSites)
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
  (readView : ∀ id, Reaches source roots (.expression id) →
    policy.readExpression source id = policy.readExpression view id)
include edited avoids sourceProfile viewProfile callables readView

/-- Existing global policy callers restrict their facts to the actual body. -/
theorem compiler_eq (fuel : Nat) {id : ExpressionId} (tree : GeneralSyntax source id directSites)
    (reached : Reaches source roots (.expression id)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope id reasonAt :=
  compiler_eq_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables readView fuel tree reached

/-- Compatibility wrapper for complete global profiles. -/
theorem accepted_original (fuel : Nat) {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax view id directSites) (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation view scope id reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation source scope id reasonAt = .ok lowered :=
  accepted_original_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables readView fuel tree reached accepted
end Compiler

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles
/-! Actual named policy recipes retain declaration-call evidence hooks. Other
recursive forms keep their original native metadata restrictions. The compiler
step returns the same static receipt and original ordered child callbacks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (SupportedForm syntax_node contextual_same evidence_none)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt Supported Child)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named} {source : TypedSource}
  {directSites : DeclarationInstantiation → Prop}

/-- Only declaration calls may carry additional ordinary requirement IDs.
Their actual compiler branch authenticates every retained dictionary entry. -/
structure MetadataFor (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : Named) (source : TypedSource) (directSites : DeclarationInstantiation → Prop) : Prop where
  requirements : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node →
    node.requirements = [] ∨ (∃ literal resolution, node.form = .integerLiteral literal resolution) ∨
      ∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation)
  coercions : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, GeneralSyntax source id directSites →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  localRead : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

theorem MetadataFor.of_native
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor prepared named source directSites) :
    MetadataFor prepared named source directSites := by
  refine ⟨?_, metadata.coercions, metadata.initializer, metadata.arguments, metadata.localRead⟩
  intro id tree node found
  rcases metadata.requirements id tree node found with empty | literal
  · exact .inl empty
  · exact .inr (.inl literal)

theorem MetadataFor.non_direct_requirements (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution := by
  rcases metadata.requirements id tree node found with empty | literal | ⟨callee, ids, instantiation, form⟩
  · exact .inl empty
  · exact .inr literal
  · exact False.elim (ordinary node found callee ids instantiation form)

/-- The original contextual step agrees with the actual evidence lowerer at a
named declaration call. No second compiler policy is selected. -/
theorem direct_hook
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) := by
  have same := contextual_same found (form ▸ SupportedForm.direct callee ids instantiation)
    (metadata.localRead id tree node found)
  rw [recipe.lowerSpecial]
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [same, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id tree, Option.filter_none]
  cases actual : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
  | error error => rfl
  | ok output => cases output <;> simp [form]

theorem special_none
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat)
    (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compilation rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id tree node found)
  have noEvidence := evidence_none prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized (context prepared named) child budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found supported
    (metadata.non_direct_requirements tree ordinary found) (metadata.coercions id tree node found)
    (metadata.arguments id tree node found)
    (fun callee ids instantiation form => False.elim (ordinary node found callee ids instantiation form))
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | proxy | index | unary | binary | conditional | group | constructor | direct | builtin => rfl
  | tuple => rfl
  | call => rfl

theorem read_policy
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites) :
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id tree node found)
  rw [recipe.readExpression]
  simp only [sameSource, bind, Except.bind]
  rfl

/-- The authentic accepted expression either took the ordinary branch or
returned the exact code supplied by its evidence hook. -/
theorem accepted_direct_action
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      (context prepared named) source scope id reasonAt = .ok lowered) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none ∨
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok (some lowered) := by
  have owner : id.occurrence.owner = source.owner := by
    apply Classical.byContradiction
    intro mismatch
    simp [SourceCoreFunctions.lowerExpressionWithPolicy, mismatch, bind, Except.bind] at accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
  have hook := direct_hook recipe metadata tree found form
    (Child policy body fuel (context prepared named)) (fuel + 1) scope reasonAt
  cases selectedHook : policy.lowerSpecial? with
  | none =>
    simp only [selectedHook] at hook
    exact .inl hook.symm
  | some lower =>
    simp only [selectedHook] at hook accepted
    rw [hook] at accepted
    cases action : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized (context prepared named) (Child policy body fuel (context prepared named))
        (fuel + 1) source scope id reasonAt
        (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
    | error error => rw [action] at accepted; cases accepted
    | ok output =>
      cases output with
      | none => exact .inl rfl
      | some actual =>
        rw [action] at accepted
        cases Except.ok.inj accepted
        exact .inr rfl

theorem recipe_policy_for
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])
    (supported : ∀ instantiation, directSites instantiation → Supported (context prepared named).plan instantiation)
    (metadata : MetadataFor prepared named source directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    StepPolicyFor policy (context prepared named) prepared.fuel
      (.initial checked) source scope reasonAt directSites := by
  constructor
  · intro id _ tree ordinary child budget
    rw [recipe.lowerSpecial]
    exact special_none compilation rootFuel metadata tree ordinary child budget scope reasonAt
  · intro id _ tree _
    exact read_policy recipe metadata tree
  · exact recipe.lowerRead
  · exact recipe.leafLowerer
  · intro body fuel id callee ids instantiation node lowered _ found form site children accepted
    have tree := GeneralSyntax.direct found form site children
    rcases accepted_direct_action recipe metadata tree found form accepted with bypass | authentic
    · obtain ⟨requirements, assumptions⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct found form bypass
      exact CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_supported found form
        (supported instantiation site) (fun child budget => by
          exact (direct_hook recipe metadata tree found form child budget scope reasonAt).trans
            (CallableCallEvidenceCertificates.direct_bypass found form requirements
              (metadata.coercions id tree node found) assumptions))
        (read_policy recipe metadata tree) accepted
    · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted found form authentic
      have projected := actual.suffix.outputProjection
      change SourceCoreCompatibleDataExpressions.projectType checked
        (.occurrence node.id.occurrence) node.type = .ok lowered.type at projected
      have actualPolicy : CallableCoercionExpressionCertificates.Direct prepared.base.sourceProgram
          ((representation prepared).atContext named.signature.key []).expressions.projectType
          named.specialized (context prepared named) (Child policy body fuel (context prepared named))
          (fuel + 1) source scope id callee ids instantiation reasonAt policy.callables node lowered := by
        rw [callables]
        exact actual
      exact CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_evidence
        (supported instantiation site) (metadata.coercions id tree node found)
        (CompatibleExpressionReads.projectType_of_accepted projected) actualPolicy accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport
/-! An actual terminal method with reads, literals and conditional selection
uses the same recursive compiler certificate and original Source typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport (Packet Support)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

def PrimitiveSource (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node →
    (∃ name resolution, node.form = .reference name resolution) ∨
    (∃ spelling resolution, node.form = .integerLiteral spelling resolution) ∨
    (∃ condition first second, node.form = .conditional condition first second)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (forms : PrimitiveSource principal.sourceBody.source)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source (fun _ => False))
  (tree : GeneralSyntax principal.sourceBody.source packet.expression (fun _ => False))

include diagnostic receiver wellFormed forms metadata tree in
theorem of_child
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child) :
    Nonempty (CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Child principal packet headers stages child
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨node, childFound, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.child_typed principal packet wellFormed selected
  have found : principal.sourceBody.source.lookupExpression? packet.expression = some node := sourceEq ▸ childFound
  have originalTyped : ExpressionHasType principal.sourceBody.source packet.sourceAt.context packet.expression node.type := sourceEq ▸ typed
  obtain ⟨fuel, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.policy_receipt principal packet
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables (fun _ impossible => False.elim impossible)
    metadata (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named))
    (principal.cached.diagnostics.reasonAt principal.named.signature.key)
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    packet.sourceAt.unique packet.sourceAt.declarations profile
    (fun id node tree found => metadata.coercions id tree node found) tree found originalTyped root.selected.accepted
  let childCertificate : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
      root.selected.policy root.selected.lowerBody (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) child.source packet.sourceAt.context
      (principal.cached.diagnostics.reasonAt principal.named.signature.key)
      (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child := by
    simpa only [sourceEq] using certificate
  have noIndirect : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirect
      (compiled := compiled) (invocation := child) childCertificate := by
    intro callFuel callScope callId callee ids callMetadata code compiler _path
    rcases forms callId compiler.original (by simpa only [sourceEq] using compiler.found) with
      ⟨name, resolution, form⟩ | ⟨spelling, resolution, form⟩ | ⟨condition, first, second, form⟩ <;>
      have impossible := compiler.originalForm <;> simp [form] at impossible
  let actual : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.Root compiled headers stages
      root.selected.policy root.selected.lowerBody (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
      compiled.indexed.fuel packet.sourceAt.context child (principal.cached.diagnostics.reasonAt principal.named.signature.key)
      (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child
      principal.sourceBody.resultType (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := {
    compilerFuel := fuel + 1
    accepted := by simpa only [sourceEq] using root.selected.accepted
    certificate := childCertificate
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
    actualFunctionType := by rw [root.callables]; rfl
    uninitialized := by
      intro current id code read _reached location
      exact CallableIndexedOwnedPreparedStagedMethodTerminalSupport.uninitialized principal diagnostic receiver
        packet.sourceAt.unique (by simpa only [sourceEq] using read) location
    callsReady := by
      intro callFuel callScope callId callee ids callMetadata code compiler path
      exact False.elim (noIndirect compiler path)
    directReady := by
      intro callFuel callScope callId callee ids instantiation code compiler _path
      rcases forms callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, resolution, form⟩ | ⟨spelling, resolution, form⟩ | ⟨condition, first, second, form⟩ <;>
        have impossible := compiler.form <;> simp [form] at impossible
    indexReady := by
      intro indexScope indexId base key actual baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _path
      rcases forms indexId actual (by simpa only [sourceEq] using indexed.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨spelling, resolution, nodeForm⟩ | ⟨condition, first, second, nodeForm⟩ <;>
        simp [nodeForm] at form
    methodReady := by
      intro callFuel callScope callId code compiler _path
      rcases forms callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨spelling, resolution, nodeForm⟩ | ⟨condition, first, second, nodeForm⟩
      all_goals
        rcases compiler.operator.form with ⟨op, operand, form, _arguments⟩ | ⟨op, left, right, form, _arguments⟩ <;>
          simp [nodeForm] at form
    noIndirect := noIndirect }
  exact ⟨⟨CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt.ofRoot actual, rfl, rfl, rfl⟩⟩

include diagnostic receiver wellFormed forms metadata tree in
theorem of_actual
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) :=
  ⟨fun _ selected => of_child principal packet diagnostic receiver wellFormed forms metadata tree selected⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalBounds
/-! The genuine method parameter entry supplies admission and the complete
physical cache. Strict expression induction closes the actual terminal body;
the static support carries neither body execution nor a semantic callback. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport (Packet Support)
open CallableIndexedOwnedPreparedStagedPhysicalRootBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMethodInvocationBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "bodyBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)
local notation "point" => Point (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child

include wellFormed beforeTyped argumentsTyped in
private theorem heap_at_parameters {environment : Dynamic.Environment} {after : Dynamic.Heap}
    (allocation : Dynamic.BindersAllocate [] before principal.sourceFunction.parameters arguments environment after) :
    Dynamic.HeapWellTyped packet.sourceAt.context after := by
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq packet.sourceAt.extended
  have rawArguments : Dynamic.ValuesHaveTypes principal.sourceBody.context before arguments
      (principal.sourceBody.source.inputs.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes, principal.source_frame.context] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping
    (principal.source_frame.context ▸ beforeTyped) rawArguments (principal.source_frame.parameters ▸ allocation)
  obtain ⟨_, typed⟩ := CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.source_typing principal packet.sourceAt wellFormed
  have runtime := typed.sourceRuntimeValid
  have fields := RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended
  exact allocated.transportClosed fields.signatures runtime.closed (fields.targetClosed runtime.closed)
    runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)

include support selected keyPhysical in
private theorem preserves_children (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow bodyBridge packet.sourceAt.context
      model stages child point faults budget := by
  obtain ⟨root⟩ := support.roots child selected
  intro size within
  have bound : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots packet.sourceAt.context model stages child point faults size :=
    children size within root.toRootAt owner keyPhysical
  rw [root.prefixLength] at bound
  intro current id code
  exact bound

include support selected keyPhysical in
private theorem reflects_children (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow bodyBridge packet.sourceAt.context
      model stages child point faults budget := by
  obtain ⟨root⟩ := support.roots child selected
  intro size within
  have bound : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots packet.sourceAt.context model stages child point faults size :=
    children size within root.toRootAt owner keyPhysical
  rw [root.prefixLength] at bound
  intro current id code
  exact bound

include support wellFormed selected keyPhysical beforeTyped argumentsTyped stable in
/-- The genuine installed frame and marked allocation establish every body
admission field before the strict expression law is used. -/
theorem source_continuation (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SourceContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata _owned history _emitted entry _added _length _spine reached _related physical slots
  intro size finalContext bodyOutcome outcome after trace matched within
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet wellFormed beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  have view : LambdaMetadataViews.MetadataView child.source principal.sourceBody.source := sourceEq ▸ .refl _
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.statements principal packet wellFormed
  rw [← sourceEq] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
      frame, metadata, returned, related, _post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
      (receipt := packet.receipt) (view := view) (bridge := bodyBridge)
      (bodyTyped := bodyTyped) (complete := completes) (certifies := fun lowered accepted =>
        show point _ _ lowered from ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans packet.receipt.generated)⟩)
      (environments := entry.environments) (heaps := entry.heaps) (locals := entry.locals)
      (agrees := entry.lookups) (typed := entry.actualTyped) (initial := initial) (admitted := admitted)
      unique budget (preserves_children principal packet support functions selected owner keyPhysical budget children)
      trace matched (Nat.le_of_lt within)
  exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, returned.base.val, related⟩

include support wellFormed selected keyPhysical beforeTyped argumentsTyped stable in
/-- Reflection uses the measured native body grade and constructs an
independently sized original Source body at the same reached entry. -/
theorem native_continuation (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    NativeContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata prefixSize bodyStore _owned history _prefixWithin value finalStore _restored
    entry _added _length _spine reached _related physical slots within
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet wellFormed beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  have view : LambdaMetadataViews.MetadataView child.source principal.sourceBody.source := sourceEq ▸ .refl _
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.statements principal packet wellFormed
  rw [← sourceEq] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result, heaps, maps, worlds,
      frame, metadata, returned, related, _post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
      (receipt := packet.receipt) (view := view) (bridge := bodyBridge)
      (bodyTyped := bodyTyped) (complete := completes) (certifies := fun lowered accepted =>
        show point _ _ lowered from ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans packet.receipt.generated)⟩)
      (environments := entry.environments) (heaps := entry.heaps) (locals := entry.locals)
      (agrees := entry.lookups) (typed := entry.actualTyped) (initial := initial) (admitted := admitted)
      unique budget (reflects_children principal packet support functions selected owner keyPhysical budget children)
      entry.completed (Nat.le_of_lt within)
  exact ⟨sourceSize, packet.sourceAt.context, CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome,
    outcome, after, finalMap, finalWorld, trace, matched, result, heaps, maps, worlds,
    frame, metadata, returned.base.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodHeadBounds
/-! Actual selected operator calls preserve and reflect the full caller state.
Ordered operand meaning supplies the reached argument heap; the real physical
method slot and marked parameter entry feed strict method body callbacks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id reasonAt lowered)
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context invocation.evidence stages)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (ownerFrame : owner.key.frameLocation = 0)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (slots : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix index.scope index.canonical)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A strict Source body callback at an authentic reached argument state. -/
def SourceBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    CallableIndexedOwnedPreparedStagedMethodInvocationBounds.SourceContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

/-- The native counterpart uses the same independently typed argument heap. -/
def NativeBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    CallableIndexedOwnedPreparedStagedMethodInvocationBounds.NativeContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

private theorem result_type : lowered.type = port.principal.named.signature.resultType :=
  receipt.result.symm.trans ((congrArg SourceCoreCalls.Signature.resultType port.signature).symm)

private theorem parameter_type : port.principal.named.signature.parameterType =
    (SourceCoreCalls.packArguments receipt.codes).type := by
  rw [port.signature]
  exact receipt.parameter

private theorem capture_read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment}
    (capture : CallableIndexedOwnedMethodPhysicalCaptures.Capture port.principal.cached port.principal.dictionary
      functions mapping world heap store canonical)
    (authority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store) :
    store.read? (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index) = some (.inRight .unit
      (.closure port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        (port.principal.cached.compilation.output.rename capture.installed.embedding.lift) capture.installed.captured)) := by
  have cachedCode : compiled.indexed.secondPass.closures[port.principal.cached.index]? = some
      (.lambda port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        port.principal.cached.compilation.output) := by
    simpa only [port.principal.cached.compilation.emitted] using port.principal.cached.cached
  simpa only [capture.embedding_eq, capture.captured_eq] using (authority.cached cachedCode).2

include owner receipt port callerBridge ownerFrame physical slots functions faults unique wellFormed runtime covers in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : PreservesBelow bridge context model stages invocation children faults size)
    (bodyMeaning : SourceBodies (headers := headers) (receiving := receiving) owner receipt port functions faults size) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨orderedTyping, sourceResult⟩ :=
    CallableIndexedOwnedPreparedStagedMethodArgumentRows.raw_types receipt port wellFormed runtime unique typed
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  have originalTrace := trace
  rcases CallableIndexedOwnedPreparedStagedMethodSourceArguments.children receipt port unique trace with
    ⟨argumentsHeap, sources, sourceTrace, bodySize, bodyEnvironment, bound, finalContext, bodyOutcome, selectedChild,
      selected, allocated, bodyTrace, matched, strict⟩ | ⟨failure, outcomeEq, sourceTrace⟩
  · obtain ⟨values, middleStore, middleMap, middleWorld, argumentsEvaluated, represented, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
      CallableIndexedOwnedPreparedStagedMethodArgumentBounds.preserves_values bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace
    obtain ⟨argumentSize, argumentsTrace⟩ := sourceTrace.sized
    obtain ⟨argumentsTyped, argumentsHeapTyped, _extension⟩ :=
      CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping.values_at
        wellFormed runtime covers locals admitted.heap orderedTyping argumentsTrace
    obtain ⟨headerHeap, headerArguments, _result⟩ :=
      CallableIndexedOwnedPreparedStagedMethodArgumentRows.at_values receipt port wellFormed runtime unique typed
        argumentsHeapTyped argumentsTyped
    have parameters := CallableIndexedOwnedPreparedStagedMethodArgumentRows.represented_arguments receipt port represented
    obtain ⟨capture⟩ := CallableIndexedOwnedMethodPhysicalCaptures.of_selected
      port.principal.cached port.principal.dictionary functions owner (callerBridge.pool reached) ownerFrame
      (physical reached) middleHeaps.runtime_hasTypes (slots reached) port.selected wellFormed
    have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
      rw [capture.canonical_eq]
      exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated⟩ :=
      CallableIndexedOwnedPreparedStagedMethodInvocationBounds.preserves
        port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner (callerBridge.pool reached)
        (capture.frame_eq.trans ownerFrame.symm) middleHeaps (physical reached) capturedSlots size
        (bodyMeaning (callerBridge.pool reached) capture.installed parameters headerHeap headerArguments post.at_values.rows selected)
        allocated bodyTrace matched strict
    have reference := agrees (slots initial _ _
      (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
    have read := capture_read receipt port functions capture (physical reached)
    have selectedValue := OptionalCell.read_success compilation.internalReason
      (show Evaluates (packValues values :: actual) middleStore
        (.var (ξ (current.length + compilation.administrativePrefix + port.principal.cached.index) + 1))
        (.cellRef (OptionalCell.cellType port.principal.named.signature.functionType)
          (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index)) middleStore from .var reference) read
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot]
      exact SourceCoreCalls.call_success argumentsEvaluated selectedValue bodyEvaluated
    · simpa only [sourceResult, nativeResult] using result
    · exact after_expression_sized initial returned admitted wellFormed runtime covers locals typed
        originalTrace (argumentFrame.trans bodyFrame)
  · subst outcome
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedPreparedStagedMethodArgumentBounds.preserves_fault bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename]
      simpa only [receipt.result] using SourceCoreCalls.call_argument_failure
        (signature := receipt.signature) (index := ξ (current.length + compilation.administrativePrefix + receipt.index))
        (internalReason := compilation.internalReason) (receipt.parameter.symm ▸ argumentsEvaluated)
    · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed originalTrace frame

include owner receipt port callerBridge ownerFrame physical slots functions faults unique wellFormed runtime covers in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : ReflectsBelow bridge context model stages invocation children faults size)
    (bodyMeaning : NativeBodies (headers := headers) (receiving := receiving) owner receipt port functions faults size) :
    ReflectsAt bridge context model stages invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨orderedTyping, sourceResult⟩ :=
    CallableIndexedOwnedPreparedStagedMethodArgumentRows.raw_types receipt port wellFormed runtime unique typed
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, middleMap, middleWorld, sourceTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge size sequence unique orderedTyping childMeaning
      environments heaps locals agrees actualTyped initial admitted argumentEvaluation smaller
  cases represented with
  | fault matched =>
    have evaluated := SourceCoreCalls.call_argument_failure
      (signature := port.principal.named.signature)
      (index := ξ (current.length + compilation.administrativePrefix + port.principal.cached.index))
      (internalReason := compilation.internalReason) (parameter.symm ▸ argumentEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
    obtain ⟨_, trace⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.arguments_fault receipt port sourceTrace
    refine ⟨_, _, argumentsHeap, middleMap, middleWorld, trace, ?_, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, ?_⟩
    · rw [nativeResult]
      exact .fault matched
    · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace argumentFrame
  | @values sources values payloads =>
    obtain ⟨argumentsTyped, argumentsHeapTyped, _extension⟩ :=
      CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping.values_at
        wellFormed runtime covers locals admitted.heap orderedTyping sourceTrace
    obtain ⟨headerHeap, headerArguments, _result⟩ :=
      CallableIndexedOwnedPreparedStagedMethodArgumentRows.at_values receipt port wellFormed runtime unique typed
        argumentsHeapTyped argumentsTyped
    have parameters := CallableIndexedOwnedPreparedStagedMethodArgumentRows.represented_arguments receipt port payloads
    obtain ⟨capture⟩ := CallableIndexedOwnedMethodPhysicalCaptures.of_selected
      port.principal.cached port.principal.dictionary functions owner (callerBridge.pool reached) ownerFrame
      (physical reached) middleHeaps.runtime_hasTypes (slots reached) port.selected wellFormed
    have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
      rw [capture.canonical_eq]
      exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
    have reference := agrees (slots initial _ _
      (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
    have read := capture_read receipt port functions capture (physical reached)
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
      argumentEvaluation.sound reference read completed
    obtain ⟨bodySourceSize, bodyEnvironment, bound, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
        allocated, bodyTrace, matched, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated⟩ :=
      CallableIndexedOwnedPreparedStagedMethodInvocationBounds.reflects
        port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner (callerBridge.pool reached)
        (capture.frame_eq.trans ownerFrame.symm) middleHeaps (physical reached) capturedSlots size
        (bodyMeaning (callerBridge.pool reached) capture.installed parameters headerHeap headerArguments post.at_values.rows port.staged)
        bodyEvaluation (Nat.le_of_lt bodySmaller)
    obtain ⟨_, trace⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.applied receipt port sourceTrace
      port.staged allocated bodyTrace matched
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · simpa only [sourceResult, nativeResult] using result
    · exact after_expression_sized initial returned admitted wellFormed runtime covers locals typed trace
        (argumentFrame.trans bodyFrame)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodHeadBounds
end
