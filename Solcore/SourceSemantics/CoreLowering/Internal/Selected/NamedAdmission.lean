import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCurrentFactoryValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBuiltinArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedContextualProductReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedLambdaBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnLambdaStaticFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReturnLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
import Solcore.SourceSemantics.SourceInferenceSoundness
import Solcore.SourceSemantics.CoreLowering.CallableIndependentSourceViews
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingLambdaBodySupport

/-!
# Selected compilations: named bodies

Admission of named bodies and their terminal children, with named invocation bounds in both directions and the lambda formations reached from a prepared body.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactorySourceCertificate
/-! Selected formation keeps the complete original scoped body. The prepared
physical receipt admits its reached projected unary diagnostics directly. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactorySourceCertificate
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
structure SourceCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (body : List StatementId) where
  expression : ExpressionId
  terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal source expression body
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  reported : Core.Ty
  found : source.lookupExpression? expression = some node
  form : node.form = .lambda parameters result statements
  owner : expression.occurrence.owner = source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
    source expression = .ok (node, reported)
  scan : ScopedSourceBodyAdmission.Scan source (fun _ => True) result true statements

abbrev Certificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) :=
  SourceCertificate compiled named named.specialized.function.typedBody
    (statements named.specialized.function.typedBody)

/-- The existing narrower certificate embeds with all original fields intact. -/
def of_legacy {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {body : List StatementId}
    (original : CallableIndexedOwnedPreparedScopedFactoryAdmission.SourceCertificate compiled named source body) :
    SourceCertificate compiled named source body := {
  expression := original.expression, terminal := original.terminal, node := original.node,
  parameters := original.parameters, result := original.result, statements := original.statements,
  reported := original.reported, found := original.found, form := original.form, owner := original.owner,
  requirements := original.requirements, coercions := original.coercions, ordinary := original.ordinary,
  read := original.read, scan := original.scan }

/-- Actual cached identity transports the source certificate to the exact
Header and its compiled statement roots. -/
def at_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) (certificate : Certificate compiled named) :
    SourceCertificate compiled prepared.named header.function.source header.function.body := by
  obtain ⟨source, body, _result⟩ := header_data prepared aligned
  rw [source, body, cached_named prepared selected same]
  exact certificate


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactorySourceCertificate
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The certificate is for this Header's original source instance and parameter context. -/
def Certified (header : Header prepared values definitions program) : Prop :=
  ∃ facts, Dynamic.FunctionInstanceTypingCertificate program header.instantiation header.sourceBody
    header.types header.context facts

theorem Certified.body {header : Header prepared values definitions program}
    (certified : Certified header) :
    ∃ facts, BodyHasType header.function.source header.context header.function.resultType facts := by
  obtain ⟨facts, certificate⟩ := certified
  rw [header.frame.source, header.frame.result]
  exact ⟨facts, certificate.typing.body_typed⟩

theorem Certified.statements {header : Header prepared values definitions program}
    (certified : Certified header) :
    ∃ final facts, StatementsHaveType header.function.source
      {returnType := header.function.resultType} header.context header.function.body final facts ∧
      BodyCompletes header.function.resultType facts := by
  obtain ⟨facts, final, typed, _, completes⟩ := certified.body
  refine ⟨final, facts, ?_, completes⟩
  simpa [header.agreement.roots, List.filterMap_map, Function.comp_def] using typed

theorem Certified.runtime {header : Header prepared values definitions program}
    (certified : Certified header) :
    Dynamic.SourceRuntimeValid program header.function.context header.function.source := by
  obtain ⟨facts, certificate⟩ := certified
  rw [header.frame.context, header.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedRuntimeFacts
/-! Indexed compilation requires the actual callable context. Its successful
preparation also supplies callable contracts and the real diagnostic program.
These facts do not depend on a restricted body profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedRuntimeFacts
open Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok output := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (present : base.callableContext = some native) :
    checked.catalog.callableContracts = true ∧ ∃ diagnostics, base.diagnostics = some diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted; cases present
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · rename_i enabled
      obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨enabled, diagnostics, rfl⟩
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted; cases present

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic)
    (present : automatic.prepared.callableContext = some native) :
    automatic.checked.catalog.callableContracts = true ∧
      ∃ diagnostics, automatic.prepared.diagnostics = some diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared present

/-- The indexed artifact itself retains the callable context that rules out
empty-root and disabled-contract preparation branches. -/
theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.compatible.checked.catalog.callableContracts = true ∧
      ∃ diagnostics, compiled.indexed.base.diagnostics = some diagnostics := by
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  have present := (congrArg (fun base => base.callableContext) same).symm.trans
    compiled.indexed.ancestry.graph.inputs.callableSelected
  have actual := of_automatic compiled.compatiblePrepared present
  rw [same]
  exact actual

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedRuntimeFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedAdmission
/-! Selected named body certificates supply the actual parameter admission and
caller context transport. Body selection requires original owner uniqueness. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open SelectedCompilationNamedSourceTyping (Certified)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : Header compiled program}

/-- The receipt describes the heap created by this actual parameter allocation. -/
theorem parameter_source (certified : Certified header)
    {before reached : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment reached)
    (beforeTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    SourceReceipt program header.function header.context environment reached := by
  obtain ⟨facts, certificate⟩ := certified
  have frame : CallableCoercionMethodFrame.Frame header.sourceBody header.function :=
    ⟨header.frame.source, header.frame.context, header.frame.parameters, header.frame.result,
      header.frame.captured, header.frame.roots, header.frame.covers⟩
  obtain ⟨runtime, covers, heapTyped, locals, finalContext, typed, completes⟩ :=
    CallableIndexedOwnedBodySourceAdmission.admission_at_frame_parameters
      certificate.toBodyInstanceTypingCertificate frame header.extended allocated beforeTyped argumentsTyped
  exact ⟨runtime, covers, heapTyped, locals, finalContext, facts, typed, completes⟩

theorem caller_supports (certified : Certified header)
    {context : SourceSemantics.Context} {source : TypedSource}
    (runtime : Dynamic.SourceRuntimeValid program context source) :
    Dynamic.TypeContextSupports header.context context := by
  obtain ⟨facts, certificate⟩ := certified
  have inherited := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have signatures : header.context.signatures = program.signatures :=
    inherited.signatures.trans
      ((congrArg (fun current : SourceSemantics.Context => current.signatures) header.frame.context).trans certificate.signatures_eq)
  have closed : header.context.typeParameters = [] :=
    inherited.typeParameters.trans
      ((congrArg (fun current : SourceSemantics.Context => current.typeParameters) header.frame.context).trans certificate.type_parameters_empty)
  have variables : header.context.typeVariables = [] :=
    inherited.typeVariables.trans
      ((congrArg (fun current : SourceSemantics.Context => current.typeVariables) header.frame.context).trans certificate.type_variables_empty)
  exact Dynamic.TypeContextSupports.ofClosed (runtime.signatures.trans signatures.symm)
    closed runtime.closed variables runtime.residual_variables_open

/-- Successful child receipts already carry the complete raw parameter row. -/
theorem arguments (certified : Certified header)
    {context : SourceSemantics.Context} {source : TypedSource} {heap : Dynamic.Heap}
    {values : List Dynamic.Value}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap values
      (header.bindings.map (fun binding => binding.1.scheme.body))) :
    Dynamic.HeapWellTyped header.function.context heap ∧
      Dynamic.ValuesHaveTypes header.function.context heap values header.types ∧
      Dynamic.TypeContextSupports header.context context := by
  obtain ⟨facts, certificate⟩ := certified
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := argumentsTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  rw [header.parameters] at bodyTypes
  have types : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
  rw [← types] at bodyArguments
  exact ⟨header.frame.context.symm ▸ bodyHeap, header.frame.context.symm ▸ bodyArguments,
    caller_supports ⟨facts, certificate⟩ runtime⟩

variable {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}

private theorem roots_functional {nodes : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots nodes left) (second : Dynamic.StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons id nodes left first ih => cases second with
    | cons remaining => exact congrArg (List.cons id) (ih remaining)

/-- Inversion uses the retained global instantiation and actual selected scope.
It preserves the original staged body outcome instead of wrapping an ordinary
execution. Source arity excludes only the separate pre-allocation fault. -/
theorem body_prefix {header : Header compiled (Program.ofChecked compiled.sourceProgram)} (sourceAt : NamedSourceAt header rawD function)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {outcome : Staging.Recursive.Outcome} {size : Nat}
    (arity : header.function.parameters.length = arguments.length)
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size invocation context before
      (.global function) arguments outcome after) :
    ∃ bodySize child environment bound finalContext bodyOutcome,
      stages.Closure header.function child ∧
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages bodySize child header.context environment bound
        header.function.body finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome ∧ bodySize < size := by
  have bodyUnique : ∀ actual, Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram) function.instantiation actual →
      RecursiveNamedCatalog.Header.sourceBody header = actual := by
    intro actual instantiated
    exact BuiltinNamedCalls.instantiation_unique owners
      sourceAt.frame.instantiated instantiated
  cases trace with
  | @globalArity _ _ _ _ _ bodyInstance instantiates mismatch =>
    have same := bodyUnique bodyInstance instantiates
    cases same
    exact False.elim (mismatch (by simpa only [sourceAt.frame.parameters] using arity))
  | @global bodySize _ _ _ bound _ _ _ environment parameterTypes bodyContext finalContext
      bodyInstance roots child bodyOutcome _ instantiates covers rootsEq selected parameters allocate body converted =>
    have same := bodyUnique bodyInstance instantiates
    cases same
    have sameRoots := roots_functional rootsEq sourceAt.frame.roots
    subst_vars
    have actualParameters : MonoBindersExtend header.function.source.owner header.function.context
        header.function.parameters parameterTypes bodyContext := by
      simpa only [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] using parameters
    have sameTypes := header.extended.bodyTypes_eq.symm.trans actualParameters.bodyTypes_eq
    subst_vars
    have sameContext := (header.extended.functional actualParameters).symm
    subst_vars
    have actualSelected : stages.Closure header.function child := by
      simpa only [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] using selected
    exact ⟨_, _, _, _, _, _, actualSelected, sourceAt.frame.parameters.symm ▸ allocate,
      body, sourceAt.frame.result.symm ▸ converted,
      Staging.Recursive.Size.child_lt_stepSize (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
/-! Exact selected definitions type the retained named handle, including its
complete substitution and dictionary, before argument bundles are aligned. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)

/-- The certificate concerns this actual handle and the original selected body. -/
def CertifiedAt : Prop :=
  ∃ facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    function.instantiation header.sourceBody header.types header.context facts

include sourceAt in
theorem certified_at (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    CertifiedAt (header := header) (function := function) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, resolved, accepted⟩ := prepared.origin
  have valid := bodies.ordinary generic
    ⟨prepared.index, prepared.named, signature, request.parameterSubstitution, prepared.selected,
      signatureMember, genericMember, by simpa only [prepared.same] using accepted⟩
  have owner : (FunctionDefinition.ofChecked generic).body.owner = function.instantiation.declaration := by
    rw [sourceAt.retained]
    change generic.declaration = header.named.specialized.declaration
    rw [aligned.named, prepared.same]
    exact ((RecursiveNamedSpecializationBodyFacts.identities accepted).2.2).symm
  obtain ⟨types, lexical, facts, certificate⟩ :=
    sourceAt.frame.instantiated.certificate_of_valid bodies.signatures bodies.function_ids
      (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) owner valid
  have extended := header.extended
  rw [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] at extended
  have contextEq := Dynamic.MonoBindersExtend.functional certificate.typing.inputs_extend extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ certificate⟩

section Rows
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping} {sourceTypes : List TypeSystem.Ty}
  {sources : List Dynamic.Value} {payloads : List Value}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  {native : Value} {unknown : Word} {context : SourceSemantics.Context} {heap : Dynamic.Heap}
  {parameter result : TypeSystem.Ty}

include sourceAt compiler in
/-- Authentic callable typing supplies literal raw signature equality. The
selected second gate supplies count independently, then both genuine compiler
bundles align the original represented values with this Header's binders. -/
theorem accepted_rows
    (certifiedAt : CertifiedAt (header := header) (function := function))
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids originalMetadata
      originalNode dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none)
    (calleeTyped : Dynamic.ValueHasType context heap (.global function) (.function parameter result))
    (nativeType : compiler.calleeCode.type =
      CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
    (represented : DataExpressionSequence.Values model mapping world
      sourceTypes (compiler.codes.map (·.type)) sources payloads)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes = parameter) :
    CallableIndexedParameterMeaning.Arguments model mapping world header.bindings sources payloads ∧
      header.function.parameters.length = sources.length ∧ result = header.function.resultType := by
  rcases calleeTyped.global_inv with ordinary | staged
  · obtain ⟨typeEq, valid, evidence⟩ := ordinary
    obtain ⟨facts, certified⟩ :=
      certifiedAt
    have signature := TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)
    have bindingTypes : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
      have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
      rw [header.parameters] at bodyTypes
      simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
    have nativeSignature : compiler.parameterType = header.named.signature.parameterType ∧
        compiler.resultType = header.named.signature.resultType := by
      have acceptedType := compiler.callableType
      rw [actualFunctionType] at acceptedType
      exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (acceptedType.trans nativeType)
    have physical := CallableIndexedOwnedAcceptedIndirectPhysicalArity.named_count
      sourceAt caller dispatch selected accepted
    have ordered := compiler.ordered_children.1
    have representedCount : compiler.codes.length = sources.length := by
      simpa only [List.length_map] using represented.length.1
    have arity : header.function.parameters.length = sources.length :=
      physical.trans (ordered.trans representedCount)
    have parameterCount : header.function.parameters.length = header.bindings.length := by
      simpa only [List.length_map] using congrArg List.length header.parameters
    have binderCount : sources.length = header.bindings.length := arity.symm.trans parameterCount
    have sourcePacked := sourceBundle.trans
      (signature.1.trans (congrArg TypeSystem.Ty.productMany bindingTypes))
    have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
        SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :=
      (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
        (compiler.packedType.symm.trans (nativeSignature.1.trans header.parameterType))
    exact ⟨CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
      header.bindings represented binderCount sourcePacked nativePacked,
      arity, signature.2.trans sourceAt.frame.result.symm⟩
  · obtain ⟨inner, impossible, innerTyped⟩ := staged
    cases impossible
end Rows

include sourceAt in
/-- Original packed typing and actual physical arity fix the complete input row. -/
theorem arguments_at (certifiedAt : CertifiedAt (header := header) (function := function))
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {context : SourceSemantics.Context} {source : TypedSource} {heap : Dynamic.Heap}
    {values : List Dynamic.Value} {types : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap values types)
    (calleeTyped : Dynamic.ValueHasType context heap (.global function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : header.function.parameters.length = values.length) :
    Dynamic.HeapWellTyped header.function.context heap ∧
      Dynamic.ValuesHaveTypes header.function.context heap values header.types ∧
      Dynamic.TypeContextSupports header.context context := by
  obtain ⟨facts, certificate⟩ := certifiedAt
  rcases calleeTyped.global_inv with ordinary | staged
  · obtain ⟨typeEq, _, _⟩ := ordinary
    obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack values
    have packedTyped := bundle ▸ packing.hasType argumentsTyped
    have parameterEq := (TypeSystem.Ty.function.inj (typeEq.trans certificate.callable_type)).1
    rw [parameterEq] at packedTyped
    have signatures := certificate.signatures_eq.trans runtime.signatures.symm
    have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
      runtime.variables_closed certificate.residual_type_variables_open
    have bodyPacked := packedTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
      runtime.variables_closed certificate.residual_type_variables_open
    have length : values.length = header.types.length := arity.symm.trans
      ((congrArg List.length sourceAt.frame.parameters).trans certificate.typing.inputs_extend.length_eq)
    have bodyArguments := packing.unpackTypes bodyPacked length
    exact ⟨sourceAt.frame.context.symm ▸ bodyHeap, sourceAt.frame.context.symm ▸ bodyArguments,
      SelectedCompilationNamedAdmission.caller_supports certified runtime⟩
  · obtain ⟨inner, impossible, _⟩ := staged
    cases impossible

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicFactoryValues
/-! Actual public issuance supplies the complete original cached capture.
The positive named leaf retains every physical slot, and builtin issuance
retains its genuine closed compiler factory. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicFactoryValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt NamedInstalledCode)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionState (State)

private theorem selected_slot {compiled : SourceCoreUnifiedCompilation.Compiled}
    {input : Input compiled} (packet : Issued input)
    {signature : SourceCoreCalls.Signature} {index : Nat}
    (found : compiled.indexed.base.globals[index]? = some signature)
    (key : signature.key = packet.header.named.signature.key) :
    signature = packet.header.named.signature ∧ index = packet.header.slot := by
  have present : (signature, index) ∈ compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = packet.header.named.signature.key)) :=
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr found, by simpa using key⟩
  rw [packet.sourceAt.row.slot] at present
  exact Prod.mk.inj (List.mem_singleton.mp present)

/-- The selected real factory keeps the full original raw callable type. -/
theorem Session.named_source_type
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    {input : Input compiled} (packet : Issued input)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
    (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
    (atRecipe : ArtifactRecipe artifact recipe) :
    issued.sourceType = packet.header.named.specialized.function.type := by
  obtain ⟨expected, callable, _same, sourceType, _budget, _encoded, factory⟩ := issuance.receipt
  have actualFactory : recipe.NamedCallableAt packet.header.named.signature.key expected callable := by
    cases artifact
    rename_i authority actualRecipe
    change actualRecipe = recipe at atRecipe
    subst recipe
    exact factory
  obtain ⟨signature, slot, specialized, location, closure, identity, descriptor,
      signatureAt, keyAt, record, actualType, _slotAt, _number, _literal, _projection⟩ :=
    actualFactory.prepared prepared
  obtain ⟨signatureEq, _slotEq⟩ := selected_slot packet signatureAt keyAt
  subst signature
  have specializedEq : specialized = packet.header.named.specialized :=
    Except.ok.inj (record.symm.trans (CallableIndexedActualNamedSourceReceipts.header_record compiled packet.header))
  subst specialized
  exact sourceType.trans actualType

/-- A real named issuance constructs the whole receiving function value from
the current owned capture. Its handle encoding survives further issuances
without depending on a top-level argument position. -/
theorem Session.named_value_represents_current
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (caller : State (headers rows) (keys compiled)
      ⟨[], mapping, world, heap, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (callerHeader : Header compiled (Program.ofChecked compiled.sourceProgram))
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact} {issuanceFuel : Nat}
    (issuance : before.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
    (atNative : before.NativeAt world store)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    (atRecipe : ArtifactRecipe artifact recipe)
    {handle : Handle} (handleValue : issued.value = .function handle)
    (certified : SelectedCompilationNamedArgumentRows.CertifiedAt (header := packet.header) (function := CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available))) :
    ∃ callable, session.EncodesAt issuanceFuel packet.header.named.specialized.function.type
      (.function handle) callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedPhysicalCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        mapping world
        packet.header.named.specialized.function.type
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available))) callable
        (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) ∧
      Dynamic.ValueHasType callerHeader.function.context heap
        (.global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available))) packet.header.named.specialized.function.type := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨expected, callable, _same, _sourceType, _budget, encoded, factory⟩ := issuance.receipt
  rw [handleValue] at encoded
  have imported := continued.encodes_function encoded
  have actualFactory : recipe.NamedCallableAt packet.header.named.signature.key expected callable := by
    cases artifact
    rename_i authority actualRecipe
    change actualRecipe = recipe at atRecipe
    subst recipe
    exact factory
  obtain ⟨signature, slot, specialized, location, closure, identity, descriptor,
      signatureAt, keyAt, record, sourceType, slotAt, number, literal, projection⟩ :=
    actualFactory.prepared prepared
  obtain ⟨signatureEq, slotEq⟩ := selected_slot packet signatureAt keyAt
  subst signature
  subst slot
  have specializedEq : specialized = packet.header.named.specialized :=
    Except.ok.inj (record.symm.trans (CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled packet.header))
  subst specialized
  have headerMember := Inventory.header_member member
  have cached := CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.cache inputs rows packet.header headerMember
  have slotLocation := recipe.native_global_location slotAt
  have originalRead := RecursiveNamedPublicBootstrapGlobals.native_slot recipe.compiled recipe.templates
    (List.mem_of_getElem? slotAt)
  have locationEq : location = CallableIndexedOwnedPhysicalGlobals.location recipe.compiled packet.header.slot := by
    have inside := (List.getElem?_eq_some_iff.mp signatureAt).1
    simp only [CallableIndexedOwnedPhysicalGlobals.location, RecursiveNamedCatalogInitialization.location]
    omega
  rw [locationEq] at originalRead
  have originalPhysical := ((CallableIndexedOwnedPhysicalGlobals.initial recipe.compiled).cached cached).2
  have closureEq : closure = .closure packet.header.named.signature.parameterType
      (LanguageResult.resultType packet.header.named.signature.resultType)
      (packet.header.code.rename (RecursiveGlobalInitializationMeaning.shift packet.header.slot).lift)
      (List.replicate packet.header.slot .unit ++ CallableIndexedOwnedPhysicalGlobals.environment recipe.compiled) := by
    have same := Option.some.inj (originalRead.symm.trans originalPhysical)
    exact Value.inRight.inj same |>.2
  have frontendRecipe : artifact.RecipeAt recipe := by
    cases artifact
    exact atRecipe
  have currentRead := issuance.native_global_read frontendRecipe atNative (List.mem_of_getElem? slotAt)
  rw [locationEq, closureEq] at currentRead
  have typedStore := atNative.heap_typed frontendRecipe
  have keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical recipe.compiled (headers rows)
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_read (mapping := mapping)
    headerMember keyPhysical.frame keyPhysical.prefixZero keyPhysical.locations packet.aligned.globals currentRead typedStore
  have installed : NamedInstalledCode capture.named :=
    NamedInstalledCode.of_cached capture.named cached capture.embedding_eq
  obtain ⟨capturedContext, capturedTyped, bodyTyped⟩ :=
    RecursiveGlobalInitializationTyping.stored_closure typedStore capture.read
  have closureTyped : RuntimeValueHasType world
      (.closure packet.header.named.signature.parameterType
        (LanguageResult.resultType packet.header.named.signature.resultType)
        (packet.header.code.rename capture.named.embedding.lift) capture.named.captured)
      packet.header.named.signature.functionType recipe.compiled.indexed.layouts.definitions :=
    .closure capturedTyped bodyTyped
  have actualClosure : closure = .closure packet.header.named.signature.parameterType
      (LanguageResult.resultType packet.header.named.signature.resultType)
      (packet.header.code.rename capture.named.embedding.lift) capture.named.captured := by
    rw [capture.embedding_eq, capture.captured_eq]
    exact closureEq
  rw [actualClosure] at literal
  have projected : recipe.compiled.compatible.checked.catalog.project packet.header.named.specialized.function.type =
      .ok (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) := by
    rw [sourceType, literal] at projection
    exact projection
  refine ⟨callable, sourceType ▸ imported, ?_, RecursiveNamedPublicCurrentFactoryValues.source_typed packet.sourceAt callerHeader heap⟩
  have related : CallableIndexedOwnedPhysicalCellOrigins.FunctionOrigins
      (headers rows) (keys recipe.compiled) bodyRegistry faults mapping
      world
      packet.header.named.specialized.function.type
      (.global (CallableNamedReversal.global (CallableNamedMetadata.global
        packet.header.named.specialized input.prepared.available))) callable
      (CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType) := by
    rw [literal]
    exact .global ⟨CallableIndexedOwnedPhysicalNamedAssociation.of_capture
      (owner recipe.compiled) packet.header capture packet.sourceAt headerMember installed
      identity number projected descriptor closureTyped⟩
  obtain ⟨_facts, certified⟩ :=
    certified
  have sourceTypeEq : packet.header.named.specialized.function.type =
      (CallableNamedReversal.global (CallableNamedMetadata.global
        packet.header.named.specialized input.prepared.available)).instantiation.type := rfl
  rw [sourceTypeEq.trans certified.callable_type] at related ⊢
  exact .function related


theorem Session.builtin_value_represents_after
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (context : SourceSemantics.Context) (heap : Dynamic.Heap)
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    (atRecipe : ArtifactRecipe artifact recipe)
    {world : StoreTyping}
    {handle : Handle} (handleValue : issued.value = .function handle) :
    ∃ callable, before.SameRuntime issued.session ∧ issued.sourceType = function.type ∧
      session.EncodesAt issuanceFuel function.type (.function handle) callable ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world function.type (.builtin ⟨function⟩) callable
        (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)) ∧
      Dynamic.ValueHasType context heap (.builtin ⟨function⟩) function.type := by
  obtain ⟨expected, callable, same, sourceType, _budget, encoded, factory⟩ := issuance.receipt
  rw [handleValue] at encoded
  have imported := continued.encodes_function encoded
  have actualFactory : recipe.BuiltinCallableAt function expected callable := by
    cases artifact
    rename_i authority actualRecipe
    change actualRecipe = recipe at atRecipe
    subst recipe
    exact factory
  obtain ⟨actualType, builtinIndex, identity, descriptor, inventory, number, literal⟩ :=
    actualFactory.prepared prepared
  refine ⟨callable, same, sourceType.trans actualType, actualType ▸ imported, ?_, .builtin ⟨function⟩⟩
  rw [literal]
  exact .function (.builtin (.prior (.prior (.builtin
    (CallableIndexedBuiltinValues.Represents.builtin inventory number descriptor .nil)))))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicFactoryValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalBounds
/-! The original prepared named Header supplies the accepted terminal compiler
receipt. The exact selected Header certificate determines the used terminal child
at the Header's real parameter context. Strict expression hypotheses establish
both staged body directions at the same actual reached parameter state,
retaining nested stage failures and the full pool post. Native parameter entry
and caller restoration remain separate producers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt Terminal)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {expression : ExpressionId}

include aligned in
/-- The actual original body callback, its read policy and terminal Source
occurrence construct this receipt; a second body compilation is not assumed. -/
theorem compiler_receipt
    (terminal : Terminal header.function.source expression header.function.body) :
    Nonempty (Receipt header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body) :=
  CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) terminal aligned.accepted

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (sourceCertified : SelectedCompilationNamedSourceTyping.Certified header)
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge header.context initial)

include selected sourceCertified terminal certifies environments heaps locals agrees typed admitted in
/-- The original named body Source typing and genuine selected child scope
construct preservation from the used strict expression hypothesis. The body
trace and nested failure scope remain recursively staged. -/
theorem preserves_body (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge header.context model stages child certificate faults budget)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size child
      header.context environment before header.function.body finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (header.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := sourceCertified.statements
  rw [← stages.source selected] at bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := bodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children trace matched within

include selected sourceCertified terminal certifies environments heaps locals agrees typed admitted in
/-- Literal native body completion reflects to an independently graded staged
Source body, using the same accepted Header code and actual parameter state.
The complete returned pool and successful Source post are retained. -/
theorem reflects_body (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge header.context model stages child certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize child
        header.context environment before header.function.body header.context
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) after ∧
      Staging.Recursive.BodyResult header.function.resultType
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := sourceCertified.statements
  rw [← stages.source selected] at bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := bodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children completed within

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceAdmission
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol}
  {context : SourceSemantics.Context}

/-- Concrete successful preservation supplies admission at the actual reached
state. Faults retain their own endpoint histories without asserting success. -/
theorem after_expression_sized_of_preserved {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (_trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (preserved : ∀ value, outcome = .value value →
      Dynamic.ExpressionEvaluationPreserved context initial.heap reached.heap value type)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last := by
  have rows := StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame
  cases outcome with
  | value value =>
    refine ⟨rows, ?_⟩
    intro actual same
    cases same
    have exactResult := preserved value rfl
    exact ⟨exactResult.value_typed, exactResult.heap_typed⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨rows, by intro value impossible; cases impossible⟩
    | stage origin call reason => exact rows

/-- The exact caller relation and state are unchanged when adding admission. -/
theorem after_related_expression_sized_of_preserved
    {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (related : callerProtocol.Relates first last)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (preserved : ∀ value, outcome = .value value →
      Dynamic.ExpressionEvaluationPreserved context initial.heap reached.heap value type)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    callerProtocol.Relates first last ∧ PostAdmission bridge context type outcome last :=
  ⟨related, after_expression_sized_of_preserved first last admitted trace preserved frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLambdaAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLambdaAdmission
open Frontend SourceInference

theorem value_typed {program : Program} {context : SourceSemantics.Context}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {evidence : Dynamic.EvidenceEnvironment} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body)
    (empty : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    Dynamic.ValueHasType context heap (.closure {
      parameters := parameters, resultType := result, body := body,
      source := source, captured := environment, context := context, evidence := evidence }) node.type := by
  generalize expectedEq : node.type = expected at typed ⊢
  have contains := lookupExpression?_sound found
  have annotation := typed.lambda_annotation_of_uncoerced runtime.graph.nodeOccurrencesUnique contains form empty
  cases typed with
  | @intro _ _ actual raw plan actualContains formTyped rawEq rawWF typeWF requirements =>
    have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique actualContains).symm.trans found)
    subst actual
    have rawAnnotation : node.rawType = .function (TypeSystem.Ty.productMany (parameters.map (·.scheme.body))) result := by
      simpa [ExpressionNode.rawType, empty] using annotation
    rw [form] at formTyped
    cases formTyped with
    | lambda names extended bodyTyped completes =>
      rw [annotation]
      refine Dynamic.ValueHasType.closure rfl ?_ covers locals
      exact {
        owner := runtime.owner
        closed := runtime.closed
        variables_closed := runtime.variables_closed
        residual_variables_open := runtime.residual_variables_open
        graph := runtime.graph
        requirement_ledger := runtime.requirements
        occurrence := ⟨id, node, contains, form, rawAnnotation, by
          rw [form]
          simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq extended] using
            ExpressionFormHasRawType.lambda names extended bodyTyped completes⟩ }

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLambdaAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
open Core Frontend SourceInference

/-- Every genuine Header retains its actual cached ordinary origin, even when
it is used as an anchor outside the current finite inventory. -/
theorem certified {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :
    SelectedCompilationNamedSourceTyping.Certified header := by
  have signature : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
      header.instantiation.declaration = signature.id := by
    have instantiated := header.frame.instantiated
    cases instantiated with
    | @intro signature _ _ member _ declaration _ _ _ _ _ =>
      exact ⟨signature, member, declaration⟩
  obtain ⟨signature, member, declaration⟩ := signature
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  have matched := CallableNamedMetadata.matches_of_exact header.target record
  have origin := SelectedCompilationCatalog.ordinary_origin compiled bodies.signatures
    (CallableNamedMetadata.specialization_of_exact record).1 member
    (matched.declaration.trans declaration)
  obtain ⟨request, actualSignature, generic, signatureMember, genericMember, _resolved, accepted⟩ := origin
  have valid := bodies.ordinary generic
    ⟨header.slot, header.named, actualSignature, request.parameterSubstitution,
      header.selected, signatureMember, genericMember, accepted⟩
  have owner : (FunctionDefinition.ofChecked generic).body.owner = header.instantiation.declaration :=
    (RecursiveNamedSpecializationBodyFacts.identities accepted).2.2.symm.trans matched.declaration
  obtain ⟨types, lexical, facts, certificate⟩ :=
    header.frame.instantiated.certificate_of_valid bodies.signatures bodies.function_ids
      (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) owner valid
  have extended := header.extended
  rw [header.frame.source, header.frame.context, header.frame.parameters] at extended
  have contextEq := Dynamic.MonoBindersExtend.functional certificate.typing.inputs_extend extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ certificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalChildReceipts
/-! The actual accepted named body retains the same compiled terminal child.
Independent Source program typing authenticates that child's original raw
result type. The genuine parameter scope and production contextual compiler
construct its finite read/literal/group/pair receipt with literal sites. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalChildReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)

include terminal selected certified in
/-- Complete original Source typing selects the same used terminal occurrence
and its raw result type at the actual parameter context. -/
theorem source_child :
    ∃ node, header.function.source.lookupExpression? expression = some node ∧
      node.type = header.function.resultType ∧
      ExpressionHasType header.function.source header.context expression node.type := by
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨final, facts, typed, complete⟩ := certified.statements
  rw [← stages.source selected] at typed
  obtain ⟨node, found, rawType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique
      (terminal.head child (stages.source selected)) typed complete
  rw [stages.source selected] at found childTyped
  exact ⟨node, found, rawType, childTyped⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalChildReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPreparedBranchingLambdaFormation
/-! Actual named compilation retains the same lambda and its complete
scoped imperative body. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPreparedBranchingLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open PreparedBranchingLambdaFormation (Formation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)

/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.Syntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result) :
    Nonempty (Formation header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLambdaProducer.of_terminal terminal
    prepared profile diagnostic member found form owner requirements coercions ordinary read
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    SelectedCompilationNamedTerminalChildReceipts.source_child terminal.receipt selected certified
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result statements header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := certified
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  have entryDeclarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations
    (values := .initial compiled.compatible.checked) produced.site.code inputs facts declarations
  have signatures : inputs.context.signatures = compiled.compatible.checked.signatures := by
    exact (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).signatures.trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
  have syntaxTree : GenericImperativeMatch.Syntax function.source
      (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax function.source)
      inputs.context (.statements true function.body) function.resultType := by
    have typed : StatementsHaveType header.function.source {returnType := result}
        inputs.context statements _finalContext _bodyFacts := by
      simpa only [function, closure, source, ← header.agreement.source] using bodyTyped
    simpa only [function, closure, source, ← header.agreement.source] using syntaxFor typed
  have diagnosticTyping : EmittedDiagnosticTokenPlan.UnaryTyped (source header.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source header.named) := by
    have originalTyping := SourceDiagnosticTyping.diagnostic_typed_of_certificate
      certificate.toBodyInstanceTypingCertificate
    simpa only [source, ← header.agreement.source, header.frame.source] using originalTyping
  exact PreparedBranchingLambdaFormation.of_produced header produced diagnosticTyping
    inputs frame ledger profile actualView signatures
    (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    entryDeclarations syntaxTree
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPreparedBranchingLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReturnLambdaFormation
/-! Actual named compilation retains the same lambda and its single
return child. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReturnLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_terminal_parameters
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLambdaProducer.of_terminal terminal
    prepared profile diagnostic member found form owner requirements coercions ordinary read
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    SelectedCompilationNamedTerminalChildReceipts.source_child terminal.receipt selected certified
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result [statement] header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := certified
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have invocationSource : child.source = function.source :=
    (stages.source selected).trans original.symm
  have returnFound : function.source.lookupStatement? statement = some returnNode := by
    simpa only [original] using returnFound
  have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression function.body := by
    change CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression [statement]
    exact .returning [] (by rw [invocationSource]; exact lookupStatement?_sound returnFound) returnForm
  obtain ⟨readNode, childFound, childType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.at_parameters frame inputs.extended invocationSource head
  rw [invocationSource] at childFound childTyped
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  obtain ⟨lowered, body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedReturnLambdaBodySupport.of_return
    produced.site.code produced.recipe inputs frame ledger profile actualView rfl
    returnFound returnForm returnType childFound childType childTyped
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Syntax expression)
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Child expression lowered) body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReturnLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPreparedLambdaBodyFormation
/-! Actual named compilation retains the same lambda and its complete
scoped imperative body. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPreparedLambdaBodyFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open PreparedLambdaBodyFormation (Formation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)

/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape header.function.source true statements)
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.PreparedSyntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result) :
    Nonempty (Formation header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLambdaProducer.of_terminal terminal
    prepared profile diagnostic member found form owner requirements coercions ordinary read
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    SelectedCompilationNamedTerminalChildReceipts.source_child terminal.receipt selected certified
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result statements header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := certified
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  have entryDeclarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations
    (values := .initial compiled.compatible.checked) produced.site.code inputs facts declarations
  have signatures : inputs.context.signatures = compiled.compatible.checked.signatures := by
    exact (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).signatures.trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
  have syntaxTree : GenericImperativeMatch.PreparedSyntax function.source
      (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax function.source)
      inputs.context (.statements true function.body) function.resultType := by
    have typed : StatementsHaveType header.function.source {returnType := result}
        inputs.context statements _finalContext _bodyFacts := by
      simpa only [function, closure, source, ← header.agreement.source] using bodyTyped
    simpa only [function, closure, source, ← header.agreement.source] using syntaxFor typed
  have diagnosticTyping : EmittedDiagnosticTokenPlan.UnaryTyped (source header.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source header.named) := by
    have originalTyping := SourceDiagnosticTyping.diagnostic_typed_of_certificate
      certificate.toBodyInstanceTypingCertificate
    simpa only [source, ← header.agreement.source, header.frame.source] using originalTyping
  exact PreparedLambdaBodyFormation.of_produced header produced diagnosticTyping
    inputs frame ledger profile actualView signatures
    (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership) catalog
    (by simpa only [source, ← header.agreement.source] using shape) entryDeclarations syntaxTree
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPreparedLambdaBodyFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingTerminalChoice
/-! The retained ordinary compiler recipe supplies the exact accepted terminal
child. This choice keeps the compiler callback and a singleton certificate;
it contains no expression or body execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingTerminalChoice
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds (Point)

private theorem terminal_view {source view : TypedSource} {expression : ExpressionId}
    {statements : List StatementId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      source expression statements) :
    CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal view expression statements := by
  cases terminal with
  | returning rest found form => exact .returning rest (metadata.symm.statement found) form
  | tail found form => exact .tail (metadata.symm.statement found) form

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {stages : Staging.Recursive.Registry}

/-- Recapture keeps the original terminal statement and the compiler's actual
lowerer. The selected Source scope is retained unchanged in the packet. -/
theorem of_actual
    (code : Code compiled.indexed function scope administrative)
    (support : PreparedLambdaBodySupport.Support code)
    (provenance : PreparedLambdaBodySupport.PreparedAt code support)
    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages,
      packet.expression = expression ∧
      packet.policy.lowerExpression = FunctionCode.children code.policy code.lowerBody code.fuel code.compilation ∧
      packet.reasonAt = code.reasonAt ∧ packet.child = child ∧
      packet.certificate = Point
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        packet.expression packet.receipt.child ∧
      code.compilation.administrativePrefix = 1 := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := provenance.issued_recipe.body_recipe
  let callback := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed support.caller.named compilation.own.assignments diagnostics callback
  have actualCallback : code.lowerBody callback = SourceCoreLoops.lowerStatementsWithPolicy policy := by
    rw [recipe]
    exact CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed support.caller.named compilation.own.assignments diagnostics callback
  have viewed : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      code.view expression function.body := terminal_view code.viewOfSource terminal
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    code policy actualCallback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed support.caller.named compilation.own.assignments diagnostics callback) viewed accepted
  let packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages := {
    policy := policy
    fuel := code.fuel
    expression := expression
    reasonAt := code.reasonAt
    fellThrough := code.compilation.internalReason
    escaped := code.compilation.internalReason
    receipt := receipt
    certificate := Point
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression receipt.child
    certifies := by
      intro lowered generated
      exact ⟨rfl, rfl, Except.ok.inj (generated.symm.trans receipt.generated)⟩
    child := child
    selected := selected }
  refine ⟨packet, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [support.compilation]
  rfl

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingTerminalChoice
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryTerminalChoice
/-! The retained ordinary compiler recipe supplies the exact accepted terminal
child. This choice keeps the compiler callback and a singleton certificate;
it contains no expression or body execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryTerminalChoice
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds (Point)

private theorem terminal_view {source view : TypedSource} {expression : ExpressionId}
    {statements : List StatementId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      source expression statements) :
    CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal view expression statements := by
  cases terminal with
  | returning rest found form => exact .returning rest (metadata.symm.statement found) form
  | tail found form => exact .tail (metadata.symm.statement found) form

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {stages : Staging.Recursive.Registry}

/-- Recapture keeps the original terminal statement and the compiler's actual
lowerer. The selected Source scope is retained unchanged in the packet. -/
theorem of_actual
    (code : Code compiled.indexed function scope administrative)
    (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
    (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages,
      packet.expression = expression ∧
      packet.policy.lowerExpression = FunctionCode.children code.policy code.lowerBody code.fuel code.compilation ∧
      packet.reasonAt = code.reasonAt ∧ packet.child = child ∧
      packet.certificate = Point
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        packet.expression packet.receipt.child ∧
      code.compilation.administrativePrefix = 1 := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := provenance.issued_recipe.body_recipe
  let callback := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed support.caller.named compilation.own.assignments diagnostics callback
  have actualCallback : code.lowerBody callback = SourceCoreLoops.lowerStatementsWithPolicy policy := by
    rw [recipe]
    exact CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed support.caller.named compilation.own.assignments diagnostics callback
  have viewed : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      code.view expression function.body := terminal_view code.viewOfSource terminal
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    code policy actualCallback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed support.caller.named compilation.own.assignments diagnostics callback) viewed accepted
  let packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages := {
    policy := policy
    fuel := code.fuel
    expression := expression
    reasonAt := code.reasonAt
    fellThrough := code.compilation.internalReason
    escaped := code.compilation.internalReason
    receipt := receipt
    certificate := Point
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression receipt.child
    certifies := by
      intro lowered generated
      exact ⟨rfl, rfl, Except.ok.inj (generated.symm.trans receipt.generated)⟩
    child := child
    selected := selected }
  refine ⟨packet, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [support.compilation]
  rfl

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryTerminalChoice
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
/-! A successful public payload retains the actual semantic result and the
returned owned pool. The Source heap, closure captures and stable history come
from the preceding execution; exporting a handle does not construct them. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  {owner : OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : NamedCapture headers owner.key header mapping world}
  {payloads : List Value} {context : SourceSemantics.Context}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
  {native payload : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

/-- Real instantiated headers share the program catalog and have closed rigid
and lexical variable scopes. Both the declaration and its parameter context
therefore support the next declaration's actual runtime type context. -/
theorem header_context_supports
    (first next : Header compiled (Program.ofChecked compiled.sourceProgram))
    (bodies : SelectedCompilationBodyTyping.Bodies compiled) :
    Dynamic.TypeContextSupports first.function.context next.function.context ∧
      Dynamic.TypeContextSupports first.context next.function.context := by
  obtain ⟨_firstFacts, firstTyped⟩ := SelectedCompilationHeaderCertificates.certified bodies first
  obtain ⟨_nextFacts, nextTyped⟩ := SelectedCompilationHeaderCertificates.certified bodies next
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields first.extended
  have signatures : first.function.context.signatures = (Program.ofChecked compiled.sourceProgram).signatures :=
    (congrArg (fun context : SourceSemantics.Context => context.signatures) first.frame.context).trans
      firstTyped.signatures_eq
  have closed : first.function.context.typeParameters = [] :=
    (congrArg (fun context : SourceSemantics.Context => context.typeParameters) first.frame.context).trans
      firstTyped.type_parameters_empty
  have variables : first.function.context.typeVariables = [] :=
    (congrArg (fun context : SourceSemantics.Context => context.typeVariables) first.frame.context).trans
      firstTyped.type_variables_empty
  rw [next.frame.context]
  exact ⟨Dynamic.TypeContextSupports.ofClosed (nextTyped.signatures_eq.trans signatures.symm)
      closed nextTyped.type_parameters_empty variables nextTyped.residual_type_variables_open,
    Dynamic.TypeContextSupports.ofClosed (nextTyped.signatures_eq.trans (fields.signatures.trans signatures).symm)
      (fields.typeParameters.trans closed) nextTyped.type_parameters_empty
      (fields.typeVariables.trans variables) nextTyped.residual_type_variables_open⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryLambdaExclusion
/-! A lambda body cannot also be the complete declaration root list of a
successfully checked source forest. This distinguishes registry entry kinds. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryLambdaExclusion
open Frontend SourceInference TypeSystem SourceCoreStageContracts
open Solcore.SourceSemantics.Dynamic

theorem method_graph {program : CheckedProgram} {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {implementation : ProgramImplementationSignature} {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : ParameterSubstitution} {body : BodyInstance}
    (instantiates : TraitMethodInstantiates (Program.ofChecked program)
      implementation method trait definition substitution body) :
    OccurrenceGraphClosed body.source := by
  cases instantiates with
  | intro _ _ _ _ definitionMember _ _ _ _ sourceEq _ _ =>
    obtain ⟨retained, member, rfl⟩ := List.mem_map.mp definitionMember
    obtain ⟨_, _, _, _, _, _, _, success⟩ := Frontend.checkProgram_success_method_body checked member
    rw [sourceEq]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters substitution
      (SourceInferenceSoundness.checkFunctionBody_success_occurrenceGraphClosed success)

theorem lambda_header {plan : Plan} {owner : Key} {id : ExpressionId}
    {active : Substitution} {function : Dynamic.Closure} {contract : Contract}
    (origin : CallableLedger.LambdaOrigin plan owner id active function contract) :
    ∃ actual node, ContainsExpression function.source actual node ∧
      node.form = .lambda function.parameters function.resultType function.body := by
  cases origin with
  | original prepared receipt _ _ source parameters result body =>
    refine ⟨id, receipt.node, ?_, ?_⟩
    · rw [source]
      exact CallContractCertificates.expression_sound receipt.selected
    · rw [parameters, result, body]
      exact receipt.form
  | @contextual sidecar contextual _ _ prepared receipt _ _ source parameters result body =>
    refine ⟨id, receipt.node.applySubstitution contextual.substitution, ?_, ?_⟩
    · rw [source]
      exact FlexibleSubstitution.ContainsExpression.applySubstitution _
        (CallContractCertificates.expression_sound receipt.selected)
    · simp only [ExpressionNode.applySubstitution, receipt.form,
        ExpressionForm.applySubstitution, parameters, result, body]
  | applied recipe _ _ _ _ _ source parameters result body =>
    refine ⟨recipe.read.entry.view.principal.initializer,
      SourceTypedRuntime.rewriteExpressionLocalRequirements recipe.read.witnesses
        (recipe.applied.node.applySubstitution recipe.read.substitution), ?_, ?_⟩
    · rw [source]
      exact lookupExpression?_sound recipe.source_node
    · rw [parameters, result, body]
      exact recipe.source_node_form

  | independentApplied recipe _ _ _ _ _ paired header =>
    obtain ⟨node, found, _, form⟩ := (CallableIndependentSourceViews.of_pair paired).expression
      recipe.source_node
    exact ⟨_, node, lookupExpression?_sound found,
      form.trans (recipe.source_node_form.trans (recipe.header.trans header.symm))⟩

theorem root_exists {source : TypedSource} {id : NodeId}
    (reachable : Reachable source id) : ∃ root, root ∈ source.roots := by
  induction reachable with
  | root member => exact ⟨_, member⟩
  | child _ _ ih => exact ih

theorem statement_root_member {nodes : List NodeId} {ids : List StatementId}
    (roots : StatementRoots nodes ids) {root : NodeId} (member : root ∈ nodes) :
    ∃ id ∈ ids, root = .statement id := by
  induction roots with
  | nil => cases member
  | cons rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, by simp, rfl⟩
    · obtain ⟨id, member, same⟩ := ih member
      exact ⟨id, by simp [member], same⟩

theorem lambda_ne_whole_body {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : Ty}
    {body : List StatementId}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsExpression source id node)
    (form : node.form = .lambda parameters result body)
    (roots : StatementRoots source.roots body) : False := by
  obtain ⟨root, member⟩ := root_exists (closed.allNodesReachable _ contains.1)
  obtain ⟨statement, inBody, rfl⟩ := statement_root_member roots member
  apply closed.rootsHaveNoParent member (parent := .expression id)
  refine ⟨.expression node, ⟨contains.1, congrArg NodeId.expression contains.2⟩, ?_⟩
  simp [nodeChildIds, Node.references, form, ExpressionForm.references, inBody]

theorem anonymous_ne_whole_body {program : CheckedProgram} {plan : Plan}
    {table : SourceCoreStageCodebook.Table} {function : Dynamic.Closure}
    {scope : Staging.Recursive.Scope}
    (selected : RecursiveStageRegistry.Selected program plan table function scope)
    (closed : OccurrenceGraphClosed function.source)
    (roots : StatementRoots function.source.roots function.body) : False := by
  cases selected with
  | lambda _ _ _ _ origin | applied _ _ _ _ _ _ _ _ _ origin =>
    obtain ⟨id, node, contains, form⟩ := lambda_header origin
    exact lambda_ne_whole_body closed contains form roots

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryLambdaExclusion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
variable {bridge context}
theorem after_expression_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType invocation.source context id type)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last := by
  have stable := StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame
  cases outcome with
  | value value =>
    have preserved := Staging.Recursive.SelectedPreservation.expression selectedBodies
      runtime covers locals admitted.heap typed trace
    exact ⟨stable, by intro found same; cases same; exact ⟨preserved.value_typed _ rfl, preserved.heap_typed⟩⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨stable, by intro value same; cases same⟩
    | stage origin call reason => exact stable

end Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedInvocationBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterMeaning CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedNamedEntryBounds (Prefix)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

include functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt in
/-- The actual Header and its authenticated named sidecar construct the body
scope. The native prefix reaches its real allocation state, where the body port
reconstructs the staged body. The original global application and the
literal restored caller are then constructed with its actual final lexical context. -/
theorem reflects_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) child faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedStagedNamedEntryBounds.native_prefix
    (functions := functions) (registry := registry) owner caller header capture sameLayouts member represented heaps completed
  let receipt := CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.parameter_receipt functions owner caller header capture packet stable heapTyped argumentsTyped
  have source := SelectedCompilationNamedAdmission.parameter_source certified receipt.body.allocation receipt.heapTyped receipt.argumentsTyped
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt prepared aligned stagePrepared descriptor
  have selected : (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  have admitted : Admission poolBridge header.context packet.reached :=
    ⟨source.heapTyped, receipt.rows⟩
  obtain ⟨sourceSize, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld, trace, matched, result,
    finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    children selected packet.entry.environments packet.entry.heaps packet.entry.locals
      packet.entry.lookups packet.entry.actualTyped packet.reached admitted owner
      (fun zero globals => receipt.packet zero globals)
      packet.completed (Nat.le_of_lt (Nat.lt_of_lt_of_le packet.strict within))
  have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.applies
    (caller := invocation) (context := context) sourceAt stagePrepared selected
    header.extended packet.entry.allocation trace matched
  have maps := packet.entry.maps.trans bodyMaps
  have worlds := packet.entry.worlds.trans bodyWorlds
  have frame := packet.entry.frame.trans bodyFrame
  have metadata := packet.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := packet.related.trans bodyRelated
  have physical : (caller.rows owner.position).authority.frameLocation = keys[owner.position.val].frameLocation :=
    (caller.rows owner.position).frame_eq
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  have storeEq : finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex (body :=
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        finalMap, finalWorld, after, packet.bodyStore, packet.entry.canonical⟩) caller owner.position).store := by
    simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical] using packet.restored
  have whole := completed.sound
  rw [storeEq] at whole
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld, applied, ?_⟩
  rw [storeEq]
  exact ⟨whole, result, restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, restoredRelated, restoredPost⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedInvocationPreservation
/-! Authentic named parameter allocation and body preservation compose with
literal caller restoration. Body ports permit arbitrary final lexical Source
contexts while restoring the entry native scope and full caller admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedInvocationPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open SelectedCompilationNamedAdmission (body_prefix)

section Native
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (store : Store) (saved : Value) :
    Evaluates (saved :: actual) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

private theorem related_cast_frame
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

private theorem readyAt_cast
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include functions owner caller header capture sourceAt in
/-- Authentic Source allocation and the strict staged body child construct the
native parameter/body continuation before literal caller restoration. The
returned state retains full representation, relates and caller PostAdmission. -/
theorem preserves_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child faults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
      size invocation context heap (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner member
    exact original.locals
  have liveReference : capture.canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.reference
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨childSize, child, environment, bound, finalContext, bodyOutcome,
    selected, allocated, bodyTrace, converted, smaller⟩ := body_prefix sourceAt owners arity trace
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
      (DataPatternValues.packValues payloads :: capture.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped capture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame model :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys model
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      model owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, parameterTransition, agreement⟩ := parameters_with_state installedAuthority
    capture.environments liveLocals liveReference capture.coherent represented installedHeaps
    layout actualTyped producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner caller header arguments :=
    ⟨origin, index, metadata, capture.administrative, _,
      .unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured,
      Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift),
      authority.frameLocation, (caller.rows owner.position).frame_eq, owned, history, emitted,
      entry, parameterState, installedRelated.trans parameterRelated, stable, heapTyped, argumentsTyped⟩
  have admitted : Admission poolBridge header.context parameterState := ⟨(SelectedCompilationNamedAdmission.parameter_source certified receipt.body.allocation receipt.heapTyped receipt.argumentsTyped).heapTyped, receipt.rows⟩
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    children selected entry.environments entry.heaps entry.locals entry.lookups
      entry.actualTyped parameterState admitted owner
      (fun zero globals => receipt.packet zero globals)
      bodyTrace converted (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
  have prefixEvaluation := agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ, physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.capturedReference
  have evaluation := CallableContextFrames.withFrame_evaluates (.var reference) authority.frame.read
    (next_evaluates index (DataPatternValues.packValues payloads :: capture.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := installedRelated.trans (parameterRelated.trans bodyRelated)
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps, maps, worlds,
    restoredFrame, sourceMetadata, CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position,
    restoredRelated, restoredPost⟩
  simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using
    (renamed.symm ▸ evaluation)
end Native
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedInvocationPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedApplicationBounds
/-! The complete retained named carrier applies its literal native closure.
The real apply rule gives the invocation its strict native grade. The original
staged Source application and exact returned caller pool remain independent of
that grade; the invocation producers retain nested stage failure identity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

open CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds (carrier)

include functions owner caller header capture sourceAt in
/-- Source allocation and its selected body construct the exact invocation,
then the physical payload apply rule. No native grade is equated to Source. -/
theorem application_preserves
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (identity descriptor : Word) (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child faults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
      size invocation context before (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [carrier (owner := owner) header capture identity descriptor, DataPatternValues.packValues payloads]
        store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    SelectedCompilationNamedInvocationPreservation.preserves_invocation
      functions owner caller header capture sourceAt sameLayouts member owners certified
      stable heapTyped argumentsTyped represented heaps supports budget children trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) result.1, result⟩

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))

include functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt in
/-- The actual complete native apply supplies a strict body invocation grade.
Its original Header and authenticated staged scope then construct the Source
application, with the exact full postcondition in the returned caller pool. -/
theorem application_reflects
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (identity descriptorWord : Word) (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        child faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [carrier (owner := owner) header capture identity descriptorWord, DataPatternValues.packValues payloads]
      store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      Evaluates [carrier (owner := owner) header capture identity descriptorWord, DataPatternValues.packValues payloads]
        store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨bodySize, smaller, invoked⟩ := completed.apply_body
    (.second (.first (.var rfl))) (.var rfl)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    SelectedCompilationNamedInvocationBounds.reflects_invocation
      functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt
      sameLayouts member certified stable heapTyped argumentsTyped represented heaps supports budget children
      invoked (Nat.le_trans (Nat.le_of_lt smaller) within)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, result⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingBodyLambdaFormation
/-! Actual named compilation retains the same lambda and its complete
scoped imperative body. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingBodyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (shape : CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape header.function.source true statements)
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.Syntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLambdaProducer.of_terminal terminal
    prepared profile diagnostic member found form owner requirements coercions ordinary read
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    SelectedCompilationNamedTerminalChildReceipts.source_child terminal.receipt selected certified
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result statements header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := certified
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  have entryDeclarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations
    (values := .initial compiled.compatible.checked) produced.site.code inputs facts declarations
  have signatures : inputs.context.signatures = compiled.compatible.checked.signatures := by
    exact (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).signatures.trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
  have syntaxTree : GenericImperativeMatch.Syntax function.source
      (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax function.source)
      inputs.context (.statements true function.body) function.resultType := by
    have typed : StatementsHaveType header.function.source {returnType := result}
        inputs.context statements _finalContext _bodyFacts := by
      simpa only [function, closure, source, ← header.agreement.source] using bodyTyped
    simpa only [function, closure, source, ← header.agreement.source] using syntaxFor typed
  obtain ⟨body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedBranchingLambdaBodySupport.of_branching
    produced.site.code produced.issuedRecipe
    (by rw [terminal.aligned.named]; exact terminal.prepared.selected) rfl receiver included
    produced.site.compilation inputs frame ledger profile actualView
    (by rw [produced.site.compilation]; rfl) produced.site.active produced.site.allocationError
    signatures (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (by rw [CallableIndexedOwnedPublicSignatureCatalog.signatures compiled]; exact catalog) entryDeclarations (by simpa only [function, closure, source, ← header.agreement.source] using shape) syntaxTree
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax
    CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Child body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingBodyLambdaFormation
end
