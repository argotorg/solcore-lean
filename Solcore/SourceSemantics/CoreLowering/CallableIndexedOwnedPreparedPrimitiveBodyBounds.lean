import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRuntimeFamilyMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBuiltinFaultBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinCertificates

/-! Primitive bodies close admitted expression members using the existing
builtin producer. Static coverage retains ordinary context validity at the
actual certified expression; runtime validity alone cannot supply that fact.
The prepared flow and typed parameter continuations are then derived internally.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex PreservesAt ReflectsAt Family)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity FlowPreserves FlowReflects)
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- All four static facts concern the same actual certified context and code.
The ordinary ledger receipt is independent of the weaker runtime ledger. -/
structure StaticAt (i : OrdinaryIndex compiled) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop where
  tree : CompatibleExpressionBuiltins.Tree i.support.body.readFuel (.initial compiled.compatible.checked)
    i.function.source context i.code.compilation.solvedRequirements i.code.reasonAt scope id lowered
  valid : CompatibleExpressionLiterals.ContextValid i.code.compilation.solvedRequirements context i.function.evidence
  reads : ReachedLoweredReadOutcomePorts.ReadPolicies i.support.body.readFuel (.initial compiled.compatible.checked)
    i.function.source context i.code.reasonAt faults
  missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) i.function.source
    functions registry (Program.ofChecked compiled.sourceProgram) context i.function.evidence i.code.reasonAt faults

/-- Coverage is requested only for an actual certificate at its genuine valid
context. It contains static and diagnostic receipts, with no execution law. -/
def StaticCoverage (i : OrdinaryIndex compiled) : Prop :=
  ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
    ∀ scope id lowered, i.certificate context scope id lowered →
      StaticAt (registry := registry) (faults := faults) functions i context scope id lowered

/-- The existing accepted compiler producer supplies the literal builtin Tree.
Independent syntax, policy, Source typing and ordinary validity remain inputs. -/
theorem StaticAt.of_functions (i : OrdinaryIndex compiled) (context : SourceSemantics.Context)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilerContext : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (sameLedger : compilerContext.solvedRequirements = i.code.compilation.solvedRequirements)
    (declarations : CompatibleExpressionReads.ScopeDeclarations i.function.source scope context)
    (signatures : context.signatures = compiled.compatible.checked.signatures)
    (constructors : CompatibleExpressionInstantiationLaws.ConstructorLaw i.function.source context
      (CompatibleExpressionBuiltins.Syntax i.function.source))
    (policyFor : CompatibleExpressionBuiltins.PolicyFor policy compilerContext i.support.body.readFuel
      (.initial compiled.compatible.checked) i.function.source scope i.code.reasonAt)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (coercions : ∀ id node, CompatibleExpressionBuiltins.Syntax i.function.source id →
      i.function.source.lookupExpression? id = some node → node.coercions = [])
    (syntaxTree : CompatibleExpressionBuiltins.Syntax i.function.source id)
    (found : i.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType i.function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilerContext
      i.function.source scope id i.code.reasonAt = .ok lowered)
    (valid : CompatibleExpressionLiterals.ContextValid i.code.compilation.solvedRequirements context i.function.evidence)
    (reads : ReachedLoweredReadOutcomePorts.ReadPolicies i.support.body.readFuel (.initial compiled.compatible.checked)
      i.function.source context i.code.reasonAt faults)
    (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) i.function.source
      functions registry (Program.ofChecked compiled.sourceProgram) context i.function.evidence i.code.reasonAt faults) :
    StaticAt (registry := registry) (faults := faults) functions i context scope id lowered := by
  have tree := CompatibleExpressionBuiltins.tree_of_functions_with_validity
    i.support.unique declarations signatures constructors policyFor native active profile coercions
    syntaxTree found typed accepted
  rw [sameLedger] at tree
  exact ⟨tree, valid, reads, missing⟩

variable (i : OrdinaryIndex compiled)
  (coverage : StaticCoverage (registry := registry) (faults := faults) functions i)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include coverage extension faithful observations functionTypes wellFormed in
/-- The builtin producer runs once. Only its extra primitive fault post is
forgotten; the same semantic tuple and admitted reached state are returned. -/
theorem preserves_at (size : Nat) :
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
      PreservesAt (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i context size := by
  intro context valid scope id lowered certified node found sourceTyped mapping world administrative environment
    canonical actual actualContext before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  have packet := coverage context valid scope id lowered certified
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves
      (bridge := bridge (headers := headers) (keys := keys)) (functions := functions) (evidence := i.function.evidence)
      (transport := administrativeTransport headers keys) (extension := extension) (faithful := faithful)
      (observations := observations) (functionTypes := functionTypes) (valid := packet.valid)
      (reads := packet.reads) (missing := packet.missing) (unique := i.support.unique)
      (wellFormed := wellFormed) (runtime := valid.2) (covers := valid.1.covers)
      packet.tree found sourceTyped environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post.1⟩

include coverage extension faithful observations functionTypes wellFormed in
/-- Reflection keeps the independently returned Source grade and the exact
native completion's returned state when forgetting that extra post. -/
theorem reflects_at (size : Nat) :
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
      ReflectsAt (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i context size := by
  intro context valid scope id lowered certified node found sourceTyped mapping world administrative environment
    canonical actual actualContext before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  have packet := coverage context valid scope id lowered certified
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects
      (bridge := bridge (headers := headers) (keys := keys)) (functions := functions) (evidence := i.function.evidence)
      (transport := administrativeTransport headers keys) (extension := extension) (faithful := faithful)
      (observations := observations) (functionTypes := functionTypes) (valid := packet.valid)
      (reads := packet.reads) (missing := packet.missing) (unique := i.support.unique)
      (wellFormed := wellFormed) (runtime := valid.2) (covers := valid.1.covers)
      packet.tree found sourceTyped environments heaps locals agrees typed initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post.1⟩

include coverage extension faithful observations functionTypes wellFormed in
/-- Primitive coverage closes this literal expression family directly. -/
theorem family_at (size : Nat) :
    Family (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i size := by
  intro context valid
  exact ⟨preserves_at functions i coverage extension faithful observations functionTypes wellFormed size context valid,
    reflects_at functions i coverage extension faithful observations functionTypes wellFormed size context valid⟩

variable {table : SourceCoreFaultSites.Table}
  (rebuilt : i.support.issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep i.support.issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep i.support.issued.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := i.support.certificates i.support.body.readFuel i.function.source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory
        i.support.diagnosticPolicy i.function.source i.support.issued.invalidOperand)
      (faults := faults) (registry := registry) i.support.issued
      (bridge (headers := headers) (keys := keys)) functions table)

include coverage extension faithful observations functionTypes wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- The prepared head and loop recipes derive actual Source flow internally. -/
theorem preserves_flow (size : Nat) :
    FlowPreserves i.captured i.code i.support.body.toBody functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size := by
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.preserves_flow
    i.support.namedCompilation i.captured i.code i.support.issued i.support.body functions
    extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets size
    (fun context valid child _ =>
      preserves_at functions i coverage extension faithful observations functionTypes wellFormed child context valid)
    size (Nat.le_refl size)

include coverage extension faithful observations functionTypes wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Exact native flow grade uses the original Below result at size+1. No
Source grade is equated with that native grade. -/
theorem reflects_flow (size : Nat) :
    FlowReflects i.captured i.code i.support.body.toBody functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size := by
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.reflects_flow
    i.support.namedCompilation i.captured i.code i.support.issued i.support.body functions
    extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets (size + 1) functionTypes
    (fun context valid child _ =>
      reflects_at functions i coverage extension faithful observations functionTypes wellFormed child context valid)
    size (Nat.lt_succ_self size)

variable (history : History i.code) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, i.mapping, i.world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped i.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes i.function.context before arguments i.support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include coverage extension faithful observations functionTypes wellFormed rebuilt operandIncluded unaryIncluded interprets beforeTyped argumentsTyped stable in
/-- Actual Source parameter entry, flow and typed finish are closed here. -/
theorem source_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      i.captured i.code history i.support.body.toBody.toContext functions owner caller budget := by
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.source_continuation
    i.support.namedCompilation i.captured i.code i.support.issued i.support.body functions
    extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets
    history owner caller beforeTyped argumentsTyped stable budget
    (fun context valid child _ =>
      preserves_at functions i coverage extension faithful observations functionTypes wellFormed child context valid)

include coverage extension faithful observations functionTypes wellFormed rebuilt operandIncluded unaryIncluded interprets beforeTyped argumentsTyped stable in
/-- The same native parameter prefix uses genuine allocation and typed finish. -/
theorem native_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      i.captured i.code history i.support.body.toBody.toContext functions owner caller budget := by
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.native_continuation
    i.support.namedCompilation i.captured i.code i.support.issued i.support.body functions
    extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets
    history owner caller beforeTyped argumentsTyped stable budget functionTypes
    (fun context valid child _ =>
      reflects_at functions i coverage extension faithful observations functionTypes wellFormed child context valid)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveBodyBounds
