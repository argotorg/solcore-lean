import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds
import Solcore.SourceSemantics.CoreLowering.ReachedNamedArgumentFaultPaths

/-! Named argument faults use the original admitted sequence producer once.
Reflection retains its actual argument child and exposes the failed-list route
conditionally. The body route is not assigned a primitive fault packet. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedArgumentFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission ExpressionFailurePostContracts
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (certificate : GenericExpressionMeaning.Certificate) (faults : GenericExpressionMeaning.FaultRep)

/-- This branch names one actual Source fault and the identical native parent
failure at the reached state. It does not extract an origin from FaultRep. -/
def FaultAt (post : ExpressionFaultPost)
    {initialIndex : ProtectedStateTransition.Index} (initial : callerProtocol.State initialIndex)
    (environment : Dynamic.Environment) (id : ExpressionId) (node : ExpressionNode)
    (lowered : SourceCoreBasic.LoweredExpr) (actual : Environment) (ξ : Renaming)
    (reason : Dynamic.SemanticFault)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop :=
  ∃ sourceSize,
    RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment
      initialIndex.heap id (.fault reason) index.heap ∧
    PostAdmission bridge context node.type (.fault reason) reached ∧
    CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt (program := program) (source := source)
      (context := context) evidence post initial environment id lowered actual ξ (.fault reason) reached

variable (post : ExpressionFaultPost) (scope : SourceCoreLocalCell.Scope) (ids : List ExpressionId)
  (codes : List SourceCoreBasic.LoweredExpr) (id : ExpressionId) (node : ExpressionNode)
  (lowered : SourceCoreBasic.LoweredExpr) (budget : Nat)

/-- The complete result of the branch keeps all original semantic effects. -/
def PreservesBranch : Prop :=
  ∀ {mapping world administrativeContext actualContext environment canonical actual before after store ξ reason size},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after →
    size ≤ budget →
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        FaultAt (program := program) bridge context evidence source post initial environment id node lowered actual ξ reason reached

/-- The child is the one first bind of the actual parent completion. Only its
failed-list alternative supplies the parent fault post and final-store equality. -/
def ReflectsArgumentsBranch (listPost : ExpressionsFaultPost) (sourceTypes : List TypeSystem.Ty) : Prop :=
  ∀ {mapping world administrativeContext actualContext environment canonical actual before store finalStore ξ value size},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore → size ≤ budget →
    ∃ child argumentValue argumentStore,
      child < size ∧
      EvaluationSize child actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) argumentValue argumentStore ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        ProtectedDataExpressionSequence.TraceAt program sourceSize context evidence source environment before ids outcome after ∧
        DataExpressionSequence.Result model finalMap finalWorld sourceTypes codes faults outcome argumentValue ∧
        GenericHeap.HeapRepresents model finalMap finalWorld after argumentStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap argumentStore ∧ Dynamic.HeapMetadataExtend before after ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, argumentStore, canonical⟩,
          callerProtocol.Relates initial reached ∧
          CallableIndexedOwnedAdmittedExpressionSequence.PostSequenceAdmission bridge (context := context) outcome reached ∧
          ListOutcomePost listPost program context evidence source environment before ids
            (SourceCoreCalls.packArguments codes).type outcome after argumentValue finalMap finalWorld argumentStore ∧
          (∀ reason, outcome = .error reason → ∃ token,
            value = .inLeft lowered.type (.word token) ∧ finalStore = argumentStore ∧
            FaultAt (program := program) bridge context evidence source post initial environment id node lowered actual ξ reason reached)

variable {bridge model context evidence source certificate faults post scope ids codes id node lowered budget}
variable {sourceTypes originalSourceTypes : List TypeSystem.Ty} {callee : ExpressionId} {calleeNode : ExpressionNode}
  {instantiation : DeclarationInstantiation} {name : String} {signature : SourceCoreCalls.Signature}
  {slot : Nat} {internalReason : Word}
  (parent : ContainsExpression source id node)
  (form : node.form = .call callee ids (.declaration instantiation))
  (calleeContains : ContainsExpression source callee calleeNode)
  (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
  (sourceTyped : ExpressionHasType source context id node.type)
  (parameterType : (SourceCoreCalls.packArguments codes).type = signature.parameterType)
  (resultType : lowered.type = signature.resultType)
  (emitted : lowered.expression = SourceCoreCalls.call signature slot
    (SourceCoreCalls.packArguments codes).expression internalReason)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include parent form calleeContains calleeForm sourceTyped parameterType resultType emitted wellFormed runtime covers in
/-- One actual sequence proof is lifted by the original native failure bind
and the two original sized Source constructors. -/
theorem preserves (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (joins : SequenceJoins expressionPost listPost program context evidence source)
    (namedJoin : NamedArgumentFaultPostContracts.ArgumentsJoin post listPost program context evidence source)
    (tree : Tree source certificate scope ids sourceTypes codes) (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds.PreservesAt
      bridge model context evidence source certificate faults expressionPost size) :
    PreservesBranch bridge model context evidence source faults post scope ids id node lowered budget := by
  intro mapping world admin actualContext environment canonical actual before after store ξ reason size
    environments heaps locals layout typed initial admitted failed bounded
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
    maps, worlds, frame, metadata, reached, related, _rows, retained⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds.preserves_fault_bounded bridge model context evidence source
      certificate faults expressionPost listPost joins budget tree unique typing meaning
      environments heaps locals layout typed initial admitted failed bounded
  have nativeFault : Evaluates actual store (lowered.expression.rename ξ)
      (.inLeft lowered.type (.word token)) finalStore := by
    rw [emitted, NamedCalls.Arguments.call_rename, resultType]
    exact SourceCoreCalls.call_argument_failure (parameterType ▸ evaluated)
  have sourceFault : RecursiveNamedCallBounds.ExpressionOutcome program
      (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [size]]) context evidence source environment
      before id (.fault reason) after :=
    .fault (NamedArgumentFaultPostContracts.source_fault parent form calleeContains calleeForm failed)
  exact ⟨token, finalStore, finalMap, finalWorld, nativeFault, matched, finalHeaps, maps, worlds,
    frame, metadata, reached, related, _, sourceFault,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped sourceFault frame,
    token, nativeFault, namedJoin.arguments parent form calleeContains calleeForm failed.sound retained⟩

include parent form calleeContains calleeForm sourceTyped parameterType resultType emitted wellFormed runtime covers in
/-- The full native parent is inverted once. The real ordered argument child
is reflected once, and determinism aligns only its actual failed-list route. -/
theorem reflects (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (joins : SequenceJoins expressionPost listPost program context evidence source)
    (namedJoin : NamedArgumentFaultPostContracts.ArgumentsJoin post listPost program context evidence source)
    (tree : Tree source certificate scope ids sourceTypes codes) (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds.ReflectsAt
      bridge model context evidence source certificate faults expressionPost size) :
    ReflectsArgumentsBranch bridge model context evidence source faults post scope ids codes id node lowered budget listPost sourceTypes := by
  intro mapping world admin actualContext environment canonical actual before store finalStore ξ value size
    environments heaps locals layout typed initial admitted completed bounded
  have nativeParent := completed
  rw [emitted, NamedCalls.Arguments.call_rename] at nativeParent
  obtain ⟨child, argumentValue, argumentStore, smaller, evaluated⟩ := RecursiveNamedCallBounds.call_arguments nativeParent
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, admission, retained⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds.reflects_bounded bridge model context evidence source
      certificate faults expressionPost listPost joins budget tree unique typing meaning
      environments heaps locals layout typed initial admitted evaluated (Nat.lt_of_lt_of_le smaller bounded)
  refine ⟨child, argumentValue, argumentStore, smaller, evaluated, sourceSize, outcome, after, finalMap,
    finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related,
    admission, retained, ?_⟩
  intro reason sameOutcome
  cases sameOutcome
  cases sourceTrace with
  | fault failed =>
    obtain ⟨token, sameValue, origin⟩ := retained
    have nativeFault : Evaluates actual store (lowered.expression.rename ξ)
        (.inLeft lowered.type (.word token)) argumentStore := by
      rw [emitted, NamedCalls.Arguments.call_rename, resultType]
      exact SourceCoreCalls.call_argument_failure (parameterType ▸ (sameValue ▸ evaluated.sound))
    obtain ⟨sameParent, sameStore⟩ := evaluation_deterministic completed.sound nativeFault
    have sourceFault : RecursiveNamedCallBounds.ExpressionOutcome program
        (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [sourceSize]]) context evidence source environment
        before id (.fault reason) after :=
      .fault (NamedArgumentFaultPostContracts.source_fault parent form calleeContains calleeForm failed)
    exact ⟨token, sameParent, sameStore, _, sourceFault,
      after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped sourceFault frame,
      token, nativeFault, namedJoin.arguments parent form calleeContains calleeForm failed.sound origin⟩

section Builtin
variable (bridge)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked) source context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) source functions registry
    program context evidence reasonAt faults)
  (unique : NodeOccurrencesUnique source)
  (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
  (tree : Tree source (CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked)
    source context solved reasonAt) scope ids sourceTypes codes)

include parent form calleeContains calleeForm sourceTyped parameterType resultType emitted wellFormed runtime covers
  transport extension faithful observations functionTypes valid reads missing unique typing tree in
/-- The concrete branch derives its actual argument packet from strict builtin
children. No completed sequence law or category-wide origin supplier is assumed. -/
theorem preserves_builtin :
    PreservesBranch bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source faults (ReachedNamedArgumentFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
      scope ids id node lowered budget := by
  exact preserves parent form calleeContains calleeForm sourceTyped parameterType resultType emitted wellFormed runtime covers
    (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
    (ReachedBuiltinExpressionFaultPaths.model_expressionsPost compiled.compatible.checked functions registry)
    (ReachedBuiltinExpressionFaultPaths.sequence_joins compiled.compatible.checked functions registry program context evidence source)
    (ReachedNamedArgumentFaultPaths.arguments_join compiled.compatible.checked functions registry program context evidence source)
    tree unique typing
    (fun size _ => CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds.preserves_builtin bridge context evidence source faults functions
      transport extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers size)

include parent form calleeContains calleeForm sourceTyped parameterType resultType emitted wellFormed runtime covers
  transport extension faithful observations functionTypes valid reads missing unique typing tree in
/-- Reflection exposes the original first-bind child and a conditional fault
route. Successful arguments retain their original sequence receipt. -/
theorem reflects_builtin :
    ReflectsArgumentsBranch bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source faults (ReachedNamedArgumentFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
      scope ids codes id node lowered budget
      (ReachedBuiltinExpressionFaultPaths.model_expressionsPost compiled.compatible.checked functions registry) sourceTypes := by
  exact reflects parent form calleeContains calleeForm sourceTyped parameterType resultType emitted wellFormed runtime covers
    (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
    (ReachedBuiltinExpressionFaultPaths.model_expressionsPost compiled.compatible.checked functions registry)
    (ReachedBuiltinExpressionFaultPaths.sequence_joins compiled.compatible.checked functions registry program context evidence source)
    (ReachedNamedArgumentFaultPaths.arguments_join compiled.compatible.checked functions registry program context evidence source)
    tree unique typing
    (fun size _ => CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds.reflects_builtin bridge context evidence source faults functions
      transport extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers size)

end Builtin
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedArgumentFaultBounds
