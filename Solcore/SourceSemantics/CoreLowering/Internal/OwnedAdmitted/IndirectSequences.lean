import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.ExpressionTrees
import Solcore.SourceSemantics.CoreLowering.ReachedNamedArgumentFaultPaths
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectCompiler

/-!
# Admitted profile: indirect sequences

Stored closure invocation, indirect sequences and named argument faults.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStoredClosureInvocation
/-! The actual argument-post caller Admission and genuine Source callee/argument
typing derive raw closure-context heap, binder and capture facts internally.
Actual Source heap extension retains callee typing from its success post.
Packed bundle equality and arity stay authentic Source call-site receipts.
The finite selected association and original strict body IH then invoke the
same payload producer and return the same actual caller pool. Stage/coercion
gates and the full parent expression remain a separate composition. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStoredClosureInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {slots : ProtectedStateTransition.Index → Prop}
  (carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  {mapping : LocationMap} {world : StoreTyping} {before calleeHeap : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}
  (association : CallableIndexedOwnedStoredClosureInvocation.Association
    headers keys registry faults mapping world function native bindings parameterCore resultCore)
  (initial : callerProtocol.State ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots carrier) context initial)
  {parameter result : TypeSystem.Ty}
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
  (extension : Dynamic.HeapTypesExtend calleeHeap before)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  {types : List TypeSystem.Ty} {packed : Dynamic.Value}
  (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments types)
  (packing : Dynamic.ValuesPack arguments packed)
  (bundle : TypeSystem.Ty.productMany types = parameter)
  (arity : arguments.length = function.parameters.length)

include wellFormed runtime association admitted calleeTyped extension represented heaps argumentsTyped packing bundle arity in
/-- Every raw callee input is derived at the actual argument post. The original
invocation selects only its strict body child and restores the current caller. -/
theorem preserves_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedStoredClosureInvocation.CallerResultAt
        (registry := registry) (faults := faults) functions carrier initial
        function resultCore outcome after value finalStore := by
  obtain ⟨raw, stable⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    (CallableIndexedOwnedIndirectCallerProtocol.forget_slots carrier) initial runtime admitted calleeTyped extension
    argumentsTyped packing bundle arity
  exact CallableIndexedOwnedStoredClosureInvocation.preserves_for functions carrier wellFormed association initial
    represented heaps raw.heaps raw.arguments raw.captures stable budget below trace within

include wellFormed runtime association admitted calleeTyped extension represented heaps argumentsTyped packing bundle arity in
/-- Native reflection retains the independently sized Source call and the
same actual caller restoration. Raw argument typing never comes from Core types. -/
theorem reflects_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedStoredClosureInvocation.CallerResultAt
        (registry := registry) (faults := faults) functions carrier initial
        function resultCore outcome after value finalStore := by
  obtain ⟨raw, stable⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    (CallableIndexedOwnedIndirectCallerProtocol.forget_slots carrier) initial runtime admitted calleeTyped extension
    argumentsTyped packing bundle arity
  exact CallableIndexedOwnedStoredClosureInvocation.reflects_for functions carrier wellFormed association initial
    represented heaps raw.heaps raw.arguments raw.captures stable budget below completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStoredClosureInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedIndirectSequence
/-! Admitted ordered arguments instantiate the neutral selected-call sequence
providers at their exact real input. The original Source typing row is independent
of the compiler parameter type vector. The same reached witness and relation
survive when the extra admission receipt is forgotten. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedIndirectSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {callerScope : SourceCoreLocalCell.Scope}
  {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  {originalSourceTypes : List TypeSystem.Ty}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (receipt : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)
  (children : DataExpressionSequence.Tree source certificate callerScope ids
    (receipt.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) codes)
  (unique : NodeOccurrencesUnique source)
  (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative callerScope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (initial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include receipt children unique typing environments heaps locals agrees typed admitted in
/-- Both original Source sequence outcomes use the actual admitted input. Success
and fault discard only the extra post receipt, retaining the identical state. -/
theorem preserves (budget : Nat)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults size) :
    SequencePreserves (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := receipt) (codes := codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) initial budget := by
  constructor
  · intro size arguments after execution bounded
    obtain ⟨payloads, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget children unique typing meaning
        environments heaps locals
        (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
        (.cons .unit (.cons receipt.typed typed)) initial admitted execution bounded
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
    exact ⟨payloads, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩
  · intro size reason after execution bounded
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_fault_bounded bridge budget children unique typing meaning
        environments heaps locals
        (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
        (.cons .unit (.cons receipt.typed typed)) initial admitted execution bounded
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩

include receipt children unique typing environments heaps locals agrees typed admitted in
/-- Native completion keeps its independent Source grade and the same actual
success or fault post; only the additional admission packet is forgotten. -/
theorem reflects (budget : Nat)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults size) :
    SequenceReflects (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := receipt) (codes := codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) initial budget := by
  intro size value finalStore evaluated bounded
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget children unique typing meaning
      environments heaps locals
      (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
      (.cons .unit (.cons receipt.typed typed)) initial admitted evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedIndirectSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedArgumentFaultBounds
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSelectedIndirectHeads
/-! The actual literal formation receipt feeds admitted ordered arguments at the
caller state transported to the formed copies. The original whole Source trace authenticates successful
value and heap typing at the exact returned witness. Faults retain their real
post and all-row stability. No uniform admission or execution law is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSelectedIndirectHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaNestedRuntimeBodyMeaning
open CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedSelectedIndirectHeads CallableIndexedOwnedSourceAdmission
open RecursiveNamedCatalogInvocationBounds (Below)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Receipt (headers := headers) (registry := registry) (faults := faults)
    (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ (bridge.pool initial))
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)

local notation "Record" => CalleeRecord owner caller prefixZero profile complete globals head bridge initial packet related
  agrees typed

include prefixZero complete globals slots related agrees typed heaps in
/-- Admitted arguments consume the actual literal callee post, at the formed
state that holds the copies of its captured cells. The original whole Source
derivation supplies successful value and heap typing at the exact returned
caller witness, with stable rows retained for either outcome. -/
theorem preserves_bounded
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (admitted : Admission bridge context initial)
    (parentTyped : ExpressionHasType source context id head.compiler.original.type)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
    (budget : Nat)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults))
    (bodies : ∀ formedRecord : Record,
      ∀ reached : callerProtocol.State ⟨scope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap,
        formedRecord.finalStore, canonical⟩,
      callerProtocol.Relates initial reached →
      SourceContinuations (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := head.ids) profile (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed heaps formedRecord)
        (head.selected environment).escaped bridge reached budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission bridge context head.compiler.original.type outcome reached := by
  obtain ⟨calleeSize, argumentsSize, callSize, calleeCaptured, calleeHeap, calleeTrace, calleeCopy, suffix,
      calleeSmall, argumentsSmall, callWithin⟩ :=
    suffix_of_source head.compiler.found head.compiler.originalForm head.parent.coercions
      head.compiler.argumentCoercions head.parent.arity head.lambda unique wellFormed runtime covers locals admitted.heap
      head.sourceArguments head.sourceCount trace
  obtain ⟨formedRecord⟩ := CallableIndexedOwnedLambdaFormationReceipts.formation_exists head.formation complete globals slots (bridge.pool initial) owner prefixZero
    packet.observed packet.carried packet.bundle related agrees typed heaps
  obtain ⟨_sourceCallee, sourceCopy, nativeCallee⟩ := formed_receipts owner caller prefixZero profile complete globals
    slots head bridge initial packet related agrees typed heaps formedRecord
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional calleeCopy sourceCopy
  rw [head.function_eq] at calleeTrace suffix
  obtain ⟨formedState, formedRelated⟩ :=
    caller_transition bridge initial formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
  have formedAdmitted : Admission bridge context formedState :=
    ⟨admitted.heap.copy formedRecord.copy,
      CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative (bridge.pool initial)
        (bridge.pool formedState) admitted.rows formedRecord.frame⟩
  have captures : FunctionValues.SourceCapturesValid formedRecord.finalHeap (.closure (formed head.formation formedRecord.captured)) :=
    formedRecord.copy.agrees locals
  let selected := head.selected environment
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceParent, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, relatedPost⟩ :=
    preserves_bounded_with_sequence profile head.compiler head.prepared head.parent (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed heaps formedRecord)
      selected.nativeTypes selected.escaped selected.rawResult selected.nativeResult
      (locals.mono formedRecord.copy.metadata_extends) captures wellFormed runtime covers formedAdmitted.heap
      head.sourceArguments head.sourceCount
      bridge formedState formedAdmitted.rows budget
      (CallableIndexedOwnedAdmittedIndirectSequence.preserves profile (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed heaps formedRecord)
        selected.children unique head.sourceArguments (related.extend formedRecord.maps formedRecord.worlds) formedRecord.heaps
        (locals.mono formedRecord.copy.metadata_extends) agrees (typed.weaken formedRecord.worlds) bridge formedState formedAdmitted budget
        arguments)
      (bodies formedRecord formedState formedRelated) initial formedRelated formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
      calleeTrace nativeCallee selected.stageAccepted selected.arityAccepted suffix
      (Nat.le_trans (Nat.le_of_lt argumentsSmall) within) (Nat.le_trans callWithin within)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, relatedPost,
    after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include prefixZero complete globals slots related agrees typed heaps in
/-- Native reflection uses the authentic emitted literal and admitted argument
sequence. Its independently graded whole Source trace authenticates successful
admission at the exact returned caller witness. -/
theorem reflects_bounded
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (admitted : Admission bridge context initial)
    (parentTyped : ExpressionHasType source context id head.compiler.original.type)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
    (budget : Nat)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults))
    (bodies : ∀ formedRecord : Record,
      ∀ reached : callerProtocol.State ⟨scope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap,
        formedRecord.finalStore, canonical⟩,
      callerProtocol.Relates initial reached →
      NativeContinuations (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := head.ids) profile (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed heaps formedRecord)
        (head.selected environment).escaped bridge reached budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission bridge context head.compiler.original.type outcome reached := by
  obtain ⟨formedRecord⟩ := CallableIndexedOwnedLambdaFormationReceipts.formation_exists head.formation complete globals slots (bridge.pool initial) owner prefixZero
    packet.observed packet.carried packet.bundle related agrees typed heaps
  obtain ⟨sourceCallee, _sourceCopy, nativeCallee⟩ := formed_receipts owner caller prefixZero profile complete globals
    slots head bridge initial packet related agrees typed heaps formedRecord
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size sourceCallee
  obtain ⟨formedState, formedRelated⟩ :=
    caller_transition bridge initial formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
  have formedAdmitted : Admission bridge context formedState :=
    ⟨admitted.heap.copy formedRecord.copy,
      CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative (bridge.pool initial)
        (bridge.pool formedState) admitted.rows formedRecord.frame⟩
  have captures : FunctionValues.SourceCapturesValid formedRecord.finalHeap (.closure (formed head.formation formedRecord.captured)) :=
    formedRecord.copy.agrees locals
  let selected := head.selected environment
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, relatedPost⟩ :=
    reflects_bounded_with_sequence profile head.compiler head.prepared head.parent (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed heaps formedRecord)
      selected.nativeTypes selected.escaped selected.rawResult selected.nativeResult
      (locals.mono formedRecord.copy.metadata_extends) captures wellFormed runtime covers formedAdmitted.heap
      head.sourceArguments head.sourceCount
      bridge formedState formedAdmitted.rows budget
      (CallableIndexedOwnedAdmittedIndirectSequence.reflects profile (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed heaps formedRecord)
        selected.children unique head.sourceArguments (related.extend formedRecord.maps formedRecord.worlds) formedRecord.heaps
        (locals.mono formedRecord.copy.metadata_extends) agrees (typed.weaken formedRecord.worlds) bridge formedState formedAdmitted budget
        arguments)
      (bodies formedRecord formedState formedRelated) initial formedRelated formedRecord.maps formedRecord.worlds formedRecord.frame formedRecord.copy.metadata_extends
      calleeTrace nativeCallee selected.stageAccepted selected.arityAccepted completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, relatedPost,
    after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

/-- This carrier projects only slot proofs; it retains the complete actual
nested packet pool and its receipt-aware return operation. -/
def nestedBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True)
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller)

/-- A body continuation obligation is asked only at the authentic literal
producer and its real admitted input. The shared mutual closer can supply its
strict body children without a universal arbitrary closure representation. -/
def SourceBodiesAt (budget : Nat) : Prop :=
  ∀ {childScope childId childLowered},
  ∀ head : Receipt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) caller certificate childScope childId childLowered,
  ∀ {mapping world administrative environment canonical actual actualContext heap store ξ},
  ∀ (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative childScope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (_locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨childScope, mapping, world, heap, store, canonical⟩),
    Admission (nestedBridge (headers := headers) owner caller) context initial →
    ∀ formedRecord : CalleeRecord owner caller prefixZero profile complete globals head
      (nestedBridge (headers := headers) owner caller) initial initial.property related agrees typed,
    ∀ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨childScope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap, formedRecord.finalStore,
        canonical⟩,
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).Relates initial reached →
    SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile
      (formedReceipt owner caller prefixZero profile complete globals slots head
        (nestedBridge (headers := headers) owner caller) initial initial.property related agrees typed heaps formedRecord)
      (head.selected environment).escaped (nestedBridge (headers := headers) owner caller) reached budget

/-- Native continuation obligations retain the same actual producer/input and
its original parameter prefix. Their Source grade remains independent. -/
def NativeBodiesAt (budget : Nat) : Prop :=
  ∀ {childScope childId childLowered},
  ∀ head : Receipt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) caller certificate childScope childId childLowered,
  ∀ {mapping world administrative environment canonical actual actualContext heap store ξ},
  ∀ (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative childScope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (_locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨childScope, mapping, world, heap, store, canonical⟩),
    Admission (nestedBridge (headers := headers) owner caller) context initial →
    ∀ formedRecord : CalleeRecord owner caller prefixZero profile complete globals head
      (nestedBridge (headers := headers) owner caller) initial initial.property related agrees typed,
    ∀ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨childScope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap, formedRecord.finalStore,
        canonical⟩,
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).Relates initial reached →
    NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile
      (formedReceipt owner caller prefixZero profile complete globals slots head
        (nestedBridge (headers := headers) owner caller) initial initial.property related agrees typed heaps formedRecord)
      (head.selected environment).escaped (nestedBridge (headers := headers) owner caller) reached budget

/-- The existing admitted Tree head callback consumes its actual input
admission. The literal receipt selects one authentic formed producer, and all
argument/body effects are returned with the identical final packet witness. -/
theorem head_preserves_at
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source) (size : Nat)
    (arguments : Below size (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (nestedBridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults))
    (bodies : SourceBodiesAt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) (certificate := certificate) owner caller prefixZero profile complete globals slots size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (nestedBridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source
      (Head (headers := headers) (registry := registry) (faults := faults)
        (source := source) (context := context) (evidence := evidence) caller certificate) faults size := by
  intro childScope childId childLowered certified node found parentTyped mapping world administrative environment canonical actual actualContext
    heap store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨head⟩ := certified
  have same := Option.some.inj (head.compiler.found.symm.trans found)
  subst node
  exact preserves_bounded owner caller prefixZero profile complete globals slots head
    (nestedBridge (headers := headers) owner caller) initial initial.property environments agrees typed
    heaps locals admitted parentTyped wellFormed runtime covers unique size arguments
    (bodies head environments heaps locals agrees typed initial admitted) trace (Nat.le_refl size)

/-- Native completion returns the same packet and an independently graded
whole Source trace with successful admission at that actual post. -/
theorem head_reflects_at
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source) (size : Nat)
    (arguments : Below size (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (nestedBridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults))
    (bodies : NativeBodiesAt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) (certificate := certificate) owner caller prefixZero profile complete globals slots size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (nestedBridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source
      (Head (headers := headers) (registry := registry) (faults := faults)
        (source := source) (context := context) (evidence := evidence) caller certificate) faults size := by
  intro childScope childId childLowered certified node found parentTyped mapping world administrative environment canonical actual actualContext
    heap store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨head⟩ := certified
  have same := Option.some.inj (head.compiler.found.symm.trans found)
  subst node
  exact reflects_bounded owner caller prefixZero profile complete globals slots head
    (nestedBridge (headers := headers) owner caller) initial initial.property environments agrees typed
    heaps locals admitted parentTyped wellFormed runtime covers unique size arguments
    (bodies head environments heaps locals agrees typed initial admitted) completed (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSelectedIndirectHeads
end
