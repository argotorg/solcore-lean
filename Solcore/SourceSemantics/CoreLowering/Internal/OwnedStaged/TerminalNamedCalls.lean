import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualStoredCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation

/-!
# Staged bounds: terminal named calls

Named calls with terminal bodies: argument rows, entry and child bounds, invocation, application, parent bounds and global dispatch.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows
/-! The same authentic Header and actual argument state retain the original
raw Source row and ordered native values. Selected physical arity is derived
before packed rows are aligned. Successful staged children supply heap typing;
no body execution, application result or equality between grades is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)

include sourceAt in
/-- The real Source certificate and its monomorphic binder extension transport
the Header's body typing back to this original caller context. -/
theorem caller_supports
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {context : SourceSemantics.Context} {source : TypedSource}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source) :
    Dynamic.TypeContextSupports header.context context := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
  have inherited := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have signatures : header.context.signatures = (Program.ofChecked compiled.sourceProgram).signatures :=
    inherited.signatures.trans
      ((congrArg (fun current : SourceSemantics.Context => current.signatures) sourceAt.frame.context).trans certified.signatures_eq)
  have closed : header.context.typeParameters = [] :=
    inherited.typeParameters.trans
      ((congrArg (fun current : SourceSemantics.Context => current.typeParameters) sourceAt.frame.context).trans certified.type_parameters_empty)
  have variables : header.context.typeVariables = [] :=
    inherited.typeVariables.trans
      ((congrArg (fun current : SourceSemantics.Context => current.typeVariables) sourceAt.frame.context).trans certified.type_variables_empty)
  exact Dynamic.TypeContextSupports.ofClosed (runtime.signatures.trans signatures.symm)
    closed runtime.closed variables runtime.residual_variables_open

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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
      CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
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

section Successful
variable {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {ids : List ExpressionId} {types : List TypeSystem.Ty}
  {arguments : List Dynamic.Value} {parameter result : TypeSystem.Ty}

include sourceAt in
/-- The actual successful staged argument trace constructs raw Header admission
at its reached heap. The separate physical receipt supplies only arity, and the
same heap extension admits the genuine global callable without a body law. -/
theorem at_successful_arguments
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types)
    (calleeTyped : Dynamic.ValueHasType context before (.global function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : header.function.parameters.length = arguments.length)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before ids (.values arguments) after) :
    Dynamic.HeapWellTyped header.function.context after ∧
      Dynamic.ValuesHaveTypes header.function.context after arguments header.types ∧
      Dynamic.TypeContextSupports header.context context := by
  obtain ⟨argumentsTyped, finalHeap, extension⟩ :=
    CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping.values_at
      wellFormed runtime covers locals heapTyped typing trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have packedTyped : Dynamic.ValueHasType context after packed parameter :=
    bundle ▸ packing.hasType argumentsTyped
  obtain ⟨bodyHeap, bodyArguments⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.arguments_at_global
      sourceAt wellFormed runtime finalHeap (calleeTyped.mono extension) packing packedTyped arity
  exact ⟨bodyHeap, bodyArguments, caller_supports sourceAt wellFormed runtime⟩
end Successful
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedChildBounds
/-! Named child laws retain the authentic nested packet when a body forms a
closure. Existing pool-only children remain a separate supported branch. The
actual parameter receipt chooses and supplies the runtime input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedChildBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header OwnedKey)
open CallableIndexedOwnedAdmittedStagedExpressionBounds

section Definitions
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)
  (certificate : GenericExpressionMeaning.Certificate) (faults : RecursiveStageMeaning.FaultRep)

abbrev poolBridge := CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
abbrev nestedBridge (owner : OwnedKey keys) := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner header

inductive PreservesBelow (budget : Nat) : Prop where
  | pool (meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (poolBridge (headers := headers) (keys := keys)) header.context model stages child certificate faults budget)
  | nested (globals : header.globals = compiled.indexed.base.globals.length)
      (zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0)
      (meaning : ∀ owner : OwnedKey keys, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
        (nestedBridge (headers := headers) header owner) header.context model stages child certificate faults budget)

inductive ReflectsBelow (budget : Nat) : Prop where
  | pool (meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (poolBridge (headers := headers) (keys := keys)) header.context model stages child certificate faults budget)
  | nested (globals : header.globals = compiled.indexed.base.globals.length)
      (zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0)
      (meaning : ∀ owner : OwnedKey keys, CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
        (nestedBridge (headers := headers) header owner) header.context model stages child certificate faults budget)

end Definitions
section Bodies
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {expression : ExpressionId}
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Receipt header.policy header.fuel header.function.source
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
  (initial : State headers keys
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
  (admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context initial)
  (owner : OwnedKey keys)
  (packet : owner.key.capturePrefix = 0 → header.globals = compiled.indexed.base.globals.length →
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial)

include selected wellFormed terminal certifies environments heaps locals agrees typed admitted packet in
/-- The original named body Source typing and genuine selected child scope
construct preservation from the used strict expression hypothesis. The body
trace and nested failure scope remain recursively staged. -/
theorem preserves_body (budget : Nat)
    (children : PreservesBelow (headers := headers) (keys := keys) header model stages child certificate faults budget)
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
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached := by
  cases children with
  | pool meaning =>
    exact CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.preserves_body
      (bridge := poolBridge) selected wellFormed terminal certifies environments heaps locals agrees typed
      initial admitted budget meaning trace matched within
  | nested globals zero meaning =>
    let wrapped : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State _ :=
      ⟨initial, packet (zero owner) globals⟩
    have nestedAdmitted : Admission (nestedBridge header owner) header.context wrapped := ⟨admitted.heap, admitted.rows⟩
    obtain ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.preserves_body
        (bridge := nestedBridge header owner) selected wellFormed terminal certifies environments heaps locals agrees typed
        wrapped nestedAdmitted budget (meaning owner) trace matched within
    refine ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps, worlds,
      frame, metadata, reached.val, related, ?_⟩
    cases outcome with
    | value => exact ⟨post.rows, post.successful⟩
    | fault failure =>
      cases failure with
      | semantic => exact ⟨post.rows, post.successful⟩
      | stage => exact post

include selected wellFormed terminal certifies environments heaps locals agrees typed admitted packet in
/-- Literal native body completion reflects to an independently graded staged
Source body, using the same accepted Header code and actual parameter state.
The complete returned pool and successful Source post are retained. -/
theorem reflects_body (budget : Nat)
    (children : ReflectsBelow (headers := headers) (keys := keys) header model stages child certificate faults budget)
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
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached := by
  cases children with
  | pool meaning =>
    exact CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.reflects_body
      (bridge := poolBridge) selected wellFormed terminal certifies environments heaps locals agrees typed
      initial admitted budget meaning completed within
  | nested globals zero meaning =>
    let wrapped : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header).State _ :=
      ⟨initial, packet (zero owner) globals⟩
    have nestedAdmitted : Admission (nestedBridge header owner) header.context wrapped := ⟨admitted.heap, admitted.rows⟩
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds.reflects_body
        (bridge := nestedBridge header owner) selected wellFormed terminal certifies environments heaps locals agrees typed
        wrapped nestedAdmitted budget (meaning owner) completed within
    refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, represented, finalHeaps,
      maps, worlds, frame, metadata, reached.val, related, ?_⟩
    cases outcome with
    | value => exact ⟨post.rows, post.successful⟩
    | fault failure =>
      cases failure with
      | semantic => exact ⟨post.rows, post.successful⟩
      | stage => exact post

end Bodies
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedChildBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEntryBounds
/-! Native completion of an actual retained named Header selects the original
hook and marked parameter prefix. The literal captured environment, installed
history, reached owned pool, strict native body grade and physical caller
restoration equation are retained. No Source body trace or application meaning
is required or produced by this independent entry producer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEntryBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions) :
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog) mapping world
      (type :: administrative) scope environment (Environment.insertAt canonical scope.length value) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by
  induction related with
  | nil suffixTyped => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed suffixTyped)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

private theorem parameters_sized_with_state (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (authority : Authority (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers owner.key.locations owner.key.capturePrefix mapping world heap store)
    {header : Header (compiled.indexed.ancestry) (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions program} (_member : header ∈ headers)
    (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
    (locals : Dynamic.EnvironmentAgrees heap header.function.context.locals [])
    (reference : capture.canonical[header.globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation))
    {functions : FunctionModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (header.parameterCode.rename ξ) result afterStore)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts (compiled.indexed.ancestry).layout.frame (CompatibleAmbientHeap.payloadModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions))
    (initial : State headers keys ⟨[], mapping, world, heap, store, capture.canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation authority.current) :
    ∃ entry : BodyState headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost,
      ∃ child, EvaluationSize child entry.actualBody entry.store (header.body.rename entry.embedding) result afterStore ∧
        child ≤ size ∧ (header.bindings ≠ [] → child < size) ∧
        ProtectedStateTransition.Transition (protocol headers keys) initial
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError header.acceptedPrefix
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) capture.canonical
      (DataPatternValues.packValues payloads :: capture.canonical) := by
    intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding, child,
    allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, bodyCompletion, childLe, childStrict, reached, related⟩ :=
    RecursiveNamedCallBounds.Stateful.parameter_prefix tree (protocol headers keys) producer header.definitions_eq header.registered represented capture.environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using reference) authority.frame.read authority.unmapped initial readyAt completed
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (header.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = header.bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical header.bindings.length
      (DataPatternValues.packValues payloads) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  rw [← header.parameters] at allocated
  have metadata := GenericLexicalContext.binders_metadata allocated
  let catalog : Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers owner.key.locations owner.key.capturePrefix (owner.key.capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld finalHeap finalStore finalLogical := by
    refine ⟨authority.extend maps worlds preservation metadata, ?_⟩
    intro target targetMember
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : header.bindings.length + (owner.key.capturePrefix + 1) + target.slot =
        added.length + (owner.key.capturePrefix + target.slot + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using capture.coherent target targetMember
  have finalReference : finalLogical[header.bindings.length + 1 + header.globals]? =
      some (.cellRef (compiled.indexed.ancestry).layout.frame.type authority.frameLocation) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + header.globals = added.length + (header.globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  have current := CallableIndexedBodyFrames.body_current authority.unmapped authority.frame preservation
  have mono := FunctionCallBody.mono_binders header.extended
  refine ⟨BodyState.of_receipts environment  finalHeap  finalLogical  finalActual  finalStore  finalMap  finalWorld  embedding
    allocated (by simpa only [List.append_nil, CallableIndexedAmbient.ambientDefinitions] using finalWithBundle) finalHeaps
    (GenericLexicalContext.binders_agree mono.1 mono.2 locals allocated)
    maps  worlds  preservation  metadata  lookups  finalTyped  catalog  finalReference  current  (by rfl)  (by rfl)  (by
      change (authority.extend maps worlds preservation metadata).ghost = authority.ghost
      rfl), child, bodyCompletion, childLe, childStrict, reached, related⟩

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


variable {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
  (arguments : List Dynamic.Value) (payloads : List Value)

/-- All fields belong to one original completed named invocation, before its
body meaning is established. The saved caller cell is restored literally. -/
structure Prefix (size : Nat) (value : Value) (finalStore : Store) where
  origin : Word
  index : Int
  metadata : MetadataState
  owned : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin
  history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (.state index) (.named origin) (some metadata)
  emitted : header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
    (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode
  actualContext : Core.Context
  entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
    (store.set (caller.rows owner.position).authority.frameLocation
      (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world capture.administrative actualContext
    (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
      DataPatternValues.packValues payloads :: capture.captured)
    (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
    (caller.rows owner.position).authority.frameLocation (.state index) (.named origin)
  nativeSize : Nat
  bodyStore : Store
  completed : EvaluationSize nativeSize entry.actualBody entry.store (header.body.rename entry.embedding) value bodyStore
  strict : nativeSize < size
  restored : finalStore = bodyStore.set (caller.rows owner.position).authority.frameLocation
    (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current)
  reached : State headers keys
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩
  related : Relates caller reached

variable {arguments payloads}
include owner caller header capture in
/-- The real retained closure completion exposes its authentic strict body
child through the original hook, install and marked allocation producers. -/
theorem native_prefix
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    Nonempty (Prefix (functions := functions) (registry := registry) owner caller header capture arguments payloads
      size value finalStore) := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  let liveCapture := capture
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner member
    exact original.locals
  have liveReference : capture.canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.reference
  obtain ⟨origin, index, owned, selected, emitted⟩ :=
    CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry header.hook
  obtain ⟨metadata, history⟩ : ∃ metadata,
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named origin) (some metadata) := by
    cases found : compiled.indexed.ancestry.graph.table.namedAt? origin with
    | none => simp [SourceCoreCallableIndexedDispatch.namedFrame, found] at selected
    | some position =>
      obtain ⟨metadata, history⟩ := named_history compiled.indexed.ancestry.graph found
      exact ⟨metadata, selected ▸ history⟩
  have reference : (DataPatternValues.packValues payloads :: liveCapture.captured)[liveCapture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ, physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using liveCapture.capturedReference
  obtain ⟨actualOrigin, actualIndex, prefixSize, bodyStore, actualOwned, actualSelected, prefixCompleted, prefixSmaller, restored⟩ :=
    RecursiveNamedCallBounds.named_hook_body compiled.indexed.ancestry header.hook reference authority.frame.read completed
  have sameOrigin : actualOrigin = origin := Option.some.inj (actualOwned.symm.trans owned)
  subst actualOrigin
  have sameIndex : actualIndex = index := by
    have same := actualSelected.symm.trans selected
    injection same
  subst actualIndex
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at prefixCompleted
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) liveCapture.embedding.lift))
      (DataPatternValues.packValues payloads :: liveCapture.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: liveCapture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift liveCapture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped liveCapture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, child, bodyCompleted, childLe, _childStrict, parameterTransition⟩ :=
    parameters_sized_with_state owner installedAuthority member liveCapture liveLocals liveReference represented installedHeaps
      layout actualTyped prefixCompleted producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  exact ⟨⟨origin, index, metadata, owned, history, emitted, _, entry,
    child, bodyStore, bodyCompleted, Nat.lt_of_le_of_lt childLe prefixSmaller, restored,
    parameterState, installedRelated.trans parameterRelated⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEntryBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
/-! Literal retained named code enters its genuine marked parameter state.
The original prepared Header selects the exact staged body scope. Strict body
reflection then constructs an independently graded global Source application
and restores the physical caller in the actual returned pool. Nested stage
failure identity, dictionary, transient effects and the complete caller post
are retained throughout. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
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

/-- This observes the same actual native parameter endpoint. Independent
Source typing is added to its receipt before any body meaning is used. -/
def parameter_receipt {size : Nat} {value : Value} {finalStore : Store}
    (packet : Prefix (functions := functions) (registry := registry) owner caller header capture
      arguments payloads size value finalStore)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner caller header arguments :=
  ⟨packet.origin, packet.index, packet.metadata, capture.administrative, packet.actualContext,
    .unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
      DataPatternValues.packValues payloads :: capture.captured,
    Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift),
    (caller.rows owner.position).authority.frameLocation, (caller.rows owner.position).frame_eq,
    packet.owned, packet.history, packet.emitted, packet.entry, packet.reached, packet.related,
    stable, heapTyped, argumentsTyped⟩

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

/-- The result contains the original whole native completion and the full
staged representation at its actual restored caller endpoint. -/
def ResultAt (context : SourceSemantics.Context) (outcome : Staging.Recursive.Outcome)
    (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (faults : RecursiveStageMeaning.FaultRep) : Prop :=
  Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
    (header.code.rename capture.embedding.lift) value finalStore ∧
  RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
    header.function.resultType header.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    Relates caller returned ∧
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission poolBridge context
      header.function.resultType outcome returned

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)

include functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt terminal certifies in
/-- The actual Header and its authenticated named sidecar construct the body
scope. The native prefix reaches its real allocation state, where strict child
reflection supplies the staged body. The original global application and the
literal restored caller are then constructed without an ordinary body law. -/
theorem reflects_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
      CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
        header model
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) child certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      ResultAt (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedStagedNamedEntryBounds.native_prefix
    (functions := functions) (registry := registry) owner caller header capture sameLayouts member represented heaps completed
  let receipt := parameter_receipt functions owner caller header capture packet stable heapTyped argumentsTyped
  have source := receipt.source wellFormed
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt prepared aligned stagePrepared descriptor
  have selected : (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  have admitted : Admission poolBridge header.context packet.reached :=
    ⟨source.heapTyped, receipt.rows⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result,
    finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    CallableIndexedOwnedPreparedStagedNamedChildBounds.reflects_body
      (owner := owner) (packet := fun zero globals => receipt.packet zero globals) (selected := selected) (wellFormed := wellFormed)
      (terminal := terminal) (certifies := certifies)
      (environments := packet.entry.environments) (heaps := packet.entry.heaps)
      (locals := packet.entry.locals) (agrees := packet.entry.lookups) (typed := packet.entry.actualTyped)
      (initial := packet.reached) (admitted := admitted)
      budget (children selected) packet.completed (Nat.le_of_lt (Nat.lt_of_lt_of_le packet.strict within))
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
/-! The original staged global application selects its authentic retained
Header body, Source allocation and child scope. The native parameter producer
runs without a completed-body premise. Strict staged body preservation then
constructs the native invocation and restores the actual returned caller pool.
Source and native grades remain independent, including nested stage failures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

section Source
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
local notation "program" => Program.ofChecked compiled.sourceProgram
variable {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {function : Dynamic.GlobalFunction}

private theorem roots_functional {nodes : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots nodes left) (second : Dynamic.StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons id nodes left first ih => cases second with
    | cons remaining => exact congrArg (List.cons id) (ih remaining)

/-- Inversion uses the retained global instantiation and actual selected scope.
It preserves the original staged body outcome instead of wrapping an ordinary
execution. Source arity excludes only the separate pre-allocation fault. -/
theorem body_prefix {header : Header compiled program} (sourceAt : NamedSourceAt header rawD function)
    (wellFormed : ProgramWellFormed program)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {outcome : Staging.Recursive.Outcome} {size : Nat}
    (arity : header.function.parameters.length = arguments.length)
    (trace : Staging.Recursive.Size.Applies program stages size invocation context before
      (.global function) arguments outcome after) :
    ∃ bodySize child environment bound finalContext bodyOutcome,
      stages.Closure header.function child ∧
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements program stages bodySize child header.context environment bound
        header.function.body finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome ∧ bodySize < size := by
  have bodyUnique : ∀ actual, Dynamic.FunctionInstantiates program function.instantiation actual →
      RecursiveNamedCatalog.Header.sourceBody header = actual := by
    intro actual instantiated
    exact BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed
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
end Source

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
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include functions owner caller header capture sourceAt terminal certifies in
/-- Authentic Source allocation and the strict staged body child construct the
native parameter/body continuation before literal caller restoration. The
returned state retains full representation, relates and caller PostAdmission. -/
theorem preserves_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
        header model stages child certificate faults budget)
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
    selected, allocated, bodyTrace, converted, smaller⟩ := body_prefix sourceAt wellFormed arity trace
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
  have admitted : Admission poolBridge header.context parameterState := ⟨(receipt.source wellFormed).heapTyped, receipt.rows⟩
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    CallableIndexedOwnedPreparedStagedNamedChildBounds.preserves_body
      (owner := owner) (packet := fun zero globals => receipt.packet zero globals) (selected := selected) (wellFormed := wellFormed)
      (terminal := terminal) (certifies := certifies)
      (environments := entry.environments) (heaps := entry.heaps) (locals := entry.locals)
      (agrees := entry.lookups) (typed := entry.actualTyped) (initial := parameterState) (admitted := admitted)
      budget (children selected) bodyTrace converted (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
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
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds
/-! The complete retained named carrier applies its literal native closure.
The real apply rule gives the invocation its strict native grade. The original
staged Source application and exact returned caller pool remain independent of
that grade; the invocation producers retain nested stage failure identity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds
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
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

/-- This is the literal carrier exposed by genuine positive named payloads.
No Source signature or code provenance is inferred from its native shape. -/
def carrier (identity descriptor : Word) : Value :=
  .pair (.pair (.inRight .unit (.word identity))
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor)

include functions owner caller header capture sourceAt terminal certifies in
/-- Source allocation and its selected body construct the exact invocation,
then the physical payload apply rule. No native grade is equated to Source. -/
theorem application_preserves
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (identity descriptor : Word) (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
        header model stages child certificate faults budget)
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
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.preserves_invocation
      functions owner caller header capture sourceAt terminal certifies sameLayouts member wellFormed
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

include functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt terminal certifies in
/-- The actual complete native apply supplies a strict body invocation grade.
Its original Header and authenticated staged scope then construct the Source
application, with the exact full postcondition in the returned caller pool. -/
theorem application_reflects
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
      CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        child certificate faults budget)
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
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.reflects_invocation
      functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt terminal certifies
      sameLayouts member wellFormed stable heapTyped argumentsTyped represented heaps supports budget children
      invoked (Nat.le_trans (Nat.le_of_lt smaller) within)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, result⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedParentBounds
/-! The actual named Header, original selected caller row and raw successful
argument trace feed the literal terminal application. Its returned pool is
restored around the original caller. The Source and native grades remain
independent, and nested stage failures retain their original scope and call.
Static named compiler provenance and strict expression coverage are inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {mapping argumentMap : LocationMap} {world argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    argumentMap argumentWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution} {function : Dynamic.GlobalFunction}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.global function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.global function))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (calleeHeapTyped : Dynamic.HeapWellTyped context calleeHeap)
  (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header argumentMap argumentWorld)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  (sourceAt : NamedSourceAt header rawD function)
  (identity descriptorWord : Word)
  (carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
    (owner := owner) header capture identity descriptorWord)
  (nativeType : compiler.calleeCode.type =
    CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (member : header ∈ headers)
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate}
  (certifies : ∀ child,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok child →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression child)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
  calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt nativeType in
private theorem arguments_at {argumentsSize : Nat}
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap) :
    CallableIndexedParameterMeaning.Arguments model argumentMap argumentWorld header.bindings sources values ∧
    Dynamic.HeapWellTyped header.function.context argumentsHeap ∧
    Dynamic.ValuesHaveTypes header.function.context argumentsHeap sources header.types ∧
    Dynamic.TypeContextSupports header.context context ∧
    compiler.original.type = header.function.resultType ∧ lowered.type = header.output := by
  have secondAccepted : CallableContract.decision prepared.site.gates .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
    rw [prepared.site.decision_known .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract dispatch.row dispatch.found]
    exact SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication
      (dispatch.row.afterArguments_ok (count.trans selected.argument_count.symm))
  obtain ⟨parameters, physicalArity, rawResult⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.accepted_rows sourceAt compiler wellFormed
      actualFunctionType callerPrepared dispatch selected secondAccepted calleeTyped nativeType represented bundle
  obtain ⟨headerHeap, headerArguments, supports⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.at_successful_arguments sourceAt wellFormed
      runtime covers locals calleeHeapTyped typing calleeTyped bundle physicalArity argumentsTrace
  have callable := compiler.callableType
  rw [actualFunctionType] at callable
  have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (callable.trans nativeType)
  have sameCore : lowered.type = header.output :=
    (congrArg (fun output => output.type) compiler.output).trans
      (compiler.resultTypeEq.symm.trans (nativeSignature.2.trans header.resultType))
  exact ⟨parameters, headerHeap, headerArguments, supports, originalResult.trans rawResult, sameCore⟩

include bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture in
private theorem restored_result {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (sameSource : compiler.original.type = header.function.resultType)
    (sameCore : lowered.type = header.output)
    (resultAt : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := registry) (payloads := values) functions owner (bridge.pool reached) header capture
      context outcome after value finalStore finalMap finalWorld faults) :
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial returned ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome returned := by
  obtain ⟨_invoked, resultRep, finalHeaps, applicationMaps, applicationWorlds, applicationFrame,
    applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ := resultAt
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers locals calleeHeapTyped
  typing calleeTyped actualFunctionType represented bundle originalResult owner header capture sourceAt
  identity descriptorWord carrierEq nativeType sameLayouts member terminal certifies in
/-- The original Source global application supplies allocation and its selected
terminal body once. The native suffix and all three original binds then join
the real callee and ordered argument effects into the whole caller result. -/
theorem preserves_parent (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
        header model stages child certificate faults budget)
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.global function) sources outcome after)
    (within : applicationSize ≤ budget)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (firstGate : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
      calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt
      nativeType argumentsTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.application_preserves
      functions owner (bridge.pool reached) header capture sourceAt terminal certifies sameLayouts member wellFormed
      admitted.rows headerHeap headerArguments parameters heaps supports identity descriptorWord budget children called within
  rw [← carrierEq] at application
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    dispatch.shape selected dispatch.found count application
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType firstGate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    value, finalStore, finalMap, finalWorld, whole, parentRep, finalHeaps, finalMaps, finalWorlds,
    finalFrame, finalMetadata, returned, relatedFinal, post⟩

variable {row : SourceSpecialization.SpecializedFunction}
  (namedPrepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt namedPrepared instantiation header)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key))
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers locals calleeHeapTyped
  typing calleeTyped actualFunctionType represented bundle originalResult owner header capture sourceAt
  identity descriptorWord carrierEq nativeType sameLayouts member terminal certifies namedPrepared aligned
  stagePrepared descriptor stageEq in
/-- The real accepted suffix gives a strict measured application. Original
named registry authority then constructs the actual Source application, and
the returned pool supplies the full original parent's caller postcondition. -/
theorem reflects_suffix (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        child certificate faults budget)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
      calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt
      nativeType argumentsTrace
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  rw [carrierEq] at application
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, _wholeApplication, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.application_reflects
      functions owner (bridge.pool reached) header capture sourceAt terminal certifies
      namedPrepared aligned stagePrepared descriptor sameLayouts member wellFormed admitted.rows headerHeap headerArguments
      parameters heaps supports identity descriptorWord budget children application (Nat.le_of_lt strict)
  have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSourceSize
      invocation context argumentsHeap (.global function) sources outcome after := by
    simpa only [stageEq] using applied
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize], outcome, after,
    finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPayloadReceipts
/-! Positive global payloads retain the actual owned named Header, its complete
Source dictionary and original native code/capture. Compatible raw type wrappers
preserve their runtime type equality; they do not manufacture a literal Source
type equality. These projections supply neither a body law nor an application
result. The named staging scope and strict executed child remain separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPayloadReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}

/-- A positive global leaf has the original owned named relation. The wrapper
case retains its raw runtime type equality and the same native type/value. -/
theorem global_representation
    (origin : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world sourceType source native type) :
    ∀ function, source = .global function →
      ∃ originalType,
        CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults mapping world
          originalType (.global function) native type ∧
        SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType originalType := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
      cases related with
      | global related =>
          intro function same
          cases same
          cases related with
          | prior prior =>
              cases prior with
              | prior original => exact ⟨_, original, rfl⟩
      | closure member => intro function impossible; cases impossible
      | builtin related => intro function impossible; cases impossible
  | compatible same _ ih =>
      intro function selected
      obtain ⟨originalType, original, rawType⟩ := ih function selected
      exact ⟨originalType, original, same.trans rawType⟩
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro function impossible
      cases impossible
  | nil | cons | empty | entry | absent | present => trivial

/-- The actual positive global value exposes the same owned Header, capture,
Source instantiation, descriptor and full native callable code. Body execution
and global application meaning are absent from both premise and conclusion. -/
theorem named_payload
    (origin : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world sourceType source native type)
    (function : Dynamic.GlobalFunction) (selected : source = .global function) :
    ∃ owner : OwnedKey keys, ∃ header : Header compiled (Program.ofChecked compiled.sourceProgram),
      ∃ rawD identity, ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
          (.named header.named.signature.key),
        header ∈ headers ∧ NamedSourceAt header rawD function ∧ NamedInstalledCode capture ∧
        Word.ofNat? (header.slot + 1) = some identity ∧
        compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
          (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) ∧
        RuntimeValueHasType world (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)
          header.named.signature.functionType compiled.indexed.layouts.definitions ∧
        SourceCoreRawMetadata.runtimeType sourceType =
          SourceCoreRawMetadata.runtimeType header.named.specialized.function.type ∧
        native = .pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id) ∧
        type = CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType := by
  obtain ⟨originalType, original, rawType⟩ := global_representation profile origin function selected
  obtain ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, installed,
      number, projection, typed, originalTypeEq, nativeEq, nativeType⟩ := original.named_payload_inv
  exact ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, installed,
    number, projection, typed, rawType.trans (congrArg SourceCoreRawMetadata.runtimeType originalTypeEq),
    nativeEq, nativeType⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPayloadReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
/-! A positive global payload retains its actual Header, Source instantiation,
dictionary and native captured code. The selected physical count is decided
at the real argument endpoint before this Header's terminal parent producer.
Static per-Header compiler coverage and numeric child coverage remain inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserDispatch (GlobalApplicationPrefix)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserPreservationDispatch (GlobalAppliedPrefix)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Each field describes this actual Header's compiler or original prepared
record. No completion, body law or desired application result is stored. -/
structure Terminal (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  instantiation : DeclarationInstantiation
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  layouts : header.layouts = compiled.indexed.layouts
  expression : ExpressionId
  receipt : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body
  certificate : GenericExpressionMeaning.Certificate
  certifies : ∀ child,
    header.policy.lowerExpression receipt.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok child →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression child

variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry preparedStages)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = source)
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include bridge profile compiler prepared initial sourceParent occurrence preparedStages stageEq callerPrepared receiver
  wellFormed runtime covers locals sourceEq tree unique parentTyped calleeFound actualFunctionType in
/-- The actual global prefix exposes its original Header before any execution
law is used. Physical mismatch returns the original arity parent; equal count
runs the retained named terminal producer at the real reached argument state. -/
theorem reflects_global
    (terminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
    {budget size : Nat} {value : Value} {finalStore : Store}
    (children : ∀ header, header ∈ headers → ∀ terminal : Terminal header,
      ∀ {child : Staging.Recursive.Scope},
        (RecursiveNamedPreparedStageScopes.registry preparedStages).Closure header.function child →
        CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry preparedStages)
          child terminal.certificate callFaults budget)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (global : GlobalApplicationPrefix (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping calleeFound
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  obtain ⟨function, rawParameter, rawResult, functionType, bundle, originalResult,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    calleePost, calleeTyped, calleeTrace, accepted, argumentsTrace, represented, calleeRelated,
    _callView, boundary, heaps, maps, worlds, frame, heapMetadata, ⟨reached, related, admitted⟩,
    suffixSize, suffix, strict⟩ := global
  have origin : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry
      completion.result.context.registry semanticFaults profile finalMap finalWorld
      calleeNode.type (.global function) carrier compiler.calleeCode.type := by
    exact calleeRelated
  obtain ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, _installed,
    _number, _projection, _nativeTyped, _runtimeType, nativeEq, nativeType⟩ :=
    CallableIndexedOwnedPreparedStagedNamedPayloadReceipts.named_payload profile origin function rfl
  have carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
      (owner := owner) header capture identity descriptor.id := nativeEq
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · obtain ⟨terminal⟩ := terminals header member
      obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have calleeHeapTyped := calleeAdmission.at_value.2.heap
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function)
          (.function rawParameter rawResult) := by
        simpa only [functionType] using calleeTyped
      obtain ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, resultRep, returnedHeaps,
        returnedMaps, returnedWorlds, returnedFrame, returnedMetadata, returned, returnedRelated, returnedPost⟩ :=
        CallableIndexedOwnedPreparedStagedTerminalNamedParentBounds.reflects_suffix
          bridge profile compiler prepared sourceParent occurrence initial reached related admitted
          heaps maps worlds frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers
          (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType represented bundle originalResult
          owner header capture sourceAt identity descriptor.id carrierEq nativeType terminal.layouts member
          terminal.receipt terminal.certifies terminal.prepared terminal.aligned preparedStages descriptor stageEq
          budget (children header member terminal) calleeTrace argumentsTrace suffix (Nat.le_of_lt strict)
      exact ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, completed.sound,
        resultRep, returnedHeaps, returnedMaps, returnedWorlds, returnedFrame, returnedMetadata,
        returned, returnedRelated, returnedPost⟩
    · have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt callerPrepared dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have mismatch : header.function.parameters.length ≠ sources.length := by
        intro same
        exact count (physical.trans (same.trans valuesCount))
      have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.arity_failure
        (actual := preparedStages) (caller := invocation) (context := context) (heap := argumentsHeap) sourceAt mismatch
      have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
          (Staging.Recursive.Size.stepSize []) invocation context argumentsHeap (.global function) sources
          (.fault (.semantic (.argumentArityMismatch header.function.parameters.length sources.length))) argumentsHeap := by
        simpa only [stageEq] using applied
      have failedSource := Staging.Recursive.Size.Expression.applied occurrence compiler.argumentCoercions
        calleeTrace accepted argumentsTrace sourceParent.arity called
      have lowerType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      obtain ⟨sameValue, sameStore⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
          dispatch.shape selected dispatch.found count suffix
      cases sameStore
      obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
        CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
          compiler prepared preparedStages selected receiver initial functions reached related heaps
          (sourceResult := compiler.original.type) (resultCore := lowered.type) count
      cases sameState
      refine ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)),
        argumentsHeap, finalMap, finalWorld, ?_, completed.sound, ?_, keptHeaps, maps, worlds, frame,
        heapMetadata, reached, keptRelated, ?_⟩
      · simpa only [physical, valuesCount] using failedSource
      · have exactValue : value = .inLeft lowered.type
            (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
              .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))) := by
          simpa only [lowerType] using sameValue
        rw [exactValue]
        exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩

include bridge profile compiler prepared initial sourceParent occurrence preparedStages callerPrepared receiver
  wellFormed runtime covers locals sourceEq tree unique parentTyped calleeFound actualFunctionType in
/-- The genuine global Source suffix retains its original allocation and body
scope. The actual Header and physical row select terminal execution or arity
failure, and both branches preserve every reached caller effect. -/
theorem preserves_global
    (terminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
    (guardFrame : invocation.guards = CallableLedger.frame sidecar)
    (budget : Nat)
    (children : ∀ header, header ∈ headers → ∀ terminal : Terminal header,
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
        CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
        header model stages child terminal.certificate callFaults budget)
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (global : GlobalAppliedPrefix (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial
      calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources outcome after)
    (within : applicationSize ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after := by
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping calleeFound
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  obtain ⟨function, selectedFunction, calleeTrace, accepted, argumentsTrace, called, prefixResult⟩ := global
  cases selectedFunction
  obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
    calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
    originalNode, originalMetadata, calleePost, calleeTyped, firstGate, argumentsNative,
    represented, calleeRelated, _callView, boundary, heaps, maps, worlds,
    frame, heapMetadata, reached, related, admitted⟩ := prefixResult
  have origin : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry
      completion.result.context.registry semanticFaults profile finalMap finalWorld
      calleeNode.type (.global function) carrier compiler.calleeCode.type := by
    exact calleeRelated
  obtain ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt, _installed,
    _number, _projection, _nativeTyped, _runtimeType, nativeEq, nativeType⟩ :=
    CallableIndexedOwnedPreparedStagedNamedPayloadReceipts.named_payload profile origin function rfl
  have carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
      (owner := owner) header capture identity descriptor.id := nativeEq
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · obtain ⟨terminal⟩ := terminals header member
      have calleeNative := calleePost.1
      obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have calleeHeapTyped := calleeAdmission.at_value.2.heap
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function)
          (.function rawParameter rawResult) := by
        simpa only [functionType] using calleeTyped
      exact CallableIndexedOwnedPreparedStagedTerminalNamedParentBounds.preserves_parent
        bridge profile compiler prepared sourceParent occurrence initial reached related admitted
        heaps maps worlds frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers
        (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType represented bundle originalResult
        owner header capture sourceAt identity descriptor.id carrierEq nativeType terminal.layouts member
        terminal.receipt terminal.certifies budget (children header member terminal)
        calleeTrace argumentsTrace called within calleeNative firstGate argumentsNative
    · have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt callerPrepared dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have different : header.function.parameters.length ≠ ids.length := by
        simpa only [physical] using count
      have bodyUnique : ∀ actualBody,
          Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram) function.instantiation actualBody →
          RecursiveNamedCatalog.Header.sourceBody header = actualBody := by
        intro actualBody instantiated
        exact BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed sourceAt.frame.instantiated instantiated
      cases called with
      | global instantiated _covers _roots _selected _parameters allocate _body _converted =>
        have same := bodyUnique _ instantiated
        cases same
        have actualCount := (congrArg List.length sourceAt.frame.parameters).trans
          (allocate.length_eq.trans valuesCount)
        exact False.elim (different actualCount)
      | globalArity instantiated mismatch =>
        have same := bodyUnique _ instantiated
        cases same
        have actualAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
            prepared.site.call ids (.global function) := by
          simpa only [guardFrame, prepared.call] using accepted
        have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
            (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
            (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
          simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
            using argumentsNative
        have native := CallableIndexedOwnedPreparedSecondCallGateRejection.user_native_preserves
          (result := compiler.resultType) dispatch selected actualAccepted count
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown calleePost.1 argumentsWeaken
        change Evaluates actual store
          (CallableContract.call prepared.site.gates
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
            (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
        rw [← prepared.lowered_rename compiler ξ] at native
        obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
          CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
            compiler prepared preparedStages selected receiver initial functions reached related heaps
            (sourceResult := compiler.original.type) (resultCore := lowered.type) count
        cases sameState
        have loweredType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
        have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
            compiler.original.type
            (.fault (.semantic (.argumentArityMismatch
              (RecursiveNamedCatalog.Header.sourceBody header).source.inputs.length sources.length))) reached :=
          ⟨admitted.rows, by intro value impossible; cases impossible⟩
        refine ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity
          (.globalArity instantiated mismatch),
          .inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
            .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))),
          argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame, heapMetadata,
          reached, keptRelated, post⟩
        · simpa only [loweredType] using native
        · simpa only [physical, sourceAt.frame.parameters, valuesCount] using faultRep

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts
/-! The branching alternative retains the accepted statement action and exact
body footer of one authentic named Header. This receipt has no semantic
children, Source trace, execution law or completed result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CompatibleEncoding (bind_ok)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def parameterScope (header : Header compiled (Program.ofChecked compiled.sourceProgram)) : SourceCoreLocalCell.Scope :=
  header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))

structure Receipt (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  flow : Expr
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (parameterScope header) header.function.body header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape header.function.source true header.function.body
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output

/-- Inversion uses the one accepted Header body action, preserving its actual
flow code and diagnostic words. -/
theorem of_accepted {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (parameterScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped =
        .ok header.body)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape header.function.source true header.function.body)
    (projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output) :
    Nonempty (Receipt header) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  exact ⟨⟨flow, generated, (Except.ok.inj returned).symm, shape, projection⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix
/-! The actual named packet determines the compiler's used administrative
prefix. Truncating only the canonical view preserves every global, the argument
bundle and the original frame, with the same owned pool and runtime environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open RecursiveNamedLambdaFormationHeads (nativePrefix)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  {administrative : Core.Context} {environment : Dynamic.Environment}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)

include packet complete related in
/-- Only actual bundle/global/frame observations determine this prefix. -/
theorem entry_prefix : NativeExpressionContextSupport.Agrees
    (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) header).length (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) header) administrative := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero =>
    have bundle := packet.bundle
    rw [typed] at bundle
    simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append] using bundle
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map,
        List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature := List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      obtain ⟨target, member, sameSlot, sameSignature⟩ := complete slot signature selected
      have found := packet.globals target member
      have atType := tag found
      rw [sameSlot] at atType
      have outside : ¬ scope.length + 1 + slot < scope.length := by omega
      have offset : scope.length + 1 + slot - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, sameSignature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag packet.reference
      have outside : ¬ scope.length + 1 + compiled.indexed.base.globals.length < scope.length := by omega
      have offset : scope.length + 1 + compiled.indexed.base.globals.length - scope.length = compiled.indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType

include packet in
/-- The retained prefix contains each genuine catalog slot and the frame.
The pool itself is identical, since canonical views do not index its contents. -/
theorem packet_take
    (slots : ∀ target, target ∈ headers → target.slot < compiled.indexed.base.globals.length) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner header
      ⟨scope, mapping, world, heap, store,
        canonical.take (scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) header).length)⟩ initial := by
  have observed := (packet.observed owner header).take
    (count := scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) header).length)
    (by
      intro target member
      have bound := slots target member
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega)
    (by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega)
  refine ⟨observed.globals, observed.reference, ?_, packet.carried⟩
  rw [List.map_take, List.getElem?_take, if_pos]
  · exact packet.bundle
  · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingEntryPrefix
end
