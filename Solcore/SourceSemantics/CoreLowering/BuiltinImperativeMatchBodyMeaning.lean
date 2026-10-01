import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchFallthrough
import Solcore.SourceSemantics.CoreLowering.ImperativeFunctionFinish
import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBodyMeaning

/-! Actual accepted builtin function bodies with recursive lexical control,
assignment, while, for and match preserve finite source calls and reflect
completed Core calls. All child meaning is closed by the concrete tree.
Escaped loop control retains its independent source fault. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes source_view)
open CompatibleNamedBody (trace_control)
open ImperativeFunctionFinish (result)

structure Certificate (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (definitions : DataEnvironment) (administrative : Core.Context)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (policy : SourceCoreLoops.Policy)
    (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
    statements type reasonAt fellThrough escaped = .ok code
  projection : values.checked.catalog.project expected = .ok type
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
    statements type reasonAt true escaped = .ok flow
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : BuiltinImperativeMatch.Tree layouts owner active frame globals onError
    readFuel values source solved reasonAt definitions administrative
    context scope (.statements true statements) expected type flow

/-- Keep the real compiler equation and the exact flow traversal. Their
composition fixes the actual finish code without an additional code equality
supplied by a caller. The tree is independent static evidence. -/
def of_extracted
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {definitions : DataEnvironment} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
      statements type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project expected = .ok type)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      statements type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frame globals onError
      readFuel values source solved reasonAt definitions administrative
      context scope (.statements true statements) expected type flow) :
    Certificate layouts owner active frame globals onError readFuel values
      source context solved reasonAt definitions administrative scope statements
      expected type policy fuel fellThrough escaped code := by
  have emitted : code = CompatibleStatements.finish type flow fellThrough escaped := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [generated] at accepted
    exact Except.ok.inj accepted.symm
  exact ⟨accepted, projection, flow, generated, emitted, tree⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.preserves
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt ambient.definitions administrative scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    (errors : GenericImperativeMatch.Tree.Ready registry faults certificate.tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  obtain ⟨resultContext, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.preserves functions definitions registered catalogValid extension program function.evidence uninitialized missing
      faithful functionLeaves functionTypes errors contextValid unique environments heaps locals agrees actualTyped reference read unmapped sourceTrace
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact certificate.tree.true_fallthrough_unit unique sourceTrace)
    certificate.projection fellThrough escaped escapedFault represented evaluated
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [certificate.emitted, ImperativeFunctionFinish.rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, ImperativeFunctionFinish.result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨resultContext, control, sourceTrace, exit, lexical⟩⟩

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.reflects
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt ambient.definitions administrative scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    (errors : GenericImperativeMatch.Tree.Ready registry faults certificate.tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  rw [certificate.emitted, ImperativeFunctionFinish.rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEval⟩ := ImperativeFunctionFinish.input evaluated
  obtain ⟨resultContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.reflects functions definitions registered catalogValid extension program function.evidence uninitialized missing
      faithful functionLeaves functionTypes errors contextValid unique environments heaps locals agrees actualTyped reference read unmapped flowEval
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact certificate.tree.true_fallthrough_unit unique trace)
    certificate.projection fellThrough escaped escapedFault represented flowEval
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact ⟨.value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact ⟨.value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (certificate.tree.control_not_fault unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
    | breaking finalEnvironment matched =>
      cases trace with
      | control executed =>
        exact ⟨_, .escaped executed (.inl ⟨_, rfl⟩), .fault matched, .breaking _⟩
    | continuing finalEnvironment matched =>
      cases trace with
      | control executed =>
        exact ⟨_, .escaped executed (.inr ⟨_, rfl⟩), .fault matched, .continuing _⟩
  obtain ⟨outcome, bodyTrace, result, exit⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, maps, worlds, frame, metadata,
    ⟨resultContext, control, trace, exit, lexical⟩⟩


include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
/-- Finite source call completion and completed Core execution are equivalent.
Suspension is outside both sides; no common fuel bound or termination premise
is required. The stronger preceding theorems retain result and heap relations. -/
theorem Certificate.finite_iff
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt ambient.definitions administrative scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    (errors : GenericImperativeMatch.Tree.Ready registry faults certificate.tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  constructor
  · rintro ⟨runtimeFuel, value, finalStore, completed⟩
    obtain ⟨outcome, after, _, _, trace, _⟩ :=
      certificate.reflects functions extension definitions registered catalogValid program
        contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
        errors environments heaps locals agrees actualTyped reference read unmapped
        (Core.runStateful_evaluation_sound completed)
    exact ⟨outcome, after, trace⟩
  · rintro ⟨outcome, after, trace⟩
    obtain ⟨value, finalStore, _, _, evaluated, _⟩ :=
      certificate.preserves functions extension definitions registered catalogValid program
        contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
        errors environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨runtimeFuel, completed⟩ :=
      Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
    exact ⟨runtimeFuel, value, finalStore, completed runtimeFuel (Nat.le_refl _)⟩

end Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBody
