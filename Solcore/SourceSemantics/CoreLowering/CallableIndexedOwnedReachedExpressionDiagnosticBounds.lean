import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinMeaning

/-! Builtin expression correspondence uses only a certified read's actual
uninitialized cell and an index header's actual unavailable mapping witness.
The original tree, literal sites, compiler tokens and finite traces remain
unchanged. Unrelated expression IDs and metadata rows need no fault law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedExpressionDiagnosticBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionBuiltins CompatibleExpressionIndices

private theorem reached_terminal {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry program context evidence reasonAt faults) :
    IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence reasonAt (fun _ => True) faults ExpressionFailurePostContracts.TrivialExpressionPost := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional, _trace, _post⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.general_index_finish header sourceType faithful functionLeaves functionTypes baseRep keyRep actualTyped heaps keyFound form baseTrace keyTrace (reasonAt id) (missing header keyFound form baseTrace keyTrace)
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional,
    index_intro header.metadata form (terminal.trace baseTrace keyTrace), ExpressionFailurePostContracts.OutcomePost.of_trivial represented⟩

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies values source functions registry program context evidence reasonAt faults)

include extension faithful functionLeaves functionTypes unique reads missing in
theorem preserves_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget
    (CompatibleExpressionBuiltins.preserves_with_literals_and_post (functions := functions) (extension := extension) (functionLeaves := functionLeaves) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (BuiltinFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.Preserves.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Preserves.of_trivial
        (ExpressionFailurePostContracts.Preserves.forget
          (ReachedLoweredReadOutcomePorts.lowered_read_preserves_with_post functions extension program context evidence reasonAt reads unique)))
      (ExpressionFailurePostContracts.TypedPreserves.of_trivial
        (CompatibleExpressionProxies.preserves functions extension program context evidence unique faults))
      (reached_terminal functions registry program context evidence reasonAt
        faithful functionLeaves functionTypes missing))

include extension faithful functionLeaves functionTypes unique reads missing in
theorem reflects_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget
    (CompatibleExpressionBuiltins.reflects_with_literals_and_post (functions := functions) (extension := extension) (functionLeaves := functionLeaves) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (BuiltinFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.Reflects.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Reflects.of_trivial
        (ExpressionFailurePostContracts.Reflects.forget
          (ReachedLoweredReadOutcomePorts.lowered_read_reflects_with_post functions extension program context evidence reasonAt reads unique)))
      (ExpressionFailurePostContracts.TypedReflects.of_trivial
        (CompatibleExpressionProxies.reflects functions extension program context evidence faults))
      (reached_terminal functions registry program context evidence reasonAt
        faithful functionLeaves functionTypes missing))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedExpressionDiagnosticBounds
