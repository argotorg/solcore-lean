import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedLiteralBounds

/-! Literal execution reuses the existing cell-aware Source proof. Native
purity supplies the extra retention of the same stored contextual descriptors;
the invocation index and its captured frame are unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLiterals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation} {program : Program}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved invocation.source id lowered

theorem preserves
    (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (unique : NodeOccurrencesUnique invocation.source) (size : Nat) :
    PreservesAt (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) index
      registry invocation (Certificate (solved := solved) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CellAwareSelectedLiteralBounds.literal_preserves functions bridge sameLedger runtimeLedger unique
      faults size receipt found typed environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨literalNode, _, literal, selected⟩ := receipt
  have evidence := selected.evidence sameLedger runtimeLedger invocation.evidence
  obtain ⟨_, _, _, _, pureEvaluation⟩ :=
    literal.evaluates_with_evidence (registry := rawRegistry) functions program context invocation.evidence evidence invocation.source
      environment before mapping world actual store ξ
  have unchanged := (evaluation_deterministic pureEvaluation evaluated).2
  have effect :
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore := by
    rw [← unchanged]
    simpa only [List.append_nil] using
      (CellAwareScopeAuthority.Effect.append (instances :=
        GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) store [] metadata maps worlds)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related, post⟩

theorem reflects
    (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) index
      registry invocation (Certificate (solved := solved) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CellAwareSelectedLiteralBounds.literal_reflects functions bridge sameLedger runtimeLedger
      faults size receipt found typed environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨literalNode, _, literal, selected⟩ := receipt
  have evidence := selected.evidence sameLedger runtimeLedger invocation.evidence
  obtain ⟨_, _, _, _, pureEvaluation⟩ :=
    literal.evaluates_with_evidence (registry := rawRegistry) functions program context invocation.evidence evidence invocation.source
      environment before mapping world actual store ξ
  have unchanged := (evaluation_deterministic pureEvaluation completed.sound).2
  have effect :
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore := by
    rw [← unchanged]
    simpa only [List.append_nil] using
      (CellAwareScopeAuthority.Effect.append (instances :=
        GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) store [] metadata maps worlds)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLiterals
