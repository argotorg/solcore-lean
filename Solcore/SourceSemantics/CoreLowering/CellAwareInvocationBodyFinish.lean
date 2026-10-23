import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary

/-! The genuine function footer consumes mixed imperative flow. Actual
zero-loop-depth Source typing excludes escaped control; the actual result
projection validates Unit fallthrough. All reached heap effects survive. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBodyFinish
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {index : ActualBodyInvocation.Index whole bodyRelation}

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
  {control : ControlContext} {staticFinal : SourceSemantics.Context} {facts : BodyFacts}

theorem preserves {budget : Nat}
    (bound : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true statements expected type code budget)
    (sourceEq : invocation.source = index.source)
    (sourceTyped : StatementsHaveType (index.source) control context statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  obtain ⟨flowValue, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    bound size within environments heaps locals agrees actualTyped runtime covers sameLedger typed
      initial admitted authority physical owner sameLocation ready trace
  have closed := Staging.Recursive.TypedControlBoundary.function
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
    (by simpa only [sourceEq] using sourceTyped) depth trace.sound
  have functionValue := Represents.to_function projection represented closed
  obtain ⟨value, complete, result⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates functionValue evaluated fellThrough escaped embedding
  exact ⟨value, finalStore, finalMap, finalWorld,
    by rwa [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename], result,
    finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

theorem reflects {budget : Nat}
    (bound : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true statements expected type code budget)
    (sourceEq : invocation.source = index.source)
    (sourceTyped : StatementsHaveType (index.source) control context statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store ((CompatibleStatements.finish type code fellThrough escaped).rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready
    value finalStore completed
  have original := completed
  rw [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at original
  obtain ⟨flowSize, flowValue, flowStore, flow, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original within
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    bound flowSize (Nat.le_of_lt strict) environments heaps locals agrees actualTyped runtime covers sameLedger typed
      initial admitted authority physical owner sameLocation ready flow
  have closed := Staging.Recursive.TypedControlBoundary.function
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
    (by simpa only [sourceEq] using sourceTyped) depth trace.sound
  have functionValue := Represents.to_function projection represented closed
  obtain ⟨native, complete, result⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates functionValue flow.sound fellThrough escaped embedding
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound complete
  cases same
  subst stores
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented.body_result,
    result, finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBodyFinish
