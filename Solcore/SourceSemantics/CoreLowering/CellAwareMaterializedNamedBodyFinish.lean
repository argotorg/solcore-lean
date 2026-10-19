import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyTreeBounds

/-! The actual named compiler footer consumes the bounded body’s original
returned value or fault. It leaves the reached mixed heap and frame unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyFinish
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

private theorem finished {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty} {type : Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.BodyOutcome}
    {value : Value} {actual : Environment} {before after : Store} {flow : Expr}
    {compiled : SourceCoreUnifiedCompilation.Compiled} {location : Core.Location}
    (represented : Represents model mapping world true raw type faults outcome value)
    (output : CellAwareMaterializedFlowOutput.FlowAt compiled mapping world location outcome value)
    (terminal : ∃ result, outcome = CallableIndexedOwnedAdmittedStagedTerminalStatements.control result)
    (evaluated : Evaluates actual before flow value after) (escaped : Word) (fallback : Expr) :
    ∃ native, Evaluates actual before
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code type flow escaped fallback) native after ∧
      RecursiveStageMeaning.ResultRepresentsFor model mapping world raw type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) native ∧
      CellAwareMaterializedOutput.OutcomeAt compiled mapping world location
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) native := by
  obtain ⟨result, rfl⟩ := terminal
  cases result with
  | value source =>
    cases represented with
    | returned payload =>
      obtain ⟨rawValue, same, positive⟩ := output source rfl
      cases same
      refine ⟨_, LocalControl.finish_returned type (LocalLoop.toControl_normal type escaped evaluated),
        .value payload, ?_⟩
      intro other sameSource
      cases sameSource
      exact ⟨_, rfl, positive⟩
  | fault failure =>
    cases represented with
    | fault matched =>
      exact ⟨_, LocalControl.finish_failure type (LocalLoop.toControl_failure type escaped evaluated),
        .fault matched, CellAwareMaterializedOutput.OutcomeAt.fault⟩

include record bindings registered in
theorem preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareMaterializedScopeBounds.PreservesBelow bridge context model named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareNativeBodyTree.Tree whole.indexed named compiled certificates administrative reasonAt
      context scope true statements expected type code)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt) (fellThrough escaped : Word) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment,
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
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  obtain ⟨flowValue, finalStore, finalMap, finalWorld, evaluated, represented, output, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareMaterializedNamedBodyTreeBounds.preserves bridge bindings compiled record producer registered children sourceEq tree issuer within
      environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready trace
  have terminal := CellAwareNamedBodyTreeBounds.terminal_outcome compiled tree sourceEq
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique) trace
  obtain ⟨value, complete, result, positive⟩ := finished represented output terminal evaluated escaped
    ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback type fellThrough).rename embedding)
  exact ⟨value, finalStore, finalMap, finalWorld,
    by rwa [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename], result, positive,
    finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyFinish
