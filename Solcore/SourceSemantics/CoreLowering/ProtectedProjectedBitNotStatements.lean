import Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatementMeaning
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderReady
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceResolution

/-! Protected unary prefixes use the existing ordered key fold. Every child
passes its actual reached caller to the next child, getter and final write. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements.Head
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPlaceExecution DataPatternValues
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v

variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (readiness : Readiness protocol)
  {exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution}
  (head : Head values source context certificate scope administrative ambient.definitions assignment)
  (keyFacts : ∀ id, id ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections → ∀ node,
    source.lookupExpression? id = some node → exprFacts context id node)
  (budget : Nat)
  (meaning : ∀ size, size < budget → ExpressionPreservesAt protocol readiness program evidence
    (payloadModel values.checked registry functions) exprFacts certificate (source := source) (context := context) (faults := faults) size)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (ready : readiness.Ready context initial)

include extension transport faithful observations keyFacts meaning environments heaps locals agrees actualTyped initial ready in
theorem preserves_prefix_bounded {updated : Dynamic.Value} {after : Dynamic.Heap} {size : Nat}
    (trace : SourceExecutionSize.SourcePlaceSnapshotUpdate program size context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  cases trace with
  | intro resolve write =>
    obtain ⟨resolution, coreLookup, getterState, getterRelated⟩ :=
      ProtectedPlaceResolution.Stateful.preserves_bounded_with_sequence budget
        head.layout.path head.layout.views head.layout.keyTypes head.layout.leafProjected head.layout.virtual extension head.layout.nonempty
        (getter_typed head.layout (virtual_closed head.layout head.ordinary)
          (environment_respects environments.runtime_hasTypes actualTyped agrees))
        protocol transport faithful observations environments locals agrees actualTyped initial
        (by
          intro target _ hiddenTyped keySize outcome after keyTrace keyBound
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, _successful⟩ :=
            ProtectedDataExpressionSequence.Stateful.WithReady.preserves_bounded protocol (readiness.Ready context)
              budget head.layout.children
              (by
                intro id member child strict current expression code generated node found
                  nextMap nextWorld admin env canon native nativeContext heap nativeStore renameVars childOutcome childAfter
                  envs relatedHeap localEnv embedding typed state stateReady childTrace
                rcases generated with ⟨rfl, generated⟩
                obtain ⟨result, resultStore, resultMap, resultWorld, executed, relatedValue, resultHeap,
                    maps, worlds, frame, metadata, reached, related, post⟩ :=
                  meaning child strict generated found (keyFacts _ member node found)
                    envs relatedHeap localEnv embedding typed state stateReady
                    (ProtectedStateTransition.SequenceBridge.call_trace childTrace)
                exact ⟨result, resultStore, resultMap, resultWorld, executed, relatedValue, resultHeap,
                  maps, worlds, frame, metadata, reached, related, by
                    intro sourceValue same
                    cases same
                    exact post.1⟩)
              environments heaps locals
              (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType head.prepared.route.rootType) target])
              hiddenTyped initial ready keyTrace keyBound
          exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
            maps, worlds, frame, metadata, reached, related⟩)
        head.slot head.writable resolve (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
    obtain ⟨commit, typed, reached, related⟩ := ProtectedStagedProjectedBitNotCommit.of_write
      head.layout head.ordinary extension protocol transport faithful observations head.profile
      environments agrees actualTyped resolution initial getterState getterRelated write
      (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
    refine ⟨commit.finalStore, resolution.mapping, commit.finalWorld,
      [.unit, commit.value, commit.replacement, .unit, .inRight .unit resolution.snapshot,
        packValues resolution.values, .cellRef (OptionalCell.cellType head.prepared.route.rootType) resolution.target],
      commit.heaps, resolution.maps, resolution.worlds.trans commit.worlds,
      resolution.frame.trans commit.frame, resolution.metadata.trans commit.metadata, rfl, typed, ⟨reached, related⟩, ?_⟩
    intro next output
    change ContinuationAgreement actual store
      ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit)
        next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) _ _ _
    rw [execute_rename head.layout.path (virtual_closed head.layout head.ordinary)]
    simpa only [renamed_packed, Expr.rename, LanguageResult.success, writtenEnvironment, modifiedEnvironment,
      rhsEnvironment, snapshotEnvironment, keysEnvironment, referenceEnvironment, List.cons_append, List.nil_append] using
      commit.prefix_agreement resolution coreLookup (next.rename ξ) output

end Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements.Head
