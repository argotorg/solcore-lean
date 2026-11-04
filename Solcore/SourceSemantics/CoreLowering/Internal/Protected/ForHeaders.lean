import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementComposition
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LoopStatements
import Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatementMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.PlaceAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForIterations
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.ForFinite
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeForTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalStatements

/-!
# Protected contracts: for headers

`for` headers in both directions, posts and payload contracts, and bit-not statements.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedBitNotStatements
/-! Bare unary assignment uses its real seven-slot result and administrative
progress to retain the installed entry. No expression child or loop proof is
introduced here; projected unary assignments remain outside the profile. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open ProtectedWhile.Body (Preserves Reflects)
open CompatibleBitNotStatements (Head bitNot_view bitNot_fault)
open TypedLexicalWhile (FlowRep)
open TypedScopedStatements (Executes source_view prepend head_fault)

variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {solved : List SolvedRequirement}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include transport in
theorem assignment_preserves {mode : Bool} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {body : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (head : Head context scope assignment)
    (headErrors : head.Errors faults)
    (unique : NodeOccurrencesUnique source)
    (continuationMeaning : Preserves (entry := entry) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode rest expected type body) :
    Preserves (entry := entry) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext environments heaps locals agrees actualTyped reference read unmapped installed trace
  have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
      (first : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
      (tail : Executes mode program middleContext evidence source next middle rest resultContext outcome after) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment resultContext after := by
    obtain ⟨rfl, same, updated, assigned⟩ := bitNot_view unique (lookupStatement?_sound found) form first
    cases same
    obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
      head.preserves_prefix functions program evidence
        environments heaps locals agrees actualTyped assigned
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
      continuationMeaning valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (transport.extend installed maps worlds frame metadata) tail
    exact ⟨value, finalStore, finalMap, finalWorld,
      (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
      represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) executed with
      ⟨_, _, _, first, tail⟩ | ⟨first, terminal⟩
    · exact go first (by cases mode <;> exact .control tail)
    · obtain ⟨_, rfl, _⟩ := bitNot_view unique (lookupStatement?_sound found) form first
      cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
      ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
    · have assigned := bitNot_fault unique (lookupStatement?_sound found) form first
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
        head.preserves_fault functions program evidence
          environments heaps locals agrees headErrors assigned body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · exact go first (by cases mode <;> exact .fault tail)

include transport in
theorem assignment_reflects
    {mode : Bool} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {body : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (head : Head context scope assignment)
    (headErrors : head.Errors faults)
    (_unique : NodeOccurrencesUnique source)
    (continuationMeaning : Reflects (entry := entry) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode rest expected type body) :
    Reflects (entry := entry) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  rcases head.reflects functions program evidence
    environments heaps locals agrees actualTyped headErrors evaluated with
    ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
    ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
  · exact ⟨context, .fault reason, after, finalMap, finalWorld,
      head_fault mode rest (.assignBitNot (lookupStatement?_sound found) form trace), .fault matched,
      finalHeaps, maps, worlds, frame, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  · obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
      continuationMeaning valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (transport.extend installed maps worlds frame metadata)
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignBitNot (lookupStatement?_sound found) form trace) tailTrace,
      represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedProjectedBitNotStatements
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderAssignmentPayloadContracts
/-! Assignment callbacks retain the original actual-state readiness and result.
Only the diagnostic input is parameterized by the selected static payload. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v
variable {Records : Type v}
def AssignmentFaultPreservesWithPayloadAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context)
    (administrative : Core.Context) (faults : FunctionCalls.FaultRep) (budget : Nat)
    (AP : ∀ {scope assignment operator rhs},
      GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs → Prop) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    (_facts : assignmentFacts context assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    AP head →
  ∀ {reason after size},
    SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before
      assignment.target operator rhs reason after → size ≤ budget → ∀ next output,
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def AssignmentReflectsWithPayloadAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context)
    (administrative : Core.Context) (faults : FunctionCalls.FaultRep) (budget : Nat)
    (AP : ∀ {scope assignment operator rhs},
      GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs → Prop) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    (_facts : assignmentFacts context assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    AP head →
  ∀ {next output value finalStore size},
    EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore → size ≤ budget →
    AssignmentResultAt protocol readiness size values.checked registry functions program context evidence source faults
      scope (head.writtenContext actualContext) assignment.target operator rhs environment canonical actual before store mapping world
      initial (next.rename ξ) output value finalStore

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful.WithReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPreservation
/-! Header prefixes retain their real stopping scope and
actual installed observations through marked allocations and seven-slot writes.
The continuation agreement concerns the real reached prefix; its execution is
not a premise of the static tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Fallthrough)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

include definitions registered producer acquire stateTransport stateBindings sites transfers extension faithful observations in
theorem Tree.preserves_prefix_bounded_for_with_return
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry) program evidence
      source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      protocol.Relates state tail.state ∧
      Nonempty (ReadyReturn protocol readiness context scope canonical finalContext tail.scope tail.canonical) ∧
      readiness.Ready finalContext tail.state ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  induction tree generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native finalContext finalEnvironment after size with
  | nil next =>
    cases trace
    exact ⟨⟨⟨_, _, mapping, world, canonical, actual, actualContext, ξ, store, next, valid,
      environments, heaps, locals, agrees, actualTyped, reference, read, unmapped⟩, state, gate⟩,
      .refl _, .refl _, .refl _ _, .refl _, protocol.refl state, ⟨ReadyReturn.refl protocol readiness _ _ canonical⟩, ready, .refl _ _ _⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining ih =>
    cases trace with | cons first rest =>
      cases first with | letUninitialized _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
          TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
            environments heaps locals agrees actualTyped reference read allocated state ((acquire _ _ gate) state read)
        obtain ⟨nextState, allocationRelated⟩ := allocationTransition
        have nextReady := transfers.absent state nextState ready extended allocated preservation
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letUninitialized mono extended allocated)
        obtain ⟨tail, maps, worlds, lastFrame, metadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        exact ⟨tail,
          (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
          (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
          preservation.trans lastFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
          protocol.trans allocationRelated tailRelated,
          ⟨ReadyReturn.then (ReadyReturn.binding stateBindings transfers extended scope canonical payload
            (.cellRef (OptionalCell.cellType payload) (store.length + 2))) tailReturn⟩, tailReady, (ContinuationAgreement.letE allocationEval).trans agreement⟩
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with
      | letInitialized initialTrace _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
          boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact (.initialized mono) found)
            environments heaps locals agrees actualTyped state ready (.value initialTrace)
        cases represented with
        | value payload =>
          obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
            TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated middleState ((acquire _ _ gate) middleState frameRead)
          obtain ⟨nextState, allocationRelated⟩ := allocationTransition
          have nextReady := transfers.initialized middleState nextState middlePost.1 extended
            (sourceType ▸ middlePost.2) allocated allocationFrame
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letInitialized initialTrace.sound mono extended allocated)
          obtain ⟨tail, finalMaps, finalWorlds, finalFrame, finalMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
            ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          refine ⟨tail,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
            protocol.trans expressionRelated (protocol.trans allocationRelated tailRelated),
            ⟨ReadyReturn.then (ReadyReturn.binding stateBindings transfers extended scope canonical lowered.type
              (.cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2))) tailReturn⟩, tailReady, ?_⟩
          rw [sequence_rename]
          exact (ContinuationAgreement.bind initialEval).trans ((ContinuationAgreement.letE allocationEval).trans agreement)
      | letInitializedGeneralized _ captures poly other allocated => exact False.elim (poly mono)
  | discard found child remaining ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | expression childTrace =>
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
          boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact .discard found)
            environments heaps locals agrees actualTyped state ready (.value childTrace)
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.expression childTrace.sound)
          obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
            ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState gate middlePost.1 rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
            protocol.trans expressionRelated tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
          rw [LoopRenaming.discard]
          rw [GenericExpressionMeaning.rename_prefix] at agreement
          exact (ContinuationAgreement.bind first).trans agreement
  | @assign context scope assignment operator rhs rest body head remaining ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | assignValue assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, assignmentTransition, prefixAgreement⟩ :=
          assignments _ valid head (sites.assignment itemFact)
            environments heaps locals agrees actualTyped state ready assigned (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        obtain ⟨middleState, assignmentRelated, middleReady⟩ := assignmentTransition
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignValue assigned.sound)
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
          protocol.trans assignmentRelated tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

  | @bitNot context scope assignment rest body head remaining ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions program evidence
            environments heaps locals agrees actualTyped assigned.sound
        let middleState := stateTransport.extend state maps worlds preservation metadata
        have middleReady := snapshots.ready state middleState ready valid (sites.snapshot itemFact) assigned.sound locals preservation
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignBitNot assigned.sound)
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
          protocol.trans (stateTransport.related state maps worlds preservation metadata) tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

  | @bitNotProjected context scope assignment rest body head remaining ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, ⟨middleState, middleRelated⟩, prefixAgreement⟩ :=
          head.preserves_prefix_bounded functions extension program evidence protocol stateTransport readiness faithful observations
            (fun id member node found => sites.expression itemFact (.projectedBitNotKey member) found)
            budget (boundedMeaning context valid) environments heaps locals agrees actualTyped state ready assigned
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        have middleReady := snapshots.ready state middleState ready valid (sites.snapshot itemFact) assigned.sound locals preservation
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignBitNot assigned.sound)
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
          protocol.trans middleRelated tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

end WithReady

include definitions registered producer acquire stateTransport stateBindings extension faithful observations in
theorem Tree.preserves_prefix_bounded_for_with_return
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry) program evidence
      source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      protocol.Relates state tail.state ∧
      Nonempty (ReturnTo protocol scope canonical tail.scope tail.canonical) ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  obtain ⟨tail, maps, worlds, frame, metadata, related, ⟨returnTo⟩, _ready, agreement⟩ :=
    WithReady.Tree.preserves_prefix_bounded_for_with_return (solved := solved)
      (functions := functions) (definitions := definitions) (registered := registered)
      (extension := extension) (faithful := faithful) (observations := observations)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) (facts := fun _ _ => True) (itemFacts := fun _ _ => True)
      (exprFacts := fun _ _ _ => True) (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
      (sites := WithReady.StaticSites.trivial program evidence source)
      (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
      (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
      validity extend budget
      (fun context valid => WithReady.assignment_prefix_trivial protocol functions program evidence source
        (certificates context) context administrative budget (assignments context valid))
      (fun context valid size within => ProtectedWhile.Body.Stateful.WithReady.expression_preserves_trivial
        protocol (boundedMeaning context valid size within))
      tree valid True.intro environments heaps locals agrees actualTyped reference read unmapped state gate True.intro trace bounded
  exact ⟨tail, maps, worlds, frame, metadata, related, ⟨returnTo.toReturnTo⟩, agreement⟩

include definitions registered producer acquire stateTransport stateBindings extension faithful observations in
theorem Tree.preserves_prefix_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry) program evidence
      source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      protocol.Relates state tail.state ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  obtain ⟨tail, maps, worlds, preservation, metadata, related, _returnTo, agreement⟩ :=
    Tree.preserves_prefix_bounded_for_with_return
      (functions := functions) (definitions := definitions) (registered := registered)
      (extension := extension) (faithful := faithful) (observations := observations)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      validity extend budget assignments boundedMeaning tree valid environments heaps locals agrees actualTyped
      reference read unmapped state gate trace bounded
  exact ⟨tail, maps, worlds, preservation, metadata, related, agreement⟩

end Stateful

private def legacyBindings (bindings : ProtectedExpressionMeaning.Binds entry) :
    ProtectedStateTransition.Bindings (ProtectedStateTransition.Lexical.legacyProtocol entry) where
  prepend state _id _type _value := ⟨bindings.prepend state.down⟩
  prepend_related _state _id _type _value := trivial
  prepend_records _state _id _type _value := rfl
  restore state := ⟨bindings.restore state.down⟩
  restore_related _state := trivial
  restore_records _state := rfl

private def legacyProducer (functions : FunctionModel values.checked.catalog ambient)
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry) :
    ProtectedStateTransition.OrdinaryAllocation.Producer (ProtectedStateTransition.Lexical.legacyProtocol entry) layouts frame
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) :=
  ProtectedStateTransition.OrdinaryAllocation.of_administrative _
    (ProtectedStateTransition.Lexical.legacyTransport transport) (legacyBindings bindings)
    layouts frame (CompatibleAmbientHeap.payloadModel values.checked registry functions)

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_prefix_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  have assignments : ∀ context, validity context → Stateful.AssignmentPrefixPreservesAt
      (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry) program evidence source
      (certificates context) context administrative budget := by
    intro context valid scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
      environments heaps locals agrees typed state updated after size assigned within
    obtain ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed, installed, agreement⟩ :=
      ProtectedAssignmentHeads.Head.preserves_prefix_bounded functions extension program evidence transport faithful observations head
        environments heaps locals agrees typed state.down budget (boundedMeaning _ valid) assigned within
    exact ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed,
      ⟨⟨installed⟩, trivial⟩, agreement⟩
  obtain ⟨tail, maps, worlds, preservation, metadata, _related, agreement⟩ :=
    Stateful.Tree.preserves_prefix_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (extension := extension) (faithful := faithful) (observations := observations)
      (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
      (producer := legacyProducer functions transport bindings)
      (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport) (stateBindings := legacyBindings bindings)
      validity extend budget assignments
      (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        functions program evidence transport (boundedMeaning context valid size smaller))
      tree valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace bounded
  exact ⟨tail.toLegacy, maps, worlds, preservation, metadata, agreement⟩

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_prefix_bounded (budget : Nat)
    (boundedMeaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  apply Tree.preserves_prefix_bounded_for (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning faithful observations transport bindings in
theorem Tree.preserves_prefix {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding)  := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForItemsExecute.has_size trace
  exact tree.preserves_prefix_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded (meaning context valid) size)
    valid environments heaps locals agrees actualTyped reference read unmapped installed sized (Nat.le_refl size)

namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

include definitions registered producer acquire stateTransport stateBindings sites transfers in
theorem Tree.preserves_fault_reachable_bounded_for_with_eliminator
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative ambient.definitions)
    (UP : GenericForHeader.Structural.UnaryPayload)
    (unaryErrors : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment),
      UP head → head.Errors faults)
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesWithPayloadAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget (fun head => AP head))
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (eliminator : GenericForHeader.Structural.Eliminates
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (certificates := certificates)
      (definitions := ambient.definitions) (administrative := administrative) (type := type)
      (continuation := continuation) AP UP context scope items code)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  let M : SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop :=
    fun context scope items code =>
    ∀ {finalContext : SourceSemantics.Context},
    ∀ (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget),
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩
  have algebra : GenericForHeader.Structural.BranchAlgebra
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (type := type) (continuation := continuation) AP UP M := by
    clear eliminator ready gate state unmapped read reference actualTyped agrees locals heaps environments
      bounded trace itemsFacts valid
    clear finalContext reason after size mapping world actualContext environment canonical actual before store ξ contextLocation native
      context scope items code
    constructor
    · intro context scope code next
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      cases trace
    · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      cases trace with
      | head failed => cases failed with | polymorphicLet poly unsupported => exact False.elim (poly mono)
      | tail first rest =>
        cases first with | letUninitialized _ other allocated =>
          cases binder_context_eq extended other
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
            TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
              environments heaps locals agrees actualTyped reference read allocated state ((acquire _ _ gate) state read)
          obtain ⟨nextState, allocationRelated⟩ := allocationTransition
          have nextReady := transfers.absent state nextState ready extended allocated preservation
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letUninitialized mono extended allocated)
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, maps, worlds, lastFrame, metadata, tailTransition⟩ :=
            ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          obtain ⟨tailState, tailRelated, tailPost⟩ := tailTransition
          let reached := stateBindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) tailState
          have restoredRelated := stateBindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) tailState
          have restoredPost := transfers.restore_fault (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (binder := binder) (type := payload) tailState tailPost
          exact ⟨token, finalStore, finalMap, finalWorld, .letE allocationEval completed, matched, finalHeaps,
            (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
            (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
            preservation.trans lastFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, ⟨reached, protocol.trans allocationRelated (protocol.trans tailRelated restoredRelated), restoredPost⟩⟩
    · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      have itemFact := sites.head itemsFacts
      rw [sequence_rename]
      cases trace with
      | head failed =>
        cases failed with
        | polymorphicLet poly unsupported => exact False.elim (poly mono)
        | letInitializer _ failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
            boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact (.initialized mono) found)
              environments heaps locals agrees actualTyped state ready (.fault failed)
          cases represented with | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩
      | tail first rest =>
        cases first with
        | letInitialized initialTrace _ other allocated =>
          cases binder_context_eq extended other
          obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
            boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact (.initialized mono) found)
              environments heaps locals agrees actualTyped state ready (.value initialTrace)
          cases represented with
          | value payload =>
            obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
            have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
            obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
              TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated middleState ((acquire _ _ gate) middleState frameRead)
            obtain ⟨nextState, allocationRelated⟩ := allocationTransition
            have nextReady := transfers.initialized middleState nextState middlePost.1 extended
              (sourceType ▸ middlePost.2) allocated allocationFrame
            have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letInitialized initialTrace.sound mono extended allocated)
            obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailTransition⟩ :=
              ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
                (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1
                nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
            obtain ⟨tailState, tailRelated, tailPost⟩ := tailTransition
            let reached := stateBindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type) tailState
            have restoredRelated := stateBindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type) tailState
            have restoredPost := transfers.restore_fault (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (binder := binder) (type := lowered.type) tailState tailPost
            exact ⟨token, finalStore, finalMap, finalWorld, LanguageResult.bind_success _ initialEval (.letE allocationEval completed), matched, finalHeaps,
              maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
              worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
              preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
              ⟨reached, protocol.trans expressionRelated (protocol.trans allocationRelated (protocol.trans tailRelated restoredRelated)), restoredPost⟩⟩
        | letInitializedGeneralized _ captures poly other allocated => exact False.elim (poly mono)
    · intro context scope expression expressionNode rest lowered body found child ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      have itemFact := sites.head itemsFacts
      rw [LoopRenaming.discard]
      cases trace with
      | head failed =>
        cases failed with | expression failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
            boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact .discard found)
              environments heaps locals agrees actualTyped state ready (.fault failed)
          cases represented with | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩
      | tail first rest =>
        cases first with | expression childTrace =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
            boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact .discard found)
              environments heaps locals agrees actualTyped state ready (.value childTrace)
          cases represented with
          | @value _ coreValue payload =>
            obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
            have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.expression childTrace.sound)
            obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, tailTransition⟩ :=
              ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
                (GenericExpressionMeaning.agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
                ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState gate middlePost.1 rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
            obtain ⟨reached, tailRelated, tailPost⟩ := tailTransition
            refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
              ⟨reached, protocol.trans expressionRelated tailRelated, tailPost⟩⟩
            rw [GenericExpressionMeaning.rename_prefix] at completed
            exact LocalSequence.discard_success _ first completed
    · intro context scope assignment operator rhs rest body head headPayload ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      have itemFact := sites.head itemsFacts
      cases trace with
      | head failed =>
        cases failed with | assignValue failed =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, assignmentTransition⟩ :=
            assignmentFaults _ valid head (sites.assignment itemFact)
              environments heaps locals agrees actualTyped state ready headPayload failed (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) body (LocalLoop.controlType type)
          exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, assignmentTransition⟩
      | tail first rest =>
        cases first with | assignValue assigned =>
          obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, assignmentTransition, prefixAgreement⟩ :=
            assignments _ valid head (sites.assignment itemFact)
              environments heaps locals agrees actualTyped state ready assigned (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          obtain ⟨middleState, assignmentRelated, middleReady⟩ := assignmentTransition
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignValue assigned.sound)
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, tailTransition⟩ :=
            ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          obtain ⟨reached, tailRelated, tailPost⟩ := tailTransition
          refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
            ⟨reached, protocol.trans assignmentRelated tailRelated, tailPost⟩⟩
          exact (prefixAgreement body (LocalLoop.controlType type)).wrap (by
            simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed)

    · intro context scope assignment rest body head headPayload ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      have headErrors := unaryErrors head headPayload
      have itemFact := sites.head itemsFacts
      cases trace with
      | head failed =>
        cases failed with | assignBitNot failed =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩ :=
            head.preserves_fault functions program evidence
              environments heaps locals agrees headErrors failed.sound body (LocalLoop.controlType type)
          exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata,
            ⟨stateTransport.extend state maps worlds preservation metadata, stateTransport.related state maps worlds preservation metadata,
              readiness.fault_after state (stateTransport.extend state maps worlds preservation metadata) (readiness.ready_fault ready) preservation⟩⟩
      | tail first rest =>
        cases first with | assignBitNot assigned =>
          obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
            head.preserves_prefix functions program evidence
              environments heaps locals agrees actualTyped assigned.sound
          let middleState := stateTransport.extend state maps worlds preservation metadata
          have middleReady := snapshots.ready state middleState ready valid (sites.snapshot itemFact) assigned.sound locals preservation
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignBitNot assigned.sound)
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, tailTransition⟩ :=
            ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          obtain ⟨reached, tailRelated, tailPost⟩ := tailTransition
          refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
            ⟨reached, protocol.trans (stateTransport.related state maps worlds preservation metadata) tailRelated, tailPost⟩⟩
          exact (prefixAgreement body (LocalLoop.controlType type)).wrap (by
            simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed)
  exact eliminator M algebra valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered producer acquire stateTransport stateBindings sites transfers in
theorem Tree.preserves_fault_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact Tree.preserves_fault_reachable_bounded_for_with_eliminator
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
    (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts) (sites := sites) (transfers := transfers)
    (fun head => head.ReachableErrors registry faults) (fun head => head.Errors faults) (fun _ receipt => receipt)
    validity snapshots extend budget assignments assignmentFaults boundedMeaning
    (GenericForHeader.Structural.of_reachable_errors errors)
    valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

end WithReady

include definitions registered producer acquire stateTransport stateBindings in
theorem Tree.preserves_fault_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    WithReady.Tree.preserves_fault_reachable_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (facts := fun _ _ => True) (itemFacts := fun _ _ => True) (exprFacts := fun _ _ _ => True)
      (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
      (sites := WithReady.StaticSites.trivial program evidence source)
      (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
      (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
      validity extend budget
      (fun context valid => WithReady.assignment_prefix_trivial protocol functions program evidence source
        (certificates context) context administrative budget (assignments context valid))
      (fun context valid => WithReady.assignment_fault_trivial protocol functions program evidence source
        (certificates context) context administrative faults budget (assignmentFaults context valid))
      (fun context valid size within => ProtectedWhile.Body.Stateful.WithReady.expression_preserves_trivial
        protocol (boundedMeaning context valid size within))
      tree errors valid True.intro environments heaps locals agrees actualTyped reference read unmapped state gate True.intro trace bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

end Stateful

include extension faithful observations transport in
private theorem legacyAssignmentPrefix (context : SourceSemantics.Context) (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) :
    Stateful.AssignmentPrefixPreservesAt (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry)
      program evidence source (certificates context) context administrative budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed state updated after size assigned within
  obtain ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed, installed, agreement⟩ :=
    ProtectedAssignmentHeads.Head.preserves_prefix_bounded functions extension program evidence transport faithful observations head
      environments heaps locals agrees typed state.down budget boundedMeaning assigned within
  exact ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed,
    ⟨⟨installed⟩, trivial⟩, agreement⟩

include extension faithful observations transport in
private theorem legacyAssignmentFault (context : SourceSemantics.Context) (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) :
    Stateful.AssignmentFaultPreservesAt (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed state errors reason after size failed within next output
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, installed⟩ :=
    ProtectedAssignmentHeads.Head.preserves_fault_reachable_bounded functions extension program evidence transport faithful observations head
      environments heaps locals agrees typed state.down budget boundedMeaning errors failed within next output
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata,
    ⟨⟨installed⟩, trivial⟩⟩

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_fault_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, _transition⟩ :=
    Stateful.Tree.preserves_fault_reachable_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
      (producer := legacyProducer functions transport bindings)
      (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport) (stateBindings := legacyBindings bindings)
      validity extend budget
      (fun context valid => legacyAssignmentPrefix functions extension program evidence transport faithful observations context budget (boundedMeaning context valid))
      (fun context valid => legacyAssignmentFault functions extension program evidence transport faithful observations context budget (boundedMeaning context valid))
      (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        functions program evidence transport (boundedMeaning context valid size smaller))
      tree errors valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_fault_reachable_bounded (budget : Nat)
    (boundedMeaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply Tree.preserves_fault_reachable_bounded_for (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning faithful observations transport bindings in
theorem Tree.preserves_fault_reachable {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after  := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForItemsFault.has_size trace
  exact tree.preserves_fault_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded (meaning context valid) size)
    errors valid environments heaps locals agrees actualTyped reference read unmapped installed sized (Nat.le_refl size)

include definitions registered extension meaning faithful observations transport bindings in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.preserves_fault {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply Tree.preserves_fault_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderReflection
/-! Completed native headers reconstruct their independent source prefix or
first fault. A successful prefix exposes the real remaining evaluation under
its actual typed environment; no source trace or child execution is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Fallthrough)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

include definitions registered producer acquire stateTransport stateBindings sites transfers in
theorem Tree.reflects_reachable_bounded_for_with_eliminator
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative ambient.definitions)
    (UP : GenericForHeader.Structural.UnaryPayload)
    (unaryErrors : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment),
      UP head → head.Errors faults)
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentReflectsWithPayloadAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget (fun head => AP head))
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionReflectsAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size))
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (eliminator : GenericForHeader.Structural.Eliminates
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (certificates := certificates)
      (definitions := ambient.definitions) (administrative := administrative) (type := type)
      (continuation := continuation) AP UP context scope items code)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor protocol readiness condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  let M : SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop :=
    fun context scope items code =>
    ∀ (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget),
    ResultAtFor protocol readiness condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore
  have algebra : GenericForHeader.Structural.BranchAlgebra
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (type := type) (continuation := continuation) AP UP M := by
    clear eliminator ready gate state unmapped read reference actualTyped agrees locals heaps environments
      bounded evaluated itemsFacts valid
    clear finalStore value size mapping world actualContext environment canonical actual before store ξ contextLocation native
      context scope items code
    constructor
    · intro context scope code next
      intro valid itemsFacts mapping world actualContext environment canonical actual before store finalStore value ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size evaluated bounded
      exact .continues ⟨⟨scope, code, mapping, world, canonical, actual, actualContext, ξ, store, next, valid,
        environments, heaps, locals, agrees, actualTyped, reference, read, unmapped⟩, state, gate⟩ .nil (.refl _) (.refl _) (.refl _ _) (.refl _) (protocol.refl state) ⟨ReadyReturn.refl protocol readiness _ _ canonical⟩ ready evaluated (Nat.le_refl _)
    · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same ih
      intro valid itemsFacts mapping world actualContext environment canonical actual before store finalStore value ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size evaluated bounded
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
        TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
          environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append state ((acquire _ _ gate) state read)
      obtain ⟨nextState, allocationRelated⟩ := allocationTransition
      have nextReady := transfers.absent state nextState ready extended Dynamic.Heap.Allocates.append preservation
      have nextFacts := sites.tail (environment := environment) (before := before) itemsFacts (Dynamic.ForItemExecutes.letUninitialized mono extended .append)
      obtain ⟨remainingSize, smaller, remainingEval⟩ := ForHeaderNativeBounds.allocation_body evaluated allocationEval
      have reflected := ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          nextState gate nextReady remainingEval (Nat.le_trans (Nat.le_of_lt smaller) bounded)
      exact reflected.prepend_binding stateBindings transfers extended nextState allocationRelated (.letUninitialized mono extended .append)
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩)
        preservation (.of_allocation Dynamic.Heap.Allocates.append) (Nat.le_of_lt smaller)
    · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same ih
      intro valid itemsFacts mapping world actualContext environment canonical actual before store finalStore value ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size evaluated bounded
      have itemFact := sites.head itemsFacts
      have expressionFact := sites.expression itemFact (.initialized mono) found
      rw [sequence_rename] at evaluated
      have input : ∃ input middle childSize, childSize < size ∧ EvaluationSize childSize actual store (lowered.expression.rename ξ) input middle := by
        cases evaluated with
        | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, _, by omega, initial⟩
      obtain ⟨input, middleStore, initialSize, initialSmaller, initialEval⟩ := input
      obtain ⟨sourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
        boundedReflection _ valid _ (Nat.lt_of_lt_of_le initialSmaller bounded) child found expressionFact
          environments heaps locals agrees actualTyped state ready initialEval
      obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
      cases represented with
      | fault matched =>
        cases initialTrace with | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LanguageResult.bind_failure _ initialEval.sound)
          exact .fault (.head (.letInitializer mono failed)) rfl matched middleHeaps maps worlds preservation metadata ⟨middleState, expressionRelated, middlePost⟩
      | value payload =>
        cases initialTrace with | value initialTrace =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
            TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append middleState ((acquire _ _ gate) middleState frameRead)
          obtain ⟨nextState, allocationRelated⟩ := allocationTransition
          have nextReady := transfers.initialized middleState nextState middlePost.1 extended
            (sourceType ▸ middlePost.2) Dynamic.Heap.Allocates.append allocationFrame
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letInitialized initialTrace.sound mono extended .append)
          obtain ⟨remainingSize, smaller, tailEval⟩ := ForHeaderNativeBounds.initialized_body evaluated initialEval.sound allocationEval
          have reflected := ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
            (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              (List.getElem?_eq_some_iff.mp frameRead).1).1
            nextState gate nextReady tailEval (Nat.le_trans (Nat.le_of_lt smaller) bounded)
          exact reflected.prepend_binding stateBindings transfers extended nextState (protocol.trans expressionRelated allocationRelated) (.letInitialized initialTrace mono extended .append)
            (maps.trans (show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩))
            (worlds.trans (show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩))
            (preservation.trans allocationFrame) (metadata.trans (.of_allocation Dynamic.Heap.Allocates.append)) (Nat.le_of_lt smaller)
    · intro context scope expression expressionNode rest lowered body found child ih
      intro valid itemsFacts mapping world actualContext environment canonical actual before store finalStore value ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size evaluated bounded
      have itemFact := sites.head itemsFacts
      have expressionFact := sites.expression itemFact .discard found
      rw [LoopRenaming.discard] at evaluated
      have complete := evaluated
      cases evaluated with
      | caseLeft childEvaluation branch =>
        obtain ⟨sourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
          boundedReflection _ valid _ (by omega) child found expressionFact
            environments heaps locals agrees actualTyped state ready childEvaluation
        obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
        cases represented with | fault matched =>
          cases trace with | fault failed =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound (LocalSequence.discard_failure _ childEvaluation.sound)
            exact .fault (.head (.expression failed)) rfl matched finalHeaps maps worlds preservation metadata ⟨middleState, expressionRelated, middlePost⟩
      | caseRight childEvaluation branch =>
        obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
          boundedReflection _ valid _ (by omega) child found expressionFact
            environments heaps locals agrees actualTyped state ready childEvaluation
        cases represented with | @value _ coreValue payload =>
          obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
          cases trace with | value childTrace =>
            have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.expression childTrace.sound)
            have reflected := ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState gate middlePost.1
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch) (by omega)
            exact reflected.prepend middleState expressionRelated (.expression childTrace) maps worlds preservation metadata (by omega)
    · intro context scope assignment operator rhs rest body head headPayload ih
      intro valid itemsFacts mapping world actualContext environment canonical actual before store finalStore value ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size evaluated bounded
      have itemFact := sites.head itemsFacts
      have assignmentFact := sites.assignment itemFact
      have assigned := assignments _ valid head assignmentFact
        environments heaps locals agrees actualTyped state ready headPayload evaluated bounded
      cases assigned with
      | fault trace same matched finalHeaps maps worlds preservation metadata assignmentTransition =>
        exact .fault (.head (.assignValue trace)) same matched finalHeaps maps worlds preservation metadata assignmentTransition
      | success trace middleHeaps maps worlds preservation metadata count typed assignmentTransition smaller remainingEval =>
        obtain ⟨middleState, assignmentRelated, middleReady⟩ := assignmentTransition
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignValue trace.sound)
        have reflected := ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
          ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 middleState gate middleReady
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using remainingEval) (Nat.le_trans (Nat.le_of_lt smaller) bounded)
        exact reflected.prepend middleState assignmentRelated (.assignValue trace) maps worlds preservation metadata (Nat.le_of_lt smaller)

    · intro context scope assignment rest body head headPayload ih
      intro valid itemsFacts mapping world actualContext environment canonical actual before store finalStore value ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size evaluated bounded
      have headErrors := unaryErrors head headPayload
      have itemFact := sites.head itemsFacts
      have snapshotFact := sites.snapshot itemFact
      rcases head.reflects_sized functions program evidence
        environments heaps locals agrees actualTyped headErrors evaluated with
        ⟨sourceSize, reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, preservation, metadata⟩ |
        ⟨sourceSize, updated, middle, written, middleMap, middleWorld, slots, remainingSize, trace, middleHeaps, maps, worlds, preservation, metadata, count, typed, smaller, remainingEval⟩
      · exact .fault (.head (.assignBitNot trace)) rfl matched finalHeaps maps worlds preservation metadata
          ⟨stateTransport.extend state maps worlds preservation metadata, stateTransport.related state maps worlds preservation metadata,
            readiness.fault_after state _ (readiness.ready_fault ready) preservation⟩
      · let middleState := stateTransport.extend state maps worlds preservation metadata
        have middleReady := snapshots.ready state middleState ready valid snapshotFact trace.sound locals preservation
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignBitNot trace.sound)
        have reflected := ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
          ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState gate middleReady
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using remainingEval) (Nat.le_trans (Nat.le_of_lt smaller) bounded)
        exact reflected.prepend middleState (stateTransport.related state maps worlds preservation metadata) (.assignBitNot trace) maps worlds preservation metadata (Nat.le_of_lt smaller)
  exact eliminator M algebra valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

include definitions registered producer acquire stateTransport stateBindings sites transfers in
theorem Tree.reflects_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentReflectsAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionReflectsAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size))
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor protocol readiness condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  exact Tree.reflects_reachable_bounded_for_with_eliminator
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
    (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts) (sites := sites) (transfers := transfers)
    (fun head => head.ReachableErrors registry faults) (fun head => head.Errors faults) (fun _ receipt => receipt)
    validity snapshots extend budget assignments boundedReflection
    (GenericForHeader.Structural.of_reachable_errors errors)
    valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

end WithReady

include definitions registered producer acquire stateTransport stateBindings in
theorem Tree.reflects_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentReflectsAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size))
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor protocol condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  have result := WithReady.Tree.reflects_reachable_bounded_for
    (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ => True) (itemFacts := fun _ _ => True) (exprFacts := fun _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := WithReady.StaticSites.trivial program evidence source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
    (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
    validity extend budget
    (fun context valid => WithReady.assignment_reflection_trivial protocol functions program evidence source
      (certificates context) context administrative faults budget (assignments context valid))
    (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt.of_true
      protocol program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (certificates context) (boundedReflection context valid size smaller))
    tree errors valid True.intro environments heaps locals agrees actualTyped reference read unmapped
    state gate True.intro evaluated bounded
  exact result.toOriginal

end Stateful

include extension faithful observations transport in
private theorem legacyAssignmentReflection (context : SourceSemantics.Context) (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry))
    (functionTypes : FunctionRuntimeViews functions) :
    Stateful.AssignmentReflectsAt (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed state errors next output value finalStore size evaluated within
  have result := ProtectedAssignmentHeads.Head.reflects_reachable_bounded functions extension program evidence transport faithful observations head
    environments heaps locals agrees typed state.down budget boundedReflection functionTypes errors evaluated within
  cases result with
  | fault trace same matched finalHeaps maps worlds preservation metadata installed =>
    exact .fault trace same matched finalHeaps maps worlds preservation metadata ⟨⟨installed⟩, trivial⟩
  | success trace finalHeaps maps worlds preservation metadata count typed installed smaller remaining =>
    exact .success trace finalHeaps maps worlds preservation metadata count typed ⟨⟨installed⟩, trivial⟩ smaller remaining

include definitions registered extension faithful observations transport bindings in
theorem Tree.reflects_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedHeaderContracts.ResultAtFor validity size (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  have result := Stateful.Tree.reflects_reachable_bounded_for
    (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
    (producer := legacyProducer functions transport bindings)
    (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
    (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport) (stateBindings := legacyBindings bindings)
    validity extend budget
    (fun context valid => legacyAssignmentReflection functions extension program evidence transport faithful observations context budget (boundedReflection context valid) functionTypes)
    (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
      functions program evidence transport (boundedReflection context valid size smaller))
    tree errors valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated bounded
  exact result.toLegacy

include definitions registered extension faithful observations transport bindings in
theorem Tree.reflects_reachable_bounded (budget : Nat)
    (boundedReflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedHeaderContracts.ResultAt size (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  apply Tree.reflects_reachable_bounded_for (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning reflection faithful observations transport bindings in
theorem Tree.reflects_reachable (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    Result (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore  := by
  have _legacyMeaning := @meaning
  obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size evaluated
  exact (tree.reflects_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded (reflection context valid) size)
    functionTypes errors valid environments heaps locals agrees actualTyped reference read unmapped installed sized (Nat.le_refl size)).erase

include definitions registered extension meaning reflection faithful observations transport bindings in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.reflects (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    Result (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  apply Tree.reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPost
/-! The post header has an actual constant fallthrough continuation. Closing
that continuation recovers finite post execution and reflection. The reached post-local guard is retained, while the original outer guard is
transported by real map/world, administrative and metadata progress. Cells and
effects are retained when the post-local scope ends. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Fallthrough)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_post_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native (Fallthrough type) finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      Evaluates actual store (code.rename ξ) (LocalLoop.fallthroughValue type) tail.store ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions ∧
      entry scope tail.mapping tail.world after tail.store canonical := by
  obtain ⟨tail, maps, worlds, preservation, metadata, agreement⟩ :=
    tree.preserves_prefix_bounded_for functions definitions registered extension program evidence transport bindings faithful observations validity extend budget boundedMeaning
      valid environments heaps locals agrees actualTyped reference read unmapped installed trace bounded
  refine ⟨tail, maps, worlds, preservation, metadata, agreement.wrap tail.toTailFor.fallthrough_evaluates,
    environments.extend maps worlds, locals.mono metadata, actualTyped.weaken worlds, transport.extend installed maps worlds preservation metadata⟩

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_post_bounded (budget : Nat)
    (boundedMeaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native (Fallthrough type) finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      Evaluates actual store (code.rename ξ) (LocalLoop.fallthroughValue type) tail.store ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions ∧
      entry scope tail.mapping tail.world after tail.store canonical := by
  apply Tree.preserves_post_bounded_for (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning faithful observations transport bindings in
theorem Tree.preserves_post {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native (Fallthrough type) finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      Evaluates actual store (code.rename ξ) (LocalLoop.fallthroughValue type) tail.store ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions ∧
      entry scope tail.mapping tail.world after tail.store canonical  := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForItemsExecute.has_size trace
  exact tree.preserves_post_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded (meaning context valid) size)
    valid environments heaps locals agrees actualTyped reference read unmapped installed sized (Nat.le_refl size)

include definitions registered extension faithful observations transport bindings in
theorem Tree.reflects_post_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    (∃ sourceSize finalContext finalEnvironment after,
      ∃ tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
        (Fallthrough type) finalContext finalEnvironment after,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions ∧
      entry scope tail.mapping tail.world after tail.store canonical) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical) := by
  have reflected := tree.reflects_reachable_bounded_for (solved := solved) functions definitions registered extension program evidence transport bindings faithful observations validity extend budget boundedReflection
    functionTypes errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated bounded
  cases reflected with
  | continues tail trace maps worlds preservation metadata remaining _ =>
    obtain ⟨same, storeEq⟩ := tail.toTailFor.fallthrough_reflects remaining.sound
    exact .inl ⟨_, _, _, _, tail, trace, same, storeEq, maps, worlds, preservation, metadata,
      environments.extend maps worlds, locals.mono metadata, actualTyped.weaken worlds, transport.extend installed maps worlds preservation metadata⟩
  | fault trace same matched finalHeaps maps worlds preservation metadata =>
    exact .inr ⟨_, _, _, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, preservation, metadata, transport.extend installed maps worlds preservation metadata⟩

include definitions registered extension faithful observations transport bindings in
theorem Tree.reflects_post_reachable_bounded (budget : Nat)
    (boundedReflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    (∃ sourceSize finalContext finalEnvironment after,
      ∃ tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
        (Fallthrough type) finalContext finalEnvironment after,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions ∧
      entry scope tail.mapping tail.world after tail.store canonical) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical) := by
  apply Tree.reflects_post_reachable_bounded_for (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning reflection faithful observations transport bindings in
theorem Tree.reflects_post_reachable (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    (∃ finalContext finalEnvironment after,
      ∃ tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
        (Fallthrough type) finalContext finalEnvironment after,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions ∧
      entry scope tail.mapping tail.world after tail.store canonical) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical)  := by
  have _legacyMeaning := @meaning
  obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size evaluated
  rcases tree.reflects_post_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded (reflection context valid) size)
    functionTypes errors valid environments heaps locals agrees actualTyped reference read unmapped installed sized (Nat.le_refl size) with done | fault
  · obtain ⟨sourceSize, finalContext, finalEnvironment, after, tail, trace, same, storeEq, maps, worlds, preservation, metadata, environments, locals, typed, installed⟩ := done
    exact .inl ⟨finalContext, finalEnvironment, after, tail, trace.sound, same, storeEq, maps, worlds, preservation, metadata, environments, locals, typed, installed⟩
  · obtain ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, heaps, maps, worlds, preservation, metadata, installed⟩ := fault
    exact .inr ⟨finalContext, reason, token, after, finalMap, finalWorld, trace.sound, same, matched, heaps, maps, worlds, preservation, metadata, installed⟩

include definitions registered extension meaning reflection faithful observations transport bindings in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.reflects_post (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    (∃ finalContext finalEnvironment after,
      ∃ tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
        (Fallthrough type) finalContext finalEnvironment after,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions ∧
      entry scope tail.mapping tail.world after tail.store canonical) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical) := by
  apply Tree.reflects_post_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (LoopState Progress postValues postValues_typed postValues_agree post_rename)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {administrative actualContext : Core.Context}
  {type : Ty} {context : SourceSemantics.Context} {scope : Scope}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {conditionCode body postCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include definitions registered extension faithful observations transport bindings solved in
theorem post_preserves_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.1.contextRead
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.1.selfTyped state.1.actualTyped
  obtain ⟨tail, maps, worlds, preservation, metadata, evaluated, _, _, _, _⟩ :=
    tree.preserves_post_bounded_for (solved := solved) functions definitions registered extension program evidence transport bindings faithful observations validity extend budget boundedMeaning
      valid state.1.environments state.1.heaps state.1.locals (postValues_agree agrees type location continued) postTyped
      reference read state.1.contextUnmapped state.2 trace bounded
  exact ⟨tail.store, tail.mapping, tail.world, by simpa only [post_rename] using evaluated,
    tail.heaps, maps, worlds, preservation, metadata⟩

include definitions registered extension faithful observations transport bindings in
theorem post_preserves_bounded (budget : Nat)
    (boundedMeaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  apply post_preserves_bounded_for (solved := solved) (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning faithful observations transport bindings in
theorem post_preserves {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore  := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForItemsExecute.has_size trace
  exact post_preserves_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded (meaning context valid) size)
    tree valid agrees reference state continued sized (Nat.le_refl size)

include definitions registered extension faithful observations transport bindings in
theorem post_fault_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.1.contextRead
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.1.selfTyped state.1.actualTyped
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, preservation, metadata⟩ :=
    tree.preserves_fault_reachable_bounded_for functions definitions registered extension program evidence transport bindings faithful observations validity extend budget boundedMeaning
      errors valid state.1.environments state.1.heaps state.1.locals (postValues_agree agrees type location continued) postTyped
      reference read state.1.contextUnmapped state.2 trace bounded
  exact ⟨token, finalStore, finalMap, finalWorld, by simpa only [post_rename] using evaluated,
    matched, heaps, maps, worlds, preservation, metadata⟩

include definitions registered extension faithful observations transport bindings in
theorem post_fault_reachable_bounded (budget : Nat)
    (boundedMeaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  apply post_fault_reachable_bounded_for (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning faithful observations transport bindings in
theorem post_fault_reachable {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore  := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForItemsFault.has_size trace
  exact post_fault_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded (meaning context valid) size)
    tree errors valid agrees reference state continued sized (Nat.le_refl size)

include definitions registered extension meaning faithful observations transport bindings in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem post_fault {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  apply post_fault_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

include definitions registered extension faithful observations transport bindings solved in
theorem post_reflects_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) (functionTypes : FunctionRuntimeViews functions)
    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    {size : Nat} (evaluated : EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) (bounded : size ≤ budget) :
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) := by
  obtain ⟨native, read⟩ := state.1.contextRead
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.1.selfTyped state.1.actualTyped
  rcases tree.reflects_post_reachable_bounded_for (solved := solved) functions definitions registered extension program evidence transport bindings faithful observations validity extend budget boundedReflection
      functionTypes errors valid state.1.environments state.1.heaps state.1.locals
      (postValues_agree agrees type location continued) postTyped reference read state.1.contextUnmapped state.2
      (by simpa only [post_rename] using evaluated) bounded with done | fault
  · obtain ⟨sourceSize, finalContext, finalEnvironment, after, tail, trace, same, storeEq, maps, worlds, preservation, metadata, _, _, _, _⟩ := done
    subst finalStore
    exact .inl ⟨sourceSize, finalContext, finalEnvironment, after, tail.mapping, tail.world, trace, same,
      tail.heaps, maps, worlds, preservation, metadata⟩
  · obtain ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, heaps, maps, worlds, preservation, metadata, _⟩ := fault
    exact .inr ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched,
      heaps, maps, worlds, preservation, metadata⟩

include definitions registered extension faithful observations transport bindings in
theorem post_reflects_reachable_bounded (budget : Nat)
    (boundedReflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) (functionTypes : FunctionRuntimeViews functions)
    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    {size : Nat} (evaluated : EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) (bounded : size ≤ budget) :
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) := by
  apply post_reflects_reachable_bounded_for (solved := solved) (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning reflection faithful observations transport bindings in
theorem post_reflects_reachable (functionTypes : FunctionRuntimeViews functions)
    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (evaluated : Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) :
    (∃ finalContext finalEnvironment after finalMap finalWorld,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore)  := by
  have _legacyMeaning := @meaning
  obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size evaluated
  rcases post_reflects_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded (reflection context valid) size)
    functionTypes tree errors valid agrees reference state continued sized (Nat.le_refl size) with done | fault
  · obtain ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, trace, same, progress⟩ := done
    exact .inl ⟨finalContext, finalEnvironment, after, finalMap, finalWorld, trace.sound, same, progress⟩
  · obtain ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, progress⟩ := fault
    exact .inr ⟨finalContext, reason, token, after, finalMap, finalWorld, trace.sound, same, matched, progress⟩

include definitions registered extension meaning reflection faithful observations transport bindings in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem post_reflects (functionTypes : FunctionRuntimeViews functions)
    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedFor.Body.State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (evaluated : Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) :
    (∃ finalContext finalEnvironment after finalMap finalWorld,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) := by
  apply post_reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedImperativeForPreservation
/-! The existing statements/initializers grammar supplies one recursive induction.
Every ordinary child consumes its actual protected entry; for and while delegate
to their shared finite helpers. Static source/native/error receipts remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (Scope ValuesContext FlowRep restored restore_rep)
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized allocate_absent allocate_initialized sequence_rename valid_extend)
open GenericImperativeFor (Tree Position)
open ProtectedWhile.Body (Preserves Reflects)
private theorem breaking_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible
    · exact ScalarStatementViews.breaking unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.breaking_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible

private theorem continuing_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible
    · exact ScalarStatementViews.continuing unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.continuing_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible

variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

abbrev PreservingHeaderFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => ProtectedFor.Body.LoopPreserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev PreservingHeader (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => ProtectedFor.Body.LoopPreserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.Errors registry faults tree

abbrev ReflectingHeaderFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => ProtectedFor.Body.LoopReflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev ReflectingHeader (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => ProtectedFor.Body.LoopReflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (entry := entry) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.Errors registry faults tree

private theorem sequence_stopped_preserves (unique : NodeOccurrencesUnique source) {context : SourceSemantics.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ProtectedLoopStatements.Control.HeadPreserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    Preserves (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) executed with
      ⟨_, _, _, headTrace, tailTrace⟩ | ⟨headTrace, terminal⟩
    · cases stops headTrace
    · obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first valid environments heaps locals agrees actualTyped reference read unmapped installed (.control headTrace)
      cases represented with
      | fallthrough _ => cases terminal
      | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
          .returned payload, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | breaking next => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
          .breaking next, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | continuing next => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
          .continuing next, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) failed with
      ⟨rfl, headTrace⟩ | ⟨_, _, _, headTrace, tailTrace⟩
    · obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first valid environments heaps locals agrees actualTyped reference read unmapped installed (.fault headTrace)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · cases stops headTrace


include definitions registered extension transport bindings meaning faithful observations in
theorem header_preserves_reachable (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : PreservingHeaderFor (diagnosticPolicy := .reachable) (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    ProtectedLoopStatements.Control.HeadPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨header, errors⟩ := headers
  cases trace with
  | control executed =>
    obtain ⟨rfl, loopContext, loopFinalContext, loopEnvironment, initialized, loopOutcome, rfl, initialization, loop⟩ :=
      ForSourceViews.success unique (lookupStatement?_sound found) form executed
    have sameContext : loopFinalContext = loopContext := by cases loop <;> rfl
    subst loopFinalContext
    obtain ⟨tail, maps, worlds, frame, metadata, agreement⟩ :=
      ProtectedForHeader.Tree.preserves_prefix functions definitions registered extension program evidence transport bindings meaning faithful observations header
        valid environments heaps locals agrees actualTyped reference read unmapped installed initialization
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
      tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.installed (.control loop)
    exact ⟨rfl, restored environment loopOutcome, value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
      restore_rep represented environment, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
      frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2.1⟩
  | fault failed =>
    rcases ForSourceViews.fault unique (lookupStatement?_sound found) form failed with initialFailure | loopFailure
    · obtain ⟨_, fault⟩ := initialFailure
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, frame, metadata⟩ :=
        ProtectedForHeader.Tree.preserves_fault_reachable functions definitions registered extension program evidence transport bindings meaning faithful observations header errors
          valid environments heaps locals agrees actualTyped reference read unmapped installed fault
      exact ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld,
        evaluated, .fault matched, heaps, maps, worlds, frame, metadata⟩
    · obtain ⟨loopContext, loopEnvironment, initialized, initialization, loop⟩ := loopFailure
      obtain ⟨tail, maps, worlds, frame, metadata, agreement⟩ :=
        ProtectedForHeader.Tree.preserves_prefix functions definitions registered extension program evidence transport bindings meaning faithful observations header
          valid environments heaps locals agrees actualTyped reference read unmapped installed initialization
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
        tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.installed (.fault loop)
      exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
        represented, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
        frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2.1⟩

include definitions registered extension transport bindings meaning faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem header_preserves (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : PreservingHeader (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    ProtectedLoopStatements.Control.HeadPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type code := by
  apply header_preserves_reachable (functions := functions) (headers := by rcases headers with ⟨header, errors⟩; exact ⟨header, errors.reachable⟩)
  all_goals assumption

include extension meaning transport bindings definitions registered faithful observations in
theorem loop_preserves_reachable (unique : NodeOccurrencesUnique source) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code) :
    ProtectedFor.Body.LoopPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  have result := ProtectedFor.Body.loop_preserves functions program evidence transport (meaning _ valid)
    conditionFound conditionTree typed unique correct
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        mapping world before after store finalContext finalEnvironment guarded continued execution
      exact ProtectedForHeader.post_preserves functions definitions registered extension program evidence transport bindings meaning faithful observations postTree
        actualValid actualAgrees actualReference guarded continued execution)
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        mapping world before after store finalContext reason guarded continued execution
      exact ProtectedForHeader.post_fault_reachable functions definitions registered extension program evidence transport bindings meaning faithful observations postTree postErrors
        actualValid actualAgrees actualReference guarded continued execution)
  exact result valid environments heaps locals agrees actualTyped reference read unmapped installed trace

abbrev PreservesAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Preserves (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => PreservingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev PreservesAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Preserves (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => PreservingHeader (certificates := certificates) (entry := entry) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => ReflectingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects (entry := entry) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => ReflectingHeader (certificates := certificates) (entry := entry) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

include extension meaning transport bindings definitions registered faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem loop_preserves (unique : NodeOccurrencesUnique source) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
    (correct : Preserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code) :
    ProtectedFor.Body.LoopPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  apply loop_preserves_reachable (functions := functions) (postErrors := postErrors.reachable)
  all_goals assumption

include definitions registered extension transport bindings meaning faithful observations in
theorem preservesAt_for (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    PreservesAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      ProtectedLexicalStatements.Tree.preserves functions definitions registered program evidence transport bindings meaning body contextValid unique environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨location, middle, allocated, tailTrace⟩ := source_view_absent unique found form mono extended trace
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (bindings.prepend (transport.extend installed ⟨_, rfl⟩ ⟨_, rfl⟩ preservation
          (Dynamic.HeapMetadataExtend.of_allocation allocated))) tailTrace
    exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    rw [sequence_rename]
    rcases source_view_initialized unique found form mono extended trace with ⟨reason, rfl, rfl, failed⟩ |
        ⟨sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid initial initialFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid initial initialFound
          environments heaps locals agrees actualTyped installed (.value initialTrace)
      cases represented with
      | value payload =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
        obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              (bindings.prepend (transport.extend
                (transport.extend installed maps worlds preservation metadata) ⟨_, rfl⟩ ⟨_, rfl⟩ allocationFrame
                (Dynamic.HeapMetadataExtend.of_allocation allocated))) tailTrace
        exact ⟨result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    rcases TypedScopedStatements.discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        meaning _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
          ih contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata) tail
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedLoopStatements.Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.block_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedLoopStatements.Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.conditional_preserves transport unique meaning (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace


  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerErrors innerIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact sequence_stopped_preserves unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.block_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found form innerIH) (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact sequence_stopped_preserves unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.conditional_preserves transport unique meaning (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form conditionFound conditionType conditionTree thenIH elseIH) (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace


  | @breaking context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨rfl, rfl, rfl⟩ := breaking_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates _ actual store,
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨rfl, rfl, rfl⟩ := continuing_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates _ actual store,
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedLoopStatements.Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.of_retained_preserves functions program evidence (ProtectedWhile.Body.while_preserves functions program evidence transport
        (meaning _ contextValid) found form conditionFound conditionTree nativeTyped unique loopIH)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
        (first : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
        (tail : Executes mode program middleContext evidence source next middle rest resultContext outcome after) :
        ∃ value finalStore finalMap finalWorld,
          Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
          FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
          LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
          AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
          LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
            context scope environment resultContext after := by
      obtain ⟨rfl, same, updated, assigned⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
      cases same
      obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, observed, continuation⟩ :=
        ProtectedAssignmentHeads.Head.preserves_prefix functions extension program evidence transport
          (meaning _ contextValid) faithful observations head
          environments heaps locals agrees actualTyped installed assigned
      have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih contextValid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference frameRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 observed tail
      exact ⟨value, finalStore, finalMap, finalWorld,
        (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count,
          SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, lexical⟩
    cases source_view trace with
    | control executed =>
      rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) executed with
        ⟨_, _, _, first, tail⟩ | ⟨first, terminal⟩
      · exact go first (by cases mode <;> exact .control tail)
      · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
        cases terminal
    | fault failed =>
      rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
        ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
      · obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, observed⟩ :=
          ProtectedAssignmentHeads.Head.preserves_fault_reachable functions extension program evidence transport
            (meaning _ contextValid) faithful observations head
            environments heaps locals agrees actualTyped installed (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors)
            (ScalarStatementViews.assignValue_fault unique (lookupStatement?_sound found) form first) body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      · exact go first (by cases mode <;> exact .fault tail)

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedBitNotStatements.assignment_preserves functions program evidence transport
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ProtectedLoopStatements.Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (header_preserves_reachable functions definitions registered extension program evidence transport bindings meaning faithful observations unique found form (by rcases initialIH with ⟨header, errors⟩; exact ⟨header, GenericForHeader.Tree.ErrorsFor.reachable errors⟩)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := loop_preserves_reachable functions definitions registered extension program evidence transport bindings meaning faithful observations unique
      conditionFound conditionTree nativeTyped postTree (GenericForHeader.Tree.ErrorsFor.reachable postErrors) loopIH
    exact ⟨.nil completed, GenericForHeader.Tree.ErrorsFor.nil (policy := diagnosticPolicy) (next := completed)⟩
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same header, .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.initialized mono extended ordinary found sourceType child allocation annotation same header, .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := child) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found child remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.discard found child header, .discard (found := found) (value := child) errors⟩
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.assign head header, .assign (head := head) errors headErrors⟩

  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.bitNot head header, .bitNot (head := head) errors headErrors⟩

include definitions registered extension transport bindings meaning faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem preservesAt (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    PreservesAt (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply preservesAt_for (functions := functions) (tree := tree) (diagnosticPolicy := .unconditional)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.ProtectedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedImperativeForReflection
/-! Completed native statements and header prefixes reconstruct independent
source traces under the same installed entry. No body execution is stored in the
static grammar, and no unguarded expression contract is synthesized. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (Scope ValuesContext FlowRep restored restore_rep)
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized allocate_absent allocate_initialized sequence_rename valid_extend)
open GenericImperativeFor (Tree Position)
open ProtectedWhile.Body (Preserves Reflects)
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

private theorem sequence_stopped_reflects (_unique : NodeOccurrencesUnique source) {context : SourceSemantics.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ProtectedLoopStatements.Control.HeadReflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    Reflects (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨wholeSize, original⟩ := evaluation_has_size evaluated
  rw [LoopRenaming.sequence] at evaluated original
  obtain ⟨headSize, middleStore, headValue, headSmaller, headSized⟩ := original.bind_computation
  have headEval := headSized.sound
  obtain ⟨outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    first valid environments heaps locals agrees actualTyped reference read unmapped installed headEval
  cases represented with
  | fallthrough next =>
    cases headTrace with | control headTrace => cases stops headTrace
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_returned _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace (.returned _),
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_failure _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace (.fault _),
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

  | breaking next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_transfer _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace (.breaking _),
      .breaking next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | continuing next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_transfer _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, TypedLexicalWhile.terminal_outcome program evidence found notTail headTrace (.continuing _),
      .continuing next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩


include definitions registered extension transport bindings meaning reflection faithful observations in
theorem header_reflects_reachable (functionTypes : FunctionRuntimeViews functions) (_unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : ReflectingHeaderFor (diagnosticPolicy := .reachable) (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    ProtectedLoopStatements.Control.HeadReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨header, errors⟩ := headers
  have result := ProtectedForHeader.Tree.reflects_reachable functions definitions registered extension program evidence transport bindings meaning reflection faithful observations functionTypes header errors
    valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  cases result with
  | continues tail trace maps worlds frame metadata remaining =>
    obtain ⟨outcome, after, finalMap, finalWorld, loop, represented, progress⟩ :=
      tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.installed remaining
    refine ⟨Dynamic.restoreControl environment outcome, after, finalMap, finalWorld, ?_, restored environment outcome,
      restore_rep represented environment, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
      frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2.1⟩
    cases loop with
    | control loop => exact .control (.forLoop (lookupStatement?_sound found) form trace loop)
    | fault loop => exact .fault (.forIteration (lookupStatement?_sound found) form trace loop)
  | fault trace same matched heaps maps worlds frame metadata =>
    subst value
    exact ⟨_, _, _, _, .fault (.forInitializer (lookupStatement?_sound found) form trace),
      (by intro next impossible; cases impossible), .fault matched, heaps, maps, worlds, frame, metadata⟩

include definitions registered extension transport bindings meaning reflection faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem header_reflects (functionTypes : FunctionRuntimeViews functions) (_unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : ReflectingHeader (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    ProtectedLoopStatements.Control.HeadReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type code := by
  apply header_reflects_reachable (functions := functions) (headers := by rcases headers with ⟨header, errors⟩; exact ⟨header, errors.reachable⟩)
  all_goals assumption

include extension meaning reflection transport bindings definitions registered faithful observations in
theorem loop_reflects_reachable (_unique : NodeOccurrencesUnique source) (functionTypes : FunctionRuntimeViews functions)
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Reflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ProtectedFor.Body.LoopReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  have result := ProtectedFor.Body.loop_reflects functions program evidence transport (reflection _ valid)
    conditionFound conditionTree typed correct bodyCannotFault
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        mapping world before store finalStore value guarded continued execution
      exact ProtectedForHeader.post_reflects_reachable functions definitions registered extension program evidence transport bindings meaning reflection faithful observations functionTypes postTree postErrors
        actualValid actualAgrees actualReference guarded continued execution)
  exact result valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

include extension meaning reflection transport bindings definitions registered faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem loop_reflects (_unique : NodeOccurrencesUnique source) (functionTypes : FunctionRuntimeViews functions)
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
    (correct : Reflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ProtectedFor.Body.LoopReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  apply loop_reflects_reachable (functions := functions) (postErrors := postErrors.reachable)
  all_goals assumption

include definitions registered extension transport bindings meaning reflection faithful observations in
theorem reflectsAt_for (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    ReflectsAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      ProtectedLexicalStatements.Tree.reflects functions definitions registered program evidence transport bindings reflection body contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact ⟨finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append
    have continuation := (ContinuationAgreement.letE allocationEval).unwrap evaluated
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (bindings.prepend (transport.extend installed ⟨_, rfl⟩ ⟨_, rfl⟩ preservation
          (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append))) continuation
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace,
      represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    rw [sequence_rename] at evaluated
    have input : ∃ input middle, Evaluates actual store (lowered.expression.rename ξ) input middle := by
      cases evaluated with
      | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, initial⟩
    obtain ⟨input, middleStore, initialEval⟩ := input
    obtain ⟨sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
      reflection _ contextValid initial initialFound
        environments heaps locals agrees actualTyped installed initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LanguageResult.bind_failure _ initialEval)
        exact ⟨context, _, middle, middleMap, middleWorld, TypedScopedStatements.head_fault mode rest (.letInitializer (lookupStatement?_sound found) form mono failed),
          .fault matched, middleHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append
        have tailEval := (ContinuationAgreement.letE allocationEval).unwrap ((ContinuationAgreement.bind initialEval).unwrap evaluated)
        obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              (bindings.prepend (transport.extend
                (transport.extend installed maps worlds preservation metadata) ⟨_, rfl⟩ ⟨_, rfl⟩ allocationFrame
                (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append))) tailEval
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letInitialized (lookupStatement?_sound found) form initialTrace mono extended .append) trace,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact ⟨context, _, after, finalMap, finalWorld, TypedScopedStatements.head_fault mode rest (.expression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        reflection _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | @value _ coreValue payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
            ih contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata)
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact ⟨resultContext, outcome, after, finalMap, finalWorld,
            TypedScopedStatements.prepend (lookupStatement?_sound found) (TypedScopedStatements.not_tail form guard) (.expression (lookupStatement?_sound found) form childTrace) tail,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical⟩

  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact ProtectedLoopStatements.Control.sequence_reflects transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.block_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact ProtectedLoopStatements.Control.sequence_reflects transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.conditional_reflects transport reflection (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerErrors innerIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact sequence_stopped_reflects unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.block_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form innerIH) (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact sequence_stopped_reflects unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.conditional_reflects transport reflection (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form conditionFound conditionType conditionTree thenIH elseIH) (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

  | @breaking context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    have nativeEval : Evaluates actual store ((LocalLoop.breaking type).rename ξ) (LocalLoop.breakingValue type) store := by
      simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.breakStmt (lookupStatement?_sound found) form) (.breaking environment),
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    have nativeEval : Evaluates actual store ((LocalLoop.continuing type).rename ξ) (LocalLoop.continuingValue type) store := by
      simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.continueStmt (lookupStatement?_sound found) form) (.continuing environment),
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact ProtectedLoopStatements.Control.sequence_reflects transport (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals)  found (by intro expression; simp [form])
      (ProtectedLoopStatements.Control.of_retained_reflects functions program evidence (ProtectedWhile.Body.while_reflects functions program evidence transport
        (reflection _ contextValid) found form conditionFound conditionTree nativeTyped loopIH
          (fun executed => loopTree.control_not_fault unique executed))) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    rcases ProtectedAssignmentHeads.Head.reflects_reachable functions extension program evidence transport
      (meaning _ contextValid) (reflection _ contextValid) faithful observations
      head environments heaps locals agrees actualTyped installed functionTypes (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors) evaluated with
      ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, preservation, metadata, observed⟩ |
      ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, preservation, metadata, count, typed, observed, continuation⟩
    · exact ⟨context, .fault reason, after, finalMap, finalWorld,
        head_fault mode rest (.assignValue (lookupStatement?_sound found) form trace), .fault matched,
        finalHeaps, maps, worlds, preservation, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih contextValid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference frameRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 observed
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
      exact ⟨resultContext, outcome, after, finalMap, finalWorld,
        prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignValue (lookupStatement?_sound found) form trace) tail,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, lexical⟩

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact ProtectedBitNotStatements.assignment_reflects functions program evidence transport
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped installed evaluated
    exact ProtectedLoopStatements.Control.sequence_reflects transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (header_reflects_reachable functions definitions registered extension program evidence transport bindings meaning reflection faithful observations functionTypes unique found form (by rcases initialIH with ⟨header, errors⟩; exact ⟨header, GenericForHeader.Tree.ErrorsFor.reachable errors⟩)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := loop_reflects_reachable functions definitions registered extension program evidence transport bindings meaning reflection faithful observations unique functionTypes
      conditionFound conditionTree nativeTyped postTree (GenericForHeader.Tree.ErrorsFor.reachable postErrors) loopIH (fun executed => loopTree.control_not_fault unique executed)
    exact ⟨.nil completed, GenericForHeader.Tree.ErrorsFor.nil (policy := diagnosticPolicy) (next := completed)⟩
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same header, .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.initialized mono extended ordinary found sourceType child allocation annotation same header, .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := child) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found child remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.discard found child header, .discard (found := found) (value := child) errors⟩
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.assign head header, .assign (head := head) errors headErrors⟩

  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.bitNot head header, .bitNot (head := head) errors headErrors⟩

include definitions registered extension transport bindings meaning reflection faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem reflectsAt (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    ReflectsAt (certificates := certificates) (entry := entry) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply reflectsAt_for (functions := functions) (tree := tree) (diagnosticPolicy := .unconditional)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.ProtectedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedImperativeCatalogPayloadContracts
/-! Payload-aware initializer results keep the actual emitted code. A result
family is assembled by the six existing header constructors; statement meaning
and all Ready witnesses retain the original contract. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogPayload
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)

abbrev HeaderReceiptFamily := Ty → (SourceSemantics.Context → Scope → Expr → Prop) →
  SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop

section HeaderReceipts
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

abbrev LegacyHeaderReceipt (policy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) : HeaderReceiptFamily :=
  fun type continuation context scope items code =>
    ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
      type continuation context scope items code, GenericForHeader.Tree.ErrorsFor policy registry faults tree

abbrev StructuralHeaderReceipt
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative definitions)
    (UP : GenericForHeader.Structural.UnaryPayload) : HeaderReceiptFamily :=
  fun type continuation context scope items code =>
    GenericForHeader.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation) AP UP context scope items code

/-- The result builder supplies only the six static header constructor rules. -/
def HeaderReceiptAlgebra (R : HeaderReceiptFamily)
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative definitions)
    (UP : GenericForHeader.Structural.UnaryPayload) : Prop :=
  ∀ (type : Ty) (continuation : SourceSemantics.Context → Scope → Expr → Prop),
    GenericForHeader.Structural.BranchAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation) AP UP
      (fun context scope items code => R type continuation context scope items code)

theorem legacy_header_algebra (policy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) :
  HeaderReceiptAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) policy registry faults)
    (fun head => head.ErrorsFor policy registry faults) (fun head => head.Errors faults) := by
  intro type continuation
  constructor
  · intro context scope code next
    exact ⟨.nil next, GenericForHeader.Tree.ErrorsFor.nil (policy := policy) (next := next)⟩
  · intro context next scope binder rest body payload mono extended ordinary projected allocation annotation same child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same tree,
      .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected)
        (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  · intro context next scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.initialized mono extended ordinary found sourceType initial allocation annotation same tree,
      .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found)
        (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  · intro context scope expression expressionNode rest lowered body found value child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.discard found value tree, .discard (found := found) (value := value) errors⟩
  · intro context scope assignment operator rhs rest body head receipt child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.assign head tree, .assign (head := head) errors receipt⟩
  · intro context scope assignment rest body head receipt child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.bitNot head tree, .bitNot (head := head) errors receipt⟩


theorem structural_header_algebra
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative definitions)
    (UP : GenericForHeader.Structural.UnaryPayload) :
  HeaderReceiptAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (StructuralHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) AP UP) AP UP := by
  intro type continuation
  constructor
  · intro context scope code next M algebra
    exact algebra.nil next
  · intro context next scope binder rest body payload mono extended ordinary projected allocation annotation same child M algebra
    exact algebra.uninitialized mono extended ordinary projected allocation annotation same (child M algebra)
  · intro context next scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same child M algebra
    exact algebra.initialized mono extended ordinary found sourceType initial allocation annotation same (child M algebra)
  · intro context scope expression expressionNode rest lowered body found value child M algebra
    exact algebra.discard found value (child M algebra)
  · intro context scope assignment operator rhs rest body head receipt child M algebra
    exact algebra.assign head receipt (child M algebra)
  · intro context scope assignment rest body head receipt child M algebra
    exact algebra.bitNot head receipt (child M algebra)

end HeaderReceipts

universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} (validity : SourceSemantics.Context → Prop) (budget : Nat)


abbrev PreservingHeaderWithReceipt (R : HeaderReceiptFamily) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  initializerFacts context items condition post statements expected →
  R type (fun context scope code => loopFacts context condition post statements expected ∧ AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol readiness conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code

abbrev ReflectingHeaderWithReceipt (R : HeaderReceiptFamily) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  initializerFacts context items condition post statements expected →
  R type (fun context scope code => loopFacts context condition post statements expected ∧ AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol readiness conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code

abbrev PreservesAtWithReceipt (R : HeaderReceiptFamily) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => AtMost budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate facts (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => PreservingHeaderWithReceipt protocol readiness conditionGate loopFacts initializerFacts (validity := validity) functions program evidence budget R
      (source := source) (frame := frame) (globals := globals)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtWithReceipt (R : HeaderReceiptFamily) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate facts (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => ReflectingHeaderWithReceipt protocol readiness conditionGate loopFacts initializerFacts (validity := validity) functions program evidence budget R
      (source := source) (frame := frame) (globals := globals)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogPayload

namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogPayload
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- A completed initializer keeps the original condition, body, and ordered
post-header compiler receipts. Its body premise is the strict recursive goal;
the pending loop Source facts are supplied at its actual normalized context. -/
inductive LoopRecipeWithPayload (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner)
    (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
    (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative))
    (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop) :
    SourceSemantics.Context → Scope → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | mk {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
        context scope (.statements false statements) expected type bodyCode)
      (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
      (postErrors : HP postTree)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
      (child : goal context scope (.statements false statements) expected type bodyCode) :
      LoopRecipeWithPayload HP goal context scope condition post statements expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason)
/-- Forget only the parameterized post-header facet in the legacy instance. -/
theorem LoopRecipeWithPayload.to_legacy (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop}
    {context scope condition post statements expected type code}
    (recipe : LoopRecipeWithPayload (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (ambient := ambient)
      (fun postTree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree)
      goal context scope condition post statements expected type code) :
    ProtectedStateImperativeCatalogReady.LoopRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) diagnosticPolicy goal context scope condition post statements expected type code := by
  cases recipe with
  | mk conditionFound conditionType conditionTree loopBody postTree postErrors nativeTyped child =>
    exact .mk conditionFound conditionType conditionTree loopBody postTree postErrors nativeTyped child

universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (validity : SourceSemantics.Context → Prop) (budget : Nat)
  (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop)

/-- The loop callback keeps its original actual-state preservation contract. -/
def PreservingLoopsWithPayload
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
      (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative)) : Prop :=
  ∀ {context scope condition post statements expected type code},
    LoopRecipeWithPayload (administrative := administrative) (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (ambient := ambient)
      HP goal context scope condition post statements expected type code →
    loopFacts context condition post statements expected →
    RecursiveNamedHeaderContracts.AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor
      protocol readiness conditionGate (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) condition post statements expected type code)

/-- The loop callback keeps its original actual-state reflection contract. -/
def ReflectingLoopsWithPayload
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
      (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative)) : Prop :=
  ∀ {context scope condition post statements expected type code},
    LoopRecipeWithPayload (administrative := administrative) (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (ambient := ambient)
      HP goal context scope condition post statements expected type code →
    loopFacts context condition post statements expected →
    RecursiveNamedHeaderContracts.AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor
      protocol readiness conditionGate (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) condition post statements expected type code)

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogPayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderCoupledReadyBounds
/-! Prepared Header endpoints derive the structural eliminator internally from
the actual joint receipt and its same Plan tokens. Genuine unary table rows
provide the unchanged unary diagnostics; assignment callbacks consume the
actual selected preparation payload at the real current state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Fallthrough)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

variable {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source invalidOperand}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}

include definitions registered producer acquire stateTransport stateBindings sites transfers in
theorem preserves_fault_coupled_bounded_for
    (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesWithPayloadAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget
        (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head))
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : GenericForHeader.Coupled factory invalidProjection missingDefault tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory (fun site root => table.reasonAt site root .bitNot) plan)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact Tree.preserves_fault_reachable_bounded_for_with_eliminator
    (values := values) (source := source) (certificates := certificates)
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
    (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts) (sites := sites) (transfers := transfers)
    (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary true source (fun site root => table.reasonAt site root .bitNot) head)
    (fun _ receipt => receipt.errors unaryTyped issued unaryIncluded)
    validity snapshots extend budget assignments assignmentFaults boundedMeaning
    (GenericForHeader.Structural.of_coupled coupled tokens)
    valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered producer acquire stateTransport stateBindings sites transfers in
theorem reflects_coupled_bounded_for
    (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentReflectsWithPayloadAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget
        (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head))
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionReflectsAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size))
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : GenericForHeader.Coupled factory invalidProjection missingDefault tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory (fun site root => table.reasonAt site root .bitNot) plan)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor protocol readiness condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  exact Tree.reflects_reachable_bounded_for_with_eliminator
    (values := values) (source := source) (certificates := certificates)
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
    (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts) (sites := sites) (transfers := transfers)
    (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary true source (fun site root => table.reasonAt site root .bitNot) head)
    (fun _ receipt => receipt.errors unaryTyped issued unaryIncluded)
    validity snapshots extend budget assignments boundedReflection
    (GenericForHeader.Structural.of_coupled coupled tokens)
    valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

end WithReady
end Stateful
end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
end
