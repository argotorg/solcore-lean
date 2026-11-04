import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.NamedCallExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForControlShape
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped
import Solcore.SourceSemantics.CoreLowering.CallableIndexedBodyFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionBindings
import Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories
import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexical
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalGate
import Solcore.SourceSemantics.CoreLowering.ProtectedStateFunctionFinishReady
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchFallthrough
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchControlShape
import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBodyMeaning
import Solcore.SourceSemantics.CoreLowering.NamedLexicalFunctionFaultPostContracts

/-!
# Recursive named rows: catalog entries

Entries, profiles and invocation bounds of the catalog, the certificates of call selection, catalog initialization, cached rows and the function finish.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfiles
/-! Static expression heads can refer to the finite header inventory, including
self and mutual targets. The same existing imperative grammar supplies body
profiles. These records contain neither body execution nor runtime meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
abbrev Scope := SourceCoreLocalCell.Scope
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

inductive Head (bodies : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (children : GenericExpressionMeaning.Certificate) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | named {id callee arguments body node calleeNode name codes expression}
      (member : body ∈ bodies)
      (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node body.output)
      (sourceType : node.type = body.function.resultType)
      (form : node.form = .call callee arguments (.declaration body.instantiation))
      (calleeFound : source.lookupExpression? callee = some calleeNode)
      (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
      (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
      (valid : SourceSemantics.DeclarationInstantiation.Valid context body.instantiation)
      (predicates : body.instantiation.predicates = []) (evidence : body.function.evidence = [])
      (arity : body.function.parameters.length = arguments.length)
      (emission : NamedCalls.Arguments.Emission compilation source scope id callee arguments
        body.instantiation body.named.signature codes ⟨body.output, expression⟩)
      (selectedSlot : emission.index = body.slot)
      (sequence : DataExpressionSequence.Tree source children scope arguments
        (body.bindings.map (fun binding => binding.1.scheme.body)) codes)
      (nativeTypes : codes.map (·.type) = body.bindings.map Prod.snd) :
      Head bodies compilation source context children scope id ⟨body.output, expression⟩

abbrev Expressions (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  CompatibleExpressionCalls.Tree (Head headers compilation source context) fuel values source context solved reasonAt

/-- The actual body pass and its independent static tree are separate from the
header inventory. Call children therefore refer to headers, rather than to
recursive body-profile records. -/
structure Profile (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where private mk ::
  initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
    header.onError values header.function.source expressionSyntax
    (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output flow
  errors : GenericImperativeFor.Tree.Errors registry faults tree

/-- Static profiles select operand laws without storing runtime body meaning. -/
structure ProfileFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where private mk ::
  initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
    header.onError values header.function.source expressionSyntax
    (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output flow
  errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree

/-- Keep the original static record as the unconditional interface. -/
def Profile.to_for
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (certificate : Profile headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    ProfileFor .unconditional headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  ⟨certificate.initialValid, certificate.accepted, certificate.projection, certificate.flow, certificate.generated, certificate.emitted, certificate.tree, certificate.errors⟩

/-- Restore only the original unconditional record, field by field. -/
def ProfileFor.to_strict
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (certificate : ProfileFor .unconditional headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    Profile headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  ⟨certificate.initialValid, certificate.accepted, certificate.projection, certificate.flow, certificate.generated, certificate.emitted, certificate.tree, certificate.errors⟩

def ProfileFor.of_extracted {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults := by
  have emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [generated] at accepted
    exact Except.ok.inj accepted.symm
  exact ⟨initialValid, accepted, projection, flow, generated, emitted, tree, errors⟩

/-- Unconditional extraction retains its explicit ordinary source condition. -/
def Profile.of_extracted
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    Profile headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  (ProfileFor.of_extracted initialValid accepted projection generated tree errors).to_strict

/-- Runtime correspondence is deliberately absent from this family. -/
def Profiles (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ header, header ∈ headers → Nonempty
    (Profile headers header compilation expressionFuel (expressionSyntax header) (administrative header) registry faults)

/-- Every header uses the same diagnostic policy; execution remains absent. -/
def ProfilesFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ header, header ∈ headers → Nonempty
    (ProfileFor diagnosticPolicy headers header compilation expressionFuel (expressionSyntax header) (administrative header) registry faults)

theorem Profiles.to_for (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profiles : Profiles headers compilation expressionFuel expressionSyntax administrative registry faults) :
    ProfilesFor .unconditional headers compilation expressionFuel expressionSyntax administrative registry faults := by
  intro header member
  obtain ⟨certificate⟩ := profiles header member
  exact ⟨certificate.to_for⟩


theorem ProfilesFor.to_strict (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profiles : ProfilesFor .unconditional headers compilation expressionFuel expressionSyntax administrative registry faults) :
    Profiles headers compilation expressionFuel expressionSyntax administrative registry faults := by
  intro header member
  obtain ⟨certificate⟩ := profiles header member
  exact ⟨certificate.to_strict⟩

/-- Existing static heads can forget their builtin-only body certificate.
The resulting call receipt refers only to the finite header inventory. -/
theorem Head.of_existing
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
    {children : GenericExpressionMeaning.Certificate} {scope : Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (head : NamedCallExpressions.Head bodies compilation source context children scope id code) :
    Head (bodies.map Header.of_body) compilation source context children scope id code := by
  cases head with
  | named member metadata sourceType form calleeFound calleeForm calleeRequirements calleeCoercions
      valid predicates evidence arity emission selectedSlot sequence nativeTypes =>
    exact .named (List.mem_map.mpr ⟨_, member, rfl⟩) metadata sourceType form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidence arity emission selectedSlot sequence nativeTypes

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries
/-! Shared physical global references connect each actual captured environment
to the complete finite catalog. Named installation and the real marked
parameter capturePrefix retain that catalog; restoration uses actual administrative
preservation. Neither typing nor heap correspondence creates this authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

abbrev Locations := Header prepared values ambient.definitions program → Location

/-- Every row retains its real captured code and references. Coherence is an
explicit observation of all shared global locations in its canonical capture
layout, independent of the caller's lexical environment. -/
structure Capture (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix : Nat) (frameLocation : Location)
    (header : Header prepared values ambient.definitions program)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  administrative : Core.Context
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world administrative [] [] canonical ambient.definitions
  locals : Dynamic.EnvironmentAgrees heap header.function.context.locals []
  layout : EnvironmentsAgree embedding canonical captured
  typed : RuntimeEnvironmentHasTypes world captured capturedContext ambient.definitions
  reference : canonical[header.globals]? = some (.cellRef prepared.layout.frame.type frameLocation)
  capturedReference : captured[embedding base.globals.length]? = some (.cellRef prepared.layout.frame.type frameLocation)
  coherent : ∀ target, target ∈ headers → canonical[capturePrefix + target.slot]? = some
    (.cellRef (OptionalCell.cellType target.named.signature.functionType) (locations target))
  unmapped : locations header ∉ mapping
  distinct : locations header ≠ frameLocation
  read : store.read? (locations header) = some (.inRight .unit
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename embedding.lift) captured))

/-- Current frame history and all exact closures share one physical frame cell.
The frame snapshots are distinct protected cells. -/
structure Authority (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix : Nat) (mapping : LocationMap) (world : StoreTyping)
    (heap : Dynamic.Heap) (store : Store) where
  frameLocation : Location
  unmapped : frameLocation ∉ mapping
  typed : world[frameLocation]? = some prepared.layout.frame.type
  current : NativeFrame
  ghost : GhostFrame
  frame : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current ghost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records
  distinct : ∀ record, record ∈ records → record.location ≠ frameLocation
  captures : ∀ header, header ∈ headers → Nonempty (Capture headers locations capturePrefix frameLocation header mapping world heap store)

structure Entry (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix callerPrefix : Nat) (scope : Scope)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (canonical : Environment) where
  authority : Authority headers locations capturePrefix mapping world heap store
  globals : ∀ header, header ∈ headers → canonical[scope.length + callerPrefix + header.slot]? = some
    (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header))

variable {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix callerPrefix : Nat} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store futureStore : Store} {location : Location}

/-- Actual administrative preservation transports every retained closure.
Its captured values and code are unchanged; only typing and source metadata
are weakened along the certified extensions. -/
def Capture.extend {header : Header prepared values ambient.definitions program}
    (capture : Capture headers locations capturePrefix location header mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Capture headers locations capturePrefix location header futureMap futureWorld after futureStore := by
  have retained :=  frame (locations header) capture.unmapped (List.getElem?_eq_some_iff.mp capture.read).1
  exact { capture with
    environments := capture.environments.extend maps worlds
    locals := capture.locals.mono metadata
    typed := capture.typed.weaken worlds
    unmapped := retained.1
    read := retained.2.trans capture.read }

def Authority.extend (authority : Authority headers locations capturePrefix mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Authority headers locations capturePrefix futureMap futureWorld after futureStore := by
  have retained :=  frame authority.frameLocation authority.unmapped (List.getElem?_eq_some_iff.mp authority.frame.read).1
  refine { authority with
    unmapped := retained.1
    typed := worlds.lookup authority.typed
    frame := ⟨retained.2.trans authority.frame.read, authority.frame.history⟩
    snapshots := authority.snapshots.transport frame
    captures := ?_ }
  intro header member
  obtain ⟨capture⟩ := authority.captures header member
  exact ⟨capture.extend maps worlds frame metadata⟩

def Entry.extend {scope : Scope} {canonical : Environment}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Entry headers locations capturePrefix callerPrefix scope futureMap futureWorld after futureStore canonical :=
  ⟨entry.authority.extend maps worlds frame metadata, entry.globals⟩

/-- Installing a named frame changes only the shared frame cell. Actual global
closure cells and protected snapshots are distinct, so their reads survive. -/
def Authority.install (authority : Authority headers locations capturePrefix mapping world heap store)
    {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    Authority headers locations capturePrefix mapping world heap
      (store.set authority.frameLocation (encode prepared.layout.frame next)) := by
  have written : store.write? authority.frameLocation (encode prepared.layout.frame next) =
      some (store.set authority.frameLocation (encode prepared.layout.frame next)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  refine { authority with
    current := next
    ghost := nextGhost
    frame := ⟨Store.write?_reads_written written, history⟩
    snapshots := CallableIndexedBodyFrames.install_snapshots authority.frame authority.snapshots authority.distinct
    captures := ?_ }
  intro header member
  obtain ⟨capture⟩ := authority.captures header member
  exact ⟨{ capture with read := (Store.write?_preserves_other written capture.distinct).trans capture.read }⟩

/-- The actual hook receipt fixes the named history and emitted wrapper. The
callee's full catalog comes from its observed capture coherence, rather than
from its source or native type. -/
theorem named_install (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) header.parameterCode ∧
      ∃ capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store,
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap
          (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) ∧
        Nonempty (Entry headers locations capturePrefix capturePrefix [] mapping world heap
          (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) capture.canonical) := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared header.hook
  obtain ⟨capture⟩ := authority.captures header member
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  exact ⟨origin, index, metadata, owned, history, emitted, capture, installedHeaps,
    ⟨authority.install (.stable history), by simpa using capture.coherent⟩⟩

/-- Restoration consumes the actual child frame relation. It recovers the
original caller authority for every catalog row and snapshot, with final source
heap effects retained. No child body execution is assumed here. -/
theorem restore {scope : Scope} {canonical : Environment}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    {next : NativeFrame} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping
      (store.set entry.authority.frameLocation (encode prepared.layout.frame next)) futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after
      (futureStore.set entry.authority.frameLocation (encode prepared.layout.frame entry.authority.current)) ∧
    Nonempty (Authority headers locations capturePrefix futureMap futureWorld after
      (futureStore.set entry.authority.frameLocation (encode prepared.layout.frame entry.authority.current))) := by
  obtain ⟨finalHeaps, restored, _⟩ := CallableIndexedBodyFrames.restore registered entry.authority.unmapped entry.authority.typed
    entry.authority.frame heaps worlds frame
  exact ⟨finalHeaps, ⟨entry.authority.extend maps worlds restored metadata⟩⟩

/-- Lookup of an actual installed target returns precisely its retained
closure, without executing any target body. -/
theorem Entry.read_target {scope : Scope} {canonical actual : Environment} {ξ : Renaming}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers) (reason : Word) :
    ∃ capture : Capture headers locations capturePrefix entry.authority.frameLocation header mapping world heap store,
      Evaluates actual store (OptionalCell.read header.named.signature.functionType
        (.var (ξ (scope.length + callerPrefix + header.slot))) reason)
        (.inRight .word (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)) store := by
  obtain ⟨capture⟩ := entry.authority.captures header member
  exact ⟨capture, OptionalCell.read_success reason (.var (agrees (entry.globals header member))) capture.read⟩

/-- Each captured global points to the same physical location as the caller's
catalog. This is obtained only from the stored coherence receipt. -/
theorem Capture.global_reference {header : Header prepared values ambient.definitions program}
    (capture : Capture headers locations capturePrefix location header mapping world heap store)
    {target : Header prepared values ambient.definitions program} (member : target ∈ headers) :
    capture.captured[capture.embedding (capturePrefix + target.slot)]? = some
      (.cellRef (OptionalCell.cellType target.named.signature.functionType) (locations target)) :=
  capture.layout (capture.coherent target member)

def protectedEntry (headers : Inventory prepared values ambient.definitions program)
    (locations : Header prepared values ambient.definitions program → Location) (capturePrefix callerPrefix : Nat) : ProtectedExpressionMeaning.Entry :=
  fun scope mapping world heap store canonical =>
    Nonempty (Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)

theorem entry_transport : ProtectedExpressionMeaning.Transport
    (protectedEntry headers locations capturePrefix callerPrefix) := by
  constructor
  intro scope mapping world heap store canonical futureMap futureWorld after futureStore entry maps worlds frame metadata
  obtain ⟨entry⟩ := entry
  exact ⟨entry.extend maps worlds frame metadata⟩

theorem entry_binds : ProtectedExpressionMeaning.Binds
    (protectedEntry headers locations capturePrefix callerPrefix) := by
  constructor
  · intro scope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨entry.authority, ?_⟩
    intro header member
    have index : ((id, type) :: scope).length + callerPrefix + header.slot =
        (scope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
    rw [index]
    exact entry.globals header member
  · intro scope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨entry.authority, ?_⟩
    intro header member
    have index : ((id, type) :: scope).length + callerPrefix + header.slot =
        (scope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
    have selected := entry.globals header member
    rw [index] at selected
    exact selected

/-- Temporary actual binders transport only variable positions. They do not
modify the retained catalog, captured values or physical locations. -/
theorem Entry.reindex {scope : Scope} {canonical actual : Environment} {ξ : Renaming}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (agrees : EnvironmentsAgree ξ canonical actual) :
    ∀ header, header ∈ headers → actual[ξ (scope.length + callerPrefix + header.slot)]? = some
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) := by
  intro header member
  exact agrees (entry.globals header member)

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {administrative : Core.Context} {scope : Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type ambient.definitions) :
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      (type :: administrative) scope environment (Environment.insertAt canonical scope.length value) ambient.definitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

/-- This receipt describes the completed parameter prefix and the next real
body environment. It contains a finite continuation agreement but no body
execution or body correspondence. -/
structure ParameterEntry (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix : Nat)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (header : Header prepared values ambient.definitions program)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (frameLocation : Location) (current : NativeFrame) (ghost : GhostFrame) where private mk ::
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before header.function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap header.context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext header.bindings actualContext) ambient.definitions
  catalog : Entry headers locations capturePrefix (capturePrefix + 1)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) mapping world heap store canonical
  reference : canonical[header.bindings.length + 1 + header.globals]? =
    some (.cellRef prepared.layout.frame.type frameLocation)
  state : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current ghost store
  catalog_frame : catalog.authority.frameLocation = frameLocation
  catalog_current : catalog.authority.current = current
  catalog_ghost : catalog.authority.ghost = ghost
  agreement : ContinuationAgreement actual initialStore (header.parameterCode.rename ξ)
    actualBody store (header.body.rename embedding)

/-- Parameter allocation depends on the captured layout and independent
source locals, so callers can retain their represented closure's exact payload
without replacing it with a separately read catalogue closure. -/
theorem parameters_of_layout (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program}
    {administrative : Core.Context} {canonical : Environment}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative [] [] canonical ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees heap header.function.context.locals [])
    (reference : canonical[header.globals]? = some (.cellRef prepared.layout.frame.type authority.frameLocation))
    (coherent : ∀ target, target ∈ headers → canonical[capturePrefix + target.slot]? = some
      (.cellRef (OptionalCell.cellType target.named.signature.functionType) (locations target)))
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    Nonempty (ParameterEntry headers locations capturePrefix functions registry header arguments heap store mapping world
      administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost) := by
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError header.acceptedPrefix
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues payloads :: canonical) := by
    intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, agreement⟩ :=
    CallableIndexedParameterTyped.prefix_typed tree header.definitions_eq header.registered represented environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using reference) authority.frame.read authority.unmapped
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
  let catalog : Entry headers locations capturePrefix (capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld finalHeap finalStore finalLogical := by
    refine ⟨authority.extend maps worlds preservation metadata, ?_⟩
    intro target targetMember
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : header.bindings.length + (capturePrefix + 1) + target.slot =
        added.length + (capturePrefix + target.slot + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using coherent target targetMember
  have finalReference : finalLogical[header.bindings.length + 1 + header.globals]? =
      some (.cellRef prepared.layout.frame.type authority.frameLocation) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + header.globals = added.length + (header.globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  have current := CallableIndexedBodyFrames.body_current authority.unmapped authority.frame preservation
  have mono := FunctionCallBody.mono_binders header.extended
  exact ⟨⟨environment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, by simpa using finalWithBundle, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 locals allocated,
    maps, worlds, preservation, metadata, lookups, finalTyped, catalog, finalReference, current, (by rfl), (by rfl), (by
      change (authority.extend maps worlds preservation metadata).ghost = authority.ghost
      rfl), agreement⟩⟩

/-- The actual marked prefix constructs all source binders and preserves every
shared global reference. Its real suffix and packed-argument slot fix the body
catalog indices; no final environment typing or catalog entry is assumed. -/
theorem parameters (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (_member : header ∈ headers)
    (capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    Nonempty (ParameterEntry headers locations capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost) := by
  exact parameters_of_layout authority capture.environments capture.locals capture.reference capture.coherent
    represented heaps agrees actualTyped

/-- The named hook and the real marked parameter prefix together produce a
body entry for the whole catalog. The saved caller frame and write-result Unit
are the actual administrative prefix slots. No body execution is required. -/
theorem named_parameters (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) header.parameterCode ∧
      ∃ capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store,
        Nonempty (ParameterEntry headers locations capturePrefix functions registry header arguments heap
          (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) mapping world
          capture.administrative
          (.unit :: prepared.layout.frame.type :: header.named.signature.parameterType :: capture.capturedContext)
          (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured)
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
          authority.frameLocation (.state index) (.named origin)) := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared header.hook
  obtain ⟨capture⟩ := authority.captures header member
  have written : store.write? authority.frameLocation (encode prepared.layout.frame (.state index)) =
      some (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  let installed := authority.install (.stable history)
  let nextCapture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap
      (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) :=
    { capture with read := (Store.write?_preserves_other written capture.distinct).trans capture.read }
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
      (DataPatternValues.packValues payloads :: capture.canonical)
      (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
      (encode prepared.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType ambient.definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped capture.typed))
  have entry := parameters installed member nextCapture represented installedHeaps layout actualTyped
  exact ⟨origin, index, metadata, owned, history, emitted, capture, entry⟩

/-- Restore also recovers the complete caller entry, rather than just its
current frame token. The caller's own lexical lookup positions stay unchanged. -/
theorem Entry.restored {scope : Scope} {canonical : Environment}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    {next : NativeFrame} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping
      (store.set entry.authority.frameLocation (encode prepared.layout.frame next)) futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after
      (futureStore.set entry.authority.frameLocation (encode prepared.layout.frame entry.authority.current)) ∧
    Nonempty (Entry headers locations capturePrefix callerPrefix scope futureMap futureWorld after
      (futureStore.set entry.authority.frameLocation (encode prepared.layout.frame entry.authority.current)) canonical) := by
  obtain ⟨finalHeaps, restored, _⟩ := CallableIndexedBodyFrames.restore registered entry.authority.unmapped entry.authority.typed
    entry.authority.frame heaps worlds frame
  exact ⟨finalHeaps, ⟨entry.extend maps worlds restored metadata⟩⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
/-! Real parameter prefixes retain the whole installed catalog and the original
body subderivation. Body contracts are pointwise runtime interfaces; static
headers and profiles remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Below := RecursiveNamedBoundedContracts.Below
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix callerPrefix : Nat} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store futureStore : Store}

structure BodyState (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix : Nat)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (header : Header prepared values ambient.definitions program)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (frameLocation : Location) (current : NativeFrame) (ghost : GhostFrame) where private mk ::
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before header.function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap header.context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext header.bindings actualContext) ambient.definitions
  catalog : Entry headers locations capturePrefix (capturePrefix + 1)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) mapping world heap store canonical
  reference : canonical[header.bindings.length + 1 + header.globals]? =
    some (.cellRef prepared.layout.frame.type frameLocation)
  state : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current ghost store
  catalog_frame : catalog.authority.frameLocation = frameLocation
  catalog_current : catalog.authority.current = current
  catalog_ghost : catalog.authority.ghost = ghost


/-- Assemble a body state only from its complete static and reached runtime receipts. -/
def BodyState.of_receipts {headers : Inventory prepared values ambient.definitions program}
    {locations : Locations} {capturePrefix : Nat}
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {header : Header prepared values ambient.definitions program}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (environment : Dynamic.Environment)
    (heap : Dynamic.Heap)
    (canonical : Environment)
    (actualBody : Environment)
    (store : Store)
    (mapping : LocationMap)
    (world : StoreTyping)
    (embedding : Renaming)
    (allocation : Dynamic.BindersAllocate [] before header.function.parameters arguments environment heap)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap header.context.locals environment)
    (maps : LocationMap.Extends initialMap mapping)
    (worlds : WorldExtends initialWorld world)
    (frame : AdministrativePreserved initialMap initialStore mapping store)
    (metadata : Dynamic.HeapMetadataExtend before heap)
    (lookups : EnvironmentsAgree embedding canonical actualBody)
    (actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext header.bindings actualContext) ambient.definitions)
    (catalog : Entry headers locations capturePrefix (capturePrefix + 1)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) mapping world heap store canonical)
    (reference : canonical[header.bindings.length + 1 + header.globals]? =
    some (.cellRef prepared.layout.frame.type frameLocation))
    (state : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current ghost store)
    (catalog_frame : catalog.authority.frameLocation = frameLocation)
    (catalog_current : catalog.authority.current = current)
    (catalog_ghost : catalog.authority.ghost = ghost) :
    BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost :=
  ⟨environment, heap, canonical, actualBody, store, mapping, world, embedding, allocation, environments, heaps, locals, maps, worlds, frame, metadata, lookups, actualTyped, catalog, reference, state, catalog_frame, catalog_current, catalog_ghost⟩


def BodyState.of_entry
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {header : Header prepared values ambient.definitions program} {arguments : List Dynamic.Value}
    {before : Dynamic.Heap} {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
    {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : ParameterEntry headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost :=
  { environment := entry.environment,
    heap := entry.heap,
    canonical := entry.canonical,
    actualBody := entry.actualBody,
    store := entry.store,
    mapping := entry.mapping,
    world := entry.world,
    embedding := entry.embedding,
    allocation := entry.allocation,
    environments := entry.environments,
    heaps := entry.heaps,
    locals := entry.locals,
    maps := entry.maps,
    worlds := entry.worlds,
    frame := entry.frame,
    metadata := entry.metadata,
    lookups := entry.lookups,
    actualTyped := entry.actualTyped,
    catalog := entry.catalog,
    reference := entry.reference,
    state := entry.state,
    catalog_frame := entry.catalog_frame,
    catalog_current := entry.catalog_current,
    catalog_ghost := entry.catalog_ghost }

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {administrative : Core.Context} {scope : Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type ambient.definitions) :
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      (type :: administrative) scope environment (Environment.insertAt canonical scope.length value) ambient.definitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih


theorem parameters_sized (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (_member : header ∈ headers)
    (capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (header.parameterCode.rename ξ) result afterStore) :
    ∃ entry : BodyState headers locations capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost,
      ∃ child, EvaluationSize child entry.actualBody entry.store (header.body.rename entry.embedding) result afterStore ∧
        child ≤ size ∧ (header.bindings ≠ [] → child < size) := by
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError header.acceptedPrefix
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) capture.canonical
      (DataPatternValues.packValues payloads :: capture.canonical) := by
    intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding, child,
    allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, bodyCompletion, childLe, childStrict⟩ :=
    RecursiveNamedCallBounds.parameter_prefix tree header.definitions_eq header.registered represented capture.environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using capture.reference) authority.frame.read authority.unmapped completed
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
  let catalog : Entry headers locations capturePrefix (capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld finalHeap finalStore finalLogical := by
    refine ⟨authority.extend maps worlds preservation metadata, ?_⟩
    intro target targetMember
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : header.bindings.length + (capturePrefix + 1) + target.slot =
        added.length + (capturePrefix + target.slot + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using capture.coherent target targetMember
  have finalReference : finalLogical[header.bindings.length + 1 + header.globals]? =
      some (.cellRef prepared.layout.frame.type authority.frameLocation) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + header.globals = added.length + (header.globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using capture.reference
  have current := CallableIndexedBodyFrames.body_current authority.unmapped authority.frame preservation
  have mono := FunctionCallBody.mono_binders header.extended
  refine ⟨⟨environment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, by simpa using finalWithBundle, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 capture.locals allocated,
    maps, worlds, preservation, metadata, lookups, finalTyped, catalog, finalReference, current, (by rfl), (by rfl), (by
      change (authority.extend maps worlds preservation metadata).ghost = authority.ghost
      rfl)⟩, child, bodyCompletion, childLe, childStrict⟩


theorem named_parameters_sized (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) result finalStore) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) header.parameterCode ∧
      ∃ entry : BodyState headers locations capturePrefix functions registry header arguments heap
        (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) mapping world
        capture.administrative
        (.unit :: prepared.layout.frame.type :: header.named.signature.parameterType :: capture.capturedContext)
        (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured)
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
        authority.frameLocation (.state index) (.named origin),
      ∃ child bodyStore, EvaluationSize child entry.actualBody entry.store (header.body.rename entry.embedding) result bodyStore ∧
        child < size ∧ finalStore = bodyStore.set authority.frameLocation (encode prepared.layout.frame authority.current) := by
  obtain ⟨origin, index, owned, selected, emitted⟩ := CallableIndexedFormation.namedBody_receipt prepared header.hook
  obtain ⟨metadata, history⟩ : ∃ metadata, Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) := by
    cases found : prepared.graph.table.namedAt? origin with
    | none => simp [SourceCoreCallableIndexedDispatch.namedFrame, found] at selected
    | some position =>
      obtain ⟨metadata, history⟩ := named_history prepared.graph found
      exact ⟨metadata, selected ▸ history⟩
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift (base.globals.length + 1)]? =
      some (.cellRef prepared.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨actualOrigin, actualIndex, prefixSize, bodyStore, actualOwned, actualSelected, prefixCompleted, prefixSmaller, restored⟩ :=
    RecursiveNamedCallBounds.named_hook_body prepared header.hook reference authority.frame.read completed
  have sameOrigin : actualOrigin = origin := Option.some.inj (actualOwned.symm.trans owned)
  subst actualOrigin
  have sameIndex : actualIndex = index := by
    have same := actualSelected.symm.trans selected
    injection same
  subst actualIndex
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at prefixCompleted
  have written : store.write? authority.frameLocation (encode prepared.layout.frame (.state index)) =
      some (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  let installed := authority.install (.stable history)
  let nextCapture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap
      (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) :=
    { capture with read := (Store.write?_preserves_other written capture.distinct).trans capture.read }
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
      (DataPatternValues.packValues payloads :: capture.canonical)
      (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
      (encode prepared.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType ambient.definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped capture.typed))
  obtain ⟨entry, child, bodyCompleted, childLe, _⟩ :=
    parameters_sized installed member nextCapture represented installedHeaps layout actualTyped prefixCompleted
  exact ⟨origin, index, metadata, owned, history, emitted, entry, child, bodyStore, bodyCompleted,
    Nat.lt_of_le_of_lt childLe prefixSmaller, restored⟩



variable (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
  (header : Header prepared values ambient.definitions program) (faults : FunctionCalls.FaultRep)

/-- A static predicate at the original, fully retained body state. It does not
contain an execution law or recover a source history from native typing. -/
abbrev BodyCondition :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost},
    BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost → Prop

/-- Actual hook ownership and its carried history authorize precisely the
state reached by the named parameter prefix. Arbitrary body states are excluded. -/
def BodyAuthorization (condition : BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header) : Prop :=
  ∀ {origin index metadata arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation},
    prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin →
    Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) →
    header.code = withFrame (.var (base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) header.parameterCode →
    ∀ entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation (.state index) (.named origin), condition entry

/-- A pointwise body obligation at the real parameter entry. The independent
source context is the one retained by this header and its marked prefix. -/
def BodyPreservesAt (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome after},
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after

/-- Reflection consumes the original body subderivation. Its independent source
cost is an output and is never compared with the native input cost. -/
def BodyReflectsAt (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value finalStore},
    EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after

/-- A pointwise body obligation at the real parameter entry. The independent
source context is the one retained by this header and its marked prefix. -/
def BodyPreservesAtWith (condition : BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header) (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome after}, condition entry →
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after

/-- Reflection consumes the original body subderivation. Its independent source
cost is an output and is never compared with the native input cost. -/
def BodyReflectsAtWith (condition : BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header) (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value finalStore}, condition entry →
    EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after

namespace Stateful
universe u v

def BodyPreservesAtWith {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (condition : BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header) (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (initial : protocol.State ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    {outcome after}, condition entry →
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- Reflection consumes the original body subderivation. Its independent source
cost is an output and is never compared with the native input cost. -/
def BodyReflectsAtWith {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (condition : BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header) (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (initial : protocol.State ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    {value finalStore}, condition entry →
    EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩

end Stateful

variable {functions registry header faults}

theorem body_preserves_of_pointwise {size : Nat} {certificate : FunctionCode.BodyCertificate}
    (certified : certificate header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.body)
    {finalContext facts} (typed : StatementsHaveType header.function.source
      {returnType := header.function.resultType, loopDepth := 0} header.context header.function.body finalContext facts)
    (meaning : RecursiveNamedBoundedContracts.BodyPreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program header.function certificate faults
      (protectedEntry headers locations capturePrefix (capturePrefix + 1))) :
    BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry outcome after trace
  exact meaning certified typed entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped ⟨entry.catalog⟩ trace

theorem body_reflects_of_pointwise {size : Nat} {certificate : FunctionCode.BodyCertificate}
    (certified : certificate header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.body)
    {finalContext facts} (typed : StatementsHaveType header.function.source
      {returnType := header.function.resultType, loopDepth := 0} header.context header.function.body finalContext facts)
    (meaning : RecursiveNamedBoundedContracts.BodyReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program header.function certificate faults
      (protectedEntry headers locations capturePrefix (capturePrefix + 1))) :
    BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry value finalStore completed
  exact meaning certified typed entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped ⟨entry.catalog⟩ completed

private theorem body_of_trace_sized {size : Nat} {arguments : List Dynamic.Value}
    {environment : Dynamic.Environment} {before bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context environment bound outcome after) :
    RecursiveNamedCallBounds.BodyOutcome program (SourceExecutionSize.stepSize [size]) header.sourceBody
      header.function.evidence before arguments outcome after := by
  have extension : MonoBindersExtend header.sourceBody.source.owner header.sourceBody.context header.sourceBody.source.inputs header.types header.context := by
    simpa only [header.frame.source, header.frame.context, header.frame.parameters] using header.extended
  have allocation := header.frame.parameters ▸ allocated
  cases trace with
  | returned executed => exact .value (.returned header.frame.covers header.frame.roots extension allocation (header.frame.source ▸ executed) rfl)
  | unit same executed => exact .value (.unit header.frame.covers (header.frame.result ▸ same) header.frame.roots extension allocation
      (header.frame.source ▸ executed) ⟨_, rfl⟩)
  | fault failed => exact .fault (.statements header.frame.roots extension allocation (header.frame.source ▸ failed))
  | escaped executed escape => exact .fault (.controlEscape header.frame.roots extension allocation (header.frame.source ▸ executed) escape)

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (store : Store) (saved : Value) :
    Evaluates (saved :: actual) store
      ((SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)).weakenAt 0)
      (encode prepared.layout.frame (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

/-- Only the real strictly smaller source body child selects the body IH. -/
theorem invocation_preserves_bounded_with
    (condition : BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : BodyAuthorization (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header condition)
    (budget : Nat)
    (bodyMeaning : Below budget (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults condition))
    {scope : Scope} {canonical : Environment}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (member : header ∈ headers) {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world heap store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨child, environment, bound, allocated, bodyTrace, smaller⟩ :=
    RecursiveNamedCallBounds.body_trace header.frame header.extended arity trace
  obtain ⟨origin, index, metadata, owned, history, emitted, capture, entry⟩ := named_parameters caller.authority member represented heaps
  obtain ⟨entry⟩ := entry
  let state := BodyState.of_entry entry
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same state.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata⟩ :=
    bodyMeaning child (Nat.lt_of_lt_of_le smaller within) state (authorized owned history emitted state) bodyTrace
  have prefixEvaluation := entry.agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift (base.globals.length + 1)]? =
      some (.cellRef prepared.layout.frame.type caller.authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  have evaluation := CallableContextFrames.withFrame_evaluates (.var reference) caller.authority.frame.read
    (next_evaluates index (DataPatternValues.packValues payloads :: capture.captured) store (encode prepared.layout.frame caller.authority.current)) prefixEvaluation
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := state.maps.trans bodyMaps
  have worlds := state.worlds.trans bodyWorlds
  have frame := state.frame.trans bodyFrame
  have sourceMetadata := state.metadata.trans bodyMetadata
  obtain ⟨restoredHeaps, restoredFrame, _⟩ := CallableIndexedBodyFrames.restore header.registered caller.authority.unmapped caller.authority.typed
    caller.authority.frame finalHeaps worlds frame
  exact ⟨capture, value, _, finalMap, finalWorld, renamed.symm ▸ evaluation, result, restoredHeaps, maps, worlds,
    restoredFrame, sourceMetadata, ⟨caller.extend maps worlds restoredFrame sourceMetadata⟩⟩

theorem invocation_preserves_bounded (budget : Nat)
    (bodyMeaning : Below budget (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults))
    {scope : Scope} {canonical : Environment}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (member : header ∈ headers) {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world heap store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact invocation_preserves_bounded_with (fun _ => True) (by unfold BodyAuthorization; intros; trivial) budget
    (by
      intro child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning child smaller entry trace) caller member represented heaps trace within
/-- Original hook and parameter sizes choose the reflected body IH. -/
theorem invocation_reflects_bounded_with
    (condition : BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : BodyAuthorization (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header condition)
    (budget : Nat)
    (bodyMeaning : Below budget (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults condition))
    {scope : Scope} {canonical : Environment}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (member : header ∈ headers) {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world heap store)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨origin, index, metadata, owned, history, emitted, entry, child, bodyStore, bodyCompleted, smaller, restored⟩ :=
    named_parameters_sized caller.authority member represented heaps capture completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata⟩ :=
    bodyMeaning child (Nat.lt_of_lt_of_le smaller within) entry (authorized owned history emitted entry) bodyCompleted
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  obtain ⟨restoredHeaps, restoredFrame, _⟩ := CallableIndexedBodyFrames.restore header.registered caller.authority.unmapped caller.authority.typed
    caller.authority.frame finalHeaps worlds frame
  subst finalStore
  exact ⟨_, outcome, after, finalMap, finalWorld, body_of_trace_sized entry.allocation trace, result, restoredHeaps,
    maps, worlds, restoredFrame, sourceMetadata, ⟨caller.extend maps worlds restoredFrame sourceMetadata⟩⟩

theorem invocation_reflects_bounded (budget : Nat)
    (bodyMeaning : Below budget (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults))
    {scope : Scope} {canonical : Environment}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (member : header ∈ headers) {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world heap store)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact invocation_reflects_bounded_with (fun _ => True) (by unfold BodyAuthorization; intros; trivial) budget
    (by
      intro child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning child smaller entry trace) caller member represented heaps capture completed within

private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ =
      CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

/-- The accepted finish wrapper supplies another original strict child. -/
theorem body_flow_sized {flow : Expr} (emitted : header.body =
      CompatibleStatements.finish header.output flow header.fellThrough header.escaped)
    {size : Nat} {actual : Environment} {store finalStore : Store} {ξ : Renaming} {value : Value}
    (completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore) :
    ∃ child flowValue middle, child < size ∧ EvaluationSize child actual store (flow.rename ξ) flowValue middle := by
  rw [emitted, finish_rename] at completed
  exact RecursiveNamedCallBounds.finish_flow completed

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallSelectionCertificates
/-! Successful selection fixes the complete global signature and plan record.
The finite header inventory still needs coverage of those real slots. Exact
source instantiation equality additionally uses the retained domain order;
native types and specialization keys do not determine that ordered record.
These receipts contain only source metadata and compiler actions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallSelectionCertificates
open Core Frontend SourceInference CallableAncestryPairedLookup RecursiveNamedCatalog

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {definitions : DataEnvironment} {program : Program}
  {headers : Inventory prepared values definitions program} {compilation : SourceCoreFunctions.Context}

/-- Coverage refers to each actual ordered global slot and the entire selected
specialization. It does not reconstruct a source header from a native type. -/
structure Coverage (headers : Inventory prepared values definitions program)
    (compilation : SourceCoreFunctions.Context) : Prop where
  plan : compilation.plan = base.plan
  slots : ∀ index signature specialized,
    compilation.globals[index]? = some signature →
    SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized →
    ∃ header, header ∈ headers ∧ header.slot = index ∧
      header.named.signature = signature ∧ header.named.specialized = specialized
  ordered : ∀ header, header ∈ headers →
    header.instantiation.parameterSubstitution.map Prod.fst =
      (header.named.specialized.parameterSubstitution.map Prod.fst).reverse

/-- Only accepted declaration calls in the admitted source domain need a
header. Unrelated globals, including coercion methods, are not covered. -/
structure ReachedCoverage (headers : Inventory prepared values definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (admitted : ExpressionId → Prop) : Prop where
  plan : compilation.plan = base.plan
  slots : ∀ policy id node callee arguments instantiation index signature specialized,
    admitted id → source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) →
    SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature) →
    SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized →
    ∃ header, header ∈ headers ∧ header.slot = index ∧
      header.named.signature = signature ∧ header.named.specialized = specialized
  ordered : ∀ header, header ∈ headers →
    header.instantiation.parameterSubstitution.map Prod.fst =
      (header.named.specialized.parameterSubstitution.map Prod.fst).reverse

/-- Existing whole-inventory coverage restricts to the actual reached sites. -/
theorem Coverage.restrict {source : TypedSource} {admitted : ExpressionId → Prop}
    (coverage : Coverage headers compilation) : ReachedCoverage headers compilation source admitted := by
  refine ⟨coverage.plan, ?_, coverage.ordered⟩
  intro policy id node callee arguments instantiation index signature specialized _allowed _found _form selected exactRecord
  exact coverage.slots index signature specialized (NamedCalls.selected_signature_target selected).2 exactRecord

/-- The admitted occurrence uses the same domain order actually retained by
source inference. All remaining fields come from the accepted matcher. -/
def Ordered (plan : SourceCompilationPlan.Plan) (instantiation : DeclarationInstantiation) : Prop :=
  ∀ key specialized, SourceCompilationPlan.exactInstantiationKey plan instantiation = .ok key →
    SourceCompilationPlan.exactSpecialization plan key = .ok specialized →
    instantiation.parameterSubstitution.map Prod.fst =
      (specialized.parameterSubstitution.map Prod.fst).reverse

private theorem selected_record {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation} {index : Nat}
    {signature : SourceCoreCalls.Signature}
    (plan : compilation.plan = base.plan)
    (headerOrder : ∀ header, header ∈ headers →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse)
    (selects : ∀ specialized, SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized →
      ∃ header, header ∈ headers ∧ header.slot = index ∧ header.named.signature = signature ∧ header.named.specialized = specialized)
    (ordered : Ordered compilation.plan instantiation)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false =
      .ok (index, signature)) :
    ∃ header, header ∈ headers ∧ header.slot = index ∧ header.named.signature = signature ∧
      instantiation = header.instantiation ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok header.named.specialized := by
  obtain ⟨specialized, exactRecord, matched, _, _⟩ :=
    CallableNamedMetadata.metadata_of_selected_signature accepted
  have target := NamedCalls.selected_signature_target accepted
  obtain ⟨header, member, slot, signatureEq, specializationEq⟩ :=
    selects specialized exactRecord
  have headerTarget : SourceCompilationPlan.exactInstantiationKey compilation.plan header.instantiation =
      .ok signature.key := by rw [plan, ← signatureEq]; exact header.target
  have headerMatch := CallableNamedMetadata.matches_of_exact headerTarget exactRecord
  have occurrenceEq := matched.retained_canonical (ordered _ _ target.1 exactRecord)
  have headerEq := headerMatch.retained_canonical (by simpa [← specializationEq] using headerOrder header member)
  exact ⟨header, member, slot, signatureEq, occurrenceEq.trans headerEq.symm,
    specializationEq.symm ▸ exactRecord⟩

/-- Full metadata follows from the same accepted matcher at the reached site. -/
theorem selected_at {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {id callee : ExpressionId} {arguments : List ExpressionId} {admitted : ExpressionId → Prop}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation} {index : Nat}
    {signature : SourceCoreCalls.Signature}
    (coverage : ReachedCoverage headers compilation source admitted)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (ordered : Ordered compilation.plan instantiation)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false =
      .ok (index, signature)) :
    ∃ header, header ∈ headers ∧ header.slot = index ∧ header.named.signature = signature ∧
      instantiation = header.instantiation ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok header.named.specialized := by
  exact selected_record coverage.plan coverage.ordered
    (fun specialized exactRecord => coverage.slots policy id node callee arguments instantiation index signature specialized
      allowed found form accepted exactRecord) ordered accepted

/-- Compatibility with whole-inventory coverage. -/
theorem selected {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation} {index : Nat}
    {signature : SourceCoreCalls.Signature}
    (coverage : Coverage headers compilation) (ordered : Ordered compilation.plan instantiation)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false =
      .ok (index, signature)) :
    ∃ header, header ∈ headers ∧ header.slot = index ∧ header.named.signature = signature ∧
      instantiation = header.instantiation ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok header.named.specialized := by
  exact selected_record coverage.plan coverage.ordered
    (fun specialized exactRecord => coverage.slots index signature specialized
      (NamedCalls.selected_signature_target accepted).2 exactRecord) ordered accepted

/-- Empty actual domains are one concrete way to close the order condition.
No permutation-sensitive equality is inferred merely from the selected key. -/
theorem ordered_monomorphic {plan : SourceCompilationPlan.Plan} {instantiation : DeclarationInstantiation}
    (empty : instantiation.parameterSubstitution = [])
    (domains : ∀ key specialized, SourceCompilationPlan.exactInstantiationKey plan instantiation = .ok key →
      SourceCompilationPlan.exactSpecialization plan key = .ok specialized → specialized.parameterSubstitution = []) :
    Ordered plan instantiation := by
  intro key specialized target exactRecord
  simp [empty, domains key specialized target exactRecord]

/-- Actual inference and specialization supply the retained domain order. -/
theorem ordered_inferred {plan : SourceCompilationPlan.Plan} {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : TypeSystem.ParameterSubstitution}
    (unique : signature.scheme.parameters.Nodup) (next : Nat)
    (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (records : ∀ key specialized,
      SourceCompilationPlan.exactInstantiationKey plan
        (CallableNamedCanonicalOrder.inferredInstantiation signature next final caller) = .ok key →
      SourceCompilationPlan.exactSpecialization plan key = .ok specialized →
      SourceSpecialization.specializeFunction signature function supplied = .ok specialized) :
    Ordered plan (CallableNamedCanonicalOrder.inferredInstantiation signature next final caller) := by
  intro key specialized target exactRecord
  rw [CallableNamedCanonicalOrder.inferred_parameterDomain signature next final caller unique,
    SourceSpecialization.specializeFunction_parameterDomain (records key specialized target exactRecord)]

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallSelectionCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInitialization
/-! Initial catalog authority is constructed from the actual reserved slots,
installed full closures and real empty indexed frame. Independent static source
headers and their empty lexical contexts remain explicit. No source body law,
source execution or decoder-derived history is used to initialize authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInitialization
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

def location (signatures : List Signature) (slot : Nat) : Nat := 1 + (signatures.length - 1 - slot)

theorem global_reference (signatures : List Signature) (layout : SourceCoreCallableIndexedFrames.Layout)
    {slot : Nat} {signature : Signature} (found : signatures[slot]? = some signature) :
    (initialEnvironment signatures layout)[slot]? =
      some (.cellRef (OptionalCell.cellType signature.functionType) (location signatures slot)) := by
  simpa only [initialEnvironment, location, List.reverse_reverse, List.length_reverse, List.length_singleton] using
    reserved_reference signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty]
      [.cellRef layout.type 0] (by simpa using found)

theorem frame_reference (signatures : List Signature) (layout : SourceCoreCallableIndexedFrames.Layout) :
    (initialEnvironment signatures layout)[signatures.length]? = some (.cellRef layout.type 0) := by
  rw [initialEnvironment, reserved_environment]
  simp

theorem frame_read (signatures : List Signature) (rows : List LambdaRow)
    (layout : SourceCoreCallableIndexedFrames.Layout) :
    (initialStore signatures rows layout).read? 0 = some (SourceCoreCallableIndexedFrames.encode layout .empty) := by
  have unchanged :=
    initialized_prefix signatures.reverse rows [.cellRef layout.type 0]
      [SourceCoreCallableIndexedFrames.encode layout .empty]
      (fun index => 1 + (signatures.length - 1 - index))
      (by intro i within; simp only [List.length_singleton]; omega) (location := 0) (by simp)
  exact unchanged.trans rfl

private theorem row_bound {signatures : List Signature} {rows : List LambdaRow}
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      signatures[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
    {i : Nat} (within : i < rows.length) : i < signatures.length := by
  obtain ⟨signature, selected, _⟩ := ordered i rows[i] (List.getElem?_eq_getElem within)
  exact (List.getElem?_eq_some_iff.mp selected).1

theorem closure_read (signatures : List Signature) (rows : List LambdaRow)
    (layout : SourceCoreCallableIndexedFrames.Layout)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      signatures[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
    {slot : Nat} {row : LambdaRow} (found : rows[slot]? = some row) :
    (initialStore signatures rows layout).read? (location signatures slot) =
      some (.inRight .unit (installedValue (initialEnvironment signatures layout) slot row)) := by
  have bounds : ∀ i, i < rows.length → location signatures (0 + i) <
      (reserve signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty] [.cellRef layout.type 0]).1.length := by
    intro i within
    simpa only [location, List.length_singleton, List.length_reverse, Nat.zero_add] using
      reserved_location_bound signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty]
        [.cellRef layout.type 0] (by simpa using row_bound ordered within)
  have distinct : ∀ i j, i < rows.length → j < rows.length → i ≠ j → location signatures (0 + i) ≠ location signatures (0 + j) := by
    intro i j hi hj different
    have left := row_bound ordered hi
    have right := row_bound ordered hj
    simp only [Nat.zero_add, location]
    omega
  have receipt := installed_read rows (location signatures) (initialEnvironment signatures layout)
      (reserve signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty] [.cellRef layout.type 0]).1
      0 bounds distinct found
  have locations : location signatures = (fun index => 1 + (signatures.length - 1 - index)) := rfl
  rw [locations] at receipt
  simpa only [initialStore, location, Nat.zero_add] using receipt

theorem row_of_cached {rows : List LambdaRow} {slot : Nat} {parameter result : Ty} {body : Expr}
    (cached : (rows.map LambdaRow.expression)[slot]? = some (.lambda parameter result body)) :
    rows[slot]? = some ⟨parameter, result, body⟩ := by
  rw [List.getElem?_map] at cached
  cases found : rows[slot]? with
  | none => simp [found] at cached
  | some row =>
    rcases row with ⟨p, r, b⟩
    simp only [found, Option.map_some, LambdaRow.expression] at cached
    cases cached
    rfl

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (rows : List LambdaRow)
  (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (globals : ∀ header, header ∈ headers → compiled.indexed.base.globals[header.slot]? = some header.named.signature)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])

include cached ordered ledger globals sizes locals in
/-- All native captures and their shared references follow from actual cache
reads and native store preservation. The independent source header and empty
source lexical context are explicit static inputs. -/
def of_stored {world : StoreTyping}
    (typed : RuntimeStoreHasTypes world
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ambient.definitions) :
    Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) := by
  have frameRead := frame_read compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame
  have frameType : world[0]? = some compiled.indexed.ancestry.layout.frame.type := by
    rw [typed.world_eq, List.getElem?_map]
    change Option.map Value.type ((initialStore _ _ _).read? 0) = _
    rw [frameRead]
    rfl
  refine {
    frameLocation := 0, unmapped := by simp, typed := frameType,
    current := .empty, ghost := .empty, frame := ⟨frameRead, .stable .empty⟩,
    records := [], snapshots := by simp [CallableIndexedSnapshots.All], distinct := by simp,
    captures := ?_ }
  intro header member
  have rowFound := row_of_cached (by rw [← cached]; exact ledger.cached header member)
  have read := closure_read compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame ordered rowFound
  obtain ⟨capturedContext, capturedTyped, _⟩ := stored_closure typed read
  obtain ⟨canonicalContext, canonicalTyped⟩ := drop_installer_units header.slot capturedTyped
  have embedding : EnvironmentsAgree (shift header.slot)
      (initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame)
      (List.replicate header.slot .unit ++ initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have reference := frame_reference compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  refine ⟨{
    administrative := canonicalContext,
    canonical := initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame,
    captured := List.replicate header.slot (Value.unit) ++ initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame,
    capturedContext := capturedContext, embedding := shift header.slot,
    environments := .nil canonicalTyped, locals := ?_, layout := embedding, typed := capturedTyped,
    reference := by simpa only [sizes header member] using reference,
    capturedReference := embedding reference, coherent := ?_, unmapped := by simp,
    distinct := by simp [location], read := read }⟩
  · rw [locals header member]
    exact .nil
  · intro target targetMember
    simpa only [Nat.zero_add] using global_reference compiled.indexed.base.globals
      compiled.indexed.ancestry.layout.frame (globals target targetMember)

include cached ordered ledger globals sizes locals in
/-- The actual recipe closes native store typing. This factory has no source
or native function-body correspondence premise. -/
theorem of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions) :
    ∃ world, Nonempty (Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)) := by
  obtain ⟨world, typed⟩ := stored accepted rows cached ordered
  rw [definitions] at typed
  exact ⟨world, ⟨of_stored compiled headers rows cached ordered ledger globals sizes locals typed⟩⟩

include cached ordered ledger globals sizes locals in
/-- A fresh source heap is represented alongside the complete initial caller
entry. The source function model is explicit; its body semantics is not used
to create administrative closures or catalog authority. -/
theorem initial_entry {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ∧
      Nonempty (Entry headers (fun header => location compiled.indexed.base.globals header.slot) 0 0 [] [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)
        (initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame)) := by
  obtain ⟨world, typed⟩ := stored accepted rows cached ordered
  rw [definitions] at typed
  refine ⟨world, ⟨rfl, ?_, typed, ?_⟩, ⟨of_stored compiled headers rows cached ordered ledger globals sizes locals typed, ?_⟩⟩
  · intro left right target impossible
    simp at impossible
  · intro source target impossible
    simp at impossible
  · intro header member
    simpa only [List.length_nil, Nat.zero_add] using global_reference compiled.indexed.base.globals
      compiled.indexed.ancestry.layout.frame (globals header member)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInitialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedRows
/-! Every row of the actual second-pass cache is extracted with its full
lambda code and ordered signature. Successful compilation fixes both list
length and slot correspondence. No runtime typing, decoder, source execution
or function-body meaning is used to identify a cached row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedRows
open Core Frontend SourceInference RecursiveGlobalInitializationMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapM_length {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} (accepted : inputs.mapM action = .ok outputs) :
    outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted; subst outputs; rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, _, accepted⟩ := bind_ok accepted
    obtain ⟨rest, acceptedRest, accepted⟩ := bind_ok accepted
    cases accepted
    simp only [List.length_cons, ih acceptedRest]

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

theorem compilation_length {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {representation : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation fuel) :
    compiled.closures.length = base.functions.length := by
  have accepted := compiled.compiled
  unfold SourceCoreCompatibleMarkedFunctions.compileClosures at accepted
  by_cases empty : base.functions.isEmpty = true
  · simp only [empty, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
    rw [← accepted, List.isEmpty_iff.mp empty]
    rfl
  · simp only [empty, Bool.false_eq_true, ↓reduceIte] at accepted
    cases diagnostics : base.diagnostics with
    | none => simp [diagnostics, bind, Except.bind, throw] at accepted
    | some diagnostics =>
      simp only [diagnostics, bind, Except.bind, pure, Except.pure] at accepted
      exact mapM_length (mapError_ok accepted)

def row : Expr → LambdaRow
  | .lambda parameter result body => ⟨parameter, result, body⟩
  | _ => ⟨.unit, .unit, .unit⟩

def rows (compiled : SourceCoreUnifiedCompilation.Compiled) : List LambdaRow :=
  compiled.indexed.secondPass.closures.map row

theorem cached_length (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.indexed.secondPass.closures.length = compiled.indexed.base.functions.length :=
  compilation_length compiled.indexed.secondPass

/-- An actual cached slot identifies the corresponding full named compilation
receipt, including its original lambda body. -/
theorem cached_at (compiled : SourceCoreUnifiedCompilation.Compiled)
    {slot : Nat} {code : Expr} (cached : compiled.indexed.secondPass.closures[slot]? = some code) :
    ∃ named diagnostics, compiled.indexed.base.functions[slot]? = some named ∧
      Nonempty (CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code) := by
  have bound := (List.getElem?_eq_some_iff.mp cached).1
  rw [cached_length compiled] at bound
  have selected := List.getElem?_eq_getElem bound
  obtain ⟨diagnostics, output, found, receipt⟩ := CallableIndexedNamedGeneration.compiled_at compiled.indexed selected
  have same := Option.some.inj (found.symm.trans cached)
  subst output
  exact ⟨_, diagnostics, selected, receipt⟩

theorem exact_cache (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.indexed.secondPass.closures = (rows compiled).map LambdaRow.expression := by
  unfold rows
  rw [List.map_map]
  calc
    compiled.indexed.secondPass.closures = compiled.indexed.secondPass.closures.map id := (List.map_id _).symm
    _ = _ := by
      apply List.map_congr_left
      intro code member
      obtain ⟨slot, cached⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨_, _, _, ⟨receipt⟩⟩ := cached_at compiled cached
      rw [receipt.emitted]
      rfl

theorem row_at (compiled : SourceCoreUnifiedCompilation.Compiled)
    {slot : Nat} {selectedRow : LambdaRow} (found : (rows compiled)[slot]? = some selectedRow) :
    ∃ named diagnostics,
      compiled.indexed.base.functions[slot]? = some named ∧
      selectedRow.parameter = named.signature.parameterType ∧
      selectedRow.result = LanguageResult.resultType named.signature.resultType ∧
      Nonempty (CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics selectedRow.expression) := by
  have cached : compiled.indexed.secondPass.closures[slot]? = some selectedRow.expression := by
    rw [exact_cache compiled, List.getElem?_map, found]
    rfl
  obtain ⟨named, diagnostics, selected, ⟨receipt⟩⟩ := cached_at compiled cached
  have emitted := receipt.emitted
  rcases selectedRow with ⟨parameter, result, body⟩
  change Expr.lambda parameter result body = _ at emitted
  exact ⟨named, diagnostics, selected, (Expr.lambda.inj emitted).1,
    (Expr.lambda.inj emitted).2.1, ⟨receipt⟩⟩

/-- The full global signature comes from the real preparation inventory.
Neither type tags nor a comparison of keys supplies this equality. -/
theorem ordered (compiled : SourceCoreUnifiedCompilation.Compiled)
    (slot : Nat) (selectedRow : LambdaRow) (found : (rows compiled)[slot]? = some selectedRow) :
    ∃ signature, compiled.indexed.base.globals[slot]? = some signature ∧
      signature.functionType = .function selectedRow.parameter selectedRow.result := by
  obtain ⟨named, _, selected, parameter, result, _⟩ := row_at compiled found
  refine ⟨named.signature, CallableIndexedPreparedInventories.cached_global_at compiled selected, ?_⟩
  rw [parameter, result]
  rfl

theorem rows_length (compiled : SourceCoreUnifiedCompilation.Compiled) :
    (rows compiled).length = compiled.indexed.base.globals.length := by
  rw [rows, List.length_map, cached_length, CallableIndexedPreparedInventories.cached_globals, List.length_map]

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedBitNotStatementContracts
/-! The existing bare unary Head exposes the independent source trace and
the actual strict native continuation. No expression child is invented for
the administrative Unit RHS. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

namespace Head
variable   {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

  {assignment : AssignmentResolution}
  (head : Head context scope assignment)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include environments heaps locals agrees actualTyped in
theorem reflects_sized (errors : head.Errors faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ sourceSize reason token after finalMap finalWorld,
      SourceExecutionSize.SourcePlaceBitNotFaults program sourceSize context evidence source environment before assignment.target reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ sourceSize updated after written finalMap finalWorld slots remainingSize,
      SourceExecutionSize.SourcePlaceSnapshotUpdate program sourceSize context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      remainingSize < size ∧ EvaluationSize remainingSize (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  cases CompatibleRenamedBareBitNot.reflects_sized (compilation := values) head.layout head.bare head.profile
    environments heaps locals agrees actualTyped head.slot head.writable errors completed with
  | fault trace same matched stores =>
    subst finalStore
    exact .inl ⟨_, _, _, before, mapping, world, trace, same, matched, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | success trace _ finalHeaps frame metadata count typed smaller continuation =>
    exact .inr ⟨_, _, _, _, mapping, world, _, _, trace, finalHeaps, .refl _, .refl _, frame, metadata, count, typed, smaller, continuation⟩

end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
/-! The actual function finish consumes the original measured flow. Source
body and flow witnesses have the same source grade; native finish inversion
selects a strict original flow child. Reflection constructs its independent
source grade, retaining the reached lexical exit and actual concrete outer transition. Legacy wrappers preserve the original guarded entry.
The Match Tree supplies source control shape; the original For entry embeds
without changing code. Flow meaning remains an explicit pointwise premise for
catalog mutual induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLoopContracts (ExecutesAt)
open RecursiveNamedCallBounds (BodyTrace)
universe u v

/-- The wrapper adds no source execution step: every case retains the same
measured function-statement witness and its distinct source call exit. -/
theorem trace_flow {program : Program} {size : Nat} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ finalContext control,
      ExecutesAt size true program context function.evidence function.source environment before function.body finalContext control after ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
  cases trace with
  | returned trace => exact ⟨_, _, .control trace, .returned _⟩
  | unit same trace => exact ⟨_, _, .control trace, .unit _ same⟩
  | fault failed => exact ⟨_, _, .fault failed, .fault _⟩
  | escaped trace escape =>
    rcases escape with ⟨next, rfl⟩ | ⟨next, rfl⟩
    · exact ⟨_, _, .control trace, .breaking next⟩
    · exact ⟨_, _, .control trace, .continuing next⟩

section Match

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {type : Ty} {flow code : Expr}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word}
  (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt fellThrough escaped = .ok code)
  (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt true escaped = .ok flow)
  (tree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax certificates ambient.definitions administrative context scope
    (.statements true function.body) function.resultType type flow)
  (projection : values.checked.catalog.project function.resultType = .ok type)
  (unique : NodeOccurrencesUnique function.source)
  {faults : FunctionCalls.FaultRep} (escapedFault : faults .controlEscapedFunction escaped)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include accepted generated in
private theorem emitted : code = CompatibleStatements.finish type flow fellThrough escaped := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  exact Except.ok.inj accepted.symm

include tree projection unique in
theorem WithReady.preserves_at_emitted_with_state_when_with_transfers_with_post (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost) {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : NamedLexicalFunctionFaultPostContracts.PreservesAtWith (post := flowPost) protocol readiness condition facts functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (transfers : ∀ {sourceSize finalContext control after},
      ExecutesAt sourceSize true program context function.evidence function.source
        environment before function.body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults escaped control)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedLexicalFunctionFaultPostContracts.FinishedPost flowPost program function context environment before size type outcome after value finalMap finalWorld finalStore := by
  obtain ⟨finalContext, control, trace, exit⟩ := trace_flow trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, post⟩, origin⟩ :=
    meaning valid bodyFacts environments heaps locals agrees typed reference read unmapped initial gate ready trace
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow_with_transfers functions (fun next same => by
    cases same
    exact GenericImperativeMatch.Tree.true_fallthrough_unit tree unique trace.sound)
    projection fellThrough escaped (transfers trace) represented evaluated
  have finishedPost := NamedLexicalFunctionFaultPostContracts.finished_post trace exit origin evaluated completed
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [emitted, ImperativeFunctionFinish.rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, ImperativeFunctionFinish.result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨finalContext, control, trace.sound, exit, lexical⟩,
    ⟨reached, retained, ProtectedStateTransition.FunctionFinish.post_of_exit exit post⟩, finishedPost⟩


include tree projection unique in
theorem WithReady.preserves_at_emitted_with_state_when_with_transfers {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (transfers : ∀ {sourceSize finalContext control after},
      ExecutesAt sourceSize true program context function.evidence function.source
        environment before function.body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults escaped control)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, exit, reached, _⟩ :=
    WithReady.preserves_at_emitted_with_state_when_with_transfers_with_post (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (functions := functions) (program := program) (tree := tree) (projection := projection) (unique := unique)
      protocol readiness condition facts emitted validity size
      (NamedLexicalFunctionFaultPostContracts.PreservesAtWith.of_trivial (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := function.evidence) (meaning := meaning))
      valid bodyFacts environments heaps locals agrees typed reference read unmapped initial gate ready transfers trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, exit, reached⟩

include tree projection unique escapedFault in
theorem WithReady.preserves_at_emitted_with_state_when {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  apply WithReady.preserves_at_emitted_with_state_when_with_transfers (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique)
    protocol readiness condition facts emitted validity size meaning valid bodyFacts environments heaps locals agrees typed reference read unmapped
    initial gate ready (fun _ => ⟨fun _ _ => escapedFault, fun _ _ => escapedFault⟩)
  exact trace


include tree projection unique escapedFault in
theorem preserves_at_emitted_with_state_when {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol condition functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ :=
    WithReady.preserves_at_emitted_with_state_when (functions := functions) (program := program)
      (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) condition
      (fun _ _ _ _ => True) emitted validity size
      (RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith.of_true
        protocol condition functions program function.evidence meaning) valid True.intro
      environments heaps locals agrees typed reference read unmapped initial gate True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ProtectedStateTransition.FunctionFinish.Reached.forget reached⟩

include tree projection unique escapedFault in
theorem preserves_at_emitted_with_state {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : ProtectedStateTransition.Lexical.PreservesAtFor protocol functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_at_emitted_with_state_when (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
    protocol (fun _ _ => True) emitted validity size
    (ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded protocol (fun _ _ => True)
      functions program function.evidence meaning) valid
    environments heaps locals agrees typed reference read unmapped initial True.intro trace

include tree projection unique escapedFault transport in
theorem preserves_at_emitted (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor (entry := entry) functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical  := by
  have stateful := ProtectedStateTransition.Lexical.legacy_preserves
    (functions := functions) (program := program) (evidence := function.evidence) transport meaning
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, transition⟩ :=
    preserves_at_emitted_with_state (functions := functions) (program := program)
      (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      (ProtectedStateTransition.Lexical.legacyProtocol entry) emitted validity size stateful valid
      environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trace
  obtain ⟨final, _⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, final.down⟩


include accepted generated tree projection unique escapedFault transport in
theorem preserves_at_with (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor (entry := entry) functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  apply preserves_at_emitted (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique)
    (escapedFault := escapedFault) (transport := transport)
    (emitted accepted generated) validity size meaning valid
  all_goals assumption

include tree projection unique in
theorem WithReady.reflects_at_emitted_with_state_when_with_transfers_with_post (flowPost : NamedLexicalFlowFaultPostContracts.FlowFaultPost) {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      NamedLexicalFunctionFaultPostContracts.ReflectsAtWith (post := flowPost) protocol readiness condition facts functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (transfers : ∀ {sourceSize finalContext control after},
      ExecutesAt sourceSize true program context function.evidence function.source
        environment before function.body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults escaped control)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedLexicalFunctionFaultPostContracts.FinishedPost flowPost program function context environment before sourceSize type outcome after value finalMap finalWorld finalStore := by
  rw [emitted, ImperativeFunctionFinish.rename] at evaluated
  obtain ⟨flowSize, flowValue, middleStore, smaller, flowEval⟩ := RecursiveNamedCallBounds.finish_flow evaluated
  obtain ⟨sourceSize, finalContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, post⟩, origin⟩ :=
    meaning flowSize (Nat.lt_of_lt_of_le smaller within) valid bodyFacts
      environments heaps locals agrees typed reference read unmapped initial gate ready flowEval
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow_with_transfers functions (fun next same => by
    cases same
    exact GenericImperativeMatch.Tree.true_fallthrough_unit tree unique trace.sound)
    projection fellThrough escaped (transfers trace) represented flowEval.sound
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound completed
  have sourceResult : ∃ outcome, BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed => exact ⟨_, .unit raw executed, .value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed => exact ⟨_, .returned executed, .value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (tree.control_not_fault unique executed.sound)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
    | breaking finalEnvironment matched =>
      cases trace with
      | control executed => exact ⟨_, .escaped executed (.inl ⟨_, rfl⟩), .fault matched, .breaking _⟩
    | continuing finalEnvironment matched =>
      cases trace with
      | control executed => exact ⟨_, .escaped executed (.inr ⟨_, rfl⟩), .fault matched, .continuing _⟩
  obtain ⟨outcome, bodyTrace, represented, exit⟩ := sourceResult
  have finishedPost := NamedLexicalFunctionFaultPostContracts.finished_post trace exit origin flowEval.sound completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, bodyTrace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨finalContext, control, trace.sound, exit, lexical⟩,
    ⟨reached, retained, ProtectedStateTransition.FunctionFinish.post_of_exit exit post⟩, finishedPost⟩


include tree projection unique in
theorem WithReady.reflects_at_emitted_with_state_when_with_transfers {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (transfers : ∀ {sourceSize finalContext control after},
      ExecutesAt sourceSize true program context function.evidence function.source
        environment before function.body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults escaped control)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, exit, reached, _⟩ :=
    WithReady.reflects_at_emitted_with_state_when_with_transfers_with_post (flowPost := NamedLexicalFlowFaultPostContracts.TrivialFlow) (functions := functions) (program := program) (tree := tree) (projection := projection) (unique := unique)
      protocol readiness condition facts emitted validity budget size within
      (fun child smaller => NamedLexicalFunctionFaultPostContracts.ReflectsAtWith.of_trivial (protocol := protocol) (readiness := readiness) (condition := condition) (facts := facts) (functions := functions) (program := program) (evidence := function.evidence) (meaning := meaning child smaller))
      valid bodyFacts environments heaps locals agrees typed reference read unmapped initial gate ready transfers evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, exit, reached⟩

include tree projection unique escapedFault in
theorem WithReady.reflects_at_emitted_with_state_when {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  apply WithReady.reflects_at_emitted_with_state_when_with_transfers (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique)
    protocol readiness condition facts emitted validity budget size within meaning valid bodyFacts environments heaps locals agrees typed reference read unmapped
    initial gate ready (fun _ => ⟨fun _ _ => escapedFault, fun _ _ => escapedFault⟩)
  exact evaluated


include tree projection unique escapedFault in
theorem reflects_at_emitted_with_state_when {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol condition functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ :=
    WithReady.reflects_at_emitted_with_state_when (functions := functions) (program := program)
      (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) condition
      (fun _ _ _ _ => True) emitted validity budget size within
      (fun child smaller => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith.of_true
        protocol condition functions program function.evidence (meaning child smaller)) valid True.intro
      environments heaps locals agrees typed reference read unmapped initial gate True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ProtectedStateTransition.FunctionFinish.Reached.forget reached⟩

include tree projection unique escapedFault in
theorem reflects_at_emitted_with_state {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.Lexical.ReflectsAtFor protocol functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_at_emitted_with_state_when (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
    protocol (fun _ _ => True) emitted validity budget size within
    (fun child smaller => ProtectedStateTransition.Lexical.Gated.reflects_of_unguarded protocol (fun _ _ => True)
      functions program function.evidence (meaning child smaller)) valid
    environments heaps locals agrees typed reference read unmapped initial True.intro evaluated

include tree projection unique escapedFault transport in
theorem reflects_at_emitted (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAtFor (entry := entry) functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical  := by
  have stateful : RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.Lexical.ReflectsAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
        functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow) :=
    fun child smaller => ProtectedStateTransition.Lexical.legacy_reflects
      (functions := functions) (program := program) (evidence := function.evidence) transport (meaning child smaller)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, transition⟩ :=
    reflects_at_emitted_with_state (functions := functions) (program := program)
      (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      (ProtectedStateTransition.Lexical.legacyProtocol entry) emitted validity budget size within stateful valid
      environments heaps locals agrees typed reference read unmapped ⟨installed⟩ evaluated
  obtain ⟨final, _⟩ := transition
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, final.down⟩

include accepted generated tree projection unique escapedFault transport in
theorem reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAtFor (entry := entry) functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  apply reflects_at_emitted (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique)
    (escapedFault := escapedFault) (transport := transport)
    (emitted accepted generated) validity budget size within meaning valid
  all_goals assumption



include accepted generated tree projection unique escapedFault transport in
theorem preserves_at_match (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program function.evidence
      (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  exact preserves_at_with functions program accepted generated tree projection unique escapedFault transport
    (fun context => CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    size meaning valid environments heaps locals agrees typed reference read unmapped installed trace

include accepted generated tree projection unique escapedFault transport in
theorem reflects_at_match (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program function.evidence
        (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  exact reflects_at_with functions program accepted generated tree projection unique escapedFault transport
    (fun context => CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    budget size within meaning valid environments heaps locals agrees typed reference read unmapped installed evaluated


end Match

/- Original For entry retains the exact emitted code. -/
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {type : Ty} {flow code : Expr}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word}
  (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt fellThrough escaped = .ok code)
  (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt true escaped = .ok flow)
  (tree : GenericImperativeFor.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax certificates ambient.definitions administrative context scope
    (.statements true function.body) function.resultType type flow)
  (projection : values.checked.catalog.project function.resultType = .ok type)
  (unique : NodeOccurrencesUnique function.source)
  {faults : FunctionCalls.FaultRep} (escapedFault : faults .controlEscapedFunction escaped)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include accepted generated tree projection unique escapedFault transport in
theorem preserves_at (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program function.evidence
      (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  exact preserves_at_match functions program accepted generated (GenericImperativeMatch.Tree.of_for tree)
    projection unique escapedFault transport size meaning valid environments heaps locals agrees typed reference read unmapped installed trace

include accepted generated tree projection unique escapedFault transport in
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program function.evidence
        (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  exact reflects_at_match functions program accepted generated (GenericImperativeMatch.Tree.of_for tree)
    projection unique escapedFault transport budget size within meaning valid environments heaps locals agrees typed reference read unmapped installed evaluated

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
end
