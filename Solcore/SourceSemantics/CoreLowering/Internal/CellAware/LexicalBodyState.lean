import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.Staging.RecursiveBodyErasure
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates

/-!
# Cell-aware lexical body state

Lexical entries of ordinary bodies inside mixed closure heaps: state, determinacy, declarations, blocks, conditionals, discards and completion, with the Source side of ordinary bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy
/-! Finite lexical completion determines every Source trace of the same body.
Each expression fact is supplied by its actual completion; allocations and
scoped control retain the exact reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}

abbrev Expression (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : ExpressionId) (outcome : Outcome) (after : Dynamic.Heap) : Prop :=
  ∀ {size otherOutcome otherHeap}, Size.Expression program registry size invocation context environment before id otherOutcome otherHeap →
    otherOutcome = outcome ∧ otherHeap = after

abbrev Body (mode : Bool) (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (finalContext : SourceSemantics.Context)
    (outcome : BodyOutcome) (after : Dynamic.Heap) : Prop :=
  ∀ {size otherContext otherOutcome otherHeap},
    Size.StatementsIn program registry mode size invocation context environment before statements otherContext otherOutcome otherHeap →
    otherContext = finalContext ∧ otherOutcome = outcome ∧ otherHeap = after

variable (unique : NodeOccurrencesUnique invocation.source)

 theorem nil {mode context environment before} :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before [] context (.fallthrough environment) before := by
  intro _ _ _ _ trace
  cases trace
  exact ⟨rfl,rfl,rfl⟩

include unique in
theorem returnUnit {mode context environment before id node rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id :: rest) context (.returned .unit) before := by
  intro _ _ _ _ trace
  exact CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.return_unit unique found form trace

include unique in
theorem terminal {mode context environment before expression statements outcome after}
    (head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode statements)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before expression outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before statements context
      (CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.control outcome) after := by
  intro _ _ _ _ trace
  obtain ⟨_,_,_,sameContext,sameOutcome,actual⟩ := CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion.child_of_body unique head trace
  obtain ⟨same,heap⟩ := child actual
  exact ⟨sameContext, sameOutcome.trans (congrArg _ same),heap⟩

private theorem allocation_unique {before : Dynamic.Heap} {type : TypeSystem.Ty} {value : Option Dynamic.Value}
    {first second : Dynamic.Location} {left right : Dynamic.Heap}
    (one : Dynamic.Heap.Allocates before type value first left)
    (two : Dynamic.Heap.Allocates before type value second right) : second = first ∧ right = left := by
  cases one
  cases two
  exact ⟨rfl,rfl⟩

include unique in
theorem absent {mode context nextContext environment before id node binder rest location bound finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode nextContext
      ((binder.id,location)::environment) bound rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  obtain ⟨_,_,_,_,actualAllocation,remaining⟩ := CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.absent unique found form extended trace
  obtain ⟨rfl,rfl⟩ := allocation_unique allocated actualAllocation
  exact tail remaining

include unique in
theorem initializedFault {mode context nextContext environment before id node binder initializer rest failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before initializer (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized unique found form mono extended trace with first | second
  · obtain ⟨_,_,_,sameContext,sameOutcome,actual⟩ := first
    obtain ⟨same,heap⟩ := child actual
    cases same
    exact ⟨sameContext,sameOutcome,heap⟩
  · obtain ⟨_,_,_,_,_,_,_,actual,_,_⟩ := second
    cases (child actual).1

include unique in
theorem initialized {mode context nextContext environment before id node binder initializer rest sourceValue middle location bound finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before initializer (.value sourceValue) middle)
    (allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location bound)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode nextContext
      ((binder.id,location)::environment) bound rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized unique found form mono extended trace with first | second
  · obtain ⟨_,_,_,_,_,actual⟩ := first
    cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,actual,actualAllocation,remaining⟩ := second
    obtain ⟨same,rfl⟩ := child actual
    cases same
    obtain ⟨rfl,rfl⟩ := allocation_unique allocated actualAllocation
    exact tail remaining

include unique in
theorem discardFault {mode semicolon context environment before id node expression rest failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
    (continuing : semicolon = true ∨ mode = false)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before expression (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion.child_and_tail unique (lookupStatement?_sound found) form continuing trace with first | second
  · obtain ⟨_,_,_,sameContext,sameOutcome,actual⟩ := first
    obtain ⟨same,heap⟩ := child actual
    cases same
    exact ⟨sameContext,sameOutcome,heap⟩
  · obtain ⟨_,_,_,_,_,actual,_⟩ := second
    cases (child actual).1

include unique in
theorem discard {mode semicolon context environment before id node expression rest sourceValue middle finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
    (continuing : semicolon = true ∨ mode = false)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before expression (.value sourceValue) middle)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode context environment middle rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion.child_and_tail unique (lookupStatement?_sound found) form continuing trace with first | second
  · obtain ⟨_,_,_,_,_,actual⟩ := first
    cases (child actual).1
  · obtain ⟨_,_,_,_,_,actual,remaining⟩ := second
    obtain ⟨_,rfl⟩ := child actual
    exact tail remaining

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyScopedDeterminacy
/-! Scoped finite-body completion determines the selected branch, restores
lexical bindings, and keeps the actual heap reached by the selected path. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy
open Frontend SourceInference Staging.Recursive
variable {program : Program} {registry : Registry} {invocation : Scope}
  (unique : NodeOccurrencesUnique invocation.source)

include unique in
theorem blockReturned {mode context environment before id node statements rest innerContext sourceValue after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment before statements innerContext (.returned sourceValue) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.returned sourceValue) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion.block_and_tail unique found form trace with first | second | third | fourth | fifth
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := first
    obtain ⟨_,same,heap⟩ := inner actual
    exact ⟨sameContext,sameOutcome.trans same,heap⟩
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := second
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := third
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := fourth
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual,remaining⟩ := fifth
    cases (inner actual).2.1

include unique in
theorem blockFault {mode context environment before id node statements rest innerContext failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment before statements innerContext (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion.block_and_tail unique found form trace with first | second | third | fourth | fifth
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := first
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := second
    obtain ⟨_,same,heap⟩ := inner actual
    exact ⟨sameContext,sameOutcome.trans same,heap⟩
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := third
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,sameContext,sameOutcome,actual⟩ := fourth
    cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual,remaining⟩ := fifth
    cases (inner actual).2.1

include unique in
theorem blockFallthrough {mode context environment before id node statements rest innerContext innerEnvironment middle finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment before statements innerContext (.fallthrough innerEnvironment) middle)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode context environment middle rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion.block_and_tail unique found form trace with first | second | third | fourth | fifth
  · obtain ⟨_,_,_,_,_,_,actual⟩ := first; cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual⟩ := second; cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual⟩ := third; cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual⟩ := fourth; cases (inner actual).2.1
  · obtain ⟨_,_,_,_,_,_,actual,remaining⟩ := fifth
    obtain ⟨_,_,rfl⟩ := inner actual
    exact tail remaining

include unique in
theorem conditionalFault {mode context environment before id node condition left right rest failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before condition (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique found form trace with first | second | third | fourth | fifth | sixth
  · obtain ⟨_,_,_,sameContext,sameOutcome,actual⟩ := first
    obtain ⟨same,heap⟩ := child actual
    cases same
    exact ⟨sameContext,sameOutcome,heap⟩
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_⟩ := second; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_⟩ := third; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_⟩ := fourth; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_⟩ := fifth; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,_,_⟩ := sixth; cases (child actual).1

include unique in
theorem conditionalReturned {mode context environment before id node condition left right rest truth middle innerContext sourceValue after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before condition (.value (.bool truth)) middle)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment middle
      (if truth then left else right.getD []) innerContext (.returned sourceValue) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.returned sourceValue) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique found form trace with first | second | third | fourth | fifth | sixth
  · obtain ⟨_,_,_,_,_,actual⟩ := first; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := second
    obtain ⟨same,rfl⟩ := child actual
    cases same
    obtain ⟨_,same,heap⟩ := inner branch
    exact ⟨sameContext,sameOutcome.trans same,heap⟩
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := third
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fourth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fifth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,branch,remaining⟩ := sixth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1

include unique in
theorem conditionalBranchFault {mode context environment before id node condition left right rest truth middle innerContext failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before condition (.value (.bool truth)) middle)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment middle
      (if truth then left else right.getD []) innerContext (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique found form trace with first | second | third | fourth | fifth | sixth
  · obtain ⟨_,_,_,_,_,actual⟩ := first; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := second
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := third
    obtain ⟨same,rfl⟩ := child actual
    cases same
    obtain ⟨_,same,heap⟩ := inner branch
    exact ⟨sameContext,sameOutcome.trans same,heap⟩
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fourth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fifth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,branch,remaining⟩ := sixth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1

include unique in
theorem conditionalFallthrough {mode context environment before id node condition left right rest truth middle innerContext innerEnvironment branchHeap finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before condition (.value (.bool truth)) middle)
    (inner : Body (program := program) (registry := registry) (invocation := invocation) false context environment middle
      (if truth then left else right.getD []) innerContext (.fallthrough innerEnvironment) branchHeap)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode context environment branchHeap rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique found form trace with first | second | third | fourth | fifth | sixth
  · obtain ⟨_,_,_,_,_,actual⟩ := first; cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := second
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := third
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fourth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,sameContext,sameOutcome,actual,branch⟩ := fifth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    cases (inner branch).2.1
  · obtain ⟨_,_,_,_,_,_,_,_,_,actual,branch,remaining⟩ := sixth
    obtain ⟨same,rfl⟩ := child actual
    cases same
    obtain ⟨_,_,rfl⟩ := inner branch
    exact tail remaining

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyState
/-! Actual lexical entries for ordinary bodies inside mixed closure heaps.
The state records the current physical frame and reached Source heap. Scoped
continuations may restore bindings while retaining every real allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory

inductive Outcome where
  | returned (value : Dynamic.Value)
  | fallthrough (environment : Dynamic.Environment)
  | fault (reason : Dynamic.SemanticFault)

def Outcome.embed : Outcome → Staging.Recursive.BodyOutcome
  | .returned value => .returned value
  | .fallthrough environment => .fallthrough environment
  | .fault reason => .fault (.semantic reason)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  (rawRegistry : SourceCoreRawMetadata.Registry)
  (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions)
  (program : Program) (invocation : Staging.Recursive.Scope)
  (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

structure Entry (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) where
  mapping : LocationMap
  world : StoreTyping
  administrative : Core.Context
  actualContext : Core.Context
  environment : Dynamic.Environment
  canonical : Environment
  actual : Environment
  heap : Dynamic.Heap
  store : Store
  embedding : Renaming
  location : Location
  native : NativeFrame
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
    mapping world administrative scope environment canonical ambient.definitions
  heaps : GenericHeap.CellHeapRepresents cells mapping world heap store
  heapTyped : Dynamic.HeapWellTyped context heap
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  agrees : EnvironmentsAgree embedding canonical actual
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions
  reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type location)
  read : store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native)
  unmapped : location ∉ mapping
  runtime : Dynamic.SourceRuntimeValid program context invocation.source
  covers : invocation.evidence.Covers context

variable {functions rawRegistry instances program invocation frame globals}

def Entry.advance {context scope}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (preserved : AdministrativePreserved entry.mapping entry.store mapping store)
    (effect : CellAwareScopeAuthority.Effect instances entry.mapping entry.world entry.heap entry.store mapping world heap store) :
    Entry functions rawRegistry instances program invocation frame globals context scope where
  mapping := mapping
  world := world
  administrative := entry.administrative
  actualContext := entry.actualContext
  environment := entry.environment
  canonical := entry.canonical
  actual := entry.actual
  heap := heap
  store := store
  embedding := entry.embedding
  location := entry.location
  native := entry.native
  environments := entry.environments.extend effect.maps effect.worlds
  heaps := heaps
  heapTyped := heapTyped
  locals := entry.locals.mono effect.metadata
  agrees := entry.agrees
  actualTyped := entry.actualTyped.weaken effect.worlds
  reference := entry.reference
  read := (preserved entry.location entry.unmapped (List.getElem?_eq_some_iff.mp entry.read).1).2.trans entry.read
  unmapped := (preserved entry.location entry.unmapped (List.getElem?_eq_some_iff.mp entry.read).1).1
  runtime := entry.runtime
  covers := entry.covers

def Entry.prefix {context scope}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (value : Value) (type : Ty) (typed : RuntimeValueHasType entry.world value type ambient.definitions) :
    Entry functions rawRegistry instances program invocation frame globals context scope :=
  { entry with
    actualContext := type :: entry.actualContext
    actual := value :: entry.actual
    embedding := Renaming.comp (Renaming.insertion 0) entry.embedding
    agrees := GenericExpressionMeaning.agree_prefix entry.agrees value
    actualTyped := .cons typed entry.actualTyped }

structure Result {context scope}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (registry : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
    (mode : Bool) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) where
  size : Nat
  finalContext : SourceSemantics.Context
  outcome : Outcome
  after : Dynamic.Heap
  value : Value
  store : Store
  mapping : LocationMap
  world : StoreTyping
  trace : Staging.Recursive.Size.StatementsIn program registry mode size invocation context entry.environment entry.heap
    statements finalContext outcome.embed after
  evaluated : Evaluates entry.actual entry.store (code.rename entry.embedding) value store
  represented : CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents model mapping world mode expected type faults outcome.embed value
  heaps : GenericHeap.CellHeapRepresents cells mapping world after store
  preserved : AdministrativePreserved entry.mapping entry.store mapping store
  effect : CellAwareScopeAuthority.Effect instances entry.mapping entry.world entry.heap entry.store mapping world after store
  fallthroughTyped : ∀ environment, outcome = .fallthrough environment → Dynamic.HeapWellTyped context after

  determines : CellAwareLexicalBodyDeterminacy.Body (program := program) (registry := registry) (invocation := invocation)
    mode context entry.environment entry.heap statements finalContext outcome.embed after

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
/-! Expression leaves in ordinary materialized bodies retain their own actual
compiler certificate and original typing derivation. Numeric evidence is
recovered from the runtime context and its covering dictionary at that leaf. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState
open Staging.Recursive.Lifting (embed)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {reasonAt : ExpressionId → Word}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

def StaticCertificate (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (reasonAt : ExpressionId → Word) (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ fuel solved node, source.lookupExpression? id = some node ∧
    ExpressionHasType source context id node.type ∧
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate fuel (.initial checked)
      source context solved reasonAt scope id lowered

abbrev Certificate (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  StaticCertificate checked invocation.source reasonAt context scope id lowered

include extension uninitialized semantic selectedBodies in
theorem expression {context scope id lowered node}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (certificate : Certificate (checked := checked) (invocation := invocation) (reasonAt := reasonAt) context scope id lowered)
    (found : invocation.source.lookupExpression? id = some node) :
    ∃ size outcome after value finalStore,
      Staging.Recursive.Size.Expression program registry size invocation context entry.environment entry.heap id (embed outcome) after ∧
      Evaluates entry.actual entry.store (lowered.expression.rename entry.embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model entry.mapping entry.world node.type lowered.type faults (embed outcome) value ∧
      GenericHeap.CellHeapRepresents cells entry.mapping entry.world after finalStore ∧
      AdministrativePreserved entry.mapping entry.store entry.mapping finalStore ∧
      CellAwareScopeAuthority.Effect instances entry.mapping entry.world entry.heap entry.store entry.mapping entry.world after finalStore ∧
      (∀ sourceValue, outcome = .value sourceValue → Dynamic.HeapWellTyped context after ∧
        Dynamic.ValueHasType context after sourceValue node.type) ∧
      ∀ {otherSize otherOutcome otherHeap},
        Staging.Recursive.Size.Expression program registry otherSize invocation context entry.environment entry.heap id otherOutcome otherHeap →
        otherOutcome = embed outcome ∧ otherHeap = after := by
  obtain ⟨fuel,solved,other,otherFound,typed,certificate⟩ := certificate
  cases Option.some.inj (otherFound.symm.trans found)
  obtain ⟨size,outcome,after,value,finalStore,trace,evaluated,represented,heaps,preserved,_,effect,determines⟩ :=
    CellAwareReadProductCompletion.completes functions extension GeneralizedLocalDescriptorHeap.ordinary_cells
      (uninitialized context fuel) semantic entry.runtime.graph.nodeOccurrencesUnique selectedBodies entry.runtime entry.covers
      certificate found typed entry.environments entry.heaps entry.heapTyped entry.locals entry.agrees
  refine ⟨size,outcome,after,value,finalStore,trace,evaluated,represented,heaps,preserved,effect,?_,determines⟩
  intro sourceValue same
  subst outcome
  have result := Staging.Recursive.SelectedPreservation.expression selectedBodies
    entry.runtime entry.covers entry.locals entry.heapTyped typed trace
  exact ⟨result.heap_typed,result.value_typed sourceValue rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyLeaves
/-! Terminal and empty lexical leaves use the actual Source occurrence and
its own expression receipt, retaining semantic faults at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyLeaves
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions

theorem nil {context scope mode expected type}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (allowed : mode = false ∨ expected = .unit) :
    Nonempty (Result entry registry faults mode [] expected type (LocalLoop.fallthrough type)) := by
  exact ⟨{
    size := _
    finalContext := context
    outcome := .fallthrough entry.environment
    after := entry.heap
    value := LocalLoop.fallthroughValue type
    store := entry.store
    mapping := entry.mapping
    world := entry.world
    trace := .nil
    evaluated := by simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type entry.actual entry.store
    represented := .fallthrough entry.environment allowed
    heaps := entry.heaps
    preserved := .refl _ _
    effect := .refl _ _ _ _
    fallthroughTyped := fun _ _ => entry.heapTyped
    determines := CellAwareLexicalBodyDeterminacy.nil }⟩

theorem returnUnit {context scope mode id node}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (rest : List StatementId)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    Nonempty (Result entry registry faults mode (id :: rest) .unit .unit (LocalLoop.returned .unit)) := by
  exact ⟨{
    size := _
    finalContext := context
    outcome := .returned .unit
    after := entry.heap
    value := LocalLoop.returnedValue .unit
    store := entry.store
    mapping := entry.mapping
    world := entry.world
    determines := CellAwareLexicalBodyDeterminacy.returnUnit entry.runtime.graph.nodeOccurrencesUnique found form
    trace := .returnUnit (lookupStatement?_sound found) form
    evaluated := by simpa only [LoopRenaming.returned, Expr.rename] using LocalLoop.returned_evaluates (Evaluates.unit (environment := entry.actual) (store := entry.store))
    represented := .returned .unit
    heaps := entry.heaps
    preserved := .refl _ _
    effect := .refl _ _ _ _
    fallthroughTyped := by intro _ impossible; cases impossible }⟩

inductive Terminal (source : TypedSource) (expression : ExpressionId) : Bool → List StatementId → Prop where
  | returning {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
      Terminal source expression mode (id :: rest)
  | tail {id node}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false) :
      Terminal source expression true [id]

theorem Terminal.value {expression mode statements}
    (head : Terminal invocation.source expression mode statements)
    {size context environment before after sourceValue}
    (child : Staging.Recursive.Size.Expression program registry size invocation context environment before expression (.value sourceValue) after) :
    Staging.Recursive.Size.StatementsIn program registry mode (Staging.Recursive.Size.stepSize [size]) invocation
      context environment before statements context (.returned sourceValue) after := by
  cases head with
  | returning rest found form => exact .returnValue (lookupStatement?_sound found) form child
  | tail found form => exact .tail (lookupStatement?_sound found) form child

theorem Terminal.fault {expression mode statements}
    (head : Terminal invocation.source expression mode statements)
    {size context environment before after reason}
    (child : Staging.Recursive.Size.Expression program registry size invocation context environment before expression (.fault reason) after) :
    Staging.Recursive.Size.StatementsIn program registry mode (Staging.Recursive.Size.stepSize [size]) invocation
      context environment before statements context (.fault reason) after := by
  cases head with
  | returning rest found form => exact .returnFault (lookupStatement?_sound found) form child
  | tail found form => exact .expressionFault (lookupStatement?_sound found) form child

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

include extension uninitialized semantic selectedBodies in
theorem terminal {context scope mode statements expression lowered node expected}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (head : Terminal invocation.source expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node) (valueType : node.type = expected)
    (certificate : CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation)
      (reasonAt := reasonAt) context scope expression lowered) :
    Nonempty (Result entry registry faults mode statements expected lowered.type (LocalLoop.returnValue lowered.type lowered.expression)) := by
  obtain ⟨size,outcome,after,value,finalStore,trace,evaluated,represented,heaps,preserved,effect,_,determines⟩ :=
    CellAwareLexicalBodyExpressions.expression functions extension uninitialized semantic selectedBodies entry certificate found
  have actualHead : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode statements := by
    cases head with
    | returning rest found form => exact .returning rest (lookupStatement?_sound found) form
    | tail found form => exact .tail (lookupStatement?_sound found) form
  cases outcome with
  | value sourceValue =>
    cases represented with
    | @value _ nativeValue payload =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .returned sourceValue
        after := after
        value := LocalLoop.returnedValue nativeValue
        store := finalStore
        mapping := entry.mapping
        world := entry.world
        determines := CellAwareLexicalBodyDeterminacy.terminal entry.runtime.graph.nodeOccurrencesUnique actualHead determines
        trace := head.value trace
        evaluated := by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated
        represented := .returned (valueType ▸ payload)
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | fault reason =>
    cases represented with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := after
        value := _
        store := finalStore
        mapping := entry.mapping
        world := entry.world
        determines := CellAwareLexicalBodyDeterminacy.terminal entry.runtime.graph.nodeOccurrencesUnique actualHead determines
        trace := head.fault trace
        evaluated := by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyLeaves
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeclarations
/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeclarations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

include definitions registered in
theorem absent {context nextContext scope mode id node binder rest expected type body payload}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projected : checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (TypedLexicalControl.absentRequest invocation.source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (TypedLexicalControl.absentRequest invocation.source scope binder payload))
    (same : annotation.original = allocation.expression)
    (remaining : ∀ next : Entry functions rawRegistry instances program invocation frame globals
        nextContext ((binder.id,payload) :: scope), Nonempty (Result next registry faults mode rest expected type body)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type (.letE annotation.expression body)) := by
  let after : Dynamic.Heap := ⟨entry.heap.cells ++ [⟨binder.scheme.body,none,none⟩]⟩
  let location : Dynamic.Location := ⟨entry.heap.cells.length⟩
  have allocated : Dynamic.Heap.Allocates entry.heap binder.scheme.body none location after := .append
  obtain ⟨captured,evaluated,environments,heaps,locals,agrees,typed,reference,read,preserved,effect⟩ :=
    CellAwareOrdinaryBodyAllocation.absent GeneralizedLocalDescriptorHeap.ordinary_cells definitions registered
      mono extended ordinary projected allocation annotation same entry.environments entry.heaps entry.locals
      entry.agrees entry.actualTyped entry.reference entry.read allocated
  let next : Entry functions rawRegistry instances program invocation frame globals nextContext ((binder.id,payload) :: scope) := {
    mapping := entry.mapping ++ [entry.store.length + 2]
    world := entry.world ++ [frame.type,allocation.entry.layout.type,OptionalCell.cellType payload]
    administrative := entry.administrative
    actualContext := OptionalCell.referenceType payload :: entry.actualContext
    environment := (binder.id,location) :: entry.environment
    canonical := .cellRef (OptionalCell.cellType payload) (entry.store.length + 2) :: entry.canonical
    actual := .cellRef (OptionalCell.cellType payload) (entry.store.length + 2) :: entry.actual
    heap := after
    store := entry.store ++ [SourceCoreCallableIndexedFrames.encode frame entry.native,
      SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,.inLeft payload .unit]
    embedding := entry.embedding.lift
    location := entry.location
    native := entry.native
    environments := environments
    heaps := heaps
    heapTyped := (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mp (entry.heapTyped.allocate (.none _) allocated)
    locals := locals
    agrees := agrees
    actualTyped := typed
    reference := reference
    read := read
    unmapped := (preserved entry.location entry.unmapped (List.getElem?_eq_some_iff.mp entry.read).1).1
    runtime := entry.runtime.transport (.ofBinderExtends extended)
    covers := (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers entry.covers }
  obtain ⟨tail⟩ := remaining next
  exact ⟨{
    size := _
    finalContext := tail.finalContext
    outcome := tail.outcome
    after := tail.after
    value := tail.value
    store := tail.store
    mapping := tail.mapping
    world := tail.world
    determines := CellAwareLexicalBodyDeterminacy.absent entry.runtime.graph.nodeOccurrencesUnique found form extended allocated tail.determines
    trace := .letUninitialized (lookupStatement?_sound found) form mono extended allocated tail.trace
    evaluated := .letE evaluated tail.evaluated
    represented := tail.represented
    heaps := tail.heaps
    preserved := preserved.trans tail.preserved
    effect := effect.trans tail.effect
    fallthroughTyped := fun environment same =>
      (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr (tail.fallthroughTyped environment same) }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeclarations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyInitialized
/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyInitialized
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

include definitions registered extension uninitialized semantic selectedBodies in
theorem completes {context nextContext scope mode id node binder initializer initializerNode rest expected type body lowered}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (initializerFound : invocation.source.lookupExpression? initializer = some initializerNode)
    (valueType : initializerNode.type = binder.scheme.body)
    (certificate : CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation)
      (reasonAt := reasonAt) context scope initializer lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (TypedLexicalControl.initializedRequest invocation.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (TypedLexicalControl.initializedRequest invocation.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (remaining : ∀ next : Entry functions rawRegistry instances program invocation frame globals
        nextContext ((binder.id,lowered.type) :: scope), Nonempty (Result next registry faults mode rest expected type body)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type
      (TypedLexicalControl.sequence type lowered.expression annotation.expression body)) := by
  obtain ⟨size,outcome,middle,value,middleStore,trace,evaluated,represented,heaps,preserved,effect,valueTyped,determines⟩ :=
    CellAwareLexicalBodyExpressions.expression functions extension uninitialized semantic selectedBodies entry certificate initializerFound
  cases outcome with
  | fault reason =>
    cases represented with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := middle
        value := _
        store := middleStore
        mapping := entry.mapping
        world := entry.world
        determines := CellAwareLexicalBodyDeterminacy.initializedFault entry.runtime.graph.nodeOccurrencesUnique found form mono extended determines
        trace := .letFault (lookupStatement?_sound found) form mono trace
        evaluated := CellAwareOrdinaryContinuation.failure evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | value sourceValue =>
    cases represented with
    | @value _ nativeValue payload =>
      obtain ⟨heapTyped,sourceTyped⟩ := valueTyped sourceValue rfl
      let reached := entry.advance heaps heapTyped preserved effect
      let after : Dynamic.Heap := ⟨middle.cells ++ [⟨binder.scheme.body,some sourceValue,none⟩]⟩
      let location : Dynamic.Location := ⟨middle.cells.length⟩
      have allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location after := .append
      obtain ⟨captured,allocationEval,environments,nextHeaps,locals,agrees,typed,reference,read,allocationFrame,allocationEffect⟩ :=
        CellAwareOrdinaryBodyAllocation.initialized GeneralizedLocalDescriptorHeap.ordinary_cells definitions registered
          mono extended ordinary allocation annotation same (valueType ▸ payload) reached.environments reached.heaps reached.locals
          reached.agrees reached.actualTyped reached.reference reached.read allocated
      let next : Entry functions rawRegistry instances program invocation frame globals nextContext ((binder.id,lowered.type) :: scope) := {
        mapping := reached.mapping ++ [reached.store.length + 2]
        world := reached.world ++ [frame.type,allocation.entry.layout.type,OptionalCell.cellType lowered.type]
        administrative := reached.administrative
        actualContext := OptionalCell.referenceType lowered.type :: lowered.type :: reached.actualContext
        environment := (binder.id,location) :: reached.environment
        canonical := .cellRef (OptionalCell.cellType lowered.type) (reached.store.length + 2) :: reached.canonical
        actual := .cellRef (OptionalCell.cellType lowered.type) (reached.store.length + 2) :: nativeValue :: reached.actual
        heap := after
        store := reached.store ++ [SourceCoreCallableIndexedFrames.encode frame reached.native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,.inRight .unit nativeValue]
        embedding := (Renaming.comp (Renaming.insertion 0) reached.embedding).lift
        location := reached.location
        native := reached.native
        environments := environments
        heaps := nextHeaps
        heapTyped := (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mp (heapTyped.allocate (.some (valueType ▸ sourceTyped)) allocated)
        locals := locals
        agrees := agrees
        actualTyped := typed
        reference := reference
        read := read
        unmapped := (allocationFrame reached.location reached.unmapped (List.getElem?_eq_some_iff.mp reached.read).1).1
        runtime := reached.runtime.transport (.ofBinderExtends extended)
        covers := (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers reached.covers }
      obtain ⟨tail⟩ := remaining next
      exact ⟨{
        size := _
        finalContext := tail.finalContext
        outcome := tail.outcome
        after := tail.after
        value := tail.value
        store := tail.store
        mapping := tail.mapping
        world := tail.world
        determines := CellAwareLexicalBodyDeterminacy.initialized entry.runtime.graph.nodeOccurrencesUnique found form mono extended determines allocated tail.determines
        trace := .letInitialized (lookupStatement?_sound found) form trace mono extended allocated tail.trace
        evaluated := (CellAwareOrdinaryContinuation.agreement evaluated allocationEval).wrap tail.evaluated
        represented := tail.represented
        heaps := tail.heaps
        preserved := preserved.trans (allocationFrame.trans tail.preserved)
        effect := effect.trans (allocationEffect.trans tail.effect)
        fallthroughTyped := fun environment same =>
          (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr (tail.fallthroughTyped environment same) }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyInitialized
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyBlock
/-! Terminal and empty lexical leaves use the actual Source occurrence and
its own expression receipt, retaining semantic faults at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyBlock
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions

theorem completes {context scope mode id node statements rest expected type innerCode body}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result start registry faults false statements expected type innerCode))
    (remaining : ∀ next : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result next registry faults mode rest expected type body)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type (LocalLoop.sequence type innerCode body)) := by
  obtain ⟨⟨size,innerContext,outcome,after,value,store,mapping,world,trace,evaluated,represented,heaps,preserved,effect,heapTyped,determines⟩⟩ := inner entry
  cases outcome with
  | returned sourceValue =>
    cases represented with
    | returned payload =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .returned sourceValue
        after := after
        value := _
        store := store
        mapping := mapping
        world := world
        determines := CellAwareLexicalBodyDeterminacy.blockReturned entry.runtime.graph.nodeOccurrencesUnique found form determines
        trace := .blockReturned (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ evaluated
        represented := .returned payload
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | fault reason =>
    cases represented with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := after
        value := _
        store := store
        mapping := mapping
        world := world
        determines := CellAwareLexicalBodyDeterminacy.blockFault entry.runtime.graph.nodeOccurrencesUnique found form determines
        trace := .blockFault (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | fallthrough innerEnvironment =>
    cases represented with
    | fallthrough _ _ =>
      let reached := entry.advance heaps (heapTyped innerEnvironment rfl) preserved effect
      let next := ((reached.prefix (.inLeft LocalLoop.transferType (.inLeft type .unit))
        (LocalLoop.controlType type) (.inLeft (.inLeft .unit))).prefix (.inLeft type .unit)
        (LocalControl.controlType type) (.inLeft .unit)).prefix .unit .unit .unit
      obtain ⟨tail⟩ := remaining next
      have tailEval : Evaluates
          (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: entry.actual)
          store (((body.rename entry.embedding).weakenAt 0).weakenAt 0 |>.weakenAt 0) tail.value tail.store := by
        simpa only [next,Entry.prefix,reached,Entry.advance,GenericExpressionMeaning.rename_prefix] using tail.evaluated
      exact ⟨{
        size := _
        finalContext := tail.finalContext
        outcome := tail.outcome
        after := tail.after
        value := tail.value
        store := tail.store
        mapping := tail.mapping
        world := tail.world
        determines := CellAwareLexicalBodyDeterminacy.blockFallthrough entry.runtime.graph.nodeOccurrencesUnique found form determines tail.determines
        trace := .blockFallthrough (lookupStatement?_sound found) form trace tail.trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_fallthrough _ evaluated tailEval
        represented := tail.represented
        heaps := tail.heaps
        preserved := preserved.trans tail.preserved
        effect := effect.trans tail.effect
        fallthroughTyped := tail.fallthroughTyped }⟩

theorem stopped {context scope mode id node statements rest expected type innerCode suffix}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (stops : GenericLexicalStatements.Stopped invocation.source statements)
    (inner : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result start registry faults false statements expected type innerCode)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix)) := by
  obtain ⟨⟨size,innerContext,outcome,after,value,store,mapping,world,trace,evaluated,represented,heaps,preserved,effect,_,determines⟩⟩ := inner entry
  cases outcome with
  | returned sourceValue =>
    cases represented with
    | returned payload =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .returned sourceValue
        after := after
        value := _
        store := store
        mapping := mapping
        world := world
        determines := CellAwareLexicalBodyDeterminacy.blockReturned entry.runtime.graph.nodeOccurrencesUnique found form determines
        trace := .blockReturned (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ evaluated
        represented := .returned payload
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | fault reason =>
    cases represented with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := after
        value := _
        store := store
        mapping := mapping
        world := world
        determines := CellAwareLexicalBodyDeterminacy.blockFault entry.runtime.graph.nodeOccurrencesUnique found form determines
        trace := .blockFault (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | fallthrough environment =>
    have impossible := stops.terminates entry.runtime.graph.nodeOccurrencesUnique false trace.sound.fallthrough_scoped
    cases impossible

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyBlock
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyConditional
/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyConditional
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

include extension uninitialized semantic selectedBodies in
theorem completes {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : invocation.source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (certificate : CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation)
      (reasonAt := reasonAt) context scope condition ⟨.bool,conditionCode⟩)
    (left : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result start registry faults false thenBody expected type thenCode))
    (right : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result start registry faults false (elseBody.getD []) expected type elseCode))
    (continuation : (∀ next : Entry functions rawRegistry instances program invocation frame globals context scope,
        Nonempty (Result next registry faults mode rest expected type body)) ∨
      (GenericLexicalStatements.Stopped invocation.source thenBody ∧
        GenericLexicalStatements.Stopped invocation.source (elseBody.getD []))) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type
      (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)) := by
  obtain ⟨testSize,outcome,middle,value,middleStore,testTrace,testEval,testRep,testHeaps,testFrame,testEffect,valueTyped,testDetermines⟩ :=
    CellAwareLexicalBodyExpressions.expression functions extension uninitialized semantic selectedBodies entry certificate conditionFound
  cases outcome with
  | fault reason =>
    cases testRep with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := middle
        value := _
        store := middleStore
        mapping := entry.mapping
        world := entry.world
        determines := CellAwareLexicalBodyDeterminacy.conditionalFault entry.runtime.graph.nodeOccurrencesUnique found form testDetermines
        trace := .ifConditionFault (lookupStatement?_sound found) form testTrace
        evaluated := by
          rw [LoopRenaming.sequence,LoopRenaming.conditional]
          exact LocalLoop.sequence_failure _ (LocalControl.choose_failure _ testEval)
        represented := .fault matched
        heaps := testHeaps
        preserved := testFrame
        effect := testEffect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | value sourceValue =>
    cases testRep with
    | @value _ nativeValue payload =>
      obtain ⟨truth,sourceEq,nativeEq⟩ := CompatibleExpressionPrimitives.bool_fields (conditionType ▸ payload)
      subst sourceValue nativeValue
      have middleTyped := (valueTyped (.bool truth) rfl).1
      let reached := entry.advance testHeaps middleTyped testFrame testEffect
      let branched := reached.prefix (.bool truth) .bool .bool
      have selected : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
          Nonempty (Result start registry faults false (if truth then thenBody else elseBody.getD []) expected type
            (if truth then thenCode else elseCode)) := by
        cases truth <;> assumption
      obtain ⟨⟨branchSize,innerContext,outcome,after,value,store,mapping,world,branchTrace,branchEval,represented,heaps,preserved,effect,heapTyped,branchDetermines⟩⟩ := selected branched
      have branchEval' : Evaluates (.bool truth :: entry.actual) middleStore
          (((if truth then thenCode else elseCode).rename entry.embedding).weakenAt 0) value store := by
        simpa only [branched,Entry.prefix,reached,Entry.advance,GenericExpressionMeaning.rename_prefix] using branchEval
      have conditionalEval : Evaluates entry.actual entry.store
          ((LocalLoop.conditional type conditionCode thenCode elseCode).rename entry.embedding) value store := by
        rw [LoopRenaming.conditional]
        cases truth with
        | false => exact LocalControl.choose_false _ testEval branchEval'
        | true => exact LocalControl.choose_true _ testEval branchEval'
      cases outcome with
      | returned sourceValue =>
        cases represented with
        | returned payload =>
          exact ⟨{
            size := _
            finalContext := context
            outcome := .returned sourceValue
            after := after
            value := _
            store := store
            mapping := mapping
            world := world
            determines := CellAwareLexicalBodyDeterminacy.conditionalReturned entry.runtime.graph.nodeOccurrencesUnique found form testDetermines branchDetermines
            trace := .ifReturned (lookupStatement?_sound found) form testTrace branchTrace
            evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ conditionalEval
            represented := .returned payload
            heaps := heaps
            preserved := testFrame.trans preserved
            effect := testEffect.trans effect
            fallthroughTyped := by intro _ impossible; cases impossible }⟩
      | fault reason =>
        cases represented with
        | fault matched =>
          exact ⟨{
            size := _
            finalContext := context
            outcome := .fault reason
            after := after
            value := _
            store := store
            mapping := mapping
            world := world
            determines := CellAwareLexicalBodyDeterminacy.conditionalBranchFault entry.runtime.graph.nodeOccurrencesUnique found form testDetermines branchDetermines
            trace := .ifFault (lookupStatement?_sound found) form testTrace branchTrace
            evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ conditionalEval
            represented := .fault matched
            heaps := heaps
            preserved := testFrame.trans preserved
            effect := testEffect.trans effect
            fallthroughTyped := by intro _ impossible; cases impossible }⟩
      | fallthrough innerEnvironment =>
        cases represented with
        | fallthrough _ _ =>
          rcases continuation with remaining | ⟨leftStops,rightStops⟩
          · let afterBranch := entry.advance heaps (heapTyped innerEnvironment rfl)
              (testFrame.trans preserved) (testEffect.trans effect)
            let next := ((afterBranch.prefix (.inLeft LocalLoop.transferType (.inLeft type .unit))
              (LocalLoop.controlType type) (.inLeft (.inLeft .unit))).prefix (.inLeft type .unit)
              (LocalControl.controlType type) (.inLeft .unit)).prefix .unit .unit .unit
            obtain ⟨tail⟩ := remaining next
            have tailEval : Evaluates
                (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: entry.actual)
                store (((body.rename entry.embedding).weakenAt 0).weakenAt 0 |>.weakenAt 0) tail.value tail.store := by
              simpa only [next,Entry.prefix,afterBranch,Entry.advance,GenericExpressionMeaning.rename_prefix] using tail.evaluated
            exact ⟨{
              size := _
              finalContext := tail.finalContext
              outcome := tail.outcome
              after := tail.after
              value := tail.value
              store := tail.store
              mapping := tail.mapping
              world := tail.world
              determines := CellAwareLexicalBodyDeterminacy.conditionalFallthrough entry.runtime.graph.nodeOccurrencesUnique found form testDetermines branchDetermines tail.determines
              trace := .ifFallthrough (lookupStatement?_sound found) form testTrace branchTrace tail.trace
              evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_fallthrough _ conditionalEval tailEval
              represented := tail.represented
              heaps := tail.heaps
              preserved := testFrame.trans (preserved.trans tail.preserved)
              effect := testEffect.trans (effect.trans tail.effect)
              fallthroughTyped := tail.fallthroughTyped }⟩
          · have stopped : GenericLexicalStatements.Stopped invocation.source (if truth then thenBody else elseBody.getD []) := by
              cases truth <;> assumption
            have impossible := stopped.terminates entry.runtime.graph.nodeOccurrencesUnique false branchTrace.sound.fallthrough_scoped
            cases impossible

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyConditional
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDiscard
/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDiscard
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

include extension uninitialized semantic selectedBodies in
theorem completes {context scope mode id node expression expressionNode semicolon rest expected type body lowered}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
    (continuing : semicolon = true ∨ mode = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (certificate : CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation)
      (reasonAt := reasonAt) context scope expression lowered)
    (remaining : ∀ next : Entry functions rawRegistry instances program invocation frame globals context scope,
        Nonempty (Result next registry faults mode rest expected type body)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)) := by
  obtain ⟨size,outcome,middle,value,middleStore,trace,evaluated,represented,heaps,preserved,effect,valueTyped,determines⟩ :=
    CellAwareLexicalBodyExpressions.expression functions extension uninitialized semantic selectedBodies entry certificate expressionFound
  cases outcome with
  | fault reason =>
    cases represented with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := middle
        value := _
        store := middleStore
        mapping := entry.mapping
        world := entry.world
        determines := CellAwareLexicalBodyDeterminacy.discardFault entry.runtime.graph.nodeOccurrencesUnique found form continuing determines
        trace := .expressionFault (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | value sourceValue =>
    cases represented with
    | @value _ nativeValue payload =>
      have heapTyped := (valueTyped sourceValue rfl).1
      let reached := entry.advance heaps heapTyped preserved effect
      let next := reached.prefix nativeValue lowered.type ((CompatibleAmbientHeap.payloadModel checked rawRegistry functions).runtime_hasType payload)
      obtain ⟨tail⟩ := remaining next
      have tailEval : Evaluates (nativeValue :: entry.actual) middleStore
          ((body.rename entry.embedding).weakenAt 0) tail.value tail.store := by
        simpa only [next,Entry.prefix,reached,Entry.advance,GenericExpressionMeaning.rename_prefix] using tail.evaluated
      have fullTrace : ∃ fullSize, Staging.Recursive.Size.StatementsIn program registry mode fullSize invocation
          context entry.environment entry.heap (id :: rest) tail.finalContext tail.outcome.embed tail.after := by
        cases semicolon with
        | true => exact ⟨_,.discard (lookupStatement?_sound found) form trace tail.trace⟩
        | false =>
          have modeFalse := continuing.resolve_left (by decide)
          subst mode
          exact ⟨_,.discardValue (lookupStatement?_sound found) form trace tail.trace⟩
      obtain ⟨fullSize,fullTrace⟩ := fullTrace
      exact ⟨{
        size := fullSize
        finalContext := tail.finalContext
        outcome := tail.outcome
        after := tail.after
        value := tail.value
        store := tail.store
        mapping := tail.mapping
        world := tail.world
        determines := CellAwareLexicalBodyDeterminacy.discard entry.runtime.graph.nodeOccurrencesUnique found form continuing determines tail.determines
        trace := fullTrace
        evaluated := by rw [LoopRenaming.discard]; exact LocalSequence.discard_success _ evaluated tailEval
        represented := tail.represented
        heaps := tail.heaps
        preserved := preserved.trans tail.preserved
        effect := effect.trans tail.effect
        fallthroughTyped := tail.fallthroughTyped }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDiscard
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyCompletion
/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

include definitions registered extension uninitialized semantic selectedBodies in
theorem completes {context scope mode statements expected type code}
    (tree : CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError (.initial checked) invocation.source
      (CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation) (reasonAt := reasonAt))
      context scope mode statements expected type code) :
    ∀ entry : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result entry registry faults mode statements expected type code) := by
  induction tree with
  | nil allowed =>
    intro entry
    exact CellAwareLexicalBodyLeaves.nil entry allowed
  | returnUnit rest found form =>
    intro entry
    exact CellAwareLexicalBodyLeaves.returnUnit entry rest found form
  | returnValue rest found form expressionFound valueType value =>
    intro entry
    exact CellAwareLexicalBodyLeaves.terminal extension uninitialized semantic selectedBodies entry
      (.returning rest found form) expressionFound valueType value
  | tail found form expressionFound valueType value =>
    intro entry
    exact CellAwareLexicalBodyLeaves.terminal extension uninitialized semantic selectedBodies entry
      (.tail found form) expressionFound valueType value
  | uninitialized found form mono extended ordinary projected allocation annotation same remaining ih =>
    intro entry
    exact CellAwareLexicalBodyDeclarations.absent definitions registered entry found form mono extended ordinary
      projected allocation annotation same ih
  | initialized found form mono extended ordinary initializerFound sourceType initial allocation annotation same remaining ih =>
    intro entry
    exact CellAwareLexicalBodyInitialized.completes definitions registered extension uninitialized semantic selectedBodies
      entry found form mono extended ordinary initializerFound sourceType initial allocation annotation same ih
  | discard found form notTail continuing expressionFound value remaining ih =>
    intro entry
    exact CellAwareLexicalBodyDiscard.completes extension uninitialized semantic selectedBodies
      entry found form continuing expressionFound value ih
  | block found form inner remaining innerIH restIH =>
    intro entry
    exact CellAwareLexicalBodyBlock.completes entry found form innerIH restIH
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH restIH =>
    intro entry
    exact CellAwareLexicalBodyConditional.completes extension uninitialized semantic selectedBodies
      entry found form conditionFound conditionType conditionTree thenIH elseIH (.inl restIH)
  | terminalBlock unique found form inner stops issued innerIH =>
    intro entry
    exact CellAwareLexicalBodyBlock.stopped entry found form stops innerIH
  | terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    intro entry
    exact CellAwareLexicalBodyConditional.completes extension uninitialized semantic selectedBodies
      entry found form conditionFound conditionType conditionTree thenIH elseIH (.inr ⟨thenStops,elseStops⟩)

include definitions registered extension uninitialized semantic selectedBodies in
theorem reflects {context scope mode statements expected type code}
    (tree : CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError (.initial checked) invocation.source
      (CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation) (reasonAt := reasonAt))
      context scope mode statements expected type code)
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    {value : Value} {finalStore : Store}
    (completed : Evaluates entry.actual entry.store (code.rename entry.embedding) value finalStore) :
    ∃ result : Result entry registry faults mode statements expected type code,
      result.value = value ∧ result.store = finalStore := by
  obtain ⟨result⟩  := completes (registry := registry) definitions registered extension uninitialized semantic selectedBodies tree entry
  have same := evaluation_deterministic result.evaluated completed
  exact ⟨result,same⟩

include definitions registered extension uninitialized semantic selectedBodies in
theorem preserves {context scope mode statements expected type code}
    (tree : CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError (.initial checked) invocation.source
      (CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation) (reasonAt := reasonAt))
      context scope mode statements expected type code)
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    {size finalContext outcome after}
    (trace : Staging.Recursive.Size.StatementsIn program registry mode size invocation context entry.environment entry.heap
      statements finalContext outcome after) :
    ∃ result : Result entry registry faults mode statements expected type code,
      finalContext = result.finalContext ∧ outcome = result.outcome.embed ∧ after = result.after := by
  obtain ⟨result⟩ := completes (registry := registry) definitions registered extension uninitialized semantic selectedBodies tree entry
  exact ⟨result,result.determines trace⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
/-! Ordinary Source lifting uses actual lexical and heap typing. These facts
come from the genuine closure and its parameter allocation; native evaluation
is not an input to this Source step. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
open Core Frontend SourceInference
open Staging.Recursive
open SelectedCompilationStageScopedLiftBounds (PlainStatements)

variable {program : Program} {registry : Registry} {invocation : Scope}

structure State (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop where
  runtime : Dynamic.SourceRuntimeValid program context invocation.source
  covers : invocation.evidence.Covers context
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  heapTyped : Dynamic.HeapWellTyped context heap

def embed : Dynamic.ControlOutcome → BodyOutcome
  | .returned value => .returned value
  | .fallthrough environment => .fallthrough environment
  | .breaking environment => .breaking environment
  | .continuing environment => .continuing environment
  | .fault reason => .fault (.semantic reason)

def Post (context : SourceSemantics.Context) (before after : Dynamic.Heap) : Dynamic.ControlOutcome → Prop
  | .fault _ => True
  | _ => Dynamic.HeapWellTyped context after ∧ Dynamic.HeapTypesExtend before after

def Lifts (context : SourceSemantics.Context) (mode : Bool) (statements : List StatementId) : Prop :=
  ∀ {environment before}, State (program := program) (invocation := invocation) context environment before →
    ∀ {size finalContext outcome after}, PlainStatements program mode size invocation context environment before
      statements finalContext outcome after →
    StatementsIn program registry mode invocation context environment before statements finalContext (embed outcome) after ∧
      Post context before after outcome

theorem expression {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context scope id lowered}
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope id lowered)
    (unique : NodeOccurrencesUnique invocation.source)
    {size environment before outcome after}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context invocation.evidence invocation.source
      environment before id outcome after) :
    Staging.Recursive.Expression program registry invocation context environment before id (Lifting.embed outcome) after := by
  obtain ⟨_,_,_,_,_,tree⟩ := certificate
  exact CellAwareSourceReadProductLifting.exact_trace tree unique trace.sound

theorem expression_typed (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context scope id lowered node}
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope id lowered)
    (found : invocation.source.lookupExpression? id = some node)
    {size environment before value after}
    (state : State (program := program) (invocation := invocation) context environment before)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context invocation.evidence invocation.source
      environment before id (.value value) after) :
    Dynamic.ValueHasType context after value node.type ∧
      State (program := program) (invocation := invocation) context environment after ∧
      Dynamic.HeapTypesExtend before after := by
  have lifted := expression (registry := registry) certificate state.runtime.graph.nodeOccurrencesUnique trace
  obtain ⟨_, graded⟩ := Staging.Recursive.Size.Expression.of_trace lifted
  obtain ⟨_,_,actual,actualFound,typed,_⟩ := certificate
  cases Option.some.inj (actualFound.symm.trans found)
  have preserved := Staging.Recursive.SelectedPreservation.expression selectedBodies
    state.runtime state.covers state.locals state.heapTyped typed graded
  exact ⟨preserved.value_typed value rfl,
    ⟨state.runtime,state.covers,state.locals.mono preserved.heap_extends,preserved.heap_typed⟩,
    preserved.heap_extends⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourcePrefixes
/-! Original ordinary declarations and terminal leaves lift without a native
store. Each successful prefix transports the actual Source heap typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
open Core Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}

theorem nil {context mode} : Lifts (program := program) (registry := registry) (invocation := invocation) context mode [] := by
  intro environment before state size finalContext outcome after trace
  obtain ⟨rfl,rfl,rfl⟩ := SelectedCompilationStageScopedTerminalInversion.nil trace
  exact ⟨.nil,state.heapTyped,.refl _⟩

theorem returnUnit {context mode id node rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  obtain ⟨rfl,rfl,rfl⟩ := SelectedCompilationStageScopedTerminalInversion.return_unit state.runtime.graph.nodeOccurrencesUnique found form trace
  exact ⟨.returnUnit (lookupStatement?_sound found) form,state.heapTyped,.refl _⟩

theorem terminal (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context scope id lowered node mode statements}
    (head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation id mode statements)
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope id lowered)
    (found : invocation.source.lookupExpression? id = some node) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode statements := by
  intro environment before state size finalContext outcome after trace
  obtain ⟨child,plain,_,rfl,rfl,childTrace⟩ := SelectedCompilationStageScopedTerminalInversion.child_of_body state.runtime.graph.nodeOccurrencesUnique head trace
  have lifted := expression (registry := registry) certificate state.runtime.graph.nodeOccurrencesUnique childTrace
  obtain ⟨_,measured⟩ := Size.Expression.of_trace lifted
  cases plain with
  | value value =>
    obtain ⟨_,reached,extension⟩ := expression_typed selectedBodies certificate found state childTrace
    exact ⟨(head.trace measured).sound,reached.heapTyped,extension⟩
  | fault reason => exact ⟨(head.trace measured).sound,trivial⟩

theorem State.allocate {context nextContext environment before binder value location after}
    (state : State (program := program) (invocation := invocation) context environment before)
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (typed : Dynamic.OptionalValueHasType context before value binder.scheme.body)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body value location after) :
    State (program := program) (invocation := invocation) nextContext ((binder.id,location)::environment) after := by
  refine ⟨state.runtime.transport (.ofBinderExtends extended),
    (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers state.covers,?_,
    (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mp (state.heapTyped.allocate typed allocated)⟩
  cases extended
  exact .cons allocated.reads_new rfl (.ordinary mono rfl)
    (state.locals.mono (.of_allocation allocated))

theorem Post.restore {context nextContext before middle after owner binder outcome}
    (extended : BinderExtends owner context binder nextContext)
    (extension : Dynamic.HeapTypesExtend before middle)
    (post : Post nextContext middle after outcome) : Post context before after outcome := by
  cases outcome <;> try exact trivial
  all_goals exact ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr post.1,extension.trans post.2⟩

theorem absent {context nextContext mode id node binder rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) nextContext mode rest) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  obtain ⟨_,_,_,_,allocated,tail⟩ := SelectedCompilationStageLexicalInversion.absent state.runtime.graph.nodeOccurrencesUnique found form mono extended trace
  obtain ⟨lifted,post⟩ := remaining (state.allocate mono extended (.none _) allocated) tail
  exact ⟨.letUninitialized (lookupStatement?_sound found) form mono extended allocated lifted,
    post.restore extended (.of_allocation allocated)⟩

theorem initialized (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context nextContext scope mode id node binder initializer initializerNode lowered rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (initializerFound : invocation.source.lookupExpression? initializer = some initializerNode)
    (sourceType : initializerNode.type = binder.scheme.body)
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope initializer lowered)
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) nextContext mode rest) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  rcases SelectedCompilationStageLexicalInversion.initialized state.runtime.graph.nodeOccurrencesUnique found form mono extended trace with failed | done
  · obtain ⟨_,_,_,rfl,rfl,child⟩ := failed
    exact ⟨.letFault (lookupStatement?_sound found) form mono (expression certificate state.runtime.graph.nodeOccurrencesUnique child),trivial⟩
  · obtain ⟨_,_,_,_,_,_,_,_,child,allocated,tail⟩ := done
    have first := expression (registry := registry) certificate state.runtime.graph.nodeOccurrencesUnique child
    obtain ⟨typed,reached,extension⟩ := expression_typed selectedBodies certificate initializerFound state child
    obtain ⟨lifted,post⟩ := remaining (reached.allocate mono extended (.some (sourceType ▸ typed)) allocated) tail
    exact ⟨.letInitialized (lookupStatement?_sound found) form first mono extended allocated lifted,
      post.restore extended (extension.trans (.of_allocation allocated))⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceScopes
/-! Exact ordinary Source lifting restores lexical environments at each block
while retaining every reached heap change. Only an actual fallthrough uses the suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
open Core Frontend SourceInference Staging.Recursive
open SelectedCompilationStageScopedLiftBounds (PlainStatements)
variable {program : Program} {registry : Registry} {invocation : Scope}

theorem Post.trans {context before middle after outcome}
    (extension : Dynamic.HeapTypesExtend before middle)
    (post : Post context middle after outcome) : Post context before after outcome := by
  cases outcome <;> try exact trivial
  all_goals exact ⟨post.1,extension.trans post.2⟩

theorem discard (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context scope mode semicolon id node expression expressionNode lowered rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
    (continuing : semicolon = true ∨ mode = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope expression lowered)
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) context mode rest) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  rcases SelectedCompilationStageDiscardInversion.child_and_tail state.runtime.graph.nodeOccurrencesUnique found form continuing trace with failed | done
  · obtain ⟨_,_,_,rfl,rfl,child⟩ := failed
    exact ⟨.expressionFault (lookupStatement?_sound found) form (CellAwareOrdinaryBodySourceState.expression certificate state.runtime.graph.nodeOccurrencesUnique child),trivial⟩
  · obtain ⟨_,_,_,_,_,_,child,tail⟩ := done
    have first := CellAwareOrdinaryBodySourceState.expression (registry := registry) certificate state.runtime.graph.nodeOccurrencesUnique child
    obtain ⟨_,reached,extension⟩ := expression_typed selectedBodies certificate expressionFound state child
    obtain ⟨lifted,post⟩ := remaining reached tail
    refine ⟨?_,post.trans extension⟩
    rcases continuing with rfl | rfl
    · exact .discard (lookupStatement?_sound found) form first lifted
    · cases semicolon with
      | false => exact .discardValue (lookupStatement?_sound found) form first lifted
      | true => exact .discard (lookupStatement?_sound found) form first lifted

theorem block {context mode id node statements rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Lifts (program := program) (registry := registry) (invocation := invocation) context false statements)
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) context mode rest ∨
      GenericLexicalStatements.Stopped invocation.source statements) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  have unique := state.runtime.graph.nodeOccurrencesUnique
  have notTail : ∀ expression, node.form ≠ .expression expression false := by
    intro expression same; rw [form] at same; cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨_,reason,_,rfl,rfl,failed⟩ | ⟨_,_,stopped,executed⟩ | ⟨_,_,middleContext,nextEnvironment,middle,_,_,executed,tail⟩
  · obtain ⟨_,innerContext,_,innerTrace⟩ := SelectedCompilationStageScopedSourceInversion.block_fault unique found form failed
    obtain ⟨lifted,_⟩ := inner state (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .fault innerTrace)
    exact ⟨.blockFault (lookupStatement?_sound found) form lifted,trivial⟩
  · obtain ⟨_,innerContext,innerOutcome,_,sameContext,sameOutcome,innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst finalContext outcome
    obtain ⟨lifted,post⟩ := inner state (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .control innerTrace)
    cases innerOutcome with
    | returned value => exact ⟨.blockReturned (lookupStatement?_sound found) form lifted,post⟩
    | breaking innerEnvironment => exact ⟨.blockBreaking (lookupStatement?_sound found) form lifted,post⟩
    | continuing innerEnvironment => exact ⟨.blockContinuing (lookupStatement?_sound found) form lifted,post⟩
    | fault reason => exact ⟨.blockFault (lookupStatement?_sound found) form lifted,trivial⟩
    | fallthrough innerEnvironment =>
      rcases stopped with impossible | rfl
      · cases impossible
      · exact ⟨.blockFallthrough (lookupStatement?_sound found) form lifted .nil,post⟩
  · obtain ⟨_,innerContext,innerOutcome,_,sameContext,restored,innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl,Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      obtain ⟨lifted,post⟩ := inner state (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .control innerTrace)
      rcases remaining with remaining | stopped
      · have reached : State (program := program) (invocation := invocation) context environment middle :=
          ⟨state.runtime,state.covers,state.locals.mono post.2,post.1⟩
        obtain ⟨restTrace,restPost⟩ := remaining reached tail
        exact ⟨.blockFallthrough (lookupStatement?_sound found) form lifted restTrace,restPost.trans post.2⟩
      · have impossible := stopped.terminates unique false innerTrace.sound
        cases impossible
    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceConditional
/-! Original Source conditions select the same branch. Actual expression
preservation excludes non-Boolean conditions and supplies the reached heap
for the selected body and any live suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
open Core Frontend SourceInference Staging.Recursive
open SelectedCompilationStageScopedLiftBounds (PlainStatements)
variable {program : Program} {registry : Registry} {invocation : Scope}

private def typeHead : TypeSystem.Ty → TypeSystem.Ty
  | .application function _ => typeHead function
  | type => type

private theorem typeHead_applyMany (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty) :
    typeHead (TypeSystem.Ty.applyMany head arguments) = typeHead head := by
  unfold TypeSystem.Ty.applyMany
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rfl

private theorem boolean_of_typed {context : SourceSemantics.Context} {heap value}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : Dynamic.ValueHasType context heap value .bool) : Dynamic.BooleanValue value := by
  generalize typeEq : TypeSystem.Ty.bool = type at typed
  cases typed with
  | bool => trivial
  | unit => simp [TypeSystem.Ty.bool,TypeSystem.Ty.unit] at typeEq
  | word => simp [TypeSystem.Ty.bool,TypeSystem.Ty.word] at typeEq
  | integer => simp [TypeSystem.Ty.bool,TypeSystem.Ty.integer] at typeEq
  | product => cases typeEq
  | proxy => cases typeEq
  | mapping => cases typeEq
  | closure => cases typeEq
  | comptime => cases typeEq
  | builtin function => rw [BuiltinFunctionId.type] at typeEq; cases typeEq
  | constructed valid _ =>
      cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner constructor_eq
          substitution_exact substitution_range payloadTypes_eq resultType_eq =>
          rw [resultType_eq] at typeEq
          have heads := congrArg typeHead typeEq
          simp [TypeSystem.Ty.nominal,typeHead_applyMany,typeHead,TypeSystem.Ty.bool] at heads
  | global valid _ =>
      cases valid with
      | intro signature member declaration_eq substitution_exact substitution_range instantiation_type_eq
          predicates_eq parameterComptime_eq returnComptime_eq =>
          have signatureValid := catalog.functions_semantic signature member
          rw [instantiation_type_eq,signatureValid.scheme_body] at typeEq
          cases typeEq

theorem conditional (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {reasonAt context scope mode id node condition conditionNode conditionCode thenBody elseBody rest}
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : invocation.source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope condition ⟨.bool,conditionCode⟩)
    (branches : ∀ truth : Bool, Lifts (program := program) (registry := registry) (invocation := invocation)
      context false (if truth then thenBody else elseBody.getD []))
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) context mode rest ∨
      ∀ truth : Bool, GenericLexicalStatements.Stopped invocation.source (if truth then thenBody else elseBody.getD [])) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  have unique := state.runtime.graph.nodeOccurrencesUnique
  have notTail : ∀ expression, node.form ≠ .expression expression false := by
    intro expression same; rw [form] at same; cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨_,reason,_,rfl,rfl,failed⟩ | ⟨_,_,stopped,executed⟩ | ⟨_,_,middleContext,nextEnvironment,middle,_,_,executed,tail⟩
  · rcases SelectedCompilationStageConditionalSourceInversion.fault unique found form failed with
      ⟨_,_,test⟩ | ⟨_,value,_,_,rfl,test,invalid,_⟩ | ⟨_,_,truth,_,_,_,_,test,branch⟩
    · exact ⟨.ifConditionFault (lookupStatement?_sound found) form (expression certificate unique (.fault test)),trivial⟩
    · obtain ⟨typed,_,_⟩ := expression_typed selectedBodies certificate conditionFound state (.value test)
      rw [conditionType] at typed
      exact False.elim (invalid (boolean_of_typed (state.runtime.signatures.symm ▸ selectedBodies.signatures) typed))
    · have first := expression (registry := registry) certificate unique (.value test)
      obtain ⟨_,reached,_⟩ := expression_typed selectedBodies certificate conditionFound state (.value test)
      obtain ⟨lifted,_⟩ := branches truth reached (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .fault branch)
      exact ⟨.ifFault (lookupStatement?_sound found) form first lifted,trivial⟩
  · obtain ⟨_,_,truth,_,_,innerOutcome,_,_,sameContext,sameOutcome,test,branch⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique found form executed
    subst finalContext outcome
    have first := expression (registry := registry) certificate unique (.value test)
    obtain ⟨_,reached,extension⟩ := expression_typed selectedBodies certificate conditionFound state (.value test)
    obtain ⟨lifted,post⟩ := branches truth reached (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .control branch)
    cases innerOutcome with
    | returned value => exact ⟨.ifReturned (lookupStatement?_sound found) form first lifted,post.trans extension⟩
    | breaking innerEnvironment => exact ⟨.ifBreaking (lookupStatement?_sound found) form first lifted,post.trans extension⟩
    | continuing innerEnvironment => exact ⟨.ifContinuing (lookupStatement?_sound found) form first lifted,post.trans extension⟩
    | fault reason => exact ⟨.ifFault (lookupStatement?_sound found) form first lifted,trivial⟩
    | fallthrough innerEnvironment =>
      rcases stopped with impossible | rfl
      · cases impossible
      · exact ⟨.ifFallthrough (lookupStatement?_sound found) form first lifted .nil,post.trans extension⟩
  · obtain ⟨_,_,truth,_,_,innerOutcome,_,_,sameContext,restored,test,branch⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique found form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl,Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      have first := expression (registry := registry) certificate unique (.value test)
      obtain ⟨_,reached,extension⟩ := expression_typed selectedBodies certificate conditionFound state (.value test)
      obtain ⟨lifted,post⟩ := branches truth reached (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .control branch)
      rcases remaining with remaining | stopped
      · have nextState : State (program := program) (invocation := invocation) context environment middle :=
          ⟨state.runtime,state.covers,state.locals.mono (extension.trans post.2),post.1⟩
        obtain ⟨restTrace,restPost⟩ := remaining nextState tail
        exact ⟨.ifFallthrough (lookupStatement?_sound found) form first lifted restTrace,
          restPost.trans (extension.trans post.2)⟩
      · have impossible := (stopped truth).terminates unique false branch.sound
        cases impossible
    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceLifting
/-! The actual finite lexical body certificate lifts ordinary Source success
and failure, with reached heaps and lexical scope restoration. No Core run or
body semantic law is required by this construction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceLifting
open Core Frontend SourceInference CellAwareOrdinaryBodySourceState

variable {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

theorem lifts (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {layouts owner active frame globals onError values reasonAt context scope mode statements expected type code}
    (tree : CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError values invocation.source
      (CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt)
      context scope mode statements expected type code) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode statements := by
  induction tree with
  | nil => exact CellAwareOrdinaryBodySourceState.nil
  | returnUnit rest found form => exact returnUnit found form
  | returnValue rest found form expressionFound _ certificate =>
      exact terminal selectedBodies (.returning rest (lookupStatement?_sound found) form) certificate expressionFound
  | tail found form expressionFound _ certificate =>
      exact terminal selectedBodies (.tail (lookupStatement?_sound found) form) certificate expressionFound
  | uninitialized found form mono extended _ _ _ _ _ _ ih =>
      exact absent found form mono extended ih
  | initialized found form mono extended _ initializerFound sourceType initial _ _ _ _ ih =>
      exact initialized selectedBodies found form mono extended initializerFound sourceType initial ih
  | discard found form _ continuing expressionFound certificate _ ih =>
      exact discard selectedBodies found form continuing expressionFound certificate ih
  | block found form _ _ inner remaining => exact block found form inner (.inl remaining)
  | ifThen found form conditionFound conditionType certificate _ _ _ thenLift elseLift remaining =>
      apply conditional selectedBodies found form conditionFound conditionType certificate
      · intro truth; cases truth <;> assumption
      · exact .inl remaining
  | terminalBlock _ found form _ stops _ inner => exact block found form inner (.inr stops)
  | terminalIf _ found form conditionFound conditionType certificate _ _ thenStops elseStops _ thenLift elseLift =>
      apply conditional selectedBodies found form conditionFound conditionType certificate
      · intro truth; cases truth <;> assumption
      · apply Or.inr
        intro truth; cases truth <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalSourceBodyAdmission
/-! The additive source profile admits ordinary initialized declarations
between generalized declarations. Existing suffixes retain their original
profile, and every new initializer uses the same finite expression profile. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalSourceBodyAdmission
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open CellAwareSourceBodyAdmission (Site site?)

inductive Scan (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    Bool → List StatementId → Prop where
  | existing {mode statements}
      (scan : CellAwareSourceBodyAdmission.Scan locals caller active source approved expected mode statements) :
      Scan locals caller active source approved expected mode statements
  | generalizedInitialized {mode id node binder initializer initializerNode parameters result body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (sourceType : node.type = .unit)
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result body)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])
      (site : Site locals caller active source binder initializer)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)
  | initialized {mode id node binder initializer initializerNode rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (sourceType : node.type = .unit)
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (mono : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (value : approved initializer)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)

def scan? (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Scan locals caller active source approved expected mode statements))
  | 0, _, _ => none
  | fuel + 1, mode, statements =>
    match CellAwareSourceBodyAdmission.scan? locals caller active source expression expected (fuel + 1) mode statements with
    | some original => some ⟨.existing original.down⟩
    | none =>
      match statements with
      | [] => none
      | id :: rest =>
        match found : source.lookupStatement? id with
        | none => none
        | some node =>
          match form : node.form with
          | .letDecl binder (some initializer) =>
            if sourceType : node.type = .unit then
              if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
                if declaration : (SourceCoreDataPlaces.declaredBinders source).filter
                    (fun actual => decide (actual.id = binder.id)) = [binder] then
                  match initializerFound : source.lookupExpression? initializer with
                  | none => none
                  | some initializerNode =>
                    if valueType : initializerNode.type = binder.scheme.body then
                      if mono : binder.scheme.quantified = [] then do
                        let ⟨value⟩ ← expression initializer
                        let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                        pure ⟨.initialized found form sourceType declaration mono ordinary initializerFound valueType value remaining⟩
                      else
                        match initializerForm : initializerNode.form with
                        | .lambda _parameters _result _body =>
                          if requirements : initializerNode.requirements = [] then
                            if coercions : initializerNode.coercions = [] then do
                              let site ← site? locals caller active source binder initializer
                              let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                              pure ⟨.generalizedInitialized found form sourceType declaration mono ordinary initializerFound
                                initializerForm valueType requirements coercions site remaining⟩
                            else none
                          else none
                        | _ => none
                    else none
                else none
              else none
            else none
          | _ => none

inductive Syntax (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    SourceSemantics.Context → Bool → List StatementId → Prop where
  | existing {context mode statements}
      (tree : CellAwareSourceBodyAdmission.Syntax locals caller active source approved expected context mode statements) :
      Syntax locals caller active source approved expected context mode statements
  | generalizedInitialized {context nextContext mode id node binder initializer initializerNode parameters result body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result body)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])
      (site : Site locals caller active source binder initializer)
      (remaining : Syntax locals caller active source approved expected nextContext mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | initialized {context nextContext mode id node binder initializer initializerNode rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType source context initializer initializerNode.type)
      (value : approved initializer)
      (remaining : Syntax locals caller active source approved expected nextContext mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original, contains, same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

/-- Context extension and child typing come from the original source checker,
including its generalized declaration rule. -/
theorem Scan.syntax {locals caller active source approved expected mode statements}
    (scan : Scan locals caller active source approved expected mode statements)
    (unique : NodeOccurrencesUnique source) {control : ControlContext} (result : control.returnType = expected)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    Syntax locals caller active source approved expected context mode statements := by
  induction scan generalizing control context final facts with
  | existing original => exact .existing (original.syntax unique result typed)
  | generalizedInitialized found form _ declaration polymorphic ordinary initializerFound initializerForm valueType requirements coercions site _ ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | letInitialized _ monomorphic _ => exact False.elim (polymorphic monomorphic)
    | letInitializedGeneralized _ _ _ _ extended =>
      exact .generalizedInitialized found form declaration polymorphic extended ordinary initializerFound
        initializerForm valueType requirements coercions site (ih result tail)
  | initialized found form _ declaration mono ordinary initializerFound valueType value _ ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    have member : _ ∈ SourceCoreDataPlaces.declaredBinders source :=
      (List.mem_filter.mp (declaration ▸ List.mem_singleton_self _)).1
    cases original with
    | letInitialized initial _ extended =>
      exact .initialized found form member mono extended ordinary initializerFound valueType
        (expression_at unique initializerFound initial) value (ih result tail)
    | letInitializedGeneralized quantified _ _ _ _ => exact False.elim (quantified mono)

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalSourceBodyAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNativeBodyTree
/-! The additive lexical tree permits ordinary and generalized declarations
in any order, while retaining the existing terminal body receipt unchanged.
Each declaration keeps its actual compiler allocation and source context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNativeBodyTree
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open TypedLexicalWhile (initializedRequest sequence)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (reasonAt : ExpressionId → Word) :
    SourceSemantics.Context → SourceCoreLocalCell.Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | existing {sourceContext scope mode statements expected type code}
      (tree : CellAwareNativeBodyTree.Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode statements expected type code) :
      Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode statements expected type code
  | generalizedInitialized {sourceContext nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders (source named)).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends (source named).owner sourceContext binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = [])
      (coercions : initializerNode.coercions = [])
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key [] (source named) binder initializer)
      (initial : GeneralizedLocalInitializerPackets.Receipt prepared
        (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
          (context prepared named) scope initializer reasonAt) site.binding [] lowered)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      {captured : Expr}
      (copied : SourceCoreSourceCells.copyScope (some (CallableIndexedNamedGeneration.allocator prepared named))
        (source named) scope (fun index => index)
        (CellAwareGeneralizedSnapshotCode.snapshotInner lowered.type lowered.expression annotation.expression) =
          .ok captured)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (CellAwareGeneralizedSnapshotCode.snapshotSequence type captured body)
  | initialized {sourceContext nextContext scope mode id node binder initializer initializerNode rest expected type lowered body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner sourceContext binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) sourceContext initializer initializerNode.type)
      (value : certificates sourceContext scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (sequence type lowered.expression annotation.expression body)

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNativeBodyTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNativeBodyCollectors
/-! The native body collector follows the actual named compiler and its
marked lexical allocations. Source typing supplies context extension; the
accepted initializer supplies the complete ordered candidate bundle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNativeBodyCollectors
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open CompatibleEncoding (bind_ok)
open GeneralizedLocalInitializerCompilation (namedInputs)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩


variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : Compilation prepared named diagnostics namedCode)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {approved : ExpressionId → Prop} {administrative : Core.Context} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreLoops.Policy}

/-- Only finite static expression and candidate profiles are inputs. All
compiler actions and native child typing are recovered from the accepted body. -/
theorem collected
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (expressionPolicy : policy.lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
        ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
        prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
        diagnostics (context prepared named) prepared.base.callableContext none none)
    (allocationPolicy : policy.sourceCells = some (CallableIndexedNamedGeneration.allocator prepared named))
    (profiles : ∀ {scope binder initializer}
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
        (source named) binder initializer) childFuel,
      ∀ candidate ∈ site.binding.atContext [],
        Nonempty (GeneralizedLocalInitializerPackets.BindingProfile
          (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
            (context prepared named) scope initializer reasonAt) site.binding candidate))
    (bodyProfiles : ∀ {scope binder initializer}
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
        (source named) binder initializer) childFuel,
      ∀ candidate ∈ site.binding.atContext [], Nonempty (GeneralizedLocalBodyProfile.Profile
        (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).locals
        (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).current.owner
        candidate.source initializer))
    (children : ∀ sourceContext,
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext →
      approved id → (source named).lookupExpression? id = some node →
      ExpressionHasType (source named) sourceContext id node.type →
      policy.lowerExpression fuel (source named) scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType prepared.layouts.definitions → certificates sourceContext scope id lowered)
    {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : CellAwareLexicalSourceBodyAdmission.Syntax prepared.base.locals named.signature.key []
      (source named) approved expected sourceContext mode statements)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    {fuel : Nat} {type : Ty} {code : Expr} {escaped : Word} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel (source named) scope statements
      type reasonAt mode escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType prepared.layouts.definitions) :
    CellAwareLexicalNativeBodyTree.Tree prepared named compiled certificates administrative reasonAt
      sourceContext scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | existing original =>
    exact .existing (CellAwareNativeBodyCollectors.collected compiled record readPolicy expressionPolicy
      allocationPolicy profiles bodyProfiles children original declarations accepted nativeTyped)
  | @generalizedInitialized sourceContext nextContext mode id node binder initializer initializerNode parameters result body rest found form declaration polymorphic extended ordinary initializerFound initializerForm valueType requirements coercions site remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨payload, _projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst payload
      obtain ⟨tailCode, generatedTail, accepted⟩ := bind_ok accepted
      have generalizedBinder : binder.scheme.quantified.isEmpty = false := by
        cases quantified : binder.scheme.quantified with
        | nil => exact absurd quantified polymorphic
        | cons _ _ => rfl
      simp only [generalizedBinder, Bool.false_eq_true, ↓reduceIte, SourceCoreSourceCells.letInitializedSnapshot,
        allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      obtain ⟨captured, copied, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      have actualGenerated := expressionPolicy ▸ generated
      obtain ⟨childFuel, fuelEq, binding, located, ⟨initial⟩⟩ :=
        GeneralizedLocalInitializerCompilation.of_named_contextual compiled record
          initializerFound initializerForm site.selected actualGenerated
      have sameBinding : binding = site.binding := by
        rw [site.selectedBinder] at located
        exact Except.ok.inj (located.symm.trans site.located)
      subst binding
      subst fuel
      obtain ⟨initial⟩ := GeneralizedLocalInitializerPackets.of_receipt prepared initial
        (profiles site childFuel) (bodyProfiles site childFuel) rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨⟨_, childTyped⟩, tailTyped⟩ := CellAwareGeneralizedSnapshotTyping.snapshot_children allocation annotation
        same copied (fun _ _ _ found => CellAwareGeneralizedSnapshotTyping.scope_cell found) nativeTyped
      have tail := ih
        (CellAwareNativeBodyCollectors.scope_generalized lowered.type declarations declaration polymorphic extended)
        generatedTail tailTyped
      exact .generalizedInitialized found form declaration polymorphic extended ordinary
        initializerFound initializerForm valueType requirements coercions site initial
        (initial.typed childTyped) allocation annotation same copied tail
  | @initialized sourceContext nextContext mode id node binder initializer initializerNode rest found form member mono extended ordinary initializerFound valueType typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨payload, _projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst payload
      obtain ⟨tailCode, generatedTail, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have tail := ih (CompatibleMatchArmScopes.scope_bind lowered.type declarations member extended)
        generatedTail (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      exact .initialized found form member mono extended ordinary initializerFound valueType typed
        (children sourceContext declarations value initializerFound typed generated childTyped)
        allocation annotation same tail

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNativeBodyCollectors
end
