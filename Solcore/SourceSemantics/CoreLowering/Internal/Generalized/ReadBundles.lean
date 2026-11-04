import Solcore.Frontend.SourceCoreGeneralFunctions
import Solcore.Frontend.SourceCoreLocalPolymorphism
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure
import Solcore.SourceSemantics.CoreLowering.CallableAppliedRuntimeMaterialization
import Solcore.SourceSemantics.CoreLowering.CallableIndexedHistory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableLedger
import Solcore.SourceSemantics.CoreLowering.CallableIndependentSourceViews
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.CallableClosedSchemeSubstitutionAgreement
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.Dynamic.Preservation

/-!
# Generalized locals: read bundles and descriptors

Instance compilation, read receipts and bundles, the descriptor heap and its origins, and call frames and prefixes.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceCompilation
/-! Receipts for the literal instance callback used by generalized local
initializers. The actual evidence preparation and recursive contextual
compilation retain the candidate's full key and its distinct read parent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceCompilation
open Core Frontend SourceInference SourceCoreLocalPolymorphism

structure Inputs where
  program : CheckedProgram
  representation : SourceCoreGeneralFunctions.Representation
  signatures : ProgramSignatures
  locals : Catalog
  candidateParents : List SourceCoreLocalEvidence.Prepared
  assignments : SourceCoreAssignmentFaultSites.Table
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  current : SourceCoreFunctions.Context
  native : Option SourceCoreGeneralFunctions.CallableContext
  parent : Option SourceCoreLocalEvidence.Prepared
  budget : Nat
  fuel : Nat
  initializer : ExpressionId
  scope : SourceCoreBasic.Scope
  reasonAt : ExpressionId → Core.Word

def Inputs.child (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) :
    Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr :=
  SourceCoreGeneralFunctions.lowerContextualExpression inputs.program inputs.representation inputs.signatures
    inputs.locals inputs.candidateParents inputs.assignments inputs.diagnostics
    { inputs.current with solvedRequirements := prepared.caller.function.solvedRequirements } inputs.native
    (some prepared) (some inputs.initializer) (min inputs.budget inputs.fuel)
    prepared.source inputs.scope inputs.initializer inputs.reasonAt

/-- This is the same callback passed to lowerInitializer by the contextual
compiler, with its inputs named for use in static certificates. -/
def compile (inputs : Inputs) (candidate : Instance) : Except SourceCoreLocalPolymorphism.Error Core.Expr := do
  let emission ← (SourceCoreLocalEvidence.prepareForEmission inputs.program inputs.current.plan candidate
    inputs.parent inputs.candidateParents).mapError fun _ =>
      SourceCoreLocalPolymorphism.Error.initializerMetadataMismatch inputs.initializer
  let lowered ← (inputs.child emission.prepared).mapError SourceCoreLocalPolymorphism.Error.metadata
  (SourceCoreBasic.ensureType (.occurrence inputs.initializer.occurrence) candidate.type lowered.type)
    |>.mapError SourceCoreLocalPolymorphism.Error.metadata
  match lowered.expression with
  | .inRight .word closure => pure closure
  | _ => throw (.initializerMetadataMismatch inputs.initializer)

structure Receipt (inputs : Inputs) (candidate : Instance) (raw : Core.Expr) where
  emission : SourceCoreLocalEvidence.Emission inputs.program inputs.current.plan candidate inputs.parent
  prepared : SourceCoreLocalEvidence.prepareForEmission inputs.program inputs.current.plan candidate
    inputs.parent inputs.candidateParents = .ok emission
  lowered : SourceCoreBasic.LoweredExpr
  compiled : inputs.child emission.prepared = .ok lowered
  nativeType : candidate.type = lowered.type
  extracted : lowered.expression = .inRight .word raw

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

theorem of_accepted {inputs : Inputs} {candidate : Instance} {raw : Core.Expr}
    (accepted : compile inputs candidate = .ok raw) : Nonempty (Receipt inputs candidate raw) := by
  unfold compile at accepted
  obtain ⟨emission, prepared, accepted⟩ := bind_ok accepted
  have prepared := mapError_ok prepared
  obtain ⟨lowered, compiled, accepted⟩ := bind_ok accepted
  have compiled := mapError_ok compiled
  obtain ⟨_, checked, accepted⟩ := bind_ok accepted
  have nativeType : candidate.type = lowered.type := by
    by_cases same : candidate.type = lowered.type
    · exact same
    · simp [SourceCoreBasic.ensureType, same, Except.mapError] at checked
  split at accepted
  · next expression extracted =>
      cases accepted
      exact ⟨⟨emission, prepared, lowered, compiled, nativeType, extracted⟩⟩
  · cases accepted

/-- Reconstructing the successful callback uses the same factory receipt and
recursive compiler result; no alternate metadata or candidate is introduced. -/
theorem Receipt.accepted {inputs : Inputs} {candidate : Instance} {raw : Core.Expr}
    (receipt : Receipt inputs candidate raw) : compile inputs candidate = .ok raw := by
  simp [compile, receipt.prepared, receipt.compiled, SourceCoreBasic.ensureType,
    receipt.nativeType, receipt.extracted, Except.mapError, bind, Except.bind, pure, Except.pure]

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceCompilation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
/-! A successful generalized local read selects an exact cumulative instance
from the stored heterogeneous bundle. These receipts retain the compiler's
original and contextual nodes, native cell, and product projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

/-- Every field is an observation of the actual local-read compiler. The
complete substitution, rather than the candidate's result type, selects it. -/
structure Certificate (catalog : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (scope : Scope) (id : ExpressionId) (reason : Core.Word)
    (lowered : SourceCoreBasic.LoweredExpr) where
  sourceOwner : source.owner = caller.declaration
  readOwner : id.occurrence.owner = source.owner
  node : ExpressionNode
  nodeFound : source.lookupExpression? id = some node
  binder : Resolved.LocalId
  nodeForm : ∃ name, node.form = .reference name (.local binder)
  binderOwner : binder.owner = source.owner
  binding : Binding
  bindingFound : catalog.binding caller binder = .ok binding
  original : ExpressionNode
  originalFound : binding.source.lookupExpression? id = some original
  originalForm : ∃ name, original.form = .reference name (.local binder)
  rawType : active.apply original.rawType = node.rawType
  child : Substitution
  matched : SourceSpecialization.matchClosedSchemeInstance?
    (Scheme.apply active binding.binder.scheme) (active.apply original.rawType) = some child
  candidate : Instance
  instanceIndex : Nat
  selected : (binding.atContext active).zipIdx.filter (fun entry =>
    decide (entry.1.origin.substitution = child.compose active)) = [(candidate, instanceIndex)]
  resultType : node.type = candidate.origin.substitution.apply binding.binder.scheme.body
  index : Nat
  payloadType : Core.Ty
  slot : SourceCoreLocalCell.lookup? scope binder = some (index, payloadType)
  bundleType : binding.bundleType active = payloadType
  projection : Core.Expr
  projected : ProductBundle.project? ((binding.atContext active).map (·.type))
    instanceIndex (.var 0) = some projection
  emitted : lowered = ⟨candidate.type,
    SourceCoreLocalPolymorphism.read payloadType candidate.type (.var index) projection reason⟩

private theorem bind_ok {α β ε : Type} {computation : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem of_accepted {catalog : Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : lowerRead catalog caller active source scope id reason = .ok lowered) :
    Nonempty (Certificate catalog caller active source scope id reason lowered) := by
  unfold lowerRead at accepted
  dsimp only at accepted
  by_cases sourceOwner : source.owner = caller.declaration
  · rw [if_neg (not_not_intro sourceOwner)] at accepted
    try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
    by_cases readOwner : id.occurrence.owner = source.owner
    · rw [if_neg (not_not_intro readOwner)] at accepted
      try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
      cases nodeFound : source.lookupExpression? id with
      | none => simp [nodeFound, throw, throwThe, MonadExceptOf.throw] at accepted
      | some node =>
        simp only [nodeFound] at accepted
        cases nodeForm : node.form <;>
          try (solve | simp [nodeForm, throw, throwThe, MonadExceptOf.throw] at accepted)
        next name resolution =>
          cases resolution <;>
            try (solve | simp [nodeForm, throw, throwThe, MonadExceptOf.throw] at accepted)
          next binder =>
            simp only [nodeForm] at accepted
            by_cases binderOwner : binder.owner = source.owner
            · rw [if_neg (not_not_intro binderOwner)] at accepted
              try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
              obtain ⟨binding, bindingFound, accepted⟩ := bind_ok accepted
              try dsimp only at accepted
              cases originalFound : binding.source.lookupExpression? id with
              | none => simp [originalFound, throw, throwThe, MonadExceptOf.throw] at accepted
              | some original =>
                simp only [originalFound] at accepted
                cases originalForm : original.form <;>
                  try (solve | simp [originalForm, throw, throwThe, MonadExceptOf.throw] at accepted)
                next originalName resolution =>
                  cases resolution <;>
                    try (solve | simp [originalForm, throw, throwThe, MonadExceptOf.throw] at accepted)
                  next originalBinder =>
                    simp only [originalForm] at accepted
                    by_cases sameBinder : originalBinder = binder
                    · subst originalBinder
                      by_cases rawType : active.apply original.rawType = node.rawType
                      · have valid : (decide (binder ≠ binder) ||
                            decide (active.apply original.rawType ≠ node.rawType)) ≠ true := by
                          simp [rawType]
                        rw [if_neg valid] at accepted
                        try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
                        cases matched : SourceSpecialization.matchClosedSchemeInstance?
                            (Scheme.apply active binding.binder.scheme) (active.apply original.rawType) with
                        | none => simp [matched, throw, throwThe, MonadExceptOf.throw] at accepted
                        | some child =>
                          simp only [matched] at accepted
                          cases selected : (binding.atContext active).zipIdx.filter (fun entry =>
                              decide (entry.1.origin.substitution = child.compose active)) with
                          | nil => simp [selected, throw, throwThe, MonadExceptOf.throw] at accepted
                          | cons first rest =>
                            cases rest with
                            | cons next tail => simp [selected, throw, throwThe, MonadExceptOf.throw] at accepted
                            | nil =>
                              obtain ⟨candidate, instanceIndex⟩ := first
                              simp only [selected] at accepted
                              by_cases resultType : node.type =
                                  candidate.origin.substitution.apply binding.binder.scheme.body
                              · rw [if_neg (not_not_intro resultType)] at accepted
                                try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
                                cases slot : SourceCoreLocalCell.lookup? scope binder with
                                | none => simp [slot, throw, throwThe, MonadExceptOf.throw] at accepted
                                | some slotValue =>
                                  obtain ⟨index, payloadType⟩ := slotValue
                                  simp only [slot] at accepted
                                  obtain ⟨_, checked, accepted⟩ := bind_ok accepted
                                  have bundleType : binding.bundleType active = payloadType := by
                                    by_cases same : binding.bundleType active = payloadType
                                    · exact same
                                    · simp [SourceCoreBasic.ensureType, same, Except.mapError] at checked
                                  cases projected : ProductBundle.project?
                                      ((binding.atContext active).map (·.type)) instanceIndex (.var 0) with
                                  | none => simp [projected, throw, throwThe, MonadExceptOf.throw] at accepted
                                  | some projection =>
                                    simp only [projected, Except.ok.injEq] at accepted
                                    exact ⟨{
                                      sourceOwner, readOwner, node, nodeFound, binder,
                                      nodeForm := ⟨name, nodeForm⟩, binderOwner,
                                      binding, bindingFound, original, originalFound,
                                      originalForm := ⟨originalName, originalForm⟩,
                                      rawType, child, matched, candidate, instanceIndex, selected,
                                      resultType, index, payloadType, slot, bundleType,
                                      projection, projected, emitted := accepted.symm
                                    }⟩
                              · simp [resultType, throw, throwThe, MonadExceptOf.throw] at accepted
                      · simp [rawType, throw, throwThe, MonadExceptOf.throw] at accepted
                    · simp [sameBinder, throw, throwThe, MonadExceptOf.throw] at accepted
            · simp [binderOwner, throw, throwThe, MonadExceptOf.throw] at accepted
    · simp [readOwner, throw, throwThe, MonadExceptOf.throw] at accepted
  · simp [sourceOwner, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

variable {catalog : Catalog} {caller : Key} {active : Substitution}
  {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
  {lowered : SourceCoreBasic.LoweredExpr}

theorem Certificate.candidate_at
    (receipt : Certificate catalog caller active source scope id reason lowered) :
    (receipt.binding.atContext active)[receipt.instanceIndex]? = some receipt.candidate := by
  have member : (receipt.candidate, receipt.instanceIndex) ∈
      (receipt.binding.atContext active).zipIdx.filter (fun entry =>
        decide (entry.1.origin.substitution = receipt.child.compose active)) := by
    rw [receipt.selected]
    exact List.mem_singleton_self _
  exact List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp member).1

theorem Certificate.candidate_key
    (receipt : Certificate catalog caller active source scope id reason lowered) :
    receipt.candidate.origin.substitution = receipt.child.compose active := by
  have member : (receipt.candidate, receipt.instanceIndex) ∈
      (receipt.binding.atContext active).zipIdx.filter (fun entry =>
        decide (entry.1.origin.substitution = receipt.child.compose active)) := by
    rw [receipt.selected]
    exact List.mem_singleton_self _
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- The emitted position is unique even if different instances have equal
native function types. -/
theorem Certificate.unique_candidate
    (receipt : Certificate catalog caller active source scope id reason lowered)
    {candidate : Instance} {index : Nat}
    (stored : (receipt.binding.atContext active)[index]? = some candidate)
    (key : candidate.origin.substitution = receipt.child.compose active) :
    candidate = receipt.candidate ∧ index = receipt.instanceIndex := by
  have member : (candidate, index) ∈
      (receipt.binding.atContext active).zipIdx.filter (fun entry =>
        decide (entry.1.origin.substitution = receipt.child.compose active)) :=
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr stored, by simpa using key⟩
  rw [receipt.selected] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleReadMeaning
/-! Runtime selection of a generalized local instance follows the exact
candidate position emitted by the compiler. The row can contain different
native types; selecting a field leaves the shared store unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleReadMeaning
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

theorem project_evaluates {types : List Core.Ty} {values : List Core.Value}
    {index : Nat} {native : Core.Value} {bundle projection : Core.Expr}
    {environment : Core.Environment} {before after : Core.Store}
    (lengths : values.length = types.length)
    (found : values[index]? = some native)
    (selected : ProductBundle.project? types index bundle = some projection)
    (evaluated : Core.Evaluates environment before bundle (ProductBundle.value values) after) :
    Core.Evaluates environment before projection native after := by
  induction types generalizing values index bundle projection with
  | nil =>
      have empty : values = [] := by simpa using lengths
      simp [empty] at found
  | cons head rest ih =>
      cases values with
      | nil => simp at lengths
      | cons value tail =>
        cases rest with
        | nil =>
            have empty : tail = [] := by simpa using lengths
            subst tail
            cases index with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                simp only [ProductBundle.project?, Option.some.injEq] at selected
                subst native
                subst projection
                exact evaluated
            | succ index => simp at found
        | cons next remaining =>
            cases tail with
            | nil => simp at lengths
            | cons nextValue remainingValues =>
                cases index with
                | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                    simp only [ProductBundle.project?, Option.some.injEq] at selected
                    subst native
                    subst projection
                    exact .first evaluated
                | succ index =>
                    exact ih (by simpa using lengths) (by simpa using found)
                      selected (.second evaluated)

variable {catalog : Catalog} {caller : Key} {active : Substitution}
  {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
  {lowered : SourceCoreBasic.LoweredExpr}

/-- A row relation authenticates each stored candidate independently. Its
selection proof needs no equation between the different candidate types. -/
theorem related_selected {relation : Instance → Core.Value → Prop}
    {instances : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise relation instances values)
    {index : Nat} {candidate : Instance}
    (found : instances[index]? = some candidate) :
    ∃ native, values[index]? = some native ∧ relation candidate native := by
  induction rows generalizing index with
  | nil => simp at found
  | @cons head native rest tail related rows ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst candidate
          exact ⟨native, rfl, related⟩
      | succ index => exact ih (by simpa using found)

theorem row_length {relation : Instance → Core.Value → Prop}
    {instances : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise relation instances values) :
    values.length = instances.length := by
  induction rows with
  | nil => rfl
  | cons _ _ ih => simpa using ih

/-- The actual lowering reads the mapped optional cell, then projects its
selected candidate without changing the heap or consulting another instance. -/
theorem preserves
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {relation : Instance → Core.Value → Prop} {values : List Core.Value}
    {environment : Core.Environment} {store : Core.Store} {location : Core.Location}
    (rows : ProductBundle.Pointwise relation (receipt.binding.atContext active) values)
    (reference : environment[receipt.index]? =
      some (.cellRef (OptionalCell.cellType receipt.payloadType) location))
    (read : store.read? location = some (.inRight .unit (ProductBundle.value values))) :
    ∃ native, relation receipt.candidate native ∧
      Core.Evaluates environment store lowered.expression (.inRight .word native) store := by
  obtain ⟨native, found, related⟩ := related_selected rows receipt.candidate_at
  refine ⟨native, related, ?_⟩
  rw [receipt.emitted]
  exact SourceCoreLocalPolymorphism.read_success
    (OptionalCell.read_success reason (.var reference) read)
    (project_evaluates (by simpa using row_length rows) found receipt.projected (.var rfl))

/-- Any finite native execution of the same emitted read returns that same
selected payload and retains the store. -/
theorem reflects
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {relation : Instance → Core.Value → Prop} {values : List Core.Value}
    {environment : Core.Environment} {before after : Core.Store} {location : Core.Location}
    {output : Core.Value}
    (rows : ProductBundle.Pointwise relation (receipt.binding.atContext active) values)
    (reference : environment[receipt.index]? =
      some (.cellRef (OptionalCell.cellType receipt.payloadType) location))
    (read : before.read? location = some (.inRight .unit (ProductBundle.value values)))
    (evaluated : Core.Evaluates environment before lowered.expression output after) :
    after = before ∧ ∃ native, output = .inRight .word native ∧ relation receipt.candidate native := by
  obtain ⟨native, related, expected⟩ := preserves receipt rows reference read
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated expected
  exact ⟨rfl, native, rfl, related⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleReadMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorHeap
/-! A generalized local cell retains its complete Source descriptor and the
ordered instances created in its lexical context. Reads keep that context
separate from the current caller's context. Instance models supply static
code and capture representations; their laws concern typing and extension. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorHeap
open Core Frontend SourceInference TypeSystem GeneralHeap GenericHeap SourceCoreLocalPolymorphism

structure InstanceModel (definitions : Core.DataEnvironment) where
  locals : Catalog
  Origin : Dynamic.GeneralizedClosure → Binding → Substitution → Prop
  Represents : LocationMap → StoreTyping → Dynamic.GeneralizedClosure → Binding → Substitution →
    Instance → Core.Value → Prop
  runtime_hasType : ∀ {mapping world function binding active candidate value},
    Represents mapping world function binding active candidate value →
    RuntimeValueHasType world value candidate.type definitions
  extend : ∀ {mapping futureMapping world futureWorld function binding active candidate value},
    Represents mapping world function binding active candidate value →
    LocationMap.Extends mapping futureMapping → WorldExtends world futureWorld →
    Represents futureMapping futureWorld function binding active candidate value

variable {definitions : Core.DataEnvironment}

/-- The source capture and full original binding are retained once, before
any read supplies its own scheme evidence. Empty unused bundles are allowed. -/
inductive Stored (model : InstanceModel definitions) (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.GeneralizedClosure → Core.Value → Core.Ty → Prop where
  | bundle {function : Dynamic.GeneralizedClosure} (binding : Binding) (lexical : Substitution)
      (registered : model.locals.binding binding.caller binding.binder.id = .ok binding)
      (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
        function.captured function.binder function.initializer function)
      (origin : model.Origin function binding lexical)
      (binder : function.binder.id = binding.binder.id)
      (initializer : function.initializer = binding.initializer)
      {values : List Core.Value}
      (rows : ProductBundle.Pointwise
        (model.Represents mapping world function binding lexical) (binding.atContext lexical) values) :
      Stored model mapping world function (ProductBundle.value values) (binding.bundleType lexical)

private theorem bundle_typed {world : StoreTyping} {values : List Core.Value} {types : List Core.Ty}
    (typed : ProductBundle.Pointwise (fun value type => RuntimeValueHasType world value type definitions)
      values types) :
    RuntimeValueHasType world (ProductBundle.value values) (ProductBundle.type types) definitions := by
  induction typed with
  | nil => exact .unit
  | @cons value type values types related rows ih =>
      cases rows with
      | nil => exact related
      | cons next rest => exact .pair related ih

private theorem rows_typed {model : InstanceModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.GeneralizedClosure}
    {binding : Binding} {lexical : Substitution} {entries : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical) entries values) :
    ProductBundle.Pointwise (fun value type => RuntimeValueHasType world value type definitions)
      values (entries.map (·.type)) := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih => exact .cons (model.runtime_hasType head) ih

private theorem rows_extend {model : InstanceModel definitions}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {entries : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical) entries values)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ProductBundle.Pointwise (model.Represents futureMapping futureWorld function binding lexical) entries values := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih => exact .cons (model.extend head maps worlds) ih

theorem Stored.runtime_hasType {model : InstanceModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.GeneralizedClosure}
    {value : Core.Value} {payload : Core.Ty}
    (stored : Stored model mapping world function value payload) :
    RuntimeValueHasType world value payload definitions := by
  cases stored with
  | bundle binding lexical registered captures origin binder initializer rows =>
      exact bundle_typed (rows_typed rows)

theorem Stored.extend {model : InstanceModel definitions}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {value : Core.Value} {payload : Core.Ty}
    (stored : Stored model mapping world function value payload)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Stored model futureMapping futureWorld function value payload := by
  cases stored with
  | bundle binding lexical registered captures origin binder initializer rows =>
      exact Stored.bundle binding lexical registered captures origin binder initializer (rows_extend rows maps worlds)

inductive CellRepresents {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (ordinary : PayloadModel catalog projects definitions) (instances : InstanceModel definitions)
    (mapping : LocationMap) (world : StoreTyping) : Dynamic.Cell → Core.Value → Core.Ty → Prop where
  | ordinary {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
      (represented : GenericHeap.CellRepresents ordinary mapping world cell value payload) :
      CellRepresents ordinary instances mapping world cell value payload
  | generalized {function : Dynamic.GeneralizedClosure} {value : Core.Value} {payload : Core.Ty}
      (stored : Stored instances mapping world function value payload) :
      CellRepresents ordinary instances mapping world
        ⟨function.binder.scheme.body, none, some function⟩ (.inRight .unit value) payload

def cellModel {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (ordinary : PayloadModel catalog projects definitions) (instances : InstanceModel definitions) :
    CellModel definitions where
  Represents := CellRepresents ordinary instances
  runtime_hasType := by
    intro mapping world cell value payload represented
    cases represented with
    | ordinary prior => exact prior.runtime_hasType
    | generalized stored => exact .inRight stored.runtime_hasType
  extend := by
    intro mapping futureMapping world futureWorld cell value payload represented maps worlds
    cases represented with
    | ordinary prior => exact .ordinary (prior.extend maps worlds)
    | generalized stored => exact .generalized (stored.extend maps worlds)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {ordinary : PayloadModel catalog projects definitions} {instances : InstanceModel definitions}

theorem initial {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    (related : GenericHeap.HeapRepresents ordinary mapping world heap store) :
    CellHeapRepresents (cellModel ordinary instances) mapping world heap store :=
  (ordinaryHeap_iff.mpr related).includes (fun prior => CellRepresents.ordinary prior)

/-- Ordinary reads retain the original ordinary payload relation. The source
descriptor field, rather than a coincident native payload type, selects it. -/
theorem ordinary_cell {mapping : LocationMap} {world : StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : CellRepresents ordinary instances mapping world cell value payload)
    (absent : cell.generalized = none) :
    GenericHeap.CellRepresents ordinary mapping world cell value payload := by
  cases represented with
  | ordinary prior => exact prior
  | generalized => cases absent

theorem ordinary_cells : OrdinaryCells ordinary (cellModel ordinary instances) where
  inject := CellRepresents.ordinary
  project := ordinary_cell

theorem descriptor_cell {mapping : LocationMap} {world : StoreTyping}
    {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    {function : Dynamic.GeneralizedClosure}
    (represented : CellRepresents ordinary instances mapping world cell value payload)
    (descriptor : cell.generalized = some function) :
    cell = ⟨function.binder.scheme.body, none, some function⟩ ∧
      ∃ bundle, value = .inRight .unit bundle ∧ Stored instances mapping world function bundle payload := by
  cases represented with
  | ordinary prior => rw [prior.ordinary] at descriptor; cases descriptor
  | generalized stored =>
      cases descriptor
      exact ⟨rfl, _, rfl, stored⟩

/-- A genuine Source heap read recovers the corresponding stored descriptor
and its whole native instance row. No current-context filter is substituted. -/
theorem read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
    (heaps : CellHeapRepresents (cellModel ordinary instances) mapping world heap store)
    (sourceRead : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function) :
    ∃ target bundle payload,
      ReferenceRepresents mapping world location target payload ∧
      store.read? target = some (.inRight .unit bundle) ∧
      Stored instances mapping world function bundle payload := by
  obtain ⟨target, value, payload, reference, found, represented⟩ := heaps.read sourceRead
  obtain ⟨_, bundle, same, stored⟩ := descriptor_cell represented descriptor
  exact ⟨target, bundle, payload, reference, same ▸ found, stored⟩

/-- Descriptor allocation follows the independent Source allocation rule and
allocates the native bundle at its own fresh location. -/
theorem allocate {mapping : LocationMap} {world : StoreTyping} {heap after : Dynamic.Heap}
    {store : Core.Store} {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    {bundle : Core.Value} {payload : Core.Ty}
    (heaps : CellHeapRepresents (cellModel ordinary instances) mapping world heap store)
    (stored : Stored instances mapping world function bundle payload)
    (allocated : Dynamic.Heap.AllocatesGeneralized heap function location after) :
    CellHeapRepresents (cellModel ordinary instances) (mapping ++ [store.length])
      (world ++ [OptionalCell.cellType payload]) after (store.allocate (.inRight .unit bundle)).1 ∧
    ReferenceRepresents (mapping ++ [store.length]) (world ++ [OptionalCell.cellType payload])
      location store.length payload :=
  heaps.allocate_generalized (CellRepresents.generalized stored) allocated

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorOrigin
/-! A descriptor keeps the real lexical frame together with its independent
Source graph. The native candidate context is retained separately from the
Source substitution history and its requirement metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorOrigin
open Core Frontend SourceInference TypeSystem
open SourceCoreLocalPolymorphism CallableIndexedHistory

structure Origin {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (function : Dynamic.GeneralizedClosure) (binding : Binding) (lexical : Substitution) where
  native : NativeFrame
  ghost : GhostFrame
  metadata : MetadataState
  carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table native ghost (some metadata)
  paired : CallableAppliedDynamicSourceMaterialization.Pair prepared.ancestry.graph.inputs ghost metadata function.source
  owner : metadata.metadata.owner = binding.caller
  active : metadata.nativeActive = lexical

/-- Materialization uses the actual read dictionary and the descriptor's
lexical Source attachment. Native metadata keeps its own requirement rewrite. -/
theorem Origin.materialize {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    (origin : Origin prepared function binding lexical)
    {callerFrame : SourceCoreCallablePairedFrames.Frame}
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerFrame
      origin.ghost caller origin.metadata id target)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder recipe.read.entry.view.principal.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actual : TypeSystem.Ty} {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = recipe.read.binder.scheme)
    (sameType : actual = recipe.read.node.rawType) :
    let instantiated := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    CallableAppliedDynamicSourceMaterialization.Pair prepared.ancestry.graph.inputs
      (.appliedView id target callerFrame origin.ghost) (recipe.read.after origin.metadata) instantiated.source ∧
    CallableAncestryMetadata.eraseRequirements (recipe.read.after origin.metadata).metadata.source =
      CallableAncestryMetadata.eraseRequirements instantiated.source ∧
    ExpressionForm.lambda instantiated.parameters instantiated.resultType instantiated.body = recipe.read.template.node.form ∧
    instantiated.captured = function.captured ∧
    instantiated.evidence = produced ++ callerEvidence.applySubstitution semantic :=
  CallableAppliedRuntimeMaterialization.materialize origin.paired recipe captures unique instantiation sameScheme sameType

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorOrigin
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallPrefix
/-! Materialized calls join the retained lexical snapshot to the actual read
recipe. The selected frame has the read's child metadata; the captured frame
keeps its lexical metadata. No equality between these contexts is required. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallPrefix
open Core Frontend SourceInference TypeSystem ReadOnly
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open GeneralizedLocalDescriptorOrigin

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : Substitution}

/-- The completed paired table consumes both authentic parent histories and
the actual read/application factories. It does not reclassify the lexical frame. -/
theorem applied_history (origin : Origin prepared function binding lexical)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id target : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id target) :
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table target origin.native
        (SourceCoreCallableIndexedDispatch.readFrame id target callerNative))
      (.appliedView id target callerGhost origin.ghost) (some (recipe.read.after origin.metadata)) := by
  obtain ⟨callerIndex, callerShape, _⟩ := callerCarried.state_shape
  obtain ⟨lexicalIndex, lexicalShape, _⟩ := origin.carried.state_shape
  have callerAt := callerShape ▸ callerCarried
  have lexicalAt := lexicalShape ▸ origin.carried
  simpa only [callerShape, lexicalShape, SourceCoreCallableIndexedDispatch.readFrame] using
    CallableIndexedHistory.applied_complete prepared.ancestry.graph callerAt lexicalAt
      recipe.read recipe.readAccepted recipe.applied recipe.appliedAccepted

/-- The emitted lambda frame load runs in the real current store. The result
is the child state certified by the same read recipe and both parent histories. -/
theorem evaluates (origin : Origin prepared function binding lexical)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id target : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id target)
    {environment : Core.Environment} {store : Store} {lexicalExpression : Core.Expr}
    {referenceIndex location : Nat}
    (selected : DataEquality.Selects environment lexicalExpression (encode prepared.ancestry.layout.frame origin.native))
    (reference : environment[referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id target callerNative))) :
    let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table target origin.native
      (SourceCoreCallableIndexedDispatch.readFrame id target callerNative)
    Evaluates environment store
      (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table prepared.ancestry.layout.frame
        target lexicalExpression (.loadCell (.var referenceIndex)))
      (encode prepared.ancestry.layout.frame next) store ∧
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
      (.appliedView id target callerGhost origin.ghost) (some (recipe.read.after origin.metadata)) := by
  refine ⟨?_, applied_history origin callerCarried recipe⟩
  obtain ⟨position, shape, _⟩ := origin.carried.state_shape
  have selectedAt := shape ▸ selected
  simpa only [shape] using
    CallableIndexedProtocol.lambdaFrame_load prepared.ancestry.graph.table target selectedAt reference read

/-- Native dispatch and independent Source materialization share the exact
read recipe. Captures and the newly resolved evidence remain those of Source. -/
theorem materialized (origin : Origin prepared function binding lexical)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id target : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id target)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder recipe.read.entry.view.principal.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actual : TypeSystem.Ty} {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = recipe.read.binder.scheme)
    (sameType : actual = recipe.read.node.rawType) :
    let instantiated := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table target origin.native
        (SourceCoreCallableIndexedDispatch.readFrame id target callerNative))
      (.appliedView id target callerGhost origin.ghost) (some (recipe.read.after origin.metadata)) ∧
    CallableAppliedDynamicSourceMaterialization.Pair prepared.ancestry.graph.inputs
      (.appliedView id target callerGhost origin.ghost) (recipe.read.after origin.metadata) instantiated.source ∧
    CallableAncestryMetadata.eraseRequirements (recipe.read.after origin.metadata).metadata.source =
      CallableAncestryMetadata.eraseRequirements instantiated.source ∧
    ExpressionForm.lambda instantiated.parameters instantiated.resultType instantiated.body = recipe.read.template.node.form ∧
    instantiated.captured = function.captured ∧
    instantiated.evidence = produced ++ callerEvidence.applySubstitution semantic :=
  ⟨applied_history origin callerCarried recipe,
    origin.materialize recipe captures unique instantiation sameScheme sameType⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallFrame
/-! The actual materialized lambda wrapper installs its paired child frame,
enters the emitted raw body once, and restores the real transient caller frame.
Parameter allocation and body meaning can be composed after this boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallFrame
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open GeneralizedLocalDescriptorOrigin

private theorem body_rename (body : Expr) (embedding : Renaming) :
    (((body.weakenAt 1).rename embedding.lift.lift).weakenAt 0).weakenAt 0 =
      body.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding embedding) := by
  simp only [← Expr.rename_insertion, Expr.rename_comp, CallableIndexedLambdaEntryPrefix.bodyEmbedding]
  congr 1
  funext index
  cases index <;> rfl

theorem agreement {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution}
    (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {actual : Core.Environment}
    (captured : Captures prepared mapping world scope function.captured actual)
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope captured.administrative viewRelation)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id code.descriptor.id)
    {argument : Value} {store : Store} {location : Core.Location}
    (reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))) :
    let current := SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative
    let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table
      code.descriptor.id origin.native current
    let bodyEnvironment := .unit :: encode prepared.ancestry.layout.frame current :: argument ::
      encode prepared.ancestry.layout.frame origin.native :: actual
    (∀ {result finalStore},
      Evaluates bodyEnvironment (store.set location (encode prepared.ancestry.layout.frame next))
        (code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding captured.embedding)) result finalStore →
      Evaluates (argument :: encode prepared.ancestry.layout.frame origin.native :: actual) store
        (code.body.rename captured.embedding.lift.lift) result
        (finalStore.set location (encode prepared.ancestry.layout.frame current))) ∧
    (∀ {result finalStore},
      Evaluates (argument :: encode prepared.ancestry.layout.frame origin.native :: actual) store
        (code.body.rename captured.embedding.lift.lift) result finalStore →
      ∃ bodyStore,
        Evaluates bodyEnvironment (store.set location (encode prepared.ancestry.layout.frame next))
          (code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding captured.embedding)) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current)) := by
  let layout := prepared.ancestry.layout.frame
  let current := SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative
  let saved := encode layout current
  let lexicalValue := encode layout origin.native
  let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native current
  have selected : DataEquality.Selects (argument :: lexicalValue :: actual)
      (.var (captured.embedding code.referenceIndex + 2)) (.cellRef layout.type location) :=
    .var (by simpa using captured.agrees reference)
  have nextEvaluation : Evaluates (saved :: argument :: lexicalValue :: actual) store
      ((SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table layout code.descriptor.id
        (.var 1) (.loadCell (.var (captured.embedding code.referenceIndex + 2)))).weakenAt 0)
      (encode layout next) store := by
    rw [CallableIndexedRenaming.lambdaFrame_weaken]
    simpa only [Expr.weakenAt, Nat.zero_le, ↓reduceIte] using
      (GeneralizedLocalCallPrefix.evaluates origin callerCarried recipe
        (environment := saved :: argument :: lexicalValue :: actual)
        (lexicalExpression := .var 2)
        (referenceIndex := captured.embedding code.referenceIndex + 3)
        (.var rfl) (by simpa [Nat.add_assoc] using captured.agrees reference) read).1
  have wrapper : code.body.rename captured.embedding.lift.lift =
      withFrame (.var (captured.embedding code.referenceIndex + 2))
        (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table layout code.descriptor.id (.var 1)
          (.loadCell (.var (captured.embedding code.referenceIndex + 2))))
        ((code.receipt.rawBody.weakenAt 1).rename captured.embedding.lift.lift) := by
    simp only [Code.body, NamedCalls.withFrame_rename, CallableIndexedRenaming.lambdaFrame, Expr.rename, Renaming.lift]
    rfl
  constructor
  · intro result finalStore evaluated
    rw [wrapper]
    apply CallableContextFrames.withFrame_evaluates selected read nextEvaluation
    rw [body_rename]
    exact evaluated
  · intro result finalStore evaluated
    rw [wrapper] at evaluated
    obtain ⟨nextValue, nextStore, bodyStore, nextEval, bodyEval, finalEq⟩ :=
      CallableContextFrames.withFrame_reflects selected read evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEval nextEvaluation
    rw [body_rename] at bodyEval
    exact ⟨bodyStore, bodyEval, finalEq⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallFrame
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAppliedSourceOrigins
/-! An actual local-scheme use supplies the source origin of its visible
descriptor. The independently substituted Source remains paired with the
read's metadata; its entire source table need not equal the rewritten table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAppliedSourceOrigins
open Core Frontend SourceInference TypeSystem GeneralHeap
open CallableAppliedViewProvenance
open SourceCoreCallableAncestryReadRecipes
open GeneralizedLocalDescriptorOrigin

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok output := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

theorem catalog_of_automatic {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic) :
    ∃ ownership : automatic.checked.signatures = program.signatures,
      SourceCoreCompatibleFunctions.prepareWithCatalog program plan automatic.checked ownership fuel =
        .ok automatic.prepared := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact ⟨_, prepared⟩

theorem catalog_of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled) :
    ∃ (program : CheckedProgram) (plan : SourceCompilationPlan.Plan)
      (ownership : compiled.compatible.checked.signatures = program.signatures) (fuel : Nat),
      SourceCoreCompatibleFunctions.prepareWithCatalog program plan compiled.compatible.checked ownership fuel =
        .ok compiled.indexed.base := by
  obtain ⟨ownership, prepared⟩ := catalog_of_automatic compiled.compatiblePrepared
  rw [SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared]
  exact ⟨_, _, ownership, _, prepared⟩

variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
    {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {id target : Word}
    (recipe : Recipe inputs callerFrame lexicalFrame caller lexical id target)

/-- The contract and runtime source originate at the same applied descriptor.
The body and captured cells remain the responsibility of the value relation. -/
theorem origin_rep {function : Dynamic.Closure} {contract : SourceCoreStageContracts.Contract}
    (canonical : CanonicalHeader inputs recipe.read.template contract)
    (retained : recipe.read.descriptor.contract = some contract)
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs
      (.appliedView id target callerFrame lexicalFrame) (recipe.read.after lexical) function.source)
    (header : ExpressionForm.lambda function.parameters function.resultType function.body =
      recipe.read.template.node.form) (payload : Value) :
    CallableLedger.OriginRep base.plan inputs.callable.table (.closure function)
      (.pair payload (.word target)) := by
  have descriptor : recipe.read.descriptor.id = target := by
    simpa using List.find?_some recipe.read.descriptorSelected
  have provenance : CallableLedger.LambdaOrigin base.plan recipe.read.template.owner recipe.read.template.id
      recipe.read.template.active function contract :=
    .independentApplied recipe canonical retained rfl rfl rfl paired header
  have result := CallableLedger.OriginRep.closure (raw := payload)
    (List.mem_of_find?_eq_some recipe.read.descriptorSelected)
    recipe.read.templateOrigin retained provenance
  simpa only [descriptor] using result

theorem materialized {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {active : Substitution}
    (origin : Origin compiled.indexed function binding active)
    {callerFrame : SourceCoreCallablePairedFrames.Frame} {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Word}
    (recipe : Recipe compiled.indexed.ancestry.graph.inputs callerFrame origin.ghost
      caller origin.metadata id target)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder recipe.read.entry.view.principal.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actual : TypeSystem.Ty} {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence function.binder
      actual requirements semantic produced)
    (sameScheme : function.binder.scheme = recipe.read.binder.scheme)
    (sameType : actual = recipe.read.node.rawType) (payload : Value) :
    let result := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    LambdaMetadataViews.MetadataView result.source (recipe.read.after origin.metadata).metadata.source ∧
      CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
        (.closure result) (.pair payload (.word target)) := by
  obtain ⟨paired, _, header, _, _⟩ :=
    origin.materialize recipe captures unique instantiation sameScheme sameType
  obtain ⟨program, plan, ownership, fuel, prepared⟩ := catalog_of_compiled compiled
  have table := (RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected).accepted
  rw [← (SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at table
  obtain ⟨contract, retained, canonical⟩ := header_of_prepared prepared table recipe.read
  exact ⟨CallableIndependentSourceViews.of_pair paired,
    origin_rep recipe canonical retained paired header payload⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAppliedSourceOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleContexts
/-! A read can have a larger active context than the declaration that created
its bundle. Context agreement makes its candidate list an ordered sublist.
The actual checked payload type then forces both lists to be identical. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleContexts
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

structure ContextExtension (lexical current : Substitution) : Prop where
  domain : ∀ metavariable ∈ lexical.domain, metavariable ∈ current.domain
  action : ∀ metavariable ∈ lexical.domain,
    current.apply (.variable metavariable) = lexical.apply (.variable metavariable)

theorem ContextExtension.agrees {lexical current candidate : Substitution}
    (extension : ContextExtension lexical current)
    (agrees : agreesOnContext candidate current = true) : agreesOnContext candidate lexical = true := by
  apply List.all_eq_true.mpr
  intro metavariable member
  exact decide_eq_true (Eq.trans
    (agreesOnContext_spec agrees metavariable (extension.domain metavariable member))
    (extension.action metavariable member))

private theorem filter_sublist {α : Type} (items : List α) {narrow broad : α → Bool}
    (included : ∀ item, narrow item = true → broad item = true) :
    List.Sublist (items.filter narrow) (items.filter broad) := by
  induction items with
  | nil => exact .slnil
  | cons head rest ih =>
      cases narrowAt : narrow head <;> cases broadAt : broad head
      · simpa [narrowAt, broadAt] using ih
      · simpa [narrowAt, broadAt] using List.Sublist.cons head ih
      · have impossible := included head narrowAt
        simp [broadAt] at impossible
      · simpa [narrowAt, broadAt] using List.Sublist.cons_cons head ih

theorem atContext_sublist {lexical current : Substitution}
    (extension : ContextExtension lexical current) (binding : Binding) :
    List.Sublist (binding.atContext current) (binding.atContext lexical) :=
  filter_sublist binding.instances (fun _ => extension.agrees)

private def bundleArity : Core.Ty → Nat
  | .product _ (.product left right) => bundleArity (.product left right) + 1
  | .product _ _ => 1
  | _ => 0

private theorem nonempty_product (head : Instance) (rest : List Instance) :
    ∃ left right, ProductBundle.type ((head :: rest).map (·.type)) = .product left right := by
  cases rest with
  | nil =>
      cases selected : head.contractId <;>
        simp [ProductBundle.type, Instance.type, selected, Core.TaggedFunction.functionType,
          Core.CallableContract.functionType]
  | cons next tail => exact ⟨_, _, rfl⟩

private theorem bundle_arity (instances : List Instance) :
    bundleArity (ProductBundle.type (instances.map (·.type))) = instances.length := by
  induction instances with
  | nil => rfl
  | cons head rest ih =>
      cases rest with
      | nil =>
          cases selected : head.contractId <;>
            simp [ProductBundle.type, Instance.type, selected, Core.TaggedFunction.functionType,
              Core.CallableContract.functionType, bundleArity]
      | cons next tail =>
          obtain ⟨left, right, shape⟩ := nonempty_product next tail
          change bundleArity (.product head.type (ProductBundle.type ((next :: tail).map (·.type)))) = _
          rw [shape]
          change bundleArity (.product left right) + 1 = _
          rw [← shape, ih]
          rfl

/-- Native type equality is used only after the real context relation gives
an ordered sublist. It cannot choose or identify instances by itself. -/
theorem atContext_eq_of_bundleType {lexical current : Substitution}
    (extension : ContextExtension lexical current) (binding : Binding)
    (checked : binding.bundleType lexical = binding.bundleType current) :
    binding.atContext lexical = binding.atContext current := by
  have lengths := congrArg bundleArity checked
  change bundleArity (ProductBundle.type ((binding.atContext lexical).map (·.type))) =
    bundleArity (ProductBundle.type ((binding.atContext current).map (·.type))) at lengths
  rw [bundle_arity, bundle_arity] at lengths
  exact ((atContext_sublist extension binding).eq_of_length lengths.symm).symm

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleContexts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadBindingIdentity
/-! A successful exact catalog lookup retains both requested key components.
The actual read certificate therefore identifies its complete binding. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceCoreLocalPolymorphism

theorem Catalog.binding_identity {catalog : Catalog} {caller : Key}
    {binder : Resolved.LocalId} {binding : Binding}
    (located : catalog.binding caller binder = .ok binding) :
    binding.caller = caller ∧ binding.binder.id = binder := by
  unfold Catalog.binding at located
  generalize filtered : catalog.bindings.filter
    (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) = entries at located
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | cons next tail => cases located
    | nil =>
      cases located
      have selected := List.mem_filter.mp (show binding ∈ catalog.bindings.filter
        (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) from by
          rw [filtered]
          exact List.mem_cons_self)
      exact of_decide_eq_true selected.2

end Solcore.Frontend.SourceCoreLocalPolymorphism

namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

theorem Certificate.binding_identity {catalog : Catalog} {caller : Key}
    {active : Substitution} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate catalog caller active source scope id reason lowered) :
    receipt.binding.caller = caller ∧ receipt.binding.binder.id = receipt.binder :=
  Catalog.binding_identity receipt.bindingFound

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBinderMetadata
/-! The actual generalized binder compiler checks the complete contextual
binder metadata before returning its bundle type. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceCoreLocalPolymorphism
open SourceInference TypeSystem

theorem lowerBinder_success
    {catalog : Catalog} {caller : Key} {active : Substitution} {source : TypedSource}
    {scope : Scope} {binder : TypedBinder} {type : Core.Ty}
    (accepted : lowerBinder catalog caller active source scope binder = .ok type) :
    ∃ binding, catalog.binding caller binder.id = .ok binding ∧
      binding.binder.applySubstitution active = binder ∧
      type = binding.bundleType active := by
  unfold lowerBinder at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases located : catalog.binding caller binder.id with
  | error error => simp only [located] at accepted; cases accepted
  | ok binding =>
    simp only [located] at accepted
    split at accepted
    · contradiction
    · exact ⟨binding, rfl, Classical.byContradiction ‹¬binding.binder.applySubstitution active ≠ binder›, (Except.ok.inj accepted).symm⟩

theorem lowerBinder_quantified
    {catalog : Catalog} {caller : Key} {active : Substitution} {source : TypedSource}
    {scope : Scope} {binder : TypedBinder} {type : Core.Ty} {binding : Binding}
    (accepted : lowerBinder catalog caller active source scope binder = .ok type)
    (located : catalog.binding caller binder.id = .ok binding) :
    binder.scheme.quantified = binding.binder.scheme.quantified := by
  obtain ⟨actual, selected, metadata, _⟩ := lowerBinder_success accepted
  have same : actual = binding := Except.ok.inj (selected.symm.trans located)
  subst actual
  rw [← metadata]
  rfl

end Solcore.Frontend.SourceCoreLocalPolymorphism
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalRuntimeInstantiation
/-! Original local-reference typing and the actual complete compiler matcher
produce a ground Dynamic instantiation. The current caller dictionary closes
the original ordered requirements, including those erased from native code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalRuntimeInstantiation
open Frontend SourceInference TypeSystem

private theorem empty_orElse {α : Type} (left right : Option α)
    (empty : left.orElse (fun _ => right) = none) : left = none ∧ right = none := by
  cases left with
  | none => exact ⟨rfl, empty⟩
  | some value => cases empty

private theorem concrete_variable (substitution : Substitution) (type : Ty)
    (concrete : SourceSpecialization.firstNonConcrete (substitution.apply type) = none) :
    ∀ metavariable ∈ type.freeVariables,
      SourceSpecialization.firstNonConcrete (substitution.apply (.variable metavariable)) = none := by
  induction type with
  | «variable» candidate =>
    intro metavariable member
    have same : metavariable = candidate := by simpa [Ty.freeVariables] using member
    subst metavariable
    exact concrete
  | parameter | constructor | error => intro metavariable member; simp [Ty.freeVariables] at member
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
    have parts := empty_orElse (SourceSpecialization.firstNonConcrete (substitution.apply left))
      (SourceSpecialization.firstNonConcrete (substitution.apply right)) concrete
    intro metavariable member
    simp at member
    rcases member with member | member
    · exact ihLeft parts.1 metavariable member
    · exact ihRight parts.2 metavariable member
  | proxy inner ih | comptime inner ih => exact ih concrete

/-- Closed matching forces every genuine exact semantic replacement to be
concrete, while original admissibility supplies nominal membership and arity. -/
theorem range_of_match {context : Context} {scheme : Scheme} {actual : Ty}
    {compiled semantic : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual = some compiled)
    (exact : ExactSubstitution semantic scheme.quantified)
    (range : SubstitutionRangeAdmissible context semantic)
    (result : semantic.apply scheme.body = actual) :
    SubstitutionRangeWellFormed context semantic := by
  intro metavariable replacement member
  have lookup := StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup exact.domain_nodup member
  have domain : metavariable ∈ semantic.domain := List.mem_map.mpr ⟨_, member, rfl⟩
  have occurs := CallableClosedSchemeSubstitutionAgreement.quantified_occurs_of_closed_match matched metavariable
    ((exact.mem_domain_iff metavariable).mp domain)
  have concrete := concrete_variable semantic scheme.body
    (result ▸ (SourceSpecialization.matchClosedSchemeInstance?_sound matched).1) metavariable occurs
  simp only [Substitution.apply, lookup, Option.getD_some] at concrete
  have admitted := range metavariable replacement member
  have typed := CallableIndexedOwnedReachedNamedConcreteRangeReceipts.admissible_concrete_at_catalog admitted concrete
  apply Dynamic.TypeWellFormed.transportContext (source := Context.ofSignatures context.signatures) (target := context) ?_ typed
  exact { signatures := rfl
          parameters := by intro parameter impossible; cases impossible
          parameterOwners := by intro parameter impossible; cases impossible
          variables := by intro metavariable impossible; cases impossible
          residualVariables := by intro impossible; cases impossible
          targetBinders := admitted.binders }

theorem of_valid {context : Context} {binder : TypedBinder} {actual : Ty}
    {requirements : List RequirementId} {compiled : Substitution}
    {evidence : Dynamic.EvidenceEnvironment}
    (matched : SourceSpecialization.matchClosedSchemeInstance? binder.scheme actual = some compiled)
    (valid : LocalSchemeInstantiationValid context binder actual requirements)
    (covers : evidence.Covers context) :
    ∃ substitution produced, Dynamic.LocalSchemeRuntimeInstantiation context evidence binder actual
      requirements substitution produced := by
  cases valid with
  | intro formation wellFormed substitution exact range result unique disjoint requirements =>
    obtain ⟨produced, produces⟩ := Dynamic.RequirementSequenceProves.produces_of_covers covers requirements
    exact ⟨substitution, produced, formation, wellFormed, exact,
      range_of_match matched exact range result, result, unique, disjoint, produces⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalRuntimeInstantiation
end
