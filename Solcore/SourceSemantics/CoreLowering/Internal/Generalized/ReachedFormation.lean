import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.LambdaCompilation
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.SourceResidualNodeSubstitutionAgreement
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.Frontend.ResidualLexicalScopes
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceStaging
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.AcceptedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission

/-!
# Generalized locals: reached formation

Initializer compilation, reached allocation and materialization, lexical domains and origins, captured scopes, and named recipes and views.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation
/-! The actual generalized initializer compiles its finite candidate list in
order. This receipt retains every candidate and raw lambda, including repeated
native types; a later read uses the cumulative candidate key. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism DataPatternValues
open GeneralizedLocalInstanceCompilation (Inputs)

structure Receipt (inputs : Inputs) (binding : Binding) (active : Substitution)
    (lowered : SourceCoreBasic.LoweredExpr) where
  closures : List Core.Expr
  generated : (binding.atContext active).mapM (GeneralizedLocalInstanceCompilation.compile inputs) = .ok closures
  rows : ListRel (fun candidate raw => Nonempty (GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw))
    (binding.atContext active) closures
  emitted : lowered = ⟨binding.bundleType active, LanguageResult.success (ProductBundle.expression closures)⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) : ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

private theorem rows_of_mapM (inputs : Inputs) {candidates : List Instance} {closures : List Core.Expr}
    (accepted : candidates.mapM (GeneralizedLocalInstanceCompilation.compile inputs) = .ok closures) :
    ListRel (fun candidate raw => Nonempty (GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw))
      candidates closures := by
  induction candidates generalizing closures with
  | nil => simp at accepted; subst closures; exact .nil
  | cons candidate tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨raw, compiled, accepted⟩ := bind_ok accepted
    obtain ⟨rest, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    exact .cons (GeneralizedLocalInstanceCompilation.of_accepted compiled) (ih remaining)

theorem of_accepted {inputs : Inputs} {binding : Binding} {active : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : lowerInitializer binding active (GeneralizedLocalInstanceCompilation.compile inputs) = .ok lowered) :
    Nonempty (Receipt inputs binding active lowered) := by
  unfold lowerInitializer at accepted
  obtain ⟨closures, generated, accepted⟩ := bind_ok accepted
  exact ⟨⟨closures, generated, rows_of_mapM inputs generated, (Except.ok.inj accepted).symm⟩⟩

/-- The callback inputs are the literal fields of the named compiler's
special branch, including the original root fuel and current child budget. -/
def namedInputs {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (rootFuel budget : Nat) (current : SourceCoreFunctions.Context)
    (scope : SourceCoreBasic.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word) : Inputs where
  program := prepared.base.sourceProgram
  representation := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
  signatures := prepared.base.sourceProgram.signatures
  locals := prepared.base.locals
  candidateParents := compiled.parents
  assignments := compiled.own.assignments
  diagnostics
  current
  native := prepared.base.callableContext
  parent := none
  budget
  fuel := rootFuel
  initializer := id
  scope
  reasonAt

/-- A reached initializer override returns the same binding and ordered
instance compilation receipts. No Source initializer evaluation is involved. -/
theorem of_named_special_output {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    {rootFuel budget : Nat} {current : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} {reasonAt : ExpressionId → Word} {initial : Binding}
    {output : Option SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (selected : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)) = some initial)
    (accepted : CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel current child budget
      source scope id reasonAt = .ok output) :
    ∃ binding lowered, output = some lowered ∧
      prepared.base.locals.binding current.owner initial.binder.id = .ok binding ∧
      Nonempty (Receipt (namedInputs compiled rootFuel budget current scope id reasonAt) binding [] lowered) := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special at accepted
  have unchanged : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram current.plan
      prepared.base.locals current.owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  rw [unchanged] at accepted
  simp only [bind, Except.bind, pure, Except.pure, found, selected, Option.filter_some,
    ne_eq, reduceCtorEq, not_false_eq_true, decide_true, ↓reduceIte] at accepted
  obtain ⟨binding, located, accepted⟩ := bind_ok accepted
  have located := mapError_ok located
  obtain ⟨actual, generated, accepted⟩ := bind_ok accepted
  have generated := mapError_ok generated
  exact ⟨binding, actual, (Except.ok.inj accepted).symm, located, of_accepted generated⟩

/-- Invert the original accepted expression at its actual compiler policy.
The generated initializer is the reached override, before ordinary lambda
formation could be selected. -/
theorem of_named_policy {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    {rootFuel fuel : Nat} {current : SourceCoreFunctions.Context}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compiled rootFuel policy)
    {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} {reasonAt : ExpressionId → Word} {initial : Binding}
    {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (selected : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)) = some initial)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      current source scope id reasonAt = .ok lowered) :
    ∃ binding, prepared.base.locals.binding current.owner initial.binder.id = .ok binding ∧
      Nonempty (Receipt (namedInputs compiled rootFuel (fuel + 1) current scope id reasonAt) binding [] lowered) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
  rw [recipe.lowerSpecial] at accepted
  obtain ⟨output, generated, accepted⟩ := bind_ok accepted
  obtain ⟨binding, actual, rfl, located, receipt⟩ :=
    of_named_special_output compiled found form selected generated
  have same : actual = lowered := Except.ok.inj accepted
  subst actual
  exact ⟨binding, located, receipt⟩

/-- The outer named expression uses this exact policy before any local read
has selected a generalized descriptor. -/
def namedPolicy {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (rootFuel : Nat) : SourceCoreFunctions.Policy :=
  let representation := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
  { representation.expressions with
    callables := SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation prepared.base.locals named.signature.key []
    readExpression := fun source id => do
      let viewed ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        (CallableIndexedNamedGeneration.context prepared named).plan prepared.base.locals
        named.signature.key none source id
      representation.expressions.readExpression viewed id
    lowerSpecial? := some (CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel) }

def namedLowerBody {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :=
  let representation := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
  SourceCoreGeneralFunctions.bodyLowererWithRepresentation representation
    named.specialized.function.solvedRequirements compiled.own.assignments diagnostics named.signature.key
    (SourceCoreGeneralFunctions.contextualBinder representation prepared.base.locals named.signature.key [])

theorem namedPolicy_recipe {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) (rootFuel : Nat) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compiled rootFuel (namedPolicy compiled rootFuel) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem named_contextual {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreBasic.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) :
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
      diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext
      none none (fuel + 1) source scope id reasonAt =
    SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled fuel) (namedLowerBody compiled)
      (fuel + 1) (CallableIndexedNamedGeneration.context prepared named) source scope id reasonAt := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def]
  dsimp only
  change (SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key
    |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = _
  rw [record]
  rfl

/-- The accepted named compiler call yields its actual initialized bundle
without a separately selected expression policy. -/
theorem of_named_contextual {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} {reasonAt : ExpressionId → Word} {initial : Binding}
    {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (selected : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = some initial)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
      diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext
      none none fuel source scope id reasonAt = .ok lowered) :
    ∃ childFuel, fuel = childFuel + 1 ∧
      ∃ binding, prepared.base.locals.binding named.signature.key initial.binder.id = .ok binding ∧
        Nonempty (Receipt (namedInputs compiled childFuel fuel
          (CallableIndexedNamedGeneration.context prepared named) scope id reasonAt) binding [] lowered) := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ fuel =>
    rw [named_contextual compiled record] at accepted
    have owner : id.occurrence.owner = source.owner := by
      by_cases same : id.occurrence.owner = source.owner
      · exact same
      · have rejected := accepted
        rw [SourceCoreFunctions.lowerExpressionWithPolicy] at rejected
        simp [same, throw, bind, Except.bind] at rejected
    obtain ⟨binding, located, receipt⟩ :=
      of_named_policy compiled (namedPolicy_recipe compiled fuel) owner found form selected accepted
    exact ⟨fuel, rfl, binding, located, receipt⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAllocation
/-! The actual reached initializer attaches body correspondence to the same
stored Snapshot. Unrelated table entries and input types are not compared. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAllocation
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open CallableBodyMetadataViews CallableLambdaBodyReachability
open CallableAncestryProfiles.SourceComposition
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInstanceValues (referenceIndex value)
open GeneralizedLocalAcceptedInstances (Snapshot)

/-- Evidence carried by the existing Snapshot, not another closure model. -/
structure Attachment (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) : Prop where
  closed : RangesClosed lexical
  view : BodyView function.source (binding.source.applySubstitution lexical)
    (lambdaRoots function.initializer function.body)

private theorem source_at {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (receipt : LambdaSourceAlignment.SourceReceipt program plan owner active source)
    {original : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok original) :
    source = original.function.typedBody.applySubstitution active := by
  cases receipt with
  | original found =>
    cases Except.ok.inj (found.symm.trans selected)
    exact (EmptySourceSubstitution.source _).symm
  | contextual accepted =>
    obtain ⟨row, found, _, _, same⟩ := LambdaSourceAlignment.prepared_source accepted
    cases Except.ok.inj (found.symm.trans selected)
    exact same

private theorem capture_roots {function : Dynamic.GeneralizedClosure}
    {roots : List NodeId}
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : Reaches function.source roots (.expression function.initializer)) :
    ∀ id ∈ lambdaRoots function.initializer function.body, Reaches function.source roots id := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  intro id member
  rcases List.mem_cons.mp member with same | inBody
  · exact same ▸ reached
  · apply Reaches.expression reached found
    simpa only [form, ExpressionForm.references] using inBody

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The invocation supplies both the source-view relation and its original
compiler receipt. The lambda roots come from the actual reached capture. -/
theorem attachment_of_invocation
    (index : ActualBodyInvocation.Index compiled ActualBodyInvocation.ReachedView)
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (owner : binding.caller = index.owner)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer))
    (closed : RangesClosed index.active) : Attachment function binding index.active := by
  obtain ⟨candidateOwner, originalSource, _, _⟩ :=
    SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨row, selected, source, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, candidateOwner, owner] at selected
  have current := source_at index.compiler_source_receipt selected
  rw [source, originalSource] at current
  have view : BodyView function.source index.compilerSource (index.statements.map NodeId.statement) := by
    rw [sameSource]
    exact index.reached_view
  have actualReached : Reaches function.source (index.statements.map NodeId.statement)
      (.expression function.initializer) := view.symm.reaches reached
  exact ⟨closed, current ▸ view.restrict (capture_roots captures unique actualReached)⟩

/-- The real creation evaluation stores the restricted proof alongside the
same candidate, captures, native value, and frame reference. -/
theorem formation_at_frame
    (index : ActualBodyInvocation.Index compiled ActualBodyInvocation.ReachedView)
    {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    {actual : Core.Environment}
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (sameLexical : indexed.lexical = index.active)
    (owner : inputs.current.owner = binding.caller)
    (currentOwner : binding.caller = index.owner)
    (initializer : inputs.initializer = binding.initializer)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer))
    (closed : RangesClosed index.active)
    (origin : Origin compiled.indexed function binding index.active)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding index.active location
      (Attachment function binding index.active) candidate
      (value indexed captured.embedding origin.native actual) := by
  have attached := attachment_of_invocation index indexed located member currentOwner sameSource
    captures unique reached closed
  obtain ⟨_, source, binder, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  exact GeneralizedLocalAcceptedInstances.formation_at_frame_with indexed sameLexical owner initializer
    source (congrArg TypedBinder.id binder) _ attached origin captured declarations ownership issuer
    typed stored reference read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalPreparedClosure
/-! The evidence preparation factory itself checks real worklist membership.
Consequently every accepted Packet, and every materialized body index built
from it, has closed native replacement ranges. No catalog-membership field is
added to the shared invocation representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalPreparedClosure
open Core Frontend SourceInference TypeSystem
open CallableAncestryProfiles.SourceComposition
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem instance_substitution_eq
    {left right : SourceSpecializationWorklist.LocalLambdaInstance}
    (same : (left == right) = true) : left.substitution = right.substitution := by
  change (left.binding == right.binding && left.substitution == right.substitution) = true at same
  simp only [Bool.and_eq_true] at same
  exact eq_of_beq same.2

/-- Successful preparation validates discovery membership before it constructs
the contextual caller. The checked comparison includes the full substitution. -/
theorem candidate_closed {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    RangesClosed candidate.origin.substitution := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨caller, _, accepted⟩ := bind_ok accepted
  split at accepted <;> try contradiction
  obtain ⟨discovered, discoveredAt, accepted⟩ := bind_ok accepted
  have discoveredAt : SourceSpecializationWorklist.localLambdaInstances candidate.origin.source = .ok discovered := by
    cases actual : SourceSpecializationWorklist.localLambdaInstances candidate.origin.source with
    | error error => simp [actual, Except.mapError] at discoveredAt
    | ok values =>
      have same : values = discovered := by simpa only [actual, Except.mapError, Except.ok.injEq] using discoveredAt
      exact congrArg Except.ok same
  split at accepted <;> try contradiction
  have present : discovered.contains candidate.origin.localInstance = true := by assumption
  obtain ⟨actual, member, same⟩ := List.contains_iff_exists_mem_beq.mp present
  have closed := PreparedLocalInstanceClosure.read_origin_closed
    (SourceSpecializationWorklist.localLambdaInstances_read_origin discoveredAt actual member)
  rw [← instance_substitution_eq same] at closed
  exact closed

theorem prepared_closed {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    RangesClosed prepared.substitution := by
  obtain ⟨_, _, _, substitution, _⟩ := LambdaSourceAlignment.prepared_source accepted
  rw [substitution]
  exact candidate_closed accepted

theorem packet_closed {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (packet : Packet inputs candidate raw) : RangesClosed packet.original.emission.prepared.substitution :=
  prepared_closed packet.original.emission.authentic

theorem materialized_closed {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function relation) :
    RangesClosed material.code.active := by
  rw [material.active]
  exact packet_closed material.packet

theorem invocation_closed {compiled : SourceCoreUnifiedCompilation.Compiled}
    {relation : ActualBodyInvocation.BodyRelation}
    (index : ActualBodyInvocation.Index compiled relation) : RangesClosed index.active := by
  cases index with
  | named receipt selected => exact RangesClosed.empty
  | contextual material view => exact materialized_closed material

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalPreparedClosure
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
/-! Accepted preparation retains real discovery ancestry. This strengthens the
origin evidence of the existing Packet; it does not replace its native code or
claim that every later read has the same lexical context as allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open SourceSpecializationWorklist

-- Reflect the structural comparison used by the worklist, before the
-- callable-principal module installs its decidable comparison.
attribute [local instance 2000] SourceInference.instBEqTypedBinder
deriving instance ReflBEq, LawfulBEq for TypedBinder
deriving instance ReflBEq, LawfulBEq for LocalLambdaBinding
deriving instance ReflBEq, LawfulBEq for LocalLambdaInstance

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

/-- The actual discovery guard compares the complete instance, including all
binder fields and the cumulative substitution. -/
theorem candidate_origin {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    LocalLambdaInstance.LexicalReadOrigin candidate.origin.source candidate.origin.localInstance := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨caller, _, accepted⟩ := bind_ok accepted
  split at accepted <;> try contradiction
  obtain ⟨discovered, discoveredAt, accepted⟩ := bind_ok accepted
  have discoveredAt : localLambdaInstances candidate.origin.source = .ok discovered := by
    cases actual : localLambdaInstances candidate.origin.source with
    | error error => simp [actual, Except.mapError] at discoveredAt
    | ok values =>
      have same : values = discovered := by
        simpa only [actual, Except.mapError, Except.ok.injEq] using discoveredAt
      exact congrArg Except.ok same
  split at accepted <;> try contradiction
  have present : discovered.contains candidate.origin.localInstance = true := by assumption
  exact localLambdaInstances_lexical_read_origin discoveredAt _
    (List.contains_iff_mem.mp present)

theorem packet_origin {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
    {raw : Core.Expr} (packet : Packet inputs candidate raw) :
    LocalLambdaInstance.LexicalReadOrigin candidate.origin.source candidate.origin.localInstance :=
  candidate_origin packet.original.emission.authentic

theorem materialized_origin {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function relation) :
    LocalLambdaInstance.LexicalReadOrigin material.candidate.origin.source
      material.candidate.origin.localInstance :=
  packet_origin material.packet

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalDomain
/-! Every native replacement key comes from an actual discovered owner's
quantified variables. This records ownership, without asserting separation
from an unrelated lexical context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

theorem domain_owner {source : TypedSource} {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin source localInstance)
    {metavariable : TypeVarId} (member : metavariable ∈ localInstance.substitution.domain) :
    ∃ owner : LocalLambdaInstance, LocalLambdaInstance.LexicalReadOrigin source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified := by
  induction origin with
  | @root localInstance binding nodes selected expression present name form matched =>
      refine ⟨localInstance, .root binding nodes selected expression present name form matched, ?_⟩
      exact (SourceSpecialization.matchClosedSchemeInstance?_sound matched).2.2.1 ▸ member
  | @contextual localInstance parent parentOrigin binding nodes selected expression present
      name form child matched cumulative ih =>
      rw [cumulative, Substitution.mem_domain_compose_iff] at member
      rcases member with old | fresh
      · exact ih old
      · refine ⟨localInstance, .contextual parentOrigin binding nodes selected expression
          present name form child matched cumulative, ?_⟩
        exact (SourceSpecialization.matchClosedSchemeInstance?_sound matched).2.2.1 ▸ fresh

theorem packet_domain_owner {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
    {raw : Core.Expr} (packet : Packet inputs candidate raw)
    {metavariable : TypeVarId}
    (member : metavariable ∈ packet.original.emission.prepared.substitution.domain) :
    ∃ owner : LocalLambdaInstance,
      LocalLambdaInstance.LexicalReadOrigin candidate.origin.source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified := by
  obtain ⟨_, _, _, substitution, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [substitution] at member
  exact domain_owner (packet_origin packet) member

theorem materialized_domain_owner {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function relation)
    {metavariable : TypeVarId} (member : metavariable ∈ material.code.active.domain) :
    ∃ owner : LocalLambdaInstance,
      LocalLambdaInstance.LexicalReadOrigin material.candidate.origin.source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified := by
  rw [material.active] at member
  exact packet_domain_owner material.packet member

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrderedDomain
/-! Domain ownership follows the authentic discovery chain. The internal
ordering input concerns only its real contextual reads; the compiled-source
adapter supplies it from initialization and lexical read provenance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

/-- The next instance is obtained from a read in the actual parent's lexical
body. Keeping that read in the premise prevents unrelated binder orders from
being used to order a discovery chain. -/
def ContextualReadOrder (source : TypedSource) : Prop :=
  ∀ parent, LocalLambdaInstance.LexicalReadOrigin source parent →
    ∀ nodes, localLambdaBodyNodes source parent = .ok nodes →
      ∀ expression, .expression expression ∈ nodes →
        ∀ name target, expression.form = .reference name (.local target) →
          target.binderIndex < parent.binding.binder.id.binderIndex

theorem domain_owner_at_or_after
    {source : TypedSource} {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin source localInstance)
    (ordered : ContextualReadOrder source)
    {metavariable : TypeVarId} (member : metavariable ∈ localInstance.substitution.domain) :
    ∃ owner : LocalLambdaInstance, LocalLambdaInstance.LexicalReadOrigin source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified ∧
      localInstance.binding.binder.id.binderIndex ≤ owner.binding.binder.id.binderIndex := by
  induction origin with
  | @root localInstance binding nodes selected expression present name form matched =>
      refine ⟨localInstance, .root binding nodes selected expression present name form matched,
        ?_, Nat.le_refl _⟩
      exact (SourceSpecialization.matchClosedSchemeInstance?_sound matched).2.2.1 ▸ member
  | @contextual localInstance parent parentOrigin binding nodes selected expression present
      name form child matched cumulative ih =>
      rw [cumulative, Substitution.mem_domain_compose_iff] at member
      rcases member with old | fresh
      · obtain ⟨owner, authentic, quantified, afterParent⟩ := ih old
        have beforeParent := ordered parent parentOrigin nodes selected expression present
          name localInstance.binding.binder.id form
        exact ⟨owner, authentic, quantified, Nat.le_trans (Nat.le_of_lt beforeParent) afterParent⟩
      · refine ⟨localInstance, .contextual parentOrigin binding nodes selected expression
          present name form child matched cumulative, ?_, Nat.le_refl _⟩
        exact (SourceSpecialization.matchClosedSchemeInstance?_sound matched).2.2.1 ▸ fresh

theorem packet_domain_owner_at_or_after
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
    {raw : Core.Expr} (packet : Packet inputs candidate raw)
    (ordered : ContextualReadOrder candidate.origin.source)
    {metavariable : TypeVarId}
    (member : metavariable ∈ packet.original.emission.prepared.substitution.domain) :
    ∃ owner : LocalLambdaInstance,
      LocalLambdaInstance.LexicalReadOrigin candidate.origin.source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified ∧
      candidate.origin.localInstance.binding.binder.id.binderIndex ≤
        owner.binding.binder.id.binderIndex := by
  obtain ⟨_, _, _, substitution, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [substitution] at member
  exact domain_owner_at_or_after (packet_origin packet) ordered member

theorem materialized_domain_owner_at_or_after
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function relation)
    (ordered : ContextualReadOrder material.candidate.origin.source)
    {metavariable : TypeVarId} (member : metavariable ∈ material.code.active.domain) :
    ∃ owner : LocalLambdaInstance,
      LocalLambdaInstance.LexicalReadOrigin material.candidate.origin.source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified ∧
      material.candidate.origin.localInstance.binding.binder.id.binderIndex ≤
        owner.binding.binder.id.binderIndex := by
  rw [material.active] at member
  exact packet_domain_owner_at_or_after material.packet ordered member

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalResidualAgreement
/-! Actual residual validation reduces a node's substitution agreement to its
own lexical scope. Embedded binder quantifiers are masked by the real binder
operation; their body and requirement metadata are both preserved. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalResidualAgreement
open Core Frontend SourceInference TypeSystem SourceSpecialization
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open CallableAncestryProfiles.SourceComposition
open CallableBodyMetadataViews CallableLambdaBodyReachability

private theorem type_congr {left right : Substitution} (type : TypeSystem.Ty)
    (same : ∀ metavariable ∈ type.freeVariables,
      left.apply (.variable metavariable) = right.apply (.variable metavariable)) :
    left.apply type = right.apply type := by
  induction type with
  | «variable» metavariable => exact same metavariable (by simp [Ty.freeVariables])
  | parameter | constructor | error => rfl
  | application _ _ first second | function _ _ first second
  | product _ _ first second | mapping _ _ first second =>
    simp only [Substitution.apply]
    rw [first (by intro v h; exact same v (by simp [h])),
      second (by intro v h; exact same v (by simp [h]))]
  | proxy _ ih | comptime _ ih =>
    simp only [Substitution.apply]
    rw [ih (by intro v h; exact same v (by simpa only [Ty.freeVariables] using h))]

/-- The same action is needed only for the actual path's variables. Quantifiers
of embedded binders are handled by their existing capture-avoiding masks. -/
theorem node_of_scope {left right : Substitution} {node : Node}
    {variables : List TypeVarId}
    (types : ∀ type ∈ residualNodeTypes node,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables)
    (binders : ∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables,
        metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified)
    (same : ∀ metavariable ∈ variables,
      left.apply (.variable metavariable) = right.apply (.variable metavariable)) :
    node.applySubstitution left = node.applySubstitution right := by
  apply SourceResidualNodeSubstitutionAgreement.node_congr
  · intro type member
    exact type_congr type (fun v occurs => same v (types type member v occurs))
  · intro binder member type inspected
    apply type_congr
    intro metavariable occurs
    by_cases quantified : metavariable ∈ binder.scheme.quantified
    · simp only [Substitution.apply, lookup_without, if_pos quantified]
    · have inScope : metavariable ∈ variables :=
        (binders binder member type inspected metavariable occurs).resolve_right quantified
      simpa only [Substitution.apply, lookup_without, if_neg quantified] using same metavariable inScope

/-- The catalog entry and accepted Packet supply the real source validation.
This endpoint does not ask for a separate residual-formation law. -/
theorem binding_node_at_scope {compiled : SourceCoreUnifiedCompilation.Compiled}
    {binding : SourceCoreLocalPolymorphism.Binding} {active left right : Substitution}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext active)
    {node : Node} (present : node ∈ binding.source.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath binding.source node.id variables)
    (same : ∀ metavariable ∈ variables,
      left.apply (.variable metavariable) = right.apply (.variable metavariable)) :
    node.applySubstitution left = node.applySubstitution right := by
  obtain ⟨types, binders⟩ :=
    SelectedCompilationResidualScopes.binding_path_support indexed located member present path
  exact node_of_scope types binders same

/-- Node agreement on the actual reached body supplies the existing body view.
Unrelated source-table rows are never compared. -/
theorem body_view_of_nodes {source : TypedSource} {roots : List NodeId}
    {left right : Substitution}
    (same : ∀ node ∈ source.nodes, Reaches source roots node.id →
      node.applySubstitution left = node.applySubstitution right) :
    BodyView (source.applySubstitution left) (source.applySubstitution right) roots where
  owner := rfl
  inputs := by simp only [TypedSource.applySubstitution_inputIds]
  expression reached _ found := by
    have path := reached.elim (reaches_substitution left).mp (reaches_substitution right).mp
    rw [lookupExpression_apply] at found
    obtain ⟨node, selected, rfl⟩ := Option.map_eq_some_iff.mp found
    have contained := lookupExpression?_sound selected
    have agreement := same (.expression node) contained.1
      (by simpa only [Node.id, contained.2] using path)
    have nodeEq := Node.expression.inj agreement
    exact ⟨node.applySubstitution left, by rw [lookupExpression_apply, selected]; rfl,
      rfl, congrArg ExpressionNode.form nodeEq⟩
  expression_back reached _ found := by
    have path := reached.elim (reaches_substitution left).mp (reaches_substitution right).mp
    rw [lookupExpression_apply] at found
    obtain ⟨node, selected, rfl⟩ := Option.map_eq_some_iff.mp found
    have contained := lookupExpression?_sound selected
    have agreement := same (.expression node) contained.1
      (by simpa only [Node.id, contained.2] using path)
    have nodeEq := Node.expression.inj agreement
    exact ⟨node.applySubstitution right, by rw [lookupExpression_apply, selected]; rfl,
      rfl, congrArg ExpressionNode.form nodeEq.symm⟩
  statement reached := by
    have path := reached.elim (reaches_substitution left).mp (reaches_substitution right).mp
    rw [lookupStatement_apply, lookupStatement_apply]
    cases selected : source.lookupStatement? _ with
    | none => rfl
    | some node =>
      have contained := lookupStatement?_sound selected
      have agreement := same (.statement node) contained.1
        (by simpa only [Node.id, contained.2] using path)
      exact congrArg some (Node.statement.inj agreement)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalResidualAgreement
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalClosedAllocation
/-! The authentic invocation factory supplies closed native ranges. Allocation
uses that fact for the same Snapshot and the same reached body attachment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAllocation
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open CallableBodyMetadataViews CallableLambdaBodyReachability
open CallableAncestryProfiles.SourceComposition
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInstanceValues (referenceIndex value)
open GeneralizedLocalAcceptedInstances (Snapshot)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The actual Packet validated its discovered local instance before creation.
No independent closedness premise is needed at the allocation boundary. -/
theorem attachment_of_actual_invocation
    (index : ActualBodyInvocation.Index compiled ActualBodyInvocation.ReachedView)
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (owner : binding.caller = index.owner)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer)) : Attachment function binding index.active := by
  exact attachment_of_invocation index indexed located member owner sameSource captures unique reached
    (GeneralizedLocalPreparedClosure.invocation_closed index)

/-- The actual frame creation stores the same captured environment and native
value; authentic preparation supplies the attachment's closedness field. -/
theorem formation_at_actual_frame
    (index : ActualBodyInvocation.Index compiled ActualBodyInvocation.ReachedView)
    {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    {actual : Core.Environment}
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (sameLexical : indexed.lexical = index.active)
    (owner : inputs.current.owner = binding.caller)
    (currentOwner : binding.caller = index.owner)
    (initializer : inputs.initializer = binding.initializer)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer))
    (origin : Origin compiled.indexed function binding index.active)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding index.active location
      (Attachment function binding index.active) candidate
      (value indexed captured.embedding origin.native actual) := by
  exact formation_at_frame index indexed located member sameLexical owner currentOwner initializer
    sameSource captures unique reached (GeneralizedLocalPreparedClosure.invocation_closed index)
    origin captured declarations ownership issuer typed stored reference read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
/-! Actual allocation records its lexical residual scope in the existing
Snapshot. A later accepted read adds the chosen lambda's own keys and supplies
scope coverage for the exact body compiled by the retained Packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalAcceptedInstances (Snapshot)
open GeneralizedLocalBundleContexts (ContextExtension)

structure Attachment (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) : Prop
    extends GeneralizedLocalReachedAllocation.Attachment function binding lexical where
  captured : CapturedResidualScope binding.source binding.initializer
    binding.binder.scheme.quantified lexical.domain

/-- Strengthening proof evidence preserves this same compiled packet, captured
frame, native value and heap location. -/
theorem retain_scope {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (snapshot : Snapshot prepared mapping world function binding lexical location
      (GeneralizedLocalReachedAllocation.Attachment function binding lexical) candidate native)
    (captured : CapturedResidualScope binding.source binding.initializer
      binding.binder.scheme.quantified lexical.domain) :
    Snapshot prepared mapping world function binding lexical location
      (Attachment function binding lexical) candidate native := by
  cases snapshot with
  | retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      attached origin frame declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      ⟨attached, captured⟩ origin frame declarations ownership issuer reference typed runtimeTyped

/-- The scope attached at an actual initialized statement comes from its own
invocation entry and direct lexical path. -/
theorem retain_at_statement {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (snapshot : Snapshot prepared mapping world function binding lexical location
      (GeneralizedLocalReachedAllocation.Attachment function binding lexical) candidate native)
    {roots : List NodeId} (entry : ResidualEntryCovered binding.source roots lexical.domain)
    {id : StatementId} (path : LocalLambdaLexicalPath binding.source roots (.statement id))
    {statement : StatementNode}
    (found : binding.source.lookupNode? id.occurrence = some (.statement statement))
    (form : statement.form = .letDecl binding.binder (some binding.initializer)) :
    Snapshot prepared mapping world function binding lexical location
      (Attachment function binding lexical) candidate native :=
  retain_scope snapshot (entry.capture path found form)

/-- Loop initializer and post items retain scope from their actual enclosing
loop occurrence, including when the surrounding invocation is contextual. -/
theorem retain_at_header {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (snapshot : Snapshot prepared mapping world function binding lexical location
      (GeneralizedLocalReachedAllocation.Attachment function binding lexical) candidate native)
    {roots : List NodeId} (entry : ResidualEntryCovered binding.source roots lexical.domain)
    {id : StatementId} (path : LocalLambdaLexicalPath binding.source roots (.statement id))
    {statement : StatementNode}
    (found : binding.source.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    (member : .letDecl binding.binder (some binding.initializer) ∈ initializers ++ post) :
    Snapshot prepared mapping world function binding lexical location
      (Attachment function binding lexical) candidate native :=
  retain_scope snapshot (ResidualScopeReachability.capture_header entry path found form member)

private theorem expression_before {source : TypedSource} {substitution : Substitution}
    {id : ExpressionId} {node : ExpressionNode}
    (accepted : (source.applySubstitution substitution).lookupExpression? id = some node) :
    ∃ original, source.lookupNode? id.occurrence = some (.expression original) ∧
      original.applySubstitution substitution = node := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode? at accepted
  simp only [TypedSource.applySubstitution, List.find?_map] at accepted
  have predicate :
      ((fun candidate => decide (candidate.occurrenceId = id.occurrence)) ∘
        Node.applySubstitution substitution) =
      (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [predicate] at accepted
  cases found : source.lookupNode? id.occurrence with
  | none => simp only [TypedSource.lookupNode?] at found; simp [found] at accepted
  | some candidate =>
    have selected := found
    unfold TypedSource.lookupNode? at selected
    cases candidate with
    | statement statement => simp [selected, Node.applySubstitution] at accepted
    | expression original =>
      refine ⟨original, rfl, ?_⟩
      simpa only [selected, Option.map_some, Node.applySubstitution, Option.some.injEq] using accepted

/-- The accepted matcher covers every own quantifier; its actual cumulative
candidate also retains every key in the saved lexical context. -/
theorem read_keys {catalog : SourceCoreLocalPolymorphism.Catalog}
    {caller : SourceCoreLocalPolymorphism.Key} {active lexical : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    (extension : ContextExtension lexical active) :
    ∀ metavariable, metavariable ∈ receipt.binding.binder.scheme.quantified ∨
      metavariable ∈ lexical.domain → metavariable ∈ receipt.candidate.origin.substitution.domain := by
  intro metavariable member
  rw [receipt.candidate_key, Substitution.mem_domain_compose_iff]
  rcases member with own | saved
  · right
    have domain : receipt.child.domain = receipt.binding.binder.scheme.quantified :=
      (SourceSpecialization.matchClosedSchemeInstance?_sound receipt.matched).2.2.1
    exact domain.symm ▸ own
  · exact .inl (extension.domain metavariable saved)

/-- The same Packet fixes the body list after specialization. This producer
uses the stored scope and actual accepted read, without a source-wide equality
or a law about arbitrary future contexts. -/
theorem body_at_read (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : SourceCoreLocalPolymorphism.Key} {active lexical : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals
      caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure}
    (attached : Attachment function receipt.binding lexical)
    (extension : ContextExtension lexical active)
    {inputs : Inputs} {raw : Core.Expr} (packet : Packet inputs receipt.candidate raw)
    (initializer : inputs.initializer = receipt.binding.initializer) :
    ResidualEntryCovered receipt.binding.source (packet.statements.map NodeId.statement)
      packet.original.emission.prepared.substitution.domain := by
  obtain ⟨_, source, _, _⟩ := GeneralizedLocalAcceptedCatalogFormation.read_origins receipt
  have accepted := packet.found
  rw [GeneralizedLocalLambdaEmissionFacts.Emission.source, source, initializer] at accepted
  obtain ⟨original, found, same⟩ := expression_before accepted
  have form := packet.form
  rw [← same] at form
  cases original with
  | mk id span type actual requirements coercions localStart =>
    cases actual <;> simp only [ExpressionNode.applySubstitution,
      ExpressionForm.applySubstitution] at form <;> try contradiction
    rename_i parameters result body
    have bodyEq : body = packet.statements := (ExpressionForm.lambda.inj form).2.2
    rw [GeneralizedLocalLambdaEmissionFacts.Emission.substitution, ← bodyEq]
    exact attached.captured.body (read_keys receipt extension) found rfl

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedLambdaHeader
/-! The retained capture identifies the original lambda header through the
saved body view. Substitution preserves its body occurrence identities. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedLambdaHeader
open Frontend SourceInference TypeSystem
open CallableBodyMetadataViews CallableLambdaBodyReachability

/-- Invert the actual substituted lookup, retaining the same lambda body.
Parameter and result types may have changed under the substitution. -/
theorem lambda_header_before_substitution
    {source : TypedSource} {active : Substitution} {initializer : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : Ty}
    {body : List StatementId}
    (found : (source.applySubstitution active).lookupExpression? initializer = some node)
    (form : node.form = .lambda parameters result body) :
    ∃ original originalParameters originalResult,
      source.lookupExpression? initializer = some original ∧
      original.form = .lambda originalParameters originalResult body := by
  rw [lookupExpression_apply] at found
  cases selected : source.lookupExpression? initializer with
  | none => simp only [selected, Option.map_none, reduceCtorEq] at found
  | some original =>
      simp only [selected, Option.map_some, Option.some.injEq] at found
      rw [← found] at form
      cases original with
      | mk id span type actual requirements coercions localStart =>
          cases actual <;>
            simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
              reduceCtorEq] at form
          next oldParameters oldResult oldBody =>
            have sameBody := (ExpressionForm.lambda.inj form).2.2
            exact ⟨_, oldParameters, oldResult, rfl, sameBody ▸ rfl⟩

/-- The stored Attachment and the real capture recover a header in the same
original binding source, without asserting whole-source equality. -/
theorem captured_header
    {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : Substitution}
    (saved : GeneralizedLocalCapturedScopes.Attachment function binding lexical)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = binding.initializer) :
    ∃ original parameters result,
      binding.source.lookupExpression? binding.initializer = some original ∧
      original.form = .lambda parameters result function.body := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  have reached : Reaches function.source (lambdaRoots function.initializer function.body)
      (.expression function.initializer) := .root (List.mem_cons_self)
  obtain ⟨original, originalFound, _, originalForm⟩ :=
    saved.view.expression_back (.inl reached) found
  rw [initializer] at originalFound
  exact lambda_header_before_substitution originalFound (originalForm.trans form)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedLambdaHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
/-! A generalized declaration retains its exact lexical compiler binding and
the native row created at its actual source location. Source metadata transport
and native row transport remain separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
open Core Frontend SourceInference TypeSystem GeneralHeap GenericHeap SourceCoreLocalPolymorphism
open GeneralizedLocalDescriptorHeap

variable {definitions : Core.DataEnvironment} {model : InstanceModel definitions}
  {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}

structure Attachment (model : InstanceModel definitions) (function : Dynamic.GeneralizedClosure)
    (binding : Binding) (lexical : Substitution) : Prop where
  registered : model.locals.binding binding.caller binding.binder.id = .ok binding
  captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
    function.captured function.binder function.initializer function
  origin : model.Origin function binding lexical
  binder : function.binder.id = binding.binder.id
  initializer : function.initializer = binding.initializer

structure Located (model : InstanceModel definitions) (function : Dynamic.GeneralizedClosure)
    (binding : Binding) (lexical : Substitution) (location : Dynamic.Location)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  attachment : Attachment model function binding lexical
  cell : Dynamic.Cell
  sourceRead : Dynamic.Heap.Reads heap location cell
  descriptor : cell.generalized = some function
  target : Core.Location
  reference : ReferenceRepresents mapping world location target (binding.bundleType lexical)
  values : List Core.Value
  rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical)
    (binding.atContext lexical) values
  nativeRead : store.read? target = some (.inRight .unit (ProductBundle.value values))

theorem Attachment.stored (attachment : Attachment model function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {values : List Core.Value}
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical)
      (binding.atContext lexical) values) :
    Stored model mapping world function (ProductBundle.value values) (binding.bundleType lexical) :=
  .bundle binding lexical attachment.registered attachment.captures attachment.origin
    attachment.binder attachment.initializer rows

private theorem extend_rows {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {candidates : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical) candidates values)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ProductBundle.Pointwise (model.Represents futureMapping futureWorld function binding lexical) candidates values := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih => exact .cons (model.extend head maps worlds) ih

/-- Metadata extension preserves the actual descriptor. The stored native row
is retained only when its real location still contains that same value. -/
theorem Located.extend {location : Dynamic.Location} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {heap after : Dynamic.Heap} {store updated : Store}
    (located : Located model function binding lexical location mapping world heap store)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (nativeRead : updated.read? located.target = some (.inRight .unit (ProductBundle.value located.values))) :
    Nonempty (Located model function binding lexical location futureMapping futureWorld after updated) := by
  obtain ⟨cell, sourceRead, _, descriptor⟩ := metadata location located.cell located.sourceRead
  exact ⟨⟨located.attachment, cell, sourceRead, descriptor.trans located.descriptor,
    located.target, ⟨maps.lookup located.reference.mapped, worlds.lookup located.reference.typed⟩,
    located.values, extend_rows located.rows maps worlds, nativeRead⟩⟩

/-- Actual parameter allocation only appends native cells. -/
theorem Located.append {location : Dynamic.Location} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {heap after : Dynamic.Heap} {store : Store} (suffix : Store)
    (located : Located model function binding lexical location mapping world heap store)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Nonempty (Located model function binding lexical location futureMapping futureWorld after (store ++ suffix)) := by
  apply located.extend metadata maps worlds
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp located.nativeRead).1).trans located.nativeRead

/-- Administrative frame changes are disjoint from the mapped descriptor. -/
theorem Located.set_unmapped {location : Dynamic.Location} {mapping : LocationMap}
    {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (located : Located model function binding lexical location mapping world heap store)
    {target : Core.Location} (value : Core.Value) (unmapped : target ∉ mapping) :
    Nonempty (Located model function binding lexical location mapping world heap (store.set target value)) := by
  have different : target ≠ located.target := by
    intro same
    exact unmapped (same.symm ▸ List.mem_of_getElem? located.reference.mapped)
  apply located.extend (.refl heap) (.refl mapping) (.refl world)
  simpa [Store.read?, different] using located.nativeRead

/-- A write to an ordinary Source cell cannot overwrite this descriptor's
native row. The separation comes from actual reads and map injectivity. -/
theorem Located.write_ordinary {location writtenLocation : Dynamic.Location} {mapping : LocationMap}
    {world : StoreTyping} {heap after : Dynamic.Heap} {store updated : Store}
    (located : Located model function binding lexical location mapping world heap store)
    (injective : LocationMap.Injective mapping)
    {cell : Dynamic.Cell} {writtenTarget : Core.Location} {payload : Core.Ty}
    (sourceRead : Dynamic.Heap.Reads heap writtenLocation cell) (ordinary : cell.generalized = none)
    (reference : ReferenceRepresents mapping world writtenLocation writtenTarget payload)
    {sourceValue : Option Dynamic.Value} {nativeValue : Core.Value}
    (written : Dynamic.Heap.Writes heap writtenLocation sourceValue after)
    (nativeWritten : store.write? writtenTarget nativeValue = some updated) :
    Nonempty (Located model function binding lexical location mapping world after updated) := by
  have different : location ≠ writtenLocation := by
    intro same
    subst writtenLocation
    have cells := located.sourceRead.functional sourceRead
    have descriptors := congrArg Dynamic.Cell.generalized cells
    rw [located.descriptor, ordinary] at descriptors
    cases descriptors
  have nativeDifferent : located.target ≠ writtenTarget := by
    intro same
    have indices := injective (same ▸ located.reference.mapped) reference.mapped
    apply different
    cases location
    cases writtenLocation
    exact congrArg Dynamic.Location.mk indices
  apply located.extend (.of_write written) (.refl mapping) (.refl world)
  exact (Store.write?_preserves_other nativeWritten nativeDifferent).trans located.nativeRead

/-- This is the actual three-cell marked allocation used by the compiler. -/
theorem of_marked_allocation {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {location : Dynamic.Location} {values : List Core.Value}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : CellHeapRepresents (cellModel ordinary model) mapping world before store)
    (attachment : Attachment model function binding lexical)
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical)
      (binding.atContext lexical) values)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType definitions)
    (markerTyped : RuntimeValueHasType world marker markerType definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function location after) :
    CellHeapRepresents (cellModel ordinary model) (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
      (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
    Nonempty (Located model function binding lexical location (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
      (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)])) := by
  obtain ⟨afterHeaps, reference⟩ := CallableIndexedCellAllocation.heap_allocate heaps snapshotTyped markerTyped
    (CellRepresents.generalized (attachment.stored rows)) (.generalized allocated)
  refine ⟨afterHeaps, ⟨⟨attachment, _, allocated.reads_new, rfl, _, reference, values,
    extend_rows rows ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩⟩⟩
  simp [Store.read?]

theorem of_marked_allocation_values {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {location : Dynamic.Location} {values : List Core.Value}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : CellHeapRepresents (cellModel ordinary model) mapping world before store)
    (attachment : Attachment model function binding lexical)
    (rows : ProductBundle.Pointwise (model.Represents mapping world function binding lexical)
      (binding.atContext lexical) values)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType definitions)
    (markerTyped : RuntimeValueHasType world marker markerType definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function location after) :
    CellHeapRepresents (cellModel ordinary model) (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
      (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
    (∃ located : Located model function binding lexical location (mapping ++ [store.length + 2])
      (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
      (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]), located.values = values) := by
  obtain ⟨afterHeaps, reference⟩ := CallableIndexedCellAllocation.heap_allocate heaps snapshotTyped markerTyped
    (CellRepresents.generalized (attachment.stored rows)) (.generalized allocated)
  refine ⟨afterHeaps, ⟨⟨attachment, _, allocated.reads_new, rfl, _, reference, values,
    extend_rows rows ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩, rfl⟩⟩
  simp [Store.read?]

private theorem project_readOnly {types : List Core.Ty} {index : Nat} {bundle projection : Core.Expr}
    (restricted : ReadOnly.Expression bundle)
    (selected : ProductBundle.project? types index bundle = some projection) :
    ReadOnly.Expression projection := by
  induction types generalizing index bundle projection with
  | nil => cases selected
  | cons head rest ih =>
    cases rest with
    | nil =>
      cases index with
      | zero => cases selected; exact restricted
      | succ index => cases selected
    | cons next remaining =>
      cases index with
      | zero => cases selected; exact .first restricted
      | succ index => exact ih (.second restricted) selected

theorem readOnly {catalog : Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered) :
    ReadOnly.Expression lowered.expression := by
  rw [receipt.emitted]
  exact .caseE (.caseE (.loadCell .var) (.inLeft .word) (.inRight .var))
    (.inLeft .var) (.inRight (project_readOnly .var receipt.projected))

/-- Actual first-match source and native lookups join the read certificate to
the row retained by its declaration. Full candidate context still selects it. -/
theorem Located.preserves {location : Dynamic.Location} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store}
    (located : Located model function binding lexical location mapping world heap store)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate model.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical : Core.Environment}
    (environments : EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location) :
    ∃ native, model.Represents mapping world function binding lexical receipt.candidate native ∧
      Evaluates canonical store lowered.expression (.inRight .word native) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    simp only [sameCaller, sameBinder, located.attachment.registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨target, referenceAt, reference⟩ := environments.lookup_visible lookup receipt.slot
  have sameTarget : target = located.target := Option.some.inj (reference.mapped.symm.trans located.reference.mapped)
  subst target
  have payload : receipt.payloadType = binding.bundleType lexical := by
    simpa [OptionalCell.cellType] using Option.some.inj (reference.typed.symm.trans located.reference.typed)
  have bundleType : binding.bundleType active = binding.bundleType lexical := by
    have checked := receipt.bundleType
    rw [sameBinding] at checked
    exact checked.trans payload
  have sameRows : receipt.binding.atContext active = binding.atContext lexical := by
    rw [sameBinding]
    exact (GeneralizedLocalBundleContexts.atContext_eq_of_bundleType context binding bundleType.symm).symm
  apply GeneralizedLocalBundleReadMeaning.preserves receipt
  · rw [sameRows]
    exact located.rows
  · exact referenceAt
  · exact located.nativeRead

/-- Renaming reads exactly the same existing closure value and store. -/
theorem Located.preserves_rename {location : Dynamic.Location} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store}
    (located : Located model function binding lexical location mapping world heap store)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate model.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ native, model.Represents mapping world function binding lexical receipt.candidate native ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  obtain ⟨native, represented, evaluated⟩ := located.preserves receipt sameCaller sameBinder context environments lookup
  exact ⟨native, represented, (readOnly receipt).evaluation_rename evaluated agrees⟩

theorem Located.reflects_rename {location : Dynamic.Location} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {before after : Store}
    (located : Located model function binding lexical location mapping world heap before)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate model.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming} {output : Core.Value}
    (environments : EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual)
    (evaluated : Evaluates actual before (lowered.expression.rename embedding) output after) :
    after = before ∧ ∃ native, output = .inRight .word native ∧
      model.Represents mapping world function binding lexical receipt.candidate native := by
  obtain ⟨native, represented, expected⟩ := located.preserves_rename receipt sameCaller sameBinder context environments lookup agrees
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated expected
  exact ⟨rfl, native, rfl, represented⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceFrames
/-! The actual snapshot reference is retained through storage and heap
extension. This is creation evidence; a shared reference is never inferred
from equal native payload types or source binder identifiers. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : Substitution} {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}

inductive Framed (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) (frameLocation : Core.Location) :
    SourceCoreLocalPolymorphism.Instance → Core.Value → Prop where
  | retained {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
      {raw : Core.Expr} {actual : Core.Environment}
      (packet : Packet inputs candidate raw) (indexed : Indexed prepared packet)
      (bodyProfile : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
        packet.original.emission.prepared.source inputs.initializer)
      (sameLexical : indexed.lexical = lexical)
      (owner : inputs.current.owner = binding.caller)
      (initializer : inputs.initializer = binding.initializer)
      (candidateSource : candidate.origin.source = binding.source)
      (candidateBinder : candidate.origin.binder.id = binding.binder.id)
      (descriptorSource : function.source = binding.source)
      (origin : Origin prepared function binding lexical)
      (namedLexical : lexical = [])
      (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
      (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
      (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
      (ownership : LocalIdentityOwnership function.source)
      (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
      (frameReference : captured.canonical[referenceIndex indexed]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
      (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
        raw candidate.type prepared.layouts.definitions)
      (runtimeTyped : RuntimeValueHasType world (value indexed captured.embedding origin.native actual)
        candidate.type prepared.layouts.definitions) :
      Framed prepared mapping world function binding lexical frameLocation candidate
        (value indexed captured.embedding origin.native actual)

theorem Framed.forget {location : Core.Location}
    (framed : Framed prepared mapping world function binding lexical location candidate native) :
    Represents prepared mapping world function binding lexical candidate native := by
  cases framed with
  | retained packet indexed profile sameLexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed profile sameLexical owner initializer candidateSource candidateBinder descriptorSource
      origin namedLexical namedMetadata captured declarations ownership issuer location reference typed runtimeTyped

theorem Framed.extend {location : Core.Location}
    (framed : Framed prepared mapping world function binding lexical location candidate native)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Framed prepared futureMapping futureWorld function binding lexical location candidate native := by
  cases framed with
  | retained packet indexed profile sameLexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed profile sameLexical owner initializer candidateSource candidateBinder descriptorSource
      origin namedLexical namedMetadata (captured.extend maps worlds) declarations ownership issuer reference typed (runtimeTyped.weaken worlds)

theorem formation_at_frame {inputs : Inputs} {raw : Core.Expr} {packet : Packet inputs candidate raw}
    (indexed : Indexed prepared packet)
    (bodyProfile : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
      packet.original.emission.prepared.source inputs.initializer)
    {actual : Core.Environment}
    (sameLexical : indexed.lexical = lexical) (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (candidateSource : candidate.origin.source = binding.source)
    (candidateBinder : candidate.origin.binder.id = binding.binder.id)
    (descriptorSource : function.source = binding.source)
    (origin : Origin prepared function binding lexical)
    (namedLexical : lexical = [])
    (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
      (ownership : LocalIdentityOwnership function.source)
      (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding) (value indexed captured.embedding origin.native actual) store ∧
    Framed prepared mapping world function binding lexical location candidate
      (value indexed captured.embedding origin.native actual) := by
  have evaluated := formation_evaluates indexed captured reference read
  obtain ⟨future, _, finalStored, outputTyped⟩ :=
    evaluation_preserves_type evaluated (typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  exact ⟨evaluated, .retained packet indexed bodyProfile sameLexical owner initializer candidateSource candidateBinder descriptorSource
    origin namedLexical namedMetadata captured declarations ownership issuer reference typed outputTyped⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues

namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
open Core Frontend SourceInference TypeSystem GeneralHeap
open SourceCoreLocalPolymorphism GeneralizedLocalInstanceValues

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
  {location : Dynamic.Location} {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store finalStore : Store}

def Located.Frames (located : Located (model prepared) function binding lexical location mapping world heap store)
    (frameLocation : Core.Location) : Prop :=
  ProductBundle.Pointwise (Framed prepared mapping world function binding lexical frameLocation)
    (binding.atContext lexical) located.values

theorem Located.Frames.transport
    {previous : Located (model prepared) function binding lexical location mapping world heap store}
    {next : Located (model prepared) function binding lexical location futureMapping futureWorld after finalStore}
    {frameLocation : Core.Location} (frames : previous.Frames frameLocation)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (sameValues : next.values = previous.values) : next.Frames frameLocation := by
  change ProductBundle.Pointwise _ _ _
  rw [sameValues]
  change ProductBundle.Pointwise _ _ _ at frames
  generalize binding.atContext lexical = selected at frames ⊢
  generalize previous.values = payload at frames ⊢
  induction frames with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extend maps worlds) ih

theorem Located.preserves_framed
    (located : Located (model prepared) function binding lexical location mapping world heap store)
    {frameLocation : Core.Location} (frames : located.Frames frameLocation)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate prepared.base.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical prepared.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ native, Framed prepared mapping world function binding lexical frameLocation receipt.candidate native ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : prepared.base.locals.binding binding.caller binding.binder.id = .ok binding := located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨target, referenceAt, reference⟩ := environments.lookup_visible lookup receipt.slot
  have sameTarget : target = located.target := Option.some.inj (reference.mapped.symm.trans located.reference.mapped)
  subst target
  have payload : receipt.payloadType = binding.bundleType lexical := by
    simpa [OptionalCell.cellType] using Option.some.inj (reference.typed.symm.trans located.reference.typed)
  have bundleType : binding.bundleType active = binding.bundleType lexical := by
    have checked := receipt.bundleType
    rw [sameBinding] at checked
    exact checked.trans payload
  have sameRows : receipt.binding.atContext active = binding.atContext lexical := by
    rw [sameBinding]
    exact (GeneralizedLocalBundleContexts.atContext_eq_of_bundleType context binding bundleType.symm).symm
  have rows : ProductBundle.Pointwise (Framed prepared mapping world function binding lexical frameLocation)
      (receipt.binding.atContext active) located.values := sameRows ▸ frames
  obtain ⟨native, framed, evaluated⟩ := GeneralizedLocalBundleReadMeaning.preserves receipt rows referenceAt located.nativeRead
  exact ⟨native, framed, (readOnly receipt).evaluation_rename evaluated agrees⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAssociationFormation
/-! The selected row of an actual generalized allocation supplies the complete
materialized association. The Source substitution and dictionary are supplied
by the actual read rule; all compiler ancestry is recovered from that row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAssociationFormation
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : LocationMap} {world : StoreTyping}
  {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem materialize
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : TypeSystem.Substitution} {native : Value}
    (row : GeneralizedLocalInstanceValues.Represents compiled.indexed mapping world descriptor
      receipt.binding lexical receipt.candidate native)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  cases row with
  | retained packet indexed bodyProfile sameLexical owner instanceInitializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer frameLocation frameReference typed runtimeTyped =>
    have initializerEq := initializer.trans instanceInitializer.symm
    have sourceEq := GeneralizedLocalNamedMaterialization.source_eq receipt instantiation sameScheme sameType
      descriptorSource candidateSource packet
    obtain ⟨code, compilation, active, _id, loweredEq, _policy, _lowerBody, _fuel, _descriptor, _certificate, codeView, reasons, valueEq⟩ :=
      GeneralizedLocalNamedMaterialization.code_at_read receipt instantiation sameScheme sameType
        descriptorSource candidateSource packet indexed captures unique initializerEq captured typed profile origin.native
    have materializedUnique : NodeOccurrencesUnique
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source := by
      change ((descriptor.source.applySubstitution semantic).nodes.map Node.occurrenceId).Nodup
      change (descriptor.source.nodes.map Node.occurrenceId).Nodup at unique
      simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique
    let material : Materialization compiled mapping world
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)) :=
      { descriptor := descriptor, binding := receipt.binding, lexical := lexical
        inputs := _, candidate := receipt.candidate, raw := _, packet := packet, indexed := indexed, bodyProfile := bodyProfile
        sameLexical := sameLexical, owner := owner, initializer := instanceInitializer
        candidateSource := candidateSource, candidateBinder := candidateBinder, descriptorSource := descriptorSource, descriptorInitializer := initializer, binderScheme := sameScheme
        origin := origin, namedLexical := namedLexical, namedMetadata := namedMetadata, descriptorUnique := unique, sourceCaptures := captures, context := context, callerEvidence := callerEvidence
        produced := produced, actualType := actualType, requirements := requirements, semantic := semantic
        instantiation := instantiation, materialized := rfl, actual := _, captured := captured
        capturedDeclarations := GeneralizedLocalScopeDeclarations.materialized declarations semantic (produced ++ callerEvidence.applySubstitution semantic)
        frameLocation := frameLocation, frameReference := frameReference, code := code
        compilation := compilation, active := active, lowered := loweredEq, codeId := _id, policy := _policy, lowerBody := _lowerBody,
        fuel := _fuel, descriptorId := _descriptor, certificate := _certificate, view := codeView, reasons := reasons, source := sourceEq,
        rawTyped := valueEq.symm ▸ runtimeTyped,
        ownership := FlexibleSubstitution.LocalIdentityOwnership.applySubstitution semantic ownership,
        issuer := issuer, unique := materializedUnique }
    exact ⟨material, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, valueEq.symm⟩


theorem materialize_framed
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : TypeSystem.Substitution} {native : Value}
    {frameLocation : Core.Location}
    (row : GeneralizedLocalInstanceValues.Framed compiled.indexed mapping world descriptor
      receipt.binding lexical frameLocation receipt.candidate native)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      material.frameLocation = frameLocation ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  cases row with
  | retained packet indexed bodyProfile sameLexical owner instanceInitializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer frameReference typed runtimeTyped =>
    have initializerEq := initializer.trans instanceInitializer.symm
    have sourceEq := GeneralizedLocalNamedMaterialization.source_eq receipt instantiation sameScheme sameType
      descriptorSource candidateSource packet
    obtain ⟨code, compilation, active, _id, loweredEq, _policy, _lowerBody, _fuel, _descriptor, _certificate, codeView, reasons, valueEq⟩ :=
      GeneralizedLocalNamedMaterialization.code_at_read receipt instantiation sameScheme sameType
        descriptorSource candidateSource packet indexed captures unique initializerEq captured typed profile origin.native
    have materializedUnique : NodeOccurrencesUnique
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source := by
      change ((descriptor.source.applySubstitution semantic).nodes.map Node.occurrenceId).Nodup
      change (descriptor.source.nodes.map Node.occurrenceId).Nodup at unique
      simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique
    let material : Materialization compiled mapping world
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)) :=
      { descriptor := descriptor, binding := receipt.binding, lexical := lexical
        inputs := _, candidate := receipt.candidate, raw := _, packet := packet, indexed := indexed, bodyProfile := bodyProfile
        sameLexical := sameLexical, owner := owner, initializer := instanceInitializer
        candidateSource := candidateSource, candidateBinder := candidateBinder, descriptorSource := descriptorSource, descriptorInitializer := initializer, binderScheme := sameScheme
        origin := origin, namedLexical := namedLexical, namedMetadata := namedMetadata, descriptorUnique := unique, sourceCaptures := captures, context := context, callerEvidence := callerEvidence
        produced := produced, actualType := actualType, requirements := requirements, semantic := semantic
        instantiation := instantiation, materialized := rfl, actual := _, captured := captured
        capturedDeclarations := GeneralizedLocalScopeDeclarations.materialized declarations semantic (produced ++ callerEvidence.applySubstitution semantic)
        frameLocation := frameLocation, frameReference := frameReference, code := code
        compilation := compilation, active := active, lowered := loweredEq, codeId := _id, policy := _policy, lowerBody := _lowerBody,
        fuel := _fuel, descriptorId := _descriptor, certificate := _certificate, view := codeView, reasons := reasons, source := sourceEq,
        rawTyped := valueEq.symm ▸ runtimeTyped,
        ownership := FlexibleSubstitution.LocalIdentityOwnership.applySubstitution semantic ownership,
        issuer := issuer, unique := materializedUnique }
    exact ⟨material, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, valueEq.symm⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAssociationFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization
/-! Actual local reads consume a reached-body attachment and the authentic
Packet. They create the same native Code without a global metadata view. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open CallableBodyMetadataViews CallableLambdaBodyReachability
open CallableAncestryProfiles.SourceComposition
variable {caller : SourceCoreLocalPolymorphism.Key} {active : Substitution}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem source_view (compiled : SourceCoreUnifiedCompilation.Compiled)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actual = receipt.node.rawType)
    (attachment : GeneralizedLocalReachedAllocation.Attachment function receipt.binding active)
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw) :
    BodyView
      (function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source
      packet.original.emission.prepared.source (lambdaRoots function.initializer function.body) := by
  obtain ⟨_, candidateSource, _, _⟩ := GeneralizedLocalAcceptedCatalogFormation.read_origins receipt
  change BodyView (function.source.applySubstitution semantic) _ _
  rw [CallableFlexibleSubstitutionAgreement.typedSource_congr
    (GeneralizedLocalContextualMaterialization.lookup_eq receipt instantiation sameScheme sameType) function.source]
  rw [GeneralizedLocalLambdaEmissionFacts.Emission.source, candidateSource,
    receipt.candidate_key, CallableAncestryProfiles.SourceComposition.source _ _ attachment.closed]
  exact attachment.view.applySubstitution receipt.child

theorem header_of_view
    {function : Dynamic.GeneralizedClosure} {semantic : Substitution} {evidence : Dynamic.EvidenceEnvironment}
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (packet : Packet inputs candidate raw)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    (view : BodyView (function.instantiate semantic evidence).source
      packet.original.emission.prepared.source (lambdaRoots function.initializer function.body)) :
    (function.instantiate semantic evidence).parameters = packet.parameters ∧
    (function.instantiate semantic evidence).resultType = packet.result ∧
    (function.instantiate semantic evidence).body = packet.statements := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  have substituted := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution
    function.source semantic function.initializer node found
  obtain ⟨sameNode, sameFound, _, sameForm⟩ := view.expression (.inl (.root (by simp [lambdaRoots, initializer]))) packet.found
  change (function.source.applySubstitution semantic).lookupExpression? inputs.initializer = some sameNode at sameFound
  rw [initializer] at substituted
  have nodes := Option.some.inj (substituted.symm.trans sameFound)
  have forms := (congrArg ExpressionNode.form nodes).trans (sameForm.trans packet.form)
  simp only [ExpressionNode.applySubstitution, form, ExpressionForm.applySubstitution] at forms
  exact ExpressionForm.lambda.inj forms

theorem code_at_read (compiled : SourceCoreUnifiedCompilation.Compiled)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actualType : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actualType requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actualType = receipt.node.rawType)
    (attachment : GeneralizedLocalReachedAllocation.Attachment function receipt.binding active)
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw)
    (indexed : GeneralizedLocalLambdaGeneration.Indexed compiled.indexed packet)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world inputs.scope function.captured actual)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw receipt.candidate.type compiled.indexed.layouts.definitions)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (native : CallableIndexedHistory.NativeFrame) :
    let instantiated := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ code : CallableIndexedLambdaValues.Code compiled.indexed instantiated inputs.scope captured.administrative
        (fun source view => BodyView source view (function.body.map NodeId.statement)),
      code.compilation = GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared ∧
      code.active = packet.original.emission.prepared.substitution ∧
      code.id = inputs.initializer ∧ code.lowered = packet.original.lowered ∧
      code.policy = GeneralizedLocalLambdaCompilation.policy inputs packet.original.emission.prepared packet.fuel ∧
      code.lowerBody = GeneralizedLocalLambdaCompilation.lowerBody inputs packet.original.emission.prepared ∧
      code.fuel = packet.fuel ∧ code.descriptor.id = indexed.descriptor.id ∧
      HEq code.receipt packet.certificate ∧
      code.view = packet.original.emission.prepared.source ∧
      code.reasonAt = inputs.reasonAt ∧
      CallableIndexedLambdaValues.value code captured.embedding native actual =
        GeneralizedLocalInstanceValues.value indexed captured.embedding native actual := by
  have view := source_view compiled receipt instantiation sameScheme sameType attachment packet
  obtain ⟨parameters, result, body⟩ := header_of_view packet captures unique initializer view
  have typedLowered : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      packet.original.lowered.expression (LanguageResult.resultType packet.original.lowered.type)
      compiled.indexed.layouts.definitions := by
    rw [packet.original.extracted, ← packet.original.nativeType]
    exact LanguageResult.success_hasType typed
  obtain ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons⟩ :=
    indexed.code_at_read_with_view
      (viewRelation := fun source target => BodyView source target (function.body.map NodeId.statement))
      _ captured.administrative parameters result body profile
      (view.restrict (fun id member => .root (List.mem_cons_of_mem _ member)))
      (by
        obtain ⟨node, found, _, form⟩ := view.expression
          (.inl (.root (by simp [lambdaRoots, initializer]))) packet.found
        exact ⟨node, found, form⟩) typedLowered
  exact ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons,
    GeneralizedLocalMaterializedCode.value_eq indexed code lowered policy id captured.embedding native actual⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization

/-! Actual first-match lookup and the descriptor allocation's retained row
supply materialization at a named read. The native read keeps both the store
and the exact previously created closure value. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization
open Core Frontend SourceInference GeneralHeap ReadOnly CompatibleEquality
open GeneralizedLocalLocatedRows GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : TypeSystem.Substitution} {location : Dynamic.Location}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem preserves
    (located : Located (GeneralizedLocalInstanceValues.model compiled.indexed) descriptor binding lexical
      location mapping world heap store)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical [])
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual)
    (unique : NodeOccurrencesUnique descriptor.source)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      Evaluates actual store (lowered.expression.rename embedding)
        (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
          material.origin.native material.actual)) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding :=
      located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨native, represented, evaluated⟩ :=
    located.preserves_rename receipt sameCaller sameBinder contextExtension environments lookup agrees
  have represented : GeneralizedLocalInstanceValues.Represents compiled.indexed mapping world descriptor
      receipt.binding lexical receipt.candidate native := by
    rw [sameBinding]
    exact represented
  have initializer : descriptor.initializer = receipt.binding.initializer := by
    rw [sameBinding]
    exact located.attachment.initializer
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEq, producedEq, requirementsEq, nativeEq⟩ :=
    GeneralizedLocalAssociationFormation.materialize receipt represented located.attachment.captures unique
      initializer instantiation sameScheme sameType profile
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
    callerEq, producedEq, requirementsEq, ?_⟩
  simpa only [nativeEq] using evaluated


theorem preserves_framed
    (located : Located (GeneralizedLocalInstanceValues.model compiled.indexed) descriptor binding lexical
      location mapping world heap store)
    {frameLocation : Core.Location} (frames : located.Frames frameLocation)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical [])
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual)
    (unique : NodeOccurrencesUnique descriptor.source)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      material.frameLocation = frameLocation ∧
      Evaluates actual store (lowered.expression.rename embedding)
        (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
          material.origin.native material.actual)) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding :=
      located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨native, represented, evaluated⟩ :=
    located.preserves_framed frames receipt sameCaller sameBinder contextExtension environments lookup agrees
  have framed : GeneralizedLocalInstanceValues.Framed compiled.indexed mapping world descriptor
      receipt.binding lexical frameLocation receipt.candidate native := by
    rw [sameBinding]
    exact represented
  have initializer : descriptor.initializer = receipt.binding.initializer := by
    rw [sameBinding]
    exact located.attachment.initializer
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEq, producedEq, requirementsEq, frameEq, nativeEq⟩ :=
    GeneralizedLocalAssociationFormation.materialize_framed receipt framed located.attachment.captures unique
      initializer instantiation sameScheme sameType profile
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
    callerEq, producedEq, requirementsEq, frameEq, ?_⟩
  simpa only [nativeEq] using evaluated

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAssociation
/-! The existing Snapshot supplies reached body correspondence. The real read
recovers the same Code, captures and Materialization with the body relation
used by the shared invocation Index. Actual compilation supplies contracts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : LocationMap} {world : StoreTyping}
  {caller : SourceCoreLocalPolymorphism.Key} {active : TypeSystem.Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem materialize_snapshot
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller active source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {native : Value}
    {frameLocation : Core.Location}
    (row : GeneralizedLocalAcceptedInstances.Snapshot compiled.indexed mapping world descriptor
      receipt.binding active frameLocation
      (GeneralizedLocalReachedAllocation.Attachment descriptor receipt.binding active)
      receipt.candidate native)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actualType = receipt.node.rawType)
    :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function
        (fun source view => CallableBodyMetadataViews.BodyView source view (function.body.map NodeId.statement)),
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = active ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      material.frameLocation = frameLocation ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  cases row with
  | retained packet indexed acceptedBody sameLexical owner instanceInitializer candidateSource candidateBinder attachment origin captured declarations ownership issuer frameReference typed runtimeTyped =>
    have initializerEq := initializer.trans instanceInitializer.symm
    obtain ⟨code, compilation, activeEq, _id, loweredEq, _policy, _lowerBody, _fuel, _descriptor, _certificate, codeView, reasons, valueEq⟩ :=
      GeneralizedLocalReachedMaterialization.code_at_read compiled receipt instantiation sameScheme sameType
        attachment packet indexed captures unique initializerEq captured typed (SelectedCompilationPreparedRuntimeFacts.of_compiled compiled).1 origin.native
    have materializedUnique : NodeOccurrencesUnique
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source := by
      change ((descriptor.source.applySubstitution semantic).nodes.map Node.occurrenceId).Nodup
      change (descriptor.source.nodes.map Node.occurrenceId).Nodup at unique
      simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique
    let material : Materialization compiled mapping world
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic))
        (fun source view => CallableBodyMetadataViews.BodyView source view (descriptor.body.map NodeId.statement)) :=
      { descriptor := descriptor, binding := receipt.binding, lexical := active
        inputs := _, candidate := receipt.candidate, raw := _, packet := packet, indexed := indexed, body := acceptedBody
        sameLexical := sameLexical, owner := owner, initializer := instanceInitializer
        candidateSource := candidateSource, candidateBinder := candidateBinder, descriptorInitializer := initializer
        origin := origin, descriptorUnique := unique, sourceCaptures := captures, context := context, callerEvidence := callerEvidence
        produced := produced, actualType := actualType, requirements := requirements, semantic := semantic
        instantiation := instantiation, materialized := rfl, actual := _, captured := captured
        capturedDeclarations := GeneralizedLocalScopeDeclarations.materialized declarations semantic (produced ++ callerEvidence.applySubstitution semantic)
        frameLocation := frameLocation, frameReference := frameReference, code := code
        compilation := compilation, active := activeEq, lowered := loweredEq, codeId := _id, policy := _policy, lowerBody := _lowerBody,
        fuel := _fuel, descriptorId := _descriptor, certificate := _certificate, view := codeView, reasons := reasons,
        rawTyped := valueEq.symm ▸ runtimeTyped,
        ownership := FlexibleSubstitution.LocalIdentityOwnership.applySubstitution semantic ownership,
        issuer := issuer, unique := materializedUnique }
    exact ⟨material, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, valueEq.symm⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedReadMaterialization
/-! A read materializes the same saved lexical Snapshot using a separately
proved active-context body view. Its code, captures and native value are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : LocationMap} {world : StoreTyping}
  {caller : SourceCoreLocalPolymorphism.Key} {active : TypeSystem.Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem materialize_snapshot_at_read
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller active source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {native : Value}
    {frameLocation : Core.Location} {lexical : TypeSystem.Substitution} {attachment : Prop}
    (row : GeneralizedLocalAcceptedInstances.Snapshot compiled.indexed mapping world descriptor
      receipt.binding lexical frameLocation attachment receipt.candidate native)
    (activeAttachment : GeneralizedLocalReachedAllocation.Attachment descriptor receipt.binding active)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actualType = receipt.node.rawType)
    :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function
        (fun source view => CallableBodyMetadataViews.BodyView source view (function.body.map NodeId.statement)),
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      material.frameLocation = frameLocation ∧
      material.candidate.origin.initializer = material.inputs.initializer ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  cases row with
  | retained packet indexed acceptedBody sameLexical owner instanceInitializer candidateSource candidateBinder savedAttachment origin captured declarations ownership issuer frameReference typed runtimeTyped =>
    have initializerEq := initializer.trans instanceInitializer.symm
    obtain ⟨code, compilation, activeEq, _id, loweredEq, _policy, _lowerBody, _fuel, _descriptor, _certificate, codeView, reasons, valueEq⟩ :=
      GeneralizedLocalReachedMaterialization.code_at_read compiled receipt instantiation sameScheme sameType
        activeAttachment packet indexed captures unique initializerEq captured typed (SelectedCompilationPreparedRuntimeFacts.of_compiled compiled).1 origin.native
    have materializedUnique : NodeOccurrencesUnique
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source := by
      change ((descriptor.source.applySubstitution semantic).nodes.map Node.occurrenceId).Nodup
      change (descriptor.source.nodes.map Node.occurrenceId).Nodup at unique
      simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique
    let material : Materialization compiled mapping world
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic))
        (fun source view => CallableBodyMetadataViews.BodyView source view (descriptor.body.map NodeId.statement)) :=
      { descriptor := descriptor, binding := receipt.binding, lexical := lexical
        inputs := _, candidate := receipt.candidate, raw := _, packet := packet, indexed := indexed, body := acceptedBody
        sameLexical := sameLexical, owner := owner, initializer := instanceInitializer
        candidateSource := candidateSource, candidateBinder := candidateBinder, descriptorInitializer := initializer
        origin := origin, descriptorUnique := unique, sourceCaptures := captures, context := context, callerEvidence := callerEvidence
        produced := produced, actualType := actualType, requirements := requirements, semantic := semantic
        instantiation := instantiation, materialized := rfl, actual := _, captured := captured
        capturedDeclarations := GeneralizedLocalScopeDeclarations.materialized declarations semantic (produced ++ callerEvidence.applySubstitution semantic)
        frameLocation := frameLocation, frameReference := frameReference, code := code
        compilation := compilation, active := activeEq, lowered := loweredEq, codeId := _id, policy := _policy, lowerBody := _lowerBody,
        fuel := _fuel, descriptorId := _descriptor, certificate := _certificate, view := codeView, reasons := reasons,
        rawTyped := valueEq.symm ▸ runtimeTyped,
        ownership := FlexibleSubstitution.LocalIdentityOwnership.applySubstitution semantic ownership,
        issuer := issuer, unique := materializedUnique }
    refine ⟨material, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, valueEq.symm⟩
    exact (GeneralizedLocalAcceptedCatalogFormation.read_origins receipt).2.2.2.trans instanceInitializer.symm

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerPackets
/-! Every finite bundle row receives the lambda packet from its actual
candidate source. The scanner observes raw metadata and compatible reads;
accepted compilation supplies the child certificate and emitted code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerPackets
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism DataPatternValues
open GeneralizedLocalInstanceCompilation (Inputs)

structure Observations (representation : SourceCoreGeneralFunctions.Representation)
    (callerKey : Key) (id : ExpressionId) (candidate : Instance) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  reported : Core.Ty
  caller : callerKey = candidate.origin.caller
  initializer : candidate.origin.initializer = id
  found : candidate.source.lookupExpression? id = some node
  form : node.form = .lambda parameters result body
  owner : id.occurrence.owner = candidate.source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  read : representation.expressions.readExpression candidate.source id = .ok (node, reported)

abbrev Profile (inputs : Inputs) :=
  Observations inputs.representation inputs.current.owner inputs.initializer

def observations? (representation : SourceCoreGeneralFunctions.Representation)
    (callerKey : Key) (id : ExpressionId) (candidate : Instance) :
    Option (Observations representation callerKey id candidate) :=
  if caller : callerKey = candidate.origin.caller then
    if initializer : candidate.origin.initializer = id then
      if owner : id.occurrence.owner = candidate.source.owner then
        match found : candidate.source.lookupExpression? id with
        | none => none
        | some node =>
          match form : node.form with
          | .lambda parameters result body =>
            if requirements : node.requirements = [] then
              if coercions : node.coercions = [] then
                match read : representation.expressions.readExpression candidate.source id with
                | .error _ => none
                | .ok (actual, reported) =>
                  if same : actual = node then
                    some ⟨node, parameters, result, body, reported, caller, initializer, found, form,
                      owner, requirements, coercions, by simpa only [same] using read⟩
                  else none
              else none
            else none
          | _ => none
      else none
    else none
  else none

def profile? (inputs : Inputs) (candidate : Instance) : Option (Profile inputs candidate) :=
  observations? inputs.representation inputs.current.owner inputs.initializer candidate

def profiles? (inputs : Inputs) : (candidates : List Instance) →
    Option (PLift (∀ candidate ∈ candidates, Nonempty (Profile inputs candidate)))
  | [] => some ⟨by intro candidate member; cases member⟩
  | candidate :: rest => do
    let head ← profile? inputs candidate
    let ⟨tail⟩ ← profiles? inputs rest
    pure ⟨by
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact ⟨head⟩
      · exact tail selected member⟩

/-- Candidate source identity is checked against the exact stored binding,
separately from its cumulative native key and projected type. -/
structure BindingObservations (representation : SourceCoreGeneralFunctions.Representation)
    (callerKey : Key) (id : ExpressionId) (binding : Binding) (candidate : Instance)
    extends Observations representation callerKey id candidate where
  originalSource : candidate.origin.source = binding.source
  originalBinder : candidate.origin.binder.id = binding.binder.id

abbrev BindingProfile (inputs : Inputs) :=
  BindingObservations inputs.representation inputs.current.owner inputs.initializer

def bindingObservations? (representation : SourceCoreGeneralFunctions.Representation)
    (callerKey : Key) (id : ExpressionId) (binding : Binding) (candidate : Instance) :
    Option (BindingObservations representation callerKey id binding candidate) := do
  let profile ← observations? representation callerKey id candidate
  if originalSource : candidate.origin.source = binding.source then
    if originalBinder : candidate.origin.binder.id = binding.binder.id then
      pure ⟨profile, originalSource, originalBinder⟩
    else none
  else none

def bindingProfile? (inputs : Inputs) (binding : Binding) (candidate : Instance) :
    Option (BindingProfile inputs binding candidate) :=
  bindingObservations? inputs.representation inputs.current.owner inputs.initializer binding candidate

def bindingProfiles? (inputs : Inputs) (binding : Binding) : (candidates : List Instance) →
    Option (PLift (∀ candidate ∈ candidates, Nonempty (BindingProfile inputs binding candidate)))
  | [] => some ⟨by intro candidate member; cases member⟩
  | candidate :: rest => do
    let head ← bindingProfile? inputs binding candidate
    let ⟨tail⟩ ← bindingProfiles? inputs binding rest
    pure ⟨by
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact ⟨head⟩
      · exact tail selected member⟩

theorem Profile.packet {inputs : Inputs} {candidate : Instance} {raw : Core.Expr}
    (profile : Profile inputs candidate)
    (receipt : GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw) :
    Nonempty (GeneralizedLocalLambdaCompilation.Packet inputs candidate raw) := by
  have sourceEq : receipt.emission.prepared.source = candidate.source :=
    GeneralizedLocalLambdaEmissionFacts.Emission.source receipt.emission
  exact GeneralizedLocalLambdaCompilation.of_receipt receipt
    (sourceEq ▸ profile.found) profile.form (sourceEq ▸ profile.owner) profile.requirements profile.coercions
    (sourceEq ▸ profile.read)

/-- The native rows remain paired in the exact original order, even when
several candidates project to the same native function type. -/
def IndexedRows {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (inputs : Inputs) (lexical : Substitution)
    (candidates : List Instance) (closures : List Core.Expr) : Prop :=
  ListRel (fun candidate raw => Nonempty (Sigma fun packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw =>
    { indexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet // indexed.lexical = lexical } ×
      GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner packet.original.emission.prepared.source inputs.initializer)) candidates closures

theorem indexed_rows {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) {inputs : Inputs}
    {candidates : List Instance} {closures : List Core.Expr}
    (rows : ListRel (fun candidate raw => Nonempty (GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw))
      candidates closures)
    (profiles : ∀ candidate ∈ candidates, Nonempty (Profile inputs candidate))
    (bodies : ∀ candidate ∈ candidates, Nonempty (GeneralizedLocalBodyProfile.Profile
      inputs.locals inputs.current.owner candidate.source inputs.initializer))
    (lexical : Substitution)
    (represented : inputs.representation =
      (CallableIndexedNamedGeneration.representation prepared).atContext inputs.current.owner lexical)
    (program : inputs.program = prepared.base.sourceProgram) (locals : inputs.locals = prepared.base.locals)
    (native : inputs.native = prepared.base.callableContext) (plan : inputs.current.plan = prepared.base.plan)
    (globals : inputs.current.globals = prepared.base.globals)
    (administrativePrefix : inputs.current.administrativePrefix = 1) :
    IndexedRows prepared inputs lexical candidates closures := by
  induction rows with
  | nil => exact .nil
  | @cons candidate raw rest remaining head tail ih =>
    obtain ⟨profile⟩ := profiles candidate (by simp)
    obtain ⟨receipt⟩ := head
    obtain ⟨packet⟩ := profile.packet receipt
    obtain ⟨indexed⟩ := GeneralizedLocalLambdaGeneration.of_packet prepared packet lexical
      represented program locals native plan profile.caller globals administrativePrefix
    let exactIndexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet :=
      { indexed with lexical := lexical, represented := represented }
    obtain ⟨body⟩ := bodies candidate (by simp)
    have sourceEq := GeneralizedLocalLambdaEmissionFacts.Emission.source packet.original.emission
    have body : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
        packet.original.emission.prepared.source inputs.initializer := sourceEq.symm ▸ body
    exact .cons ⟨⟨packet, ⟨⟨exactIndexed, rfl⟩, body⟩⟩⟩
      (ih (fun child member => profiles child (List.mem_cons_of_mem _ member))
        (fun child member => bodies child (List.mem_cons_of_mem _ member)))

structure Receipt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (inputs : Inputs)
    (binding : Binding) (active : Substitution) (lowered : SourceCoreBasic.LoweredExpr) where
  original : GeneralizedLocalInitializerCompilation.Receipt inputs binding active lowered
  rows : IndexedRows prepared inputs active (binding.atContext active) original.closures
  sources : ∀ candidate ∈ binding.atContext active, candidate.origin.source = binding.source
  binders : ∀ candidate ∈ binding.atContext active, candidate.origin.binder.id = binding.binder.id

theorem of_receipt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) {inputs : Inputs}
    {binding : Binding} {active : Substitution} {lowered : SourceCoreBasic.LoweredExpr}
    (original : GeneralizedLocalInitializerCompilation.Receipt inputs binding active lowered)
    (profiles : ∀ candidate ∈ binding.atContext active, Nonempty (BindingProfile inputs binding candidate))
    (bodies : ∀ candidate ∈ binding.atContext active, Nonempty (GeneralizedLocalBodyProfile.Profile
      inputs.locals inputs.current.owner candidate.source inputs.initializer))
    (represented : inputs.representation =
      (CallableIndexedNamedGeneration.representation prepared).atContext inputs.current.owner active)
    (program : inputs.program = prepared.base.sourceProgram) (locals : inputs.locals = prepared.base.locals)
    (native : inputs.native = prepared.base.callableContext) (plan : inputs.current.plan = prepared.base.plan)
    (globals : inputs.current.globals = prepared.base.globals)
    (administrativePrefix : inputs.current.administrativePrefix = 1) :
    Nonempty (Receipt prepared inputs binding active lowered) :=
  ⟨⟨original, indexed_rows prepared original.rows (fun candidate member => by
      obtain ⟨profile⟩ := profiles candidate member
      exact ⟨profile.toObservations⟩) bodies active represented program locals native plan globals administrativePrefix,
    fun candidate member => by obtain ⟨profile⟩ := profiles candidate member; exact profile.originalSource,
    fun candidate member => by obtain ⟨profile⟩ := profiles candidate member; exact profile.originalBinder⟩⟩

private theorem indexed_type {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {candidate : Instance} {raw : Core.Expr}
    {packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw}
    (indexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context raw type definitions) : type = candidate.type := by
  rw [indexed.emitted] at typed
  cases typed with
  | pair tagged identifier =>
    cases identifier
    cases tagged with
    | pair marker function =>
      cases marker with
      | inLeft _ marker =>
        cases marker
        cases function with
        | letE snapshot closure =>
          cases closure
          exact indexed.nativeType.symm

private theorem rows_typed {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {lexical : Substitution} {candidates : List Instance} {closures : List Core.Expr}
    (rows : IndexedRows prepared inputs lexical candidates closures)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context (ProductBundle.expression closures) type definitions) :
    type = ProductBundle.type (candidates.map (·.type)) ∧
      ListRel (fun candidate raw => HasType context raw candidate.type definitions) candidates closures := by
  induction rows generalizing type with
  | nil => cases typed; exact ⟨rfl, .nil⟩
  | @cons candidate raw rest remaining head tail ih =>
    obtain ⟨⟨packet, ⟨indexed, _lexical⟩, _body⟩⟩ := head
    cases tail with
    | nil =>
      have same := indexed_type indexed typed
      exact ⟨same, .cons (same ▸ typed) .nil⟩
    | cons next restRows =>
      cases typed with
      | pair left right =>
        have first := indexed_type indexed left
        obtain ⟨remainingType, remainingTyped⟩ := ih right
        exact ⟨by simp only [List.map_cons, ProductBundle.type, first, remainingType],
          .cons (first ▸ left) remainingTyped⟩

/-- Static typing of the actual emitted bundle recovers every row's exact
native type from its authentic snapshot-lambda header. -/
theorem Receipt.raw_typed {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {binding : Binding} {active : Substitution} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding active lowered)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context lowered.expression type definitions) :
    type = LanguageResult.resultType lowered.type ∧
      ListRel (fun candidate raw => HasType context raw candidate.type definitions)
        (binding.atContext active) receipt.original.closures := by
  rw [receipt.original.emitted] at typed
  have loweredType : lowered.type = binding.bundleType active :=
    congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted
  rw [loweredType]
  cases typed with
  | inRight _ bundle =>
    obtain ⟨same, rows⟩ := rows_typed receipt.rows bundle
    exact ⟨by simpa only [Binding.bundleType, LanguageResult.resultType] using congrArg (Core.Ty.sum .word) same, rows⟩

theorem Receipt.typed {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {binding : Binding} {active : Substitution} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding active lowered)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context lowered.expression type definitions) :
    HasType context lowered.expression (LanguageResult.resultType lowered.type) definitions :=
  (receipt.raw_typed typed).1 ▸ typed

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerPackets
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedAttachment
/-! A named invocation has the empty active substitution. Any saved lexical
context extending into it is itself empty, so its existing attachment applies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
open Frontend TypeSystem
open GeneralizedLocalBundleContexts (ContextExtension)

private theorem lexical_empty {lexical : Substitution}
    (extension : ContextExtension lexical .empty) : lexical = .empty := by
  cases lexical with
  | nil => rfl
  | cons entry rest =>
    have impossible := extension.domain entry.1 (by simp [Substitution.domain])
    simp [Substitution.empty, Substitution.domain] at impossible

/-- The saved attachment already describes this same closure in the empty
context of a named invocation. -/
theorem Attachment.at_empty {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : Substitution}
    (extension : ContextExtension lexical .empty)
    (saved : Attachment function binding lexical) :
    GeneralizedLocalReachedAllocation.Attachment function binding .empty := by
  have same := lexical_empty extension
  exact same ▸ saved.toAttachment

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadCompilation
/-! A generalized read retains the actual contextual normalization and indexed
view wrapper. The original raw occurrence is kept beside the normalized row;
no equality between their complete requirement lists is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadCompilation
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CompatibleEncoding (bind_ok)

structure Observations {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) where
  original : ExpressionNode
  originalFound : source.lookupExpression? id = some original
  name : String
  binder : Resolved.LocalId
  originalForm : original.form = .reference name (.local binder)
  originalCoercions : original.coercions = []
  normalized : TypedSource
  contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
    (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok normalized
  normalizedOwner : normalized.owner = source.owner
  node : ExpressionNode
  found : normalized.lookupExpression? id = some node
  form : node.form = original.form
  rawType : node.rawType = original.rawType
  type : node.type = original.type
  requirements : node.requirements = []
  coercions : node.coercions = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  localPresent : prepared.base.locals.bindings.any (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = true

def observations? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) : Option (Observations prepared named source id) :=
  match originalFound : source.lookupExpression? id with
  | none => none
  | some original =>
    match originalForm : original.form with
    | .reference name (.local binder) =>
      if originalCoercions : original.coercions = [] then
        match contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
            (context prepared named).plan prepared.base.locals named.signature.key none source id with
        | .error _ => none
        | .ok normalized =>
          if normalizedOwner : normalized.owner = source.owner then
            match found : normalized.lookupExpression? id with
            | none => none
            | some node =>
              if form : node.form = original.form then
                if rawType : node.rawType = original.rawType then
                  if type : node.type = original.type then
                    if requirements : node.requirements = [] then
                      if coercions : node.coercions = [] then
                        if notInitializer : prepared.base.locals.bindings.find? (fun binding =>
                            decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none then
                          if localPresent : prepared.base.locals.bindings.any (fun binding =>
                              decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = true then
                            some ⟨original, originalFound, name, binder, originalForm, originalCoercions, normalized, contextual,
                              normalizedOwner, node, found, form, rawType, type, requirements, coercions,
                              notInitializer, localPresent⟩
                          else none
                        else none
                      else none
                    else none
                  else none
                else none
              else none
          else none
      else none
    | _ => none

structure Certificate {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  observations : Observations prepared named source id
  raw : SourceCoreBasic.LoweredExpr
  read : GeneralizedLocalReadReceipts.Certificate prepared.base.locals named.signature.key []
    observations.normalized scope id (reasonAt id) raw
  readAccepted : SourceCoreLocalPolymorphism.lowerRead prepared.base.locals named.signature.key []
    observations.normalized scope id (reasonAt id) = .ok raw
  viewAccepted : SourceCoreCallableIndexedAncestry.lowerView prepared.ancestry named.signature.key []
    observations.normalized scope id raw = .ok lowered
  type : raw.type = lowered.type

private theorem evidence_none {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {source : TypedSource} {id : ExpressionId} (observed : Observations prepared named source id)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget observed.normalized scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? observed.node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [observed.requirements, observed.coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, observed.found, observed.form, observed.originalForm,
    ordinary, observed.requirements, observed.coercions]

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The reached special callback produces the exact raw read and actual
indexed wrapper. Its child evaluator is never called by this branch. -/
theorem of_special {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {rootFuel budget : Nat} {child : SourceCoreFunctions.ExpressionLowerer}
    {output : Option SourceCoreBasic.LoweredExpr}
    (observed : Observations prepared named source id)
    (accepted : CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok output) :
    ∃ lowered, output = some lowered ∧ Nonempty (Certificate prepared named source scope id reasonAt lowered) := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special at accepted
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq] at accepted
  rw [observed.contextual] at accepted
  simp only [bind, Except.bind, pure, Except.pure, observed.found, observed.notInitializer,
    Option.filter_none] at accepted
  rw [evidence_none observed child budget scope reasonAt] at accepted
  simp only [observed.form, observed.originalForm,
    observed.localPresent, ↓reduceIte] at accepted
  obtain ⟨raw, readAccepted, accepted⟩ := bind_ok accepted
  have readAccepted := mapError_ok readAccepted
  obtain ⟨viewed, viewAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
  cases checkedType
  have type := ensure_type sameType
  have outputEq : output = some viewed := (Except.ok.inj accepted).symm
  obtain ⟨read⟩ := GeneralizedLocalReadReceipts.of_accepted readAccepted
  exact ⟨viewed, outputEq, ⟨⟨observed, raw, read, readAccepted, viewAccepted, type⟩⟩⟩

/-- This receipt follows the same root policy at every recursive child budget. -/
theorem of_policy {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {rootFuel fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (observed : Observations prepared named source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) (fuel + 1) (context prepared named) source scope id reasonAt = .ok lowered) :
    Nonempty (Certificate prepared named source scope id reasonAt lowered) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, observed.originalFound,
      bind, Except.bind, pure, Except.pure] at accepted
    change (do
      let output ← CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
        (context prepared named) _ (fuel + 1) source scope id reasonAt
      _) = .ok lowered at accepted
    obtain ⟨output, special, accepted⟩ := bind_ok accepted
    obtain ⟨actual, rfl, receipt⟩ := of_special compiled observed special
    have same : actual = lowered := Except.ok.inj accepted
    exact same ▸ receipt
  · simp [owner, throw, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadCompilation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
/-! Named read admission checks the actual metadata factories before execution.
These finite observations contain no native body or execution callback and are
independent of the eventual native scope and emitted read expression. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
open Core Frontend SourceInference TypeSystem
open CallableIndexedNamedGeneration (Prepared state)
open SourceCoreCallableAncestryReadRecipes

structure Observations {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) where
  entry : SourceCoreCallableViews.Entry prepared.base.sourceProgram prepared.base.plan
  found : prepared.ancestry.views.viewAt? named.signature.key id [] = some entry
  generalized : entry.view.wrapsPrincipal = true
  viewCandidate : SourceCoreLocalPolymorphism.Instance
  selected : entry.view.selectedInstance = some viewCandidate
  target : Word
  targetSelected : prepared.ancestry.graph.inputs.callable.table.idAt?
    (.lambda viewCandidate.origin.caller viewCandidate.origin.initializer viewCandidate.origin.substitution) = some target
  read : Read prepared.ancestry.graph.inputs (state named) entry.id target
  readAccepted : prepareRead prepared.ancestry.graph.inputs (state named) entry.id target = .ok read
  applied : Applied read (state named)
  appliedAccepted : applyRead read (state named) = .ok applied
  binding : SourceCoreLocalPolymorphism.Binding
  namedCaller : binding.caller = named.signature.key
  namedSource : binding.source = CallableIndexedNamedGeneration.source named
  declaration : (SourceCoreDataPlaces.declaredBinders (CallableIndexedNamedGeneration.source named)).filter
    (fun binder => decide (binder.id = binding.binder.id)) = [binding.binder]
  polymorphic : binding.binder.scheme.quantified ≠ []
  bindingFound : prepared.base.locals.binding named.signature.key read.entry.view.binding.binder.id = .ok binding
  sameEntry : read.entry = entry
  initializer : read.entry.view.principal.initializer = binding.initializer
  scheme : read.binder.scheme = binding.binder.scheme
  original : ExpressionNode
  originalFound : source.lookupExpression? id = some original
  name : String
  originalForm : original.form = .reference name (.local binding.binder.id)
  rawType : read.node.rawType = original.rawType
  candidate : SourceCoreLocalPolymorphism.Instance
  rows : (binding.atContext []).filter (fun item => decide (item.origin.substitution = read.substitution)) = [candidate]
  candidateInitializer : candidate.origin.initializer = binding.initializer
  origin : SourceCoreStageCodebook.Origin.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution =
    .lambda viewCandidate.origin.caller viewCandidate.origin.initializer viewCandidate.origin.substitution

private theorem find_unique_key {α β : Type} [DecidableEq β] (items : List α) (key : α → β)
    (unique : (items.map key).Nodup) {item : α} (member : item ∈ items) :
    items.find? (fun candidate => decide (key candidate = key item)) = some item := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · subst item; simp
    · have different : key head ≠ key item := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨item, member, same.symm⟩)
      simpa [List.find?_cons, different] using ih unique.2 member

private theorem same_entry {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : Prepared checked} {named : SourceCoreGeneralFunctions.Function} {id : ExpressionId}
    {entry : SourceCoreCallableViews.Entry prepared.base.sourceProgram prepared.base.plan} {target : Word}
    (found : prepared.ancestry.views.viewAt? named.signature.key id [] = some entry)
    (read : Read prepared.ancestry.graph.inputs (state named) entry.id target) : read.entry = entry := by
  have selected : prepared.ancestry.views.entryAt? entry.id = some entry :=
    find_unique_key _ _ prepared.ancestry.views.idsUnique (List.mem_of_find?_eq_some found)
  exact Option.some.inj (read.selected.symm.trans selected)

def observations? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) : Option (Observations prepared named source id) :=
  match found : prepared.ancestry.views.viewAt? named.signature.key id [] with
  | none => none
  | some entry =>
    if generalized : entry.view.wrapsPrincipal = true then
      match selected : entry.view.selectedInstance with
      | none => none
      | some viewCandidate =>
        match targetSelected : prepared.ancestry.graph.inputs.callable.table.idAt?
            (.lambda viewCandidate.origin.caller viewCandidate.origin.initializer viewCandidate.origin.substitution) with
        | none => none
        | some target =>
          match readAccepted : prepareRead prepared.ancestry.graph.inputs (state named) entry.id target with
          | .error _ => none
          | .ok read =>
            match appliedAccepted : applyRead read (state named) with
            | .error _ => none
            | .ok applied =>
              match bindingFound : prepared.base.locals.binding named.signature.key read.entry.view.binding.binder.id with
              | .error _ => none
              | .ok binding =>
               if namedCaller : binding.caller = named.signature.key then
                if namedSource : binding.source = CallableIndexedNamedGeneration.source named then
                 if declaration : (SourceCoreDataPlaces.declaredBinders (CallableIndexedNamedGeneration.source named)).filter
                     (fun binder => decide (binder.id = binding.binder.id)) = [binding.binder] then
                  if polymorphic : binding.binder.scheme.quantified ≠ [] then
                   if initializer : read.entry.view.principal.initializer = binding.initializer then
                  if scheme : read.binder.scheme = binding.binder.scheme then
                    match originalFound : source.lookupExpression? id with
                    | none => none
                    | some original =>
                      match originalForm : original.form with
                      | .reference name (.local binder) =>
                        if sameBinder : binder = binding.binder.id then
                          if rawType : read.node.rawType = original.rawType then
                            match rows : (binding.atContext []).filter (fun item => decide (item.origin.substitution = read.substitution)) with
                            | [candidate] =>
                              if candidateInitializer : candidate.origin.initializer = binding.initializer then
                               if origin : SourceCoreStageCodebook.Origin.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution =
                                  .lambda viewCandidate.origin.caller viewCandidate.origin.initializer viewCandidate.origin.substitution then
                                some ⟨entry, found, generalized, viewCandidate, selected, target, targetSelected,
                                  read, readAccepted, applied, appliedAccepted, binding, namedCaller, namedSource, declaration, polymorphic, bindingFound,
                                  same_entry found read, initializer, scheme, original, originalFound, name,
                                  by simpa only [sameBinder] using originalForm, rawType, candidate, rows, candidateInitializer, origin⟩
                               else none
                              else none
                            | _ => none
                          else none
                        else none
                      | _ => none
                  else none
                 else none
                else none
                else none
                 else none
               else none
    else none

structure Receipt {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope id reasonAt lowered) where
  observations : Observations prepared named source id
  binding : observations.binding = certificate.read.binding
  candidate : observations.candidate = certificate.read.candidate
  rawType : observations.read.node.rawType = certificate.read.node.rawType
  parameter : Core.Ty
  result : Core.Ty
  nativeType : certificate.raw.type = CallableContract.functionType parameter result
  emitted : lowered = {certificate.raw with expression := (SourceCoreCallableIndexedAncestry.viewLower
    prepared.ancestry.layout.frame parameter result observations.entry.id observations.target
    (scope.length + 1 + prepared.base.globals.length) certificate.raw.expression)}

private theorem binding_id {catalog : SourceCoreLocalPolymorphism.Catalog}
    {caller : SourceCoreLocalPolymorphism.Key} {id : Resolved.LocalId}
    {binding : SourceCoreLocalPolymorphism.Binding}
    (found : catalog.binding caller id = .ok binding) : binding.binder.id = id := by
  unfold SourceCoreLocalPolymorphism.Catalog.binding at found
  generalize rowsEq : catalog.bindings.filter (fun entry => decide (entry.caller = caller ∧ entry.binder.id = id)) = rows at found
  cases rows with
  | nil => cases found
  | cons head tail =>
    cases tail with
    | nil =>
      cases found
      have member : binding ∈ catalog.bindings.filter (fun entry => decide (entry.caller = caller ∧ entry.binder.id = id)) := by
        rw [rowsEq]
        exact List.mem_singleton_self _
      exact (of_decide_eq_true (List.mem_filter.mp member).2).2
    | cons => cases found

/-- The accepted native read determines the same full candidate as the static
metadata factories, even when several instances have equal native types. -/
theorem of_certificate {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (observed : Observations prepared named source id)
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope id reasonAt lowered) :
    Nonempty (Receipt certificate) := by
  have originalEq : observed.original = certificate.observations.original :=
    Option.some.inj (observed.originalFound.symm.trans certificate.observations.originalFound)
  have nodeEq : certificate.read.node = certificate.observations.node :=
    Option.some.inj (certificate.read.nodeFound.symm.trans certificate.observations.found)
  have rawType : observed.read.node.rawType = certificate.read.node.rawType := by
    rw [nodeEq, certificate.observations.rawType, ← originalEq]
    exact observed.rawType
  obtain ⟨name, form⟩ := certificate.read.nodeForm
  have sameForm := form.symm.trans (congrArg ExpressionNode.form nodeEq)
  rw [certificate.observations.form, ← originalEq, observed.originalForm] at sameForm
  have binderEq : certificate.read.binder = observed.binding.binder.id := by
    injection sameForm with _ resolution
    injection resolution
  have observedBinder := binding_id observed.bindingFound
  have bindingEq : observed.binding = certificate.read.binding := by
    have selected := observed.bindingFound
    rw [← observedBinder, ← binderEq] at selected
    exact Except.ok.inj (selected.symm.trans certificate.read.bindingFound)
  have matched := CallableAncestryProfiles.SourceComposition.witnesses_matched observed.read.factory
  have rawMatched := certificate.read.matched
  simp only [EmptySourceSubstitution.scheme, EmptySourceSubstitution.type] at rawMatched
  have originalType : certificate.read.original.rawType = certificate.read.node.rawType := by
    simpa only [EmptySourceSubstitution.type] using certificate.read.rawType
  rw [originalType, ← bindingEq, ← observed.scheme, ← rawType] at rawMatched
  have childEq : certificate.read.child = observed.read.substitution :=
    Option.some.inj (rawMatched.symm.trans matched)
  have key : certificate.read.candidate.origin.substitution = observed.read.substitution := by
    have actualKey := certificate.read.candidate_key
    have identity : certificate.read.child.compose [] = certificate.read.child := by
      simp [Substitution.compose, List.filter_eq_self]
    exact actualKey.trans (identity.trans childEq)
  have member : certificate.read.candidate ∈ (observed.binding.atContext []).filter
      (fun item => decide (item.origin.substitution = observed.read.substitution)) := by
    apply List.mem_filter.mpr
    constructor
    · rw [bindingEq]
      exact List.mem_of_getElem? certificate.read.candidate_at
    · simp only [key, decide_true]
  rw [observed.rows] at member
  have candidateEq := (List.mem_singleton.mp member).symm
  obtain ⟨viewed, _, route⟩ := CallableIndexedFormation.lowerView_receipt prepared.ancestry certificate.viewAccepted
  have entryEq : viewed.entry = observed.entry := Option.some.inj (viewed.found.symm.trans observed.found)
  rcases route with ⟨ordinary, _⟩ | ⟨_, candidate, target, parameter, result, selected, targetSelected, type, emitted⟩
  · rw [entryEq, observed.generalized] at ordinary
    cases ordinary
  · rw [entryEq, observed.selected] at selected
    have candidateViewEq := Option.some.inj selected
    rw [← candidateViewEq, observed.targetSelected] at targetSelected
    have targetEq := Option.some.inj targetSelected
    refine ⟨⟨observed, bindingEq, candidateEq, rawType, parameter, result, type, ?_⟩⟩
    simpa only [entryEq, ← targetEq] using emitted

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipe
/-! Actual named caller and allocation histories instantiate the checked static
read recipe. The selected target keeps its entire specialization key. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
open Core Frontend SourceInference TypeSystem
open CallableIndexedNamedGeneration (Prepared state)
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id : ExpressionId}

/-- Runtime histories authenticate the two real parents of the static recipe. -/
def Observations.recipe (observed : Observations prepared named source id)
    {callerGhost lexicalGhost : GhostFrame} {caller lexical : MetadataState}
    (callerEq : caller = state named) (lexicalEq : lexical = state named)
    (callerHistory : CallableAncestryPairedLookup.Authenticates prepared.ancestry.graph.inputs callerGhost (some caller))
    (lexicalHistory : CallableAncestryPairedLookup.Authenticates prepared.ancestry.graph.inputs lexicalGhost (some lexical)) :
    CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost lexicalGhost caller lexical
      observed.entry.id observed.target := by
  subst caller
  subst lexical
  exact ⟨callerHistory, lexicalHistory, observed.read, observed.readAccepted, observed.applied, observed.appliedAccepted⟩

theorem Observations.recipe_fields (observed : Observations prepared named source id)
    {callerGhost lexicalGhost : GhostFrame} {caller lexical : MetadataState}
    (callerEq : caller = state named) (lexicalEq : lexical = state named)
    (callerHistory : CallableAncestryPairedLookup.Authenticates prepared.ancestry.graph.inputs callerGhost (some caller))
    (lexicalHistory : CallableAncestryPairedLookup.Authenticates prepared.ancestry.graph.inputs lexicalGhost (some lexical)) :
    let recipe := observed.recipe callerEq lexicalEq callerHistory lexicalHistory
    recipe.read.entry = observed.read.entry ∧ recipe.read.binder = observed.read.binder ∧
      recipe.read.node = observed.read.node := by
  subst caller
  subst lexical
  exact ⟨rfl, rfl, rfl⟩

variable {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope id reasonAt lowered}

theorem Receipt.target (receipt : Receipt certificate) :
    prepared.ancestry.graph.inputs.callable.table.idAt?
      (.lambda certificate.read.candidate.origin.caller certificate.read.candidate.origin.initializer
        certificate.read.candidate.origin.substitution) = some receipt.observations.target := by
  rw [← receipt.candidate, receipt.observations.origin]
  exact receipt.observations.targetSelected

theorem Receipt.initializer (receipt : Receipt certificate) :
    receipt.observations.read.entry.view.principal.initializer = certificate.read.binding.initializer :=
  receipt.observations.initializer.trans (congrArg (·.initializer) receipt.binding)

theorem Receipt.scheme (receipt : Receipt certificate) :
    receipt.observations.read.binder.scheme = certificate.read.binding.binder.scheme :=
  receipt.observations.scheme.trans (congrArg (fun binding => binding.binder.scheme) receipt.binding)

theorem Receipt.candidate_initializer (receipt : Receipt certificate) :
    certificate.read.candidate.origin.initializer = certificate.read.binding.initializer := by
  rw [← receipt.candidate, ← receipt.binding]
  exact receipt.observations.candidateInitializer

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalViewedFormation
/-! Native typing for the materialized wrapper follows from its accepted
emission and actual read execution in the unchanged store. The resulting
positive association is the one used by mixed public function values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {material : Materialization compiled mapping world function}

theorem View.formation (view : View material) {store : Store}
    (read : Evaluates view.environment store (view.original.expression.rename view.embedding)
      (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual)) store)
    (snapshot : store.read? view.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.callerNative)) :
    Evaluates view.environment store (view.lowered.expression.rename view.embedding)
      (.inRight .word view.native) store := by
  rw [view.emitted]
  exact GeneralizedLocalReadView.formation read view.reference snapshot

theorem View.runtime_hasType (view : View material) {context : Core.Context}
    (environments : RuntimeEnvironmentHasTypes world view.environment context compiled.indexed.layouts.definitions) :
    RuntimeValueHasType world view.native
      (CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore)
      compiled.indexed.layouts.definitions := by
  have raw := material.rawTyped
  rw [material.native_type] at raw
  exact GeneralizedLocalReadView.runtime_hasType (CallableIndexedAmbient.frame_registered compiled.indexed)
    raw environments view.reference

theorem View.represents (view : View material) {store : Store} {context : Core.Context}
    (read : Evaluates view.environment store (view.original.expression.rename view.embedding)
      (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual)) store)
    (snapshot : store.read? view.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.callerNative))
    (typed : HasType context (view.lowered.expression.rename view.embedding)
      (LanguageResult.resultType (CallableContract.functionType material.code.receipt.parameterCore
        material.code.receipt.resultCore)) compiled.indexed.layouts.definitions)
    (environments : RuntimeEnvironmentHasTypes world view.environment context compiled.indexed.layouts.definitions)
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Nonempty (Association compiled mapping world function view.native material.code.receipt.loweredParameters
      material.code.receipt.parameterCore material.code.receipt.resultCore) := by
  have evaluated := view.formation read snapshot
  obtain ⟨future, _, finalStored, outputTyped⟩ := evaluation_preserves_type evaluated typed environments stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  cases outputTyped with
  | inRight typed => exact ⟨.viewed material view typed⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedViewFormation
/-! The actual named caller and lexical allocation history instantiate the
static recipe and emitted wrapper for the materialized selected row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedViewFormation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues
open GeneralizedLocalMaterializedAssociation
open GeneralizedLocalNamedRecipeCompilation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered}

theorem target (receipt : Receipt certificate) (material : Materialization compiled mapping world function)
    (binding : material.binding = certificate.read.binding)
    (candidate : material.candidate = certificate.read.candidate) :
    material.code.descriptor.id = receipt.observations.target := by
  have found := material.indexed.descriptor.found
  conv at found => lhs; rw [material.indexed.owner, material.initializer, GeneralizedLocalLambdaEmissionFacts.Emission.substitution,
    binding, candidate, ← receipt.candidate_initializer]
  exact material.descriptorId.trans (Option.some.inj (found.symm.trans receipt.target))

theorem native_types (receipt : Receipt certificate) (material : Materialization compiled mapping world function)
    (candidate : material.candidate = certificate.read.candidate) :
    receipt.parameter = material.code.receipt.parameterCore ∧ receipt.result = material.code.receipt.resultCore := by
  have rawType : certificate.raw.type = certificate.read.candidate.type :=
    congrArg SourceCoreBasic.LoweredExpr.type certificate.read.emitted
  have same := receipt.nativeType.symm.trans (rawType.trans (candidate ▸ material.native_type))
  simpa only [CallableContract.functionType, TaggedFunction.functionType, LanguageResult.resultType,
    Ty.product.injEq, Ty.function.injEq, Ty.sum.injEq, true_and, and_true] using same

private theorem retarget_fields {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
    {callerGhost lexicalGhost : GhostFrame} {caller lexical : MetadataState} {id target next : Word}
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerGhost lexicalGhost caller lexical id target)
    (same : target = next) :
    let changed : CallableAppliedViewProvenance.Recipe inputs callerGhost lexicalGhost caller lexical id next := same ▸ recipe
    changed.read.entry = recipe.read.entry ∧ changed.read.binder = recipe.read.binder ∧ changed.read.node = recipe.read.node := by
  subst next
  exact ⟨rfl, rfl, rfl⟩

def view (receipt : Receipt certificate) (material : Materialization compiled mapping world function)
    (binding : material.binding = certificate.read.binding)
    (candidate : material.candidate = certificate.read.candidate)
    (actualType : material.actualType = certificate.read.node.rawType)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState}
    (callerCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      callerNative callerGhost (some caller))
    (callerEq : caller = CallableIndexedNamedGeneration.state named)
    {embedding : Renaming} {environment : Environment} {location : Core.Location}
    (reference : environment[embedding (scope.length + 1 + compiled.indexed.base.globals.length)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (lexicalReference : material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location)) : View material := by
  have targetEq := target receipt material binding candidate
  have types := native_types receipt material candidate
  have lexicalEq : material.origin.metadata = CallableIndexedNamedGeneration.state named := by
    rw [material.namedMetadata]
    simp only [binding, ← receipt.binding, receipt.observations.namedCaller, receipt.observations.namedSource]
    rfl
  let originalRecipe := receipt.observations.recipe callerEq lexicalEq callerCarried.authenticates material.origin.carried.authenticates
  have fields := receipt.observations.recipe_fields callerEq lexicalEq callerCarried.authenticates material.origin.carried.authenticates
  let recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs callerGhost
      material.origin.ghost caller material.origin.metadata receipt.observations.entry.id material.code.descriptor.id :=
    targetEq.symm ▸ originalRecipe
  have changed := retarget_fields originalRecipe targetEq.symm
  have entryEq : recipe.read.entry = receipt.observations.read.entry := changed.1.trans fields.1
  have schemeEq : recipe.read.binder = receipt.observations.read.binder := changed.2.1.trans fields.2.1
  have nodeEq : recipe.read.node = receipt.observations.read.node := changed.2.2.trans fields.2.2
  exact
    { owner := named.signature.key, active := [], source := certificate.observations.normalized
      scope := scope, expression := id, original := certificate.raw, lowered := lowered
      accepted := certificate.viewAccepted, id := receipt.observations.entry.id
      referenceIndex := scope.length + 1 + compiled.indexed.base.globals.length
      emitted := by
        have emitted := congrArg SourceCoreBasic.LoweredExpr.expression receipt.emitted
        simpa only [types.1, types.2, ← targetEq] using emitted
      callerNative := callerNative, callerGhost := callerGhost, caller := caller, carried := callerCarried
      recipe := recipe
      initializer := by rw [entryEq, receipt.initializer, ← binding]; exact material.descriptorInitializer
      scheme := by rw [schemeEq, receipt.scheme, ← binding]; exact material.binderScheme
      actualType := actualType.trans (receipt.rawType.symm.trans (congrArg ExpressionNode.rawType nodeEq.symm))
      embedding := embedding, environment := environment, location := location, reference := reference
      lexicalReference := lexicalReference }

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedViewFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadFormation
/-! The actual named read combines its stored framed row, original Dynamic
instantiation, compiler wrapper and current physical caller. The returned
positive association retains the same frame used by a following application. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatibleEquality
open CallableIndexedHistory GeneralizedLocalLocatedRows GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : TypeSystem.Substitution} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}

theorem preserves
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered)
    (recipe : GeneralizedLocalNamedRecipeCompilation.Receipt certificate)
    (located : Located (GeneralizedLocalInstanceValues.model compiled.indexed) descriptor binding lexical
      sourceLocation mapping world heap store)
    (frames : located.Frames frameLocation)
    (sameCaller : named.signature.key = binding.caller) (sameBinder : certificate.read.binder = binding.binder.id)
    (contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical [])
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming} {actualContext : Core.Context}
    (environments : DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment certificate.read.binder sourceLocation)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (unique : NodeOccurrencesUnique descriptor.source)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = certificate.read.binding.binder.scheme)
    (sameType : actualType = certificate.read.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState}
    (callerCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      callerNative callerGhost (some caller))
    (callerEq : caller = CallableIndexedNamedGeneration.state named)
    (reference : actual[embedding (scope.length + 1 + compiled.indexed.base.globals.length)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation))
    (snapshot : store.read? frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame callerNative))
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
    ∃ view : View material,
      material.frameLocation = frameLocation ∧ view.location = frameLocation ∧
      lowered.type = CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word view.native) store ∧
      ∃ member : Association compiled mapping world function view.native material.code.receipt.loweredParameters
          material.code.receipt.parameterCore material.code.receipt.resultCore,
        member.AtFrame frameLocation := by
  obtain ⟨material, _descriptor, materialBinding, _lexical, materialCandidate, materialType, _semantic,
      _context, _evidence, _produced, _requirements, materialFrame, rawRead⟩ :=
    GeneralizedLocalReachedMaterialization.preserves_framed located frames certificate.read sameCaller sameBinder
      contextExtension environments lookup agrees unique instantiation sameScheme sameType profile
  have lexicalReference : material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) :=
    materialFrame ▸ material.frame_reference
  let view := GeneralizedLocalNamedViewFormation.view recipe material materialBinding materialCandidate
    (materialType.trans sameType) callerCarried callerEq reference lexicalReference
  have evaluated : Evaluates actual store (lowered.expression.rename embedding) (.inRight .word view.native) store :=
    view.formation rawRead snapshot
  have outputType : lowered.type = CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore := by
    have rawType := congrArg SourceCoreBasic.LoweredExpr.type certificate.read.emitted
    exact certificate.type.symm.trans (rawType.trans (materialCandidate ▸ material.native_type))
  exact ⟨material, view, materialFrame, rfl, outputType, evaluated,
    .viewed material view (view.runtime_hasType actualTyped), rfl⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadFormation
end
