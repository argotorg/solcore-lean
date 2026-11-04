import Solcore.Frontend.SourceCore.CompatibleFunctions
import Solcore.Frontend.Internal.RuntimeValidation
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.Frontend.SourceCore.Internal.Allocation

/-!
# Callable views

Source views of local lambda reads, marked functions, the marked ledger and lambda templates.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableViews
/-! Compile-time source views of direct local lambda reads. Each view keeps the
principal closure's source metadata separate from the compiler's contextual
ledger, and keeps the occurrence's own substitution separate from its parent.

These receipts contain no Core closure or capture authentication. An emission
receipt and source allocation ledger must supply those before an output/heap
adapter can reconstruct a source closure. This module neither executes source
nor adds runtime source-table traversal. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableViews
open SourceInference TypeSystem
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Binding := SourceCoreLocalPolymorphism.Binding
abbrev Instance := SourceCoreLocalPolymorphism.Instance
abbrev Parent := SourceCoreLocalEvidence.Prepared
abbrev Reference := SourceCoreLocalEvidence.Reference
abbrev Witness := SourceCoreLocalEvidence.Witness
abbrev Checked := SourceCoreCompatibleCatalog.Checked

mutual
private def evidenceDecEq : (left right : TypedTraitResolution.Evidence) → Decidable (left = right)
  | .byImpl goal implementation premises, .byImpl otherGoal otherImplementation otherPremises => by
    letI : Decidable (premises = otherPremises) := evidenceListDecEq premises otherPremises
    simpa only [TraitResolution.Evidence.byImpl.injEq] using
      (inferInstance : Decidable (goal = otherGoal ∧ implementation = otherImplementation ∧ premises = otherPremises))
termination_by left _ => sizeOf left

private def evidenceListDecEq : (left right : List TypedTraitResolution.Evidence) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | head :: tail, otherHead :: otherTail => by
    letI : Decidable (head = otherHead) := evidenceDecEq head otherHead
    letI : Decidable (tail = otherTail) := evidenceListDecEq tail otherTail
    simpa only [List.cons.injEq] using (inferInstance : Decidable (head = otherHead ∧ tail = otherTail))
termination_by left _ => sizeOf left
end

private instance : DecidableEq TypedTraitResolution.Evidence := evidenceDecEq

private instance : DecidableEq Witness := fun left right => by
  cases left with
  | mk lt la lp le =>
    cases right with
    | mk rt ra rp re =>
      simpa only [SourceTypedRuntime.LocalRequirementWitness.mk.injEq] using
        (inferInstance : Decidable (lt = rt ∧ la = ra ∧ lp = rp ∧ le = re))

private def rawReference (reference : Reference) : ExpressionNode :=
  let node := reference.original
  {node with type := node.rawType, requirements := reference.owned, coercions := []}


structure Limits where
  maxViews : Nat := 65536
  maxContexts : Nat := 4096
  maxSourceNodes : Nat := 65536
  deriving Repr

inductive Error where
  | plan (error : SourceCompilationPlan.Error)
  | evidence (error : SourceCoreLocalEvidence.Error)
  | discovery (error : SourceSpecializationWorklist.Error)
  | ownerMismatch (expected actual : Resolved.DeclarationId)
  | duplicateNode (id : NodeId)
  | missingNode (id : NodeId)
  | duplicateBinding (binder : Resolved.LocalId)
  | missingBinding (binder : Resolved.LocalId)
  | invalidInitializer (id : ExpressionId)
  | invalidContext (owner : Key) (initializer : ExpressionId)
  | missingInstance (binder : Resolved.LocalId) (context : Substitution)
  | duplicateInstance (binder : Resolved.LocalId) (context : Substitution)
  | referenceMismatch (id : ExpressionId)
  | traversalBudgetExhausted (id : NodeId)
  | viewBudgetExhausted (limit : Nat)
  | contextBudgetExhausted (limit : Nat)
  | sourceNodeBudgetExhausted (limit : Nat)
  | zeroFirstId
  | idSpaceExhausted (next : Nat)
  | duplicateView (owner : Key) (read : ExpressionId) (parent : Substitution)
  | duplicateId
  deriving Repr

private def parentActive (parent : Option Parent) : Substitution := parent.map (·.substitution) |>.getD []
private def parentWitnesses (parent : Option Parent) : List Witness := parent.map (·.witnesses) |>.getD []

/-- Every field which an old principal closure retained, except its dynamic
captured locations. `originalSource` is immutable declaration metadata;
`source` includes the parent's substitution and exact requirement-ID rewrite. -/
structure Principal (binding : Binding) (parent : Option Parent) where private mk ::
  source : TypedSource
  parameters : List TypedBinder
  resultType : Ty
  body : List StatementId
  evidence : SourceCompilationPlan.EvidenceEnvironment
  private sourceExact : source = SourceTypedRuntime.rewriteLocalRequirements (parentWitnesses parent)
    (binding.source.applySubstitution (parentActive parent))
  private node : ExpressionNode
  private found : source.lookupExpression? binding.initializer = some node
  private shape : node.form = .lambda parameters resultType body

namespace Principal

def owner {binding : Binding} {parent : Option Parent} (_ : Principal binding parent) : Key := binding.caller
def binder {binding : Binding} {parent : Option Parent} (_ : Principal binding parent) : TypedBinder := binding.binder
def initializer {binding : Binding} {parent : Option Parent} (_ : Principal binding parent) : ExpressionId := binding.initializer
def originalSource {binding : Binding} {parent : Option Parent} (_ : Principal binding parent) : TypedSource := binding.source
theorem lambdaMetadata {binding : Binding} {parent : Option Parent} (principal : Principal binding parent) :
    ∃ node, principal.source.lookupExpression? principal.initializer = some node ∧
      node.form = .lambda principal.parameters principal.resultType principal.body :=
  ⟨principal.node, principal.found, principal.shape⟩
end Principal

structure View (program : CheckedProgram) (plan : Plan) where private mk ::
  binding : Binding
  parent : Option Parent
  principal : Principal binding parent
  read : ExpressionId
  compilerCaller : SourceSpecialization.SpecializedFunction
  ownSubstitution : Substitution
  ownWitnesses : List Witness
  reference : Reference
  selectedInstance : Option Instance
  private authenticated : SourceCoreLocalEvidence.authenticateReference program plan
    { caller := principal.owner, source := principal.originalSource,
      binder := principal.binder, initializer := principal.initializer, instances := [] }
    parent read = .ok reference
  private factory : SourceCompilationPlan.localRequirementWitnesses compilerCaller principal.evidence
    (principal.binder.applySubstitution (parentActive parent))
    (rawReference reference) = .ok (ownSubstitution, ownWitnesses)
  cumulativeExact : reference.cumulative = ownSubstitution.compose (parentActive parent)
  witnessesExact : reference.witnesses = ownWitnesses

namespace View

/-- Eligibility in the old detector. A runtime value must additionally be a
principal closure before the old evaluator creates an instantiated wrapper. -/
def wrapsPrincipal {program : CheckedProgram} {plan : Plan} (view : View program plan) : Bool :=
  !view.binding.binder.scheme.quantified.isEmpty

def rawRead {program : CheckedProgram} {plan : Plan} (view : View program plan) : ExpressionNode :=
  rawReference view.reference

def parentActive {program : CheckedProgram} {plan : Plan} (view : View program plan) : Substitution :=
  SourceCoreCallableViews.parentActive view.parent

def inheritedWitnesses {program : CheckedProgram} {plan : Plan} (view : View program plan) : List Witness :=
  parentWitnesses view.parent

theorem exactPrincipalSource {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    view.principal.source = SourceTypedRuntime.rewriteLocalRequirements view.inheritedWitnesses
      (view.principal.originalSource.applySubstitution view.parentActive) := view.principal.sourceExact

def owner {program : CheckedProgram} {plan : Plan} (view : View program plan) : Key := view.principal.owner

def cumulative {program : CheckedProgram} {plan : Plan} (view : View program plan) : Substitution := view.reference.cumulative

def key {program : CheckedProgram} {plan : Plan} (view : View program plan) : Key × ExpressionId × Substitution :=
  (view.owner, view.read, view.parentActive)

theorem authenticatedReference {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    SourceCoreLocalEvidence.authenticateReference program plan
      { caller := view.principal.owner, source := view.principal.originalSource,
        binder := view.principal.binder, initializer := view.principal.initializer, instances := [] }
      view.parent view.read = .ok view.reference := view.authenticated

theorem exactFactory {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    SourceCompilationPlan.localRequirementWitnesses view.compilerCaller view.principal.evidence
      (view.principal.binder.applySubstitution view.parentActive)
      view.rawRead =
      .ok (view.ownSubstitution, view.ownWitnesses) := view.factory
end View

private def validateSource (limits : Limits) (owner : Key) (source : TypedSource) : Except Error Unit := do
  if source.owner != owner.declaration then throw (.ownerMismatch owner.declaration source.owner)
  if source.nodes.length > limits.maxSourceNodes then throw (.sourceNodeBudgetExhausted limits.maxSourceNodes)
  let mut seen := []
  for node in source.nodes do
    if node.id.occurrenceId.owner != source.owner then
      throw (.ownerMismatch source.owner node.id.occurrenceId.owner)
    if seen.contains node.id then throw (.duplicateNode node.id)
    seen := node.id :: seen

/-- Direct monomorphic lets are included for principal reconstruction. The
existing generalized binding detector still determines wrapper generation. -/
private def directBindings (owner : Key) (source : TypedSource) : Except Error (List Binding) := do
  let mut bindings := []
  for node in source.nodes do
    match node with
    | .statement {form := .letDecl binder (some initializer), ..} =>
        if SourceSpecialization.isDirectLambdaInitializer source initializer then
          if binder.id.owner != source.owner then throw (.ownerMismatch source.owner binder.id.owner)
          if bindings.any (fun binding : Binding => decide (binding.binder.id = binder.id)) then
            throw (.duplicateBinding binder.id)
          bindings := bindings ++ [{ caller := owner, source, binder, initializer, instances := [] }]
    | _ => pure ()
  pure bindings

private def lexicalChildren (source : TypedSource) (boundaries : List ExpressionId) (id : NodeId) :
    Except Error (List NodeId) := do
  let node ← match source.lookupNode? id.occurrenceId with
    | some node => pure node
    | none => throw (.missingNode id)
  if node.id != id then throw (.missingNode id)
  match node with
  | .expression node =>
      if boundaries.contains node.id then pure []
      else pure (SourceSpecialization.expressionChildNodeIds node)
  | .statement node => pure (SourceSpecialization.statementChildNodeIds source node)

private def lexicalIds (source : TypedSource) (boundaries : List ExpressionId) : Nat →
    List NodeId → List NodeId → Except Error (List NodeId)
  | 0, [], seen => pure seen
  | 0, next :: _, _ => throw (.traversalBudgetExhausted next)
  | _ + 1, [], seen => pure seen
  | fuel + 1, next :: pending, seen => do
      if seen.contains next then lexicalIds source boundaries fuel pending seen
      else
        let children ← lexicalChildren source boundaries next
        lexicalIds source boundaries fuel (pending ++ children) (next :: seen)

private def rootNodes (source : TypedSource) (bindings : List Binding) : Except Error (List Node) := do
  let boundaries := (bindings.filter (fun binding => !binding.binder.scheme.quantified.isEmpty)).map (·.initializer)
  let edges := source.nodes.foldl (fun total node => total + match node with
    | .expression expression => (SourceSpecialization.expressionChildNodeIds expression).length
    | .statement statement => (SourceSpecialization.statementChildNodeIds source statement).length) 0
  let ids ← lexicalIds source boundaries (source.roots.length + edges + 1) source.roots []
  pure (source.nodes.filter (fun node => ids.contains node.id))

private def principal (program : CheckedProgram) (plan : Plan) (binding : Binding) (parent : Option Parent) :
    Except Error (Principal binding parent × SourceSpecialization.SpecializedFunction) := do
  let caller ← (SourceCoreLocalEvidence.exactCaller plan binding).mapError Error.evidence
  let active := parentActive parent
  let inherited := parentWitnesses parent
  let compilerCaller := SourceCoreLocalEvidence.contextualCaller caller active inherited
  let source := SourceTypedRuntime.rewriteLocalRequirements inherited (binding.source.applySubstitution active)
  match found : source.lookupExpression? binding.initializer with
  | none => throw (.invalidInitializer binding.initializer)
  | some node =>
    match shape : node.form with
    | .lambda parameters resultType body =>
      for parameter in parameters do
        if parameter.id.owner != source.owner then throw (.ownerMismatch source.owner parameter.id.owner)
      let available ← (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions).mapError Error.plan
      pure (⟨source, parameters, resultType, body, available, rfl, node, found, shape⟩, compilerCaller)
    | _ => throw (.invalidInitializer binding.initializer)

/-- Authenticate one read using the unchanged pure witness factory. This is a
metadata receipt, not evidence that a particular runtime cell holds a closure. -/
def authenticate (program : CheckedProgram) (plan : Plan) (binding : Binding) (parent : Option Parent)
    (id : ExpressionId) : Except Error (View program plan) := do
  let binding := {binding with instances := []}
  let (principal, caller) ← principal program plan binding parent
  let active := parentActive parent
  match authenticated : SourceCoreLocalEvidence.authenticateReference program plan binding parent id with
  | .error error => throw (.evidence error)
  | .ok reference =>
      let raw := rawReference reference
      match factory : SourceCompilationPlan.localRequirementWitnesses caller principal.evidence
          (binding.binder.applySubstitution active) raw with
      | .error error => throw (.plan error)
      | .ok (own, witnesses) =>
          if cumulative : reference.cumulative = own.compose active then
            if sameWitnesses : reference.witnesses = witnesses then
              pure (.mk binding parent principal id caller own witnesses reference none
                authenticated factory cumulative sameWitnesses)
            else throw (.referenceMismatch id)
          else throw (.referenceMismatch id)

structure Entry (program : CheckedProgram) (plan : Plan) where private mk ::
  id : Core.Word
  view : View program plan

structure Table (program : CheckedProgram) (plan : Plan) where private mk ::
  entries : List (Entry program plan)
  idsUnique : (entries.map (·.id)).Nodup
  viewsUnique : (entries.map (fun entry => entry.view.key)).Nodup

namespace Table

def viewAt? {program : CheckedProgram} {plan : Plan} (table : Table program plan)
    (owner : Key) (read : ExpressionId) (parent : Substitution) : Option (Entry program plan) :=
  table.entries.find? (fun entry => decide (entry.view.key = (owner, read, parent)))

def entryAt? {program : CheckedProgram} {plan : Plan} (table : Table program plan) (id : Core.Word) : Option (Entry program plan) :=
  table.entries.find? (fun entry => decide (entry.id = id))
end Table

private def selectInstance {program : CheckedProgram} {plan : Plan} (catalog : SourceCoreLocalPolymorphism.Catalog)
    (view : View program plan) : Except Error (View program plan) := do
  if !view.wrapsPrincipal then return view
  let binding ← match catalog.bindings.filter (fun binding =>
      decide (binding.caller = view.owner ∧ binding.binder.id = view.binding.binder.id)) with
    | [] => throw (.missingBinding view.binding.binder.id)
    | [binding] => pure binding
    | _ => throw (.duplicateBinding view.binding.binder.id)
  if binding.source != view.binding.source || binding.binder != view.binding.binder ||
      binding.initializer != view.binding.initializer then throw (.invalidInitializer view.binding.initializer)
  let selected ← match binding.instances.filter (fun candidate =>
      decide (candidate.origin.substitution = view.cumulative)) with
    | [] => throw (.missingInstance binding.binder.id view.cumulative)
    | [candidate] => pure candidate
    | _ => throw (.duplicateInstance binding.binder.id view.cumulative)
  if selected.origin.caller != view.owner || selected.origin.source != view.binding.source ||
      selected.origin.binder != view.binding.binder || selected.origin.initializer != view.binding.initializer then
    throw (.invalidInitializer view.binding.initializer)
  pure {view with selectedInstance := some selected}

private def insert {program : CheckedProgram} {plan : Plan} (limits : Limits) (firstId : Nat)
    (entries : List (Entry program plan)) (view : View program plan) : Except Error (List (Entry program plan)) := do
  if entries.any (fun entry => decide (entry.view.key = view.key)) then
    throw (.duplicateView view.owner view.read view.parentActive)
  if entries.length ≥ limits.maxViews then throw (.viewBudgetExhausted limits.maxViews)
  let next := firstId + entries.length
  let id ← match Core.Word.ofNat? next with
    | some id => pure id
    | none => throw (.idSpaceExhausted next)
  pure (entries ++ [.mk id view])

private def collect {program : CheckedProgram} {plan : Plan} (limits : Limits) (firstId : Nat)
    (locals : SourceCoreLocalPolymorphism.Catalog) (bindings : List Binding) (parent : Option Parent)
    (nodes : List Node) (entries : List (Entry program plan)) : Except Error (List (Entry program plan)) := do
  let mut entries := entries
  for node in nodes do
    match node with
    | .expression node@{form := .reference _ (.local binder), ..} =>
        match bindings.find? (fun binding => decide (binding.binder.id = binder)) with
        | none => pure ()
        | some binding =>
            let view ← authenticate program plan binding parent node.id
            if node != view.reference.original then throw (.referenceMismatch node.id)
            let view ← selectInstance locals view
            entries ← insert limits firstId entries view
    | _ => pure ()
  pure entries

private def validateContext (program : CheckedProgram) (plan : Plan) (parent : Parent) : Except Error Unit := do
  let origin := parent.instance.origin
  let binding : Binding := {
    caller := origin.caller
    source := origin.source
    binder := origin.binder
    initializer := origin.initializer
    instances := []
  }
  let caller ← (SourceCoreLocalEvidence.exactCaller plan binding).mapError Error.evidence
  if parent.caller.key != caller.key || parent.source != origin.source.applySubstitution parent.substitution ||
      origin.parameterSubstitution != caller.parameterSubstitution then
    throw (.invalidContext caller.key origin.initializer)
  let expected ← (SourceSpecializationWorklist.localLambdaBodyNodes origin.source origin.localInstance).mapError Error.discovery
  if origin.bodyNodes != expected then throw (.invalidContext caller.key origin.initializer)
  let _ ← (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions).mapError Error.plan
  pure ()

/-- Inventory root lexical nodes and the direct bodies of cached authenticated
local instances. Nested generalized lambda bodies are visited only under their
own cumulative context; monomorphic nested bodies inherit the current context.
The enclosing compatible artifact already owns its program, plan and catalog. -/
def prepare {checked : Checked} (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (limits : Limits := {}) (firstId : Nat := 1) :
    Except Error (Table prepared.sourceProgram prepared.plan) := do
  if firstId = 0 then throw .zeroFirstId
  if prepared.contexts.length > limits.maxContexts then throw (.contextBudgetExhausted limits.maxContexts)
  let mut entries := []
  for caller in prepared.plan.specializations do
    let source := caller.function.typedBody
    validateSource limits caller.key source
    let bindings ← directBindings caller.key source
    let nodes ← rootNodes source bindings
    entries ← collect limits firstId prepared.locals bindings none nodes entries
  for parent in prepared.contexts do
    validateContext prepared.sourceProgram prepared.plan parent
    let origin := parent.instance.origin
    validateSource limits origin.caller parent.source
    let bindings ← directBindings origin.caller origin.source
    let nodes := origin.bodyNodes.map (Node.applySubstitution parent.substitution)
    entries ← collect limits firstId prepared.locals bindings (some parent) nodes entries
  if ids : (entries.map (·.id)).Nodup then
    if views : (entries.map (fun entry => entry.view.key)).Nodup then
      pure (.mk entries ids views)
    else
      match entries.head? with
      | some entry => throw (.duplicateView entry.view.owner entry.view.read entry.view.parentActive)
      | none => throw .duplicateId
  else throw .duplicateId

end Solcore.Frontend.SourceCoreCallableViews
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableViewLowering
/-! Select a cached local-read view and wrap its actual native expression.
No evidence is selected and no source body is traversed at runtime. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableViewLowering
open SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

inductive Error where
  | missingView (owner : Key) (read : ExpressionId) (active : TypeSystem.Substitution)
  | sourceOwnerMismatch
  | occurrenceMismatch (read : ExpressionId)
  | unsupportedCarrier (type : Core.Ty)
  deriving Repr

structure Viewed {program : CheckedProgram} {plan : Plan}
    (table : SourceCoreCallableViews.Table program plan) (owner : Key) (active : TypeSystem.Substitution)
    (read : ExpressionId) (original : SourceCoreBasic.LoweredExpr) where private mk ::
  entry : SourceCoreCallableViews.Entry program plan
  found : table.viewAt? owner read active = some entry
  lowered : SourceCoreBasic.LoweredExpr
  typeExact : lowered.type = original.type

def lowerWithReceipt {program : CheckedProgram} {plan : Plan}
    (table : SourceCoreCallableViews.Table program plan) (owner : Key) (active : TypeSystem.Substitution)
    (source : TypedSource) (read : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) :
    Except Error (Viewed table owner active read lowered) := do
  let entry ← match found : table.viewAt? owner read active with
    | none => throw (.missingView owner read active)
    | some entry => pure (⟨entry, found⟩ : {entry // table.viewAt? owner read active = some entry})
  unless source.owner = owner.declaration do throw .sourceOwnerMismatch
  let current ← match source.lookupExpression? read with
    | none => throw (.occurrenceMismatch read)
    | some current => pure current
  let reference := entry.val.view.reference
  unless current = reference.original || current = reference.normalized || current = entry.val.view.rawRead do
    throw (.occurrenceMismatch read)
  if !entry.val.view.wrapsPrincipal then pure ⟨entry.val, entry.property, lowered, rfl⟩ else
    match lowered.type with
    | .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word =>
        pure ⟨entry.val, entry.property, {
          lowered with expression := SourceCoreCallableViewWrappers.lower parameter result entry.val.id lowered.expression }, rfl⟩
    | type => throw (.unsupportedCarrier type)

def lower {program : CheckedProgram} {plan : Plan}
    (table : SourceCoreCallableViews.Table program plan) (owner : Key) (active : TypeSystem.Substitution)
    (source : TypedSource) (read : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) :
    Except Error SourceCoreBasic.LoweredExpr :=
  (lowerWithReceipt table owner active source read lowered).map (·.lowered)

end Solcore.Frontend.SourceCoreCallableViewLowering
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
/-! Compile source allocation metadata through the common compiler twice.
The discovery pass retains its actual compiler equation. Its reached requests
determine one shared nominal-definition suffix. The second pass authenticates
each request against that inventory and emits ordinary Core allocation code.
Entries and checkpoints are checked against this complete definition list.

Source inputs use the original admission plan and cached globals. No source
expression is evaluated by this runtime. Source heap export is a separate
consumer of the allocation ledger. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Layouts := SourceCoreAllocationLayouts.Prepared
abbrev Representation := SourceCoreGeneralFunctions.Representation

structure ViewTable where
  program : CheckedProgram
  plan : SourceSpecializationWorklist.Plan
  table : SourceCoreCallableViews.Table program plan

inductive Error where
  | contexts (error : SourceCoreAllocationContexts.Error)
  | discovery (error : SourceCoreAllocationDiscovery.Error)
  | layouts (error : SourceCoreAllocationLayouts.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | inputs (error : SourceCoreCompatibleInputs.Error)
  | native (error : SourceCoreGeneralEntry.NativeCompileError)
  | diagnosticsUnavailable
  | missingRoot (key : Key)
  | views (error : SourceCoreCallableViews.Error)
  deriving Repr

def packClosures : List Core.Expr → Core.Expr
  | [] => .unit
  | expression :: rest => .pair expression (packClosures rest)

mutual
  /-- Count Core nodes and branch-list links, independently of source or
  runtime fuel. Lowered helpers and the number of cached functions contribute. -/
  def scanBudget : Core.Expr → Nat
    | .unit | .bool _ | .word _ | .integer _ | .var _ => 1
    | .construct _ payload | .first payload | .second payload | .loadCell payload
    | .unary _ payload | .lambda _ _ payload | .inLeft _ payload | .inRight _ payload
    | .newCell _ payload => 1 + scanBudget payload
    | .pair left right | .apply left right | .storeCell left right | .binary _ left right
    | .letE left right => 1 + scanBudget left + scanBudget right
    | .caseE condition left right | .ifE condition left right | .ternary _ condition left right =>
      1 + scanBudget condition + scanBudget left + scanBudget right
    | .matchData _ _ scrutinee branches => 1 + scanBudget scrutinee + scanBranchesBudget branches
  def scanBranchesBudget : List Core.Expr → Nat
    | [] => 1
    | expression :: rest => 1 + scanBudget expression + scanBranchesBudget rest
end

def discoveryRepresentation {checked : Checked} (base : Base checked) (fuel : Nat)
    (discovery : SourceCoreAllocationDiscovery.Prepared)
    (views : Option (SourceCoreCallableViews.Table base.sourceProgram base.plan) := none) : Representation :=
  {SourceCoreCompatibleFunctions.representation (.initial checked) fuel with
    allocatorAt := fun owner active => some (discovery.allocatorAt owner active
      (fun error => .sourceAllocation (reprStr error)))
    localReadView := fun owner active source _ read lowered =>
      match views with
      | none => pure lowered
      | some views => (SourceCoreCallableViewLowering.lower views owner active source read lowered)
          |>.mapError (fun error => .callableMetadata (reprStr error))}

def markedRepresentation (checked : Checked) (fuel : Nat) (layouts : Layouts)
    (views : Option ViewTable := none) : Representation :=
  {SourceCoreCompatibleFunctions.representation (.initial checked) fuel with
    allocatorAt := fun owner active => some (layouts.allocatorAt owner active
      (fun error => .sourceAllocation (reprStr error)))
    localReadView := fun owner active source _ read lowered =>
      match views with
      | none => pure lowered
      | some views => (SourceCoreCallableViewLowering.lower views.table owner active source read lowered)
          |>.mapError (fun error => .callableMetadata (reprStr error))}

/-- This is the actual shared contextual function compiler, with its retained
diagnostic and local-evidence inventories. -/
def compileClosures {checked : Checked} (base : Base checked) (representation : Representation)
    (fuel : Nat) : Except Error (List Core.Expr) := do
  if base.functions.isEmpty then pure [] else
    let diagnostics ← match base.diagnostics with
      | none => throw .diagnosticsUnavailable
      | some diagnostics => pure diagnostics.program
    let diagnostics := match base.callableContext with
      | none => diagnostics
      | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
    (base.functions.mapM (SourceCoreGeneralFunctions.compileClosureWithRepresentation
      base.sourceProgram representation base.sourceProgram.signatures base.plan base.globals
      diagnostics base.locals base.callableContext fuel)).mapError Error.functions

structure Compilation {checked : Checked} (base : Base checked) (representation : Representation)
    (fuel : Nat) where private mk ::
  closures : List Core.Expr
  compiled : compileClosures base representation fuel = .ok closures

def compileWithReceipt {checked : Checked} (base : Base checked) (representation : Representation)
    (fuel : Nat) : Except Error (Compilation base representation fuel) :=
  match compiled : compileClosures base representation fuel with
  | .error error => .error error
  | .ok closures => .ok ⟨closures, compiled⟩

structure Entry (layouts : Layouts) where private mk ::
  key : Key
  inputs : List TypedBinder
  sourceResultType : TypeSystem.Ty
  native : SourceCoreGeneralEntry.NativeEntry layouts.definitions

structure SourceInputs (checked : Checked) (layouts : Layouts) where private mk ::
  context : SourceCoreCompatibleInputs.Context
  valuesExact : context.values = SourceCoreCompatibleValues.Context.initial checked
  definitionsExact : context.definitions = layouts.definitions

private def prepareInputs (checked : Checked) (base : Base checked) (layouts : Layouts) :
    Except Error (SourceInputs checked layouts) :=
  match accepted : SourceCoreCompatibleInputs.prepare (.initial checked) base.plan base.globals
      (base.callableContext.map (·.table)) layouts.definitions Core.Word.zero (some base.validationPlan) with
  | .error error => .error (.inputs error)
  | .ok context => .ok ⟨context, SourceCoreCompatibleInputs.prepare_values accepted, by
      unfold SourceCoreCompatibleInputs.prepare at accepted
      split at accepted
      · contradiction
      · cases accepted; rfl⟩

structure Prepared (checked : Checked) where private mk ::
  base : Base checked
  fuel : Nat
  views : SourceCoreCallableViews.Table base.sourceProgram base.plan
  viewsPrepared : SourceCoreCallableViews.prepare base = .ok views
  contexts : SourceCoreAllocationContexts.Inventory base.plan base.contexts
  contextsPrepared : SourceCoreAllocationContexts.fromPrepared base.plan base.contexts = .ok contexts
  discovery : SourceCoreAllocationDiscovery.Prepared
  discoveryPrepared : SourceCoreAllocationDiscovery.prepare checked.catalog.definitions contexts.contexts = .ok discovery
  firstPass : Compilation base (discoveryRepresentation base fuel discovery (some views)) fuel
  discovered : SourceCoreAllocationDiscovery.Discovered discovery (scanBudget (packClosures firstPass.closures))
    (packClosures firstPass.closures)
  scanned : SourceCoreAllocationDiscovery.discover discovery (scanBudget (packClosures firstPass.closures))
    (packClosures firstPass.closures) = .ok discovered
  layouts : Layouts
  layoutsPrepared : SourceCoreAllocationLayouts.prepare discovered = .ok layouts
  secondPass : Compilation base (markedRepresentation checked fuel layouts
    (some ⟨base.sourceProgram, base.plan, views⟩)) fuel
  sourceInputs : SourceInputs checked layouts
  entries : List (Entry layouts)

def prepare {checked : Checked} (base : Base checked) (fuel : Nat) : Except Error (Prepared checked) := do
  let views ← match accepted : SourceCoreCallableViews.prepare base with
    | .error error => throw (.views error)
    | .ok views => pure (⟨views, accepted⟩ : {views // SourceCoreCallableViews.prepare base = .ok views})
  let contexts ← match accepted : SourceCoreAllocationContexts.fromPrepared base.plan base.contexts with
    | .error error => throw (.contexts error)
    | .ok inventory => pure (⟨inventory, accepted⟩ : {inventory //
        SourceCoreAllocationContexts.fromPrepared base.plan base.contexts = .ok inventory})
  let discovery ← match accepted : SourceCoreAllocationDiscovery.prepare checked.catalog.definitions contexts.val.contexts with
    | .error error => throw (.discovery error)
    | .ok discovery => pure (⟨discovery, accepted⟩ : {discovery //
        SourceCoreAllocationDiscovery.prepare checked.catalog.definitions contexts.val.contexts = .ok discovery})
  let firstPass ← compileWithReceipt base (discoveryRepresentation base fuel discovery.val (some views.val)) fuel
  let discovered ← match accepted : SourceCoreAllocationDiscovery.discover discovery.val
      (scanBudget (packClosures firstPass.closures)) (packClosures firstPass.closures) with
    | .error error => throw (.discovery error)
    | .ok discovered => pure (⟨discovered, accepted⟩ : {discovered //
        SourceCoreAllocationDiscovery.discover discovery.val (scanBudget (packClosures firstPass.closures))
          (packClosures firstPass.closures) = .ok discovered})
  let layouts ← match accepted : SourceCoreAllocationLayouts.prepare discovered.val with
    | .error error => throw (.layouts error)
    | .ok layouts => pure (⟨layouts, accepted⟩ : {layouts //
        SourceCoreAllocationLayouts.prepare discovered.val = .ok layouts})
  let secondPass ← compileWithReceipt base (markedRepresentation checked fuel layouts.val
    (some ⟨base.sourceProgram, base.plan, views.val⟩)) fuel
  let sourceInputs ← prepareInputs checked base layouts.val
  let entries ← base.plan.seedKeys.mapM fun key => do
    let function ← match base.functions.find? (fun function => decide (function.signature.key = key)) with
      | none => throw (.missingRoot key)
      | some function => pure function
    let arguments := SourceCoreCalls.packArguments (function.inputs.zipIdx.map fun ((_, type), index) =>
      ⟨type, Core.OptionalCell.read type (.var (base.globals.length + function.inputs.length - 1 - index)) Core.Word.zero⟩)
    let body ← (SourceCoreGeneralFunctions.assembleCall base.globals base.functions secondPass.closures key arguments)
      |>.mapError Error.functions
    let native ← (SourceCoreGeneralEntry.NativeEntry.compile layouts.val.definitions (function.inputs.map Prod.snd)
      function.signature.resultType body).mapError Error.native
    pure (Entry.mk key (function.inputs.map Prod.fst) function.specialized.function.inferredBodyType native)
  pure ⟨base, fuel, views.val, views.property, contexts.val, contexts.property, discovery.val, discovery.property,
    firstPass, discovered.val, discovered.property, layouts.val, layouts.property, secondPass, sourceInputs, entries⟩

def Prepared.find? {checked : Checked} (prepared : Prepared checked) (key : Key) : Option (Entry prepared.layouts) :=
  prepared.entries.find? (fun entry => decide (entry.key = key))

inductive RunError where
  | missingEntry (key : Key)
  | input (error : SourceCoreCompatibleInputs.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | compile (error : SourceCoreGeneralEntry.NativeCompileError)
  | native (error : SourceCoreGeneralEntry.RunError)
  | diagnostics (error : SourceCoreCompatibleDataPlaceFaultSites.Error)
  deriving Repr

structure Result {checked : Checked} (prepared : Prepared checked) (entry : Entry prepared.layouts) where private mk ::
  context : SourceCoreCompatibleValues.Context
  contextOwner : context.checked = checked
  extension : SourceCoreRawMetadata.Extends checked.staticRegistry context.registry
  diagnostics : SourceCoreFaultSites.Table
  native : SourceCoreGeneralEntry.Result prepared.layouts.definitions entry.native.resultType

structure Completion {checked : Checked} (prepared : Prepared checked) where private mk ::
  entry : Entry prepared.layouts
  result : Result prepared entry

private def diagnosticTable {checked : Checked} (prepared : Prepared checked) (entry : Entry prepared.layouts)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry) : Except RunError SourceCoreFaultSites.Table := do
  let table ← match prepared.base.diagnostics with
    | some diagnostics => (diagnostics.tableForRegistry registry extension).mapError RunError.diagnostics
    | none => pure {
        owner := entry.key.declaration
        resultType := entry.sourceResultType
        reads := []
        escapedReason := Core.Word.zero }
  pure <| match prepared.base.callableDiagnostics with
    | none => table
    | some diagnostics => {table with additional := table.additional ++
        diagnostics.rootTable.additional.filter (fun item => diagnostics.unknown.val ≤ item.1.val)}

def Prepared.runSource {checked : Checked} (prepared : Prepared checked) (key : Key)
    (arguments : List SourceTypedRuntime.Value) (executionFuel : Nat) (validationFuel : Nat := 256) :
    Except RunError (Completion prepared) := do
  let entry ← match prepared.find? key with
    | none => throw (.missingEntry key)
    | some entry => pure entry
  let ready := prepared.sourceInputs
  let encoded ← (SourceCoreCompatibleInputs.encode ready.context (entry.inputs.map (·.scheme.body))
    arguments validationFuel).mapError RunError.input
  have extension : SourceCoreRawMetadata.Extends checked.staticRegistry encoded.values.registry := by
    change SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry _
    rw [← ready.valuesExact]
    exact encoded.preserves
  let context := (SourceCoreCompatibleValues.Context.initial checked).extend encoded.values.registry extension
  let body ← (SourceCoreGeneralFunctions.assembleCall prepared.base.globals prepared.base.functions
    prepared.secondPass.closures key ⟨encoded.type, encoded.expression⟩).mapError RunError.functions
  let native ← match accepted : SourceCoreGeneralEntry.NativeEntry.compile prepared.layouts.definitions []
      entry.native.resultType body with
    | .error error => throw (.compile error)
    | .ok runner =>
        let result ← (runner.run [] executionFuel).mapError RunError.native
        have resultType := (SourceCoreGeneralEntry.NativeEntry.compile_fields accepted).2.1
        pure (resultType ▸ result)
  let table ← diagnosticTable prepared entry encoded.values.registry extension
  pure ⟨entry, ⟨context, rfl, extension, table, native⟩⟩

def Completion.resume {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (fuel : Nat) : Completion prepared :=
  match completion.result.native.checkpoint? with
  | none => completion
  | some checkpoint => ⟨completion.entry, {completion.result with native := checkpoint.resume fuel}⟩

end Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleMarkedLedger
/-! Typed allocation-ledger observations of the actual marked compiler's Core
results. Success, language failure and suspension all expose their actual
store, typed in its canonical finite world under the artifact's definitions.
Suspension is retained as a checkpoint; observing it does not resume execution.

The supplied initial source heap remains an opaque prefix. This adapter does
not decode native payloads, authenticate arbitrary stores as execution traces,
or assert source evaluation correspondence. Its completion argument retains
the two real compiler receipts and the native result typing. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleMarkedLedger
open Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCompatibleMarkedFunctions.Prepared
abbrev Completion {checked : Checked} (prepared : Prepared checked) :=
  SourceCoreCompatibleMarkedFunctions.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap

def observedStore : LanguageResult.Observation → Store
  | .succeeded _ store | .failed _ store | .invalidCarrier _ store => store
  | .outOfFuel state | .internalFault _ state => state.store

private theorem canonical_store {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typed : RuntimeStoreHasTypes world store definitions) :
    RuntimeStoreHasTypes (store.map Value.type) store definitions := by
  rw [← typed.world_eq]
  exact typed

theorem native_store_typed {definitions : DataEnvironment} {type : Ty}
    (result : SourceCoreGeneralEntry.Result definitions type) :
    RuntimeStoreHasTypes ((observedStore result.observation).map Value.type)
      (observedStore result.observation) definitions := by
  have typed := result.typed
  cases outcome : result.observation with
  | succeeded value store =>
    rw [outcome] at typed
    exact canonical_store typed.choose_spec.1
  | failed reason store =>
    rw [outcome] at typed
    obtain ⟨world, stored⟩ := typed
    exact canonical_store stored
  | outOfFuel state =>
    rw [outcome] at typed
    cases typed with
    | eval stored _ _ _ => exact canonical_store stored
    | ret stored _ _ => exact canonical_store stored
  | internalFault error state =>
    exact False.elim (result.ne_internalFault error state outcome)
  | invalidCarrier value store =>
    exact False.elim (result.ne_invalidCarrier value store outcome)

def store {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) : Store :=
  observedStore completion.result.native.observation

def world {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) : StoreTyping :=
  (store completion).map Value.type

theorem store_typed {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    RuntimeStoreHasTypes (world completion) (store completion) prepared.layouts.definitions :=
  native_store_typed completion.result.native

abbrev Receipt {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initial : SourceHeap) :=
  SourceCoreAllocationLedger.TypedLedger prepared.layouts initial (world completion) (store completion)

def scan {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initial : SourceHeap := []) :
    Except SourceCoreAllocationLedger.Error (Receipt completion initial) :=
  SourceCoreAllocationLedger.scanTyped prepared.layouts initial (world completion) (store completion)
    (store_typed completion)

theorem succeeded_store {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) {value : Value} {actual : Store}
    (success : completion.result.native.observation = .succeeded value actual) : store completion = actual := by
  simp only [store, success, observedStore]

theorem failed_store {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) {reason : Word} {actual : Store}
    (failure : completion.result.native.observation = .failed reason actual) : store completion = actual := by
  simp only [store, failure, observedStore]

theorem suspended_store {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) {checkpoint : State}
    (suspended : completion.result.native.observation = .outOfFuel checkpoint) :
    store completion = checkpoint.store := by
  simp only [store, suspended, observedStore]

theorem receipt_prefix {checked : Checked} {prepared : Prepared checked}
    {completion : Completion prepared} {initial : SourceHeap} (receipt : Receipt completion initial)
    {ε : Type} (decode : SourceCoreAllocationLedger.Row prepared.layouts (store completion) →
      Except ε SourceTypedRuntime.Cell) {heap : SourceHeap}
    (exported : receipt.ledger.exportHeap decode = .ok heap) : heap.take initial.length = initial :=
  receipt.ledger.exportHeap_prefix decode exported

end Solcore.Frontend.SourceCoreCompatibleMarkedLedger
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreLambdaTemplates
/-! Source-lambda manifests and exact native templates. The ordinary Core
manifest records owned callable and binder keys, actual payload types, and
actual lexical reference variables. Later weakening acts on those variables.

Structural scanning is not source emission history. `Compiled` additionally
retains the actual compiler equation; an enclosing artifact must retain that
receipt and its chosen source representation. Authentication checks exact code,
descriptor and typed captures, while source locations require the allocation
ledger. Dynamic ancestry of occurrence-specific instantiated views remains a
separate transport boundary. Unused principal bundles emit no native lambda.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreLambdaTemplates
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Scope := SourceCoreFunctions.Scope
abbrev Origin := SourceCoreStageCodebook.Origin
abbrev Context := SourceCoreAllocationCodebook.IndexedContext
abbrev Active := TypeSystem.Substitution

inductive Error where
  | contexts (error : SourceCoreAllocationContexts.Error)
  | metadata (error : SourceCoreAllocationCodebook.Error)
  | contractsUnavailable
  | missingOrigin (origin : Origin)
  | missingContext (owner : Key) (active : Active)
  | invalidLambda (id : ExpressionId)
  | sourceViewMismatch (owner : Key)
  | projection (error : SourceCoreCompatibleCatalog.Error)
  | scopeMismatch (id : Resolved.LocalId)
  | duplicateScope
  | invalidCaptureType (type : Core.Ty)
  | malformedManifest (detail : String)
  | descriptorMismatch (expected actual : Word)
  | unknownDescriptor (id : Word)
  | callableTypeMismatch
  | missingCapture (index : Nat)
  | captureMismatch (index : Nat)
  | captureOutsideWorld (location : Nat)
  | closureMismatch
  | foreignDefinitions
  | globalSlotMismatch (index : Nat)
  | globalEnvironmentMismatch
  | traversalExhausted
  | compilation (error : SourceCoreCompatibleMarkedFunctions.Error)
  deriving Repr

structure Lambda where private mk ::
  descriptor : Word
  owner : Key
  id : ExpressionId
  active : Active
  context : Context
  originalSource : TypedSource
  principalSource : TypedSource
  original : ExpressionNode
  node : ExpressionNode
  parameterType : Core.Ty
  resultType : Core.Ty

structure Inventory (checked : Checked) where private mk ::
  base : Base checked
  contexts : SourceCoreAllocationDiscovery.Prepared
  lambdas : List Lambda

/-- The source heap can retain these principal closures even though their
native empty bundle is Unit. Their source metadata/captures must be recovered
from the allocation ledger, not from a nonexistent executable template. -/
def Inventory.unusedPrincipals {checked : Checked} (inventory : Inventory checked) : List SourceCoreLocalPolymorphism.Binding :=
  inventory.base.locals.bindings.filter (fun binding => binding.instances.isEmpty)

def Inventory.lambdaAt? {checked : Checked} (inventory : Inventory checked) (id : Word) : Option Lambda :=
  inventory.lambdas.find? (fun lambda => decide (lambda.descriptor = id))

/-- Actual metadata from the sealed base artifact, including both original and
contextual sources. The static principal view is retained separately; it does
not claim to encode dynamic read-view ancestry. -/
def prepare {checked : Checked} (base : Base checked) : Except Error (Inventory checked) := do
  let receipts ← (SourceCoreAllocationContexts.fromPrepared base.plan base.contexts).mapError Error.contexts
  let contexts ← (SourceCoreAllocationDiscovery.prepare checked.catalog.definitions receipts.contexts).mapError Error.metadata
  let callable ← match base.callableContext with
    | some callable => pure callable | none => throw .contractsUnavailable
  let mut lambdas := []
  for entry in callable.table.entries do
    match entry.origin with
    | .lambda owner id active =>
      let context ← match contexts.metadata.contextAt? owner active with
        | some context => pure context | none => throw (.missingContext owner active)
      let caller ← (SourceCompilationPlan.exactSpecialization base.plan owner).mapError
        (fun _ => Error.missingOrigin entry.origin)
      let original ← match caller.function.typedBody.lookupExpression? id with
        | some node => pure node | none => throw (.invalidLambda id)
      let node ← match context.inventory.source.lookupExpression? id with
        | some node => pure node | none => throw (.invalidLambda id)
      let (parameters, result) ← match node.form with
        | .lambda parameters result _ => pure (parameters, result)
        | _ => throw (.invalidLambda id)
      let inherited := (base.contexts.find? (fun parent => decide
        (parent.caller.key = owner ∧ parent.substitution = active))).map (·.witnesses) |>.getD []
      let principalSource := SourceTypedRuntime.rewriteLocalRequirements inherited
        (caller.function.typedBody.applySubstitution active)
      let parameterType ← (checked.catalog.project (TypeSystem.Ty.productMany (parameters.map (·.scheme.body)))).mapError Error.projection
      let resultType ← (checked.catalog.project result).mapError Error.projection
      lambdas := lambdas ++ [⟨entry.id, owner, id, active, context, caller.function.typedBody,
        principalSource, original, node, parameterType, resultType⟩]
    | _ => pure ()
  pure ⟨base, contexts, lambdas⟩

/-- Type annotations have unit payloads. Real capture references remain in a
separate product, so renaming never hides their actual environment indices. -/
def scopeManifest : List (Word × Core.Ty) → Expr
  | [] => .unit
  | (key, type) :: rest => .pair (.pair (.word key) (.inLeft type .unit)) (scopeManifest rest)

def scopeManifestType : List (Word × Core.Ty) → Core.Ty
  | [] => .unit
  | (_, type) :: rest => .product (.product .word (.sum .unit type)) (scopeManifestType rest)

private def scopeManifest? : Expr → Option (List (Word × Core.Ty))
  | .unit => some []
  | .pair (.pair (.word key) (.inLeft type .unit)) rest => (scopeManifest? rest).map ((key, type) :: ·)
  | _ => none

private def capturedIndices? : Scope → Expr → Option (List Nat)
  | [], .unit => some []
  | [_], .var index => some [index]
  | _ :: next :: rest, .pair (.var index) tail => (capturedIndices? (next :: rest) tail).map (index :: ·)
  | _, _ => none

def manifestBody (descriptor : Word) (fields : List (Word × Core.Ty)) (captures body : Expr) : Expr :=
  .letE (.pair (.word descriptor) (.pair (scopeManifest fields) (captures.weakenAt 0))) (body.weakenAt 0)

private def scopeFields (lambda : Lambda) (scope : Scope) : Except Error (List (Word × Core.Ty)) := do
  unless (scope.map Prod.fst).Nodup do throw .duplicateScope
  scope.mapM fun (binder, type) => do
    let row ← match lambda.context.bindingAt? binder with
      | some row => pure row | none => throw (.scopeMismatch binder)
    pure (row.key, type)

/-- The shared compiler calls this after parameter allocation has been
lowered. Source lexical references occupy contiguous saved-environment slots;
the raw lambda argument adds the initial shift inside its body. -/
def hook {checked : Checked} (inventory : Inventory checked) (owner : Key) (active : Active) :
    SourceCoreFunctions.RawLambdaBodyHook := fun context source scope node parameter result body => do
  let fail := fun error => SourceCoreBasic.Error.sourceAllocation (reprStr error)
  let lambda ← match inventory.lambdas.find? (fun lambda => decide
      (lambda.owner = owner ∧ lambda.id = node.id ∧ lambda.active = active)) with
    | some lambda => pure lambda
    | none => throw (fail (.missingOrigin (.lambda owner node.id active)))
  if context.owner != owner || source.owner != owner.declaration ||
      SourceCoreAllocationCodebook.sourceView source != SourceCoreAllocationCodebook.sourceView lambda.context.inventory.source then
    throw (fail (.sourceViewMismatch owner))
  if node.form != lambda.node.form || parameter != lambda.parameterType || result != lambda.resultType then
    throw (fail .callableTypeMismatch)
  let fields ← (scopeFields lambda scope).mapError fail
  for (_, type) in scope do
    unless type.isWellFormed checked.catalog.definitions do throw (fail (.invalidCaptureType type))
  pure (manifestBody lambda.descriptor fields (SourceCoreSourceCells.captures id scope) body)

def representation {checked : Checked} (inventory : Inventory checked)
    (original : SourceCoreGeneralFunctions.Representation) : SourceCoreGeneralFunctions.Representation :=
  {original with rawLambdaBodyAt := hook inventory}

structure Receipt where private mk ::
  lambda : Lambda
  scope : Scope
  scopeFields : List (Word × Core.Ty)
  /-- Indices in the saved Core closure environment, after installation and
  every surrounding administrative renaming. -/
  references : List Nat
  parameterType : Core.Ty
  resultType : Core.Ty
  body : Expr
  carrier : Expr

/-- Decode one complete contracted anonymous lambda. Scope keys are checked
against immutable source binder metadata; payload types are checked by the
actual native checker and the capture authenticator, rather than inferred
from those source binder schemes. -/
def decode {checked : Checked} (inventory : Inventory checked) (carrier : Expr) : Except Error Receipt := do
  let .pair (.pair (.inLeft .word .unit) (.lambda parameter (.sum .word result) body)) (.word descriptor) := carrier
    | throw (.malformedManifest "complete callable shape")
  let .letE (.pair (.word key) (.pair fields captures)) _ := body | throw (.malformedManifest "shape")
  if descriptor != key then throw (.descriptorMismatch key descriptor)
  let lambda ← match inventory.lambdaAt? key with
    | some lambda => pure lambda | none => throw (.unknownDescriptor key)
  if parameter != lambda.parameterType || result != lambda.resultType then throw .callableTypeMismatch
  let fields ← match scopeManifest? fields with | some fields => pure fields | none => throw (.malformedManifest "shape")
  unless (fields.map Prod.fst).Nodup do throw .duplicateScope
  let scope ← fields.mapM fun (key, type) => do
    let row ← match lambda.context.bindings.find? (fun row => decide (row.key = key)) with
      | some row => pure row | none => throw (.malformedManifest "shape")
    unless type.isWellFormed checked.catalog.definitions do throw (.invalidCaptureType type)
    pure (row.binding.binder.id, type)
  let references ← match capturedIndices? scope captures with
    | some references => pure references | none => throw (.malformedManifest "shape")
  unless references.Nodup do throw .duplicateScope
  if references.any (· == 0) then throw (.malformedManifest "lambda argument in source captures")
  pure ⟨lambda, scope, fields, references.map (· - 1), parameter, result, body, carrier⟩

/-- Syntactic manifest recognition only. The complete decoder owns all keys,
source metadata and actual shape checks. -/
private def hasManifest : Expr → Bool
  | .lambda _ _ (.letE (.pair (.word _) (.pair fields _)) _) => (scopeManifest? fields).isSome
  | _ => false

mutual
  def scan {checked : Checked} (inventory : Inventory checked) : Nat → Expr → Except Error (List Receipt)
    | 0, _ => .error .traversalExhausted
    | fuel + 1, expression => do
      match expression with
      | .pair (.pair identity lambda) descriptor =>
        if hasManifest lambda then
          let receipt ← decode inventory expression
          let .lambda _ _ (.letE _ inner) := lambda | throw (.malformedManifest "shape")
          pure (receipt :: (← scan inventory fuel inner))
        else
          -- The left child can itself be a complete contracted callable,
          -- for example the first component of a polymorphic bundle. Keep
          -- that pair intact so its manifested lambda is not scanned alone.
          pure ((← scan inventory fuel (.pair identity lambda)) ++ (← scan inventory fuel descriptor))
      | .unit | .bool _ | .word _ | .integer _ | .var _ => pure []
      | .lambda _ _ body =>
        if hasManifest expression then throw (.malformedManifest "manifest outside complete callable carrier")
        scan inventory fuel body
      | .pair left right | .apply left right | .storeCell left right | .binary _ left right | .letE left right =>
        pure ((← scan inventory fuel left) ++ (← scan inventory fuel right))
      | .first operand | .second operand | .loadCell operand | .inLeft _ operand | .inRight _ operand |
        .newCell _ operand | .construct _ operand | .unary _ operand => scan inventory fuel operand
      | .caseE first second third | .ifE first second third | .ternary _ first second third =>
        pure ((← scan inventory fuel first) ++ (← scan inventory fuel second) ++ (← scan inventory fuel third))
      | .matchData _ _ scrutinee branches => pure ((← scan inventory fuel scrutinee) ++ (← scanBranches inventory fuel branches))
  def scanBranches {checked : Checked} (inventory : Inventory checked) : Nat → List Expr → Except Error (List Receipt)
    | _, [] => pure []
    | 0, _ :: _ => .error .traversalExhausted
    | fuel + 1, head :: tail => do
      pure ((← scan inventory fuel head) ++ (← scanBranches inventory fuel tail))
end

def installedTemplate (index : Nat) (expression : Expr) : Expr :=
  (List.range index).foldl (fun expression _ => expression.weakenAt 0) expression

structure Compiled {checked : Checked} (inventory : Inventory checked)
    (original : SourceCoreGeneralFunctions.Representation) (fuel : Nat) where private mk ::
  compilation : SourceCoreCompatibleMarkedFunctions.Compilation inventory.base (representation inventory original) fuel
  /-- Templates are scanned after the exact administrative weakening used
  when the compiled globals are installed. Duplicated emission sites remain. -/
  groups : List (List Receipt)
  scanned : (compilation.closures.zipIdx.mapM fun (closure, index) =>
    scan inventory (SourceCoreCompatibleMarkedFunctions.scanBudget (installedTemplate index closure))
      (installedTemplate index closure)) = .ok groups


def Compiled.templates {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) : List Receipt := compiled.groups.flatten

def compile {checked : Checked} (inventory : Inventory checked)
    (original : SourceCoreGeneralFunctions.Representation) (fuel : Nat) :
    Except Error (Compiled inventory original fuel) := do
  let compilation ← (SourceCoreCompatibleMarkedFunctions.compileWithReceipt inventory.base
    (representation inventory original) fuel).mapError Error.compilation
  match scanned : compilation.closures.zipIdx.mapM (fun (closure, index) =>
      scan inventory (SourceCoreCompatibleMarkedFunctions.scanBudget (installedTemplate index closure))
        (installedTemplate index closure)) with
  | .error error => throw error
  | .ok groups => pure ⟨compilation, groups, scanned⟩

structure Captured (scope : Scope) (references : List Nat) (environment : Core.Environment) (world : StoreTyping) where private mk ::
  locations : List Nat
  exact : (references.zip scope |>.zip locations |>.all (fun ((index, (_, type)), location) =>
    decide (environment[index]? = some (.cellRef (OptionalCell.cellType type) location) ∧
      world[location]? = some (OptionalCell.cellType type)))) = true
  lengths : references.length = scope.length ∧ locations.length = scope.length

private def captureLocations (scope : Scope) (references : List Nat) (environment : Core.Environment)
    (world : StoreTyping) : Except Error (Captured scope references environment world) := do
  if references.length != scope.length then throw (.malformedManifest "shape")
  let locations ← (references.zip scope).mapM fun (index, (_, type)) => do
    let captured ← match environment[index]? with
      | some captured => pure captured | none => throw (.missingCapture index)
    let .cellRef actual location := captured | throw (.captureMismatch index)
    if actual != OptionalCell.cellType type then throw (.captureMismatch index)
    if world[location]? != some (OptionalCell.cellType type) then throw (.captureOutsideWorld location)
    pure location
  if lengths : references.length = scope.length ∧ locations.length = scope.length then
    if exact : (references.zip scope |>.zip locations |>.all (fun ((index, (_, type)), location) =>
        decide (environment[index]? = some (.cellRef (OptionalCell.cellType type) location) ∧
          world[location]? = some (OptionalCell.cellType type)))) = true then
      pure ⟨locations, exact, lengths⟩
    else throw (.malformedManifest "shape")
  else throw (.malformedManifest "shape")

/-- This receipt checks exact native code and typed capture references. It
must be paired with `Compiled` membership from the enclosing artifact and the
source allocation ledger before identifying a source closure. -/
structure Authenticated (receipt : Receipt) (definitions : DataEnvironment) (world : StoreTyping)
    (store : Store) (value : Core.Value) where private mk ::
  environment : Core.Environment
  captures : Captured receipt.scope receipt.references environment world
  stored : RuntimeStoreHasTypes world store definitions
  typed : RuntimeValueHasType world value
    (CallableContract.functionType receipt.parameterType receipt.resultType) definitions
  exact : value = .pair (.pair (.inLeft .word .unit)
    (.closure receipt.parameterType (LanguageResult.resultType receipt.resultType) receipt.body environment))
    (.word receipt.lambda.descriptor)

def authenticate (receipt : Receipt) {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (stored : RuntimeStoreHasTypes world store definitions) (value : Core.Value)
    (typed : RuntimeValueHasType world value
      (CallableContract.functionType receipt.parameterType receipt.resultType) definitions) :
    Except Error (Authenticated receipt definitions world store value) := do
  let .pair (.pair (.inLeft .word .unit) (.closure parameter result body environment)) (.word descriptor) := value
    | throw .closureMismatch
  if parameter != receipt.parameterType || result != LanguageResult.resultType receipt.resultType ||
      body != receipt.body || descriptor != receipt.lambda.descriptor then throw .closureMismatch
  let captures ← captureLocations receipt.scope receipt.references environment world
  if exact : value = .pair (.pair (.inLeft .word .unit)
      (.closure receipt.parameterType (LanguageResult.resultType receipt.resultType) receipt.body environment))
      (.word receipt.lambda.descriptor) then
    pure ⟨environment, captures, stored, typed, exact⟩
  else throw .closureMismatch

def freshGlobals (globals : List SourceCoreCalls.Signature) (base : Nat := 0) : Core.Environment :=
  globals.zipIdx.map fun (signature, index) =>
    .cellRef (OptionalCell.cellType signature.functionType) (base + globals.length - 1 - index)

private def expectedGlobals {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) (base : Nat) : Except Error (List (Nat × Core.Value)) := do
  let globals := inventory.base.globals
  if compiled.compilation.closures.length != globals.length then throw .globalEnvironmentMismatch
  globals.zipIdx.mapM fun (signature, index) => do
    let cached ← match compiled.compilation.closures[index]? with
      | some cached => pure cached | none => throw (.globalSlotMismatch index)
    let .lambda parameter result body := installedTemplate index cached | throw (.globalSlotMismatch index)
    if parameter != signature.parameterType || result != LanguageResult.resultType signature.resultType then
      throw (.globalSlotMismatch index)
    let captured := List.replicate index Core.Value.unit ++ freshGlobals globals base
    pure (base + globals.length - 1 - index,
      .inRight .unit (.closure parameter result body captured))

structure Globals {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) (store : Store) (base : Nat) where private mk ::
  slots : List (Nat × Core.Value)
  generated : expectedGlobals compiled base = .ok slots
  exact : slots.all (fun (index, value) => decide (store[index]? = some value)) = true

def snapshotGlobals {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) (store : Store) (base : Nat := 0) :
    Except Error (Globals compiled store base) := do
  match generated : expectedGlobals compiled base with
  | .error error => throw error
  | .ok slots =>
    if exact : slots.all (fun (index, value) => decide (store[index]? = some value)) = true then
      pure ⟨slots, generated, exact⟩
    else
      match slots.find? (fun (index, value) => decide (store[index]? != some value)) with
      | some (index, _) => throw (.globalSlotMismatch index)
      | none => throw .globalEnvironmentMismatch

/-- An export receipt is indexed by the artifact's actual compiler/scanner
receipt. Structural manifest decoding alone cannot produce this membership. -/
structure Export {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) (definitions : DataEnvironment)
    (world : StoreTyping) (store : Store) (value : Core.Value) where private mk ::
  /-- Ambient marker definitions may extend this artifact's definitions, but
  cannot replace the constructor payload table of its catalog. -/
  definitionsPrefix : definitions.take checked.catalog.definitions.length = checked.catalog.definitions
  globalsBase : Nat
  globals : Globals compiled store globalsBase
  template : Receipt
  member : template ∈ compiled.templates
  closure : Authenticated template definitions world store value
  capturedGlobals : (closure.environment.drop (closure.environment.length - inventory.base.globals.length)) =
    freshGlobals inventory.base.globals globalsBase

def authenticateCompiled {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) {definitions : DataEnvironment}
    {world : StoreTyping} {store : Store} (stored : RuntimeStoreHasTypes world store definitions)
    (value : Core.Value) (parameter result : Core.Ty)
    (typed : RuntimeValueHasType world value (CallableContract.functionType parameter result) definitions)
    (globalsBase : Nat := 0) : Except Error (Export compiled definitions world store value) := do
  if definitionsPrefix : definitions.take checked.catalog.definitions.length = checked.catalog.definitions then
    let globals ← snapshotGlobals compiled store globalsBase
    let .pair (.pair (.inLeft .word .unit) (.closure _ _ body _)) (.word descriptor) := value | throw .closureMismatch
    let selected ← match compiled.templates.attach.find? (fun item => decide
        (item.val.lambda.descriptor = descriptor ∧ item.val.body = body ∧
          item.val.parameterType = parameter ∧ item.val.resultType = result)) with
      | some item => pure item | none => throw .closureMismatch
    if types : selected.val.parameterType = parameter ∧ selected.val.resultType = result then
      let authenticated ← authenticate selected.val stored value (by simpa only [types.1, types.2] using typed)
      if capturedGlobals : authenticated.environment.drop
          (authenticated.environment.length - inventory.base.globals.length) =
          freshGlobals inventory.base.globals globalsBase then
        pure ⟨definitionsPrefix, globalsBase, globals, selected.val, selected.property, authenticated, capturedGlobals⟩
      else throw .globalEnvironmentMismatch
    else throw .closureMismatch
  else throw .foreignDefinitions

theorem scopeManifest_hasType {definitions : DataEnvironment} {context : Core.Context}
    (fields : List (Word × Core.Ty)) (wellFormed : ∀ field ∈ fields, field.2.WellFormed definitions) :
    HasType context (scopeManifest fields) (scopeManifestType fields) definitions := by
  induction fields with
  | nil => exact .unit
  | cons head tail ih =>
    exact .pair (.pair .word (.inLeft (wellFormed head (by simp)) .unit))
      (ih (fun field member => wellFormed field (List.mem_cons_of_mem head member)))

/-- The manifest's saved references run before parameter binding. Its pure
metadata/capture product adds one private environment value and no heap cell. -/
theorem manifestBody_hasType {definitions : DataEnvironment} {context : Core.Context}
    {fields : List (Word × Core.Ty)} {captures body : Expr} {captureType resultType parameterType : Core.Ty}
    (descriptor : Word) (fieldsWF : ∀ field ∈ fields, field.2.WellFormed definitions)
    (capturesTyped : HasType context captures captureType definitions)
    (bodyTyped : HasType (parameterType :: context) body resultType definitions) :
    HasType (parameterType :: context) (manifestBody descriptor fields captures body) resultType definitions := by
  have shifted : HasType (parameterType :: context) (captures.weakenAt 0) captureType definitions := by
    simpa only [Core.Context.insertAt] using capturesTyped.weakenAt (inserted := parameterType) 0
  unfold manifestBody
  apply HasType.letE (.pair .word (.pair (scopeManifest_hasType fields fieldsWF) shifted))
  simpa only [Core.Context.insertAt] using bodyTyped.weakenAt 0

def scopeManifestValue : List (Word × Core.Ty) → Core.Value
  | [] => .unit
  | (key, type) :: rest => .pair (.pair (.word key) (.inLeft type .unit)) (scopeManifestValue rest)

theorem scopeManifest_evaluates (fields : List (Word × Core.Ty)) (environment : Core.Environment) (store : Store) :
    Evaluates environment store (scopeManifest fields) (scopeManifestValue fields) store := by
  induction fields with
  | nil => exact .unit
  | cons head tail ih => exact .pair (.pair .word (.inLeft .unit)) ih

/-- Adding the private manifest binder preserves higher-order results and
stores under Core's established relational renaming, with finite evaluation
witnesses on both sides. Exact closure environments may grow. -/
theorem manifestBody_related {environment : Core.Environment} {store finalStore : Store}
    {fields : List (Word × Core.Ty)} {captures body : Expr} {captureValue result : Core.Value}
    (descriptor : Word)
    (captureEvaluation : Evaluates environment store (captures.weakenAt 0) captureValue store)
    (bodyEvaluation : Evaluates environment store body result finalStore) :
    ∃ result' finalStore', Evaluates environment store (manifestBody descriptor fields captures body) result' finalStore' ∧
      ValuesRelated result result' ∧ StoresRelated finalStore finalStore' := by
  let manifest := Core.Value.pair (.word descriptor) (.pair (scopeManifestValue fields) captureValue)
  have evaluated : Evaluates environment store
      (.pair (.word descriptor) (.pair (scopeManifest fields) (captures.weakenAt 0))) manifest store :=
    .pair .word (.pair (scopeManifest_evaluates fields environment store) captureEvaluation)
  have environments : EnvironmentsRelated (Renaming.insertion 0) environment (manifest :: environment) := by
    refine EnvironmentsRelated.intro (fun index bound => ?_) (fun index bound => ?_)
    · simpa [Renaming.insertion] using Nat.succ_lt_succ bound
    · simpa [Renaming.insertion] using ValuesRelated.refl environment[index]
  obtain ⟨result', finalStore', renamed, resultRelated, storesRelated⟩ :=
    bodyEvaluation.rename environments (StoresRelated.refl store)
  exact ⟨result', finalStore', .letE evaluated (by simpa only [Expr.rename_insertion] using renamed),
    resultRelated, storesRelated⟩

/-- Evaluation uses the actual extended environment. Higher-order results and
stores should be compared with `Core.Evaluates.rename` / `ValuesRelated`,
rather than an invalid exact-store weakening assertion. -/
theorem manifestBody_evaluates {environment : Core.Environment} {store finalStore : Store}
    {fields : List (Word × Core.Ty)} {captures body : Expr} {manifest result : Core.Value}
    (descriptor : Word)
    (pureManifest : Evaluates environment store
      (.pair (.word descriptor) (.pair (scopeManifest fields) (captures.weakenAt 0))) manifest store)
    (bodyEvaluation : Evaluates (manifest :: environment) store (body.weakenAt 0) result finalStore) :
    Evaluates environment store (manifestBody descriptor fields captures body) result finalStore :=
  .letE pureManifest bodyEvaluation

end Solcore.Frontend.SourceCoreLambdaTemplates
end
