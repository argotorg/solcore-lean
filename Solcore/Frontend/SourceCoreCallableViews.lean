import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceRuntimeHeapTyping

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
