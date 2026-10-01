import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreAllocationContexts
import Solcore.Frontend.SourceCoreAllocationLayouts
import Solcore.Frontend.SourceRuntimeHeapTyping

/-! Cached principal metadata for every direct lambda declaration, including
unused generalized lets whose native instance bundle is unit. Collection scans
original declarations, including for headers, without projecting open types or
requiring a read, emitted lambda, or successful runtime execution.

The canonical compiler source and the runtime principal source are retained
separately. The latter applies the full parent substitution and then rewrites
only inherited local requirement IDs. Captured locations, native closure code,
and dynamic instantiated-view ancestry remain separate authentication duties. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePrincipals
open SourceInference TypeSystem
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Parent := SourceCoreLocalEvidence.Prepared
abbrev Witness := SourceCoreLocalEvidence.Witness
abbrev Origin := SourceCoreAllocationContexts.Origin
abbrev Checked := SourceCoreCompatibleCatalog.Checked
private instance : BEq TypedBinder := instBEqOfDecidableEq

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

structure Declaration where
  binder : TypedBinder
  initializer : ExpressionId
  deriving Repr, DecidableEq

/-- This traversal includes all source nodes, even uninstantiated generic
bodies. No source type is lowered. -/
def declarations (source : TypedSource) : List Declaration :=
  source.nodes.flatMap fun
    | .statement node => match node.form with
      | .letDecl binder (some initializer) => [⟨binder, initializer⟩]
      | .forLoop initial _ post _ => (initial ++ post).filterMap fun
        | .letDecl binder (some initializer) => some ⟨binder, initializer⟩
        | _ => none
      | _ => []
    | _ => []

def directDeclarations (source : TypedSource) : List Declaration :=
  (declarations source).filter fun declaration =>
    SourceSpecialization.isDirectLambdaInitializer source declaration.initializer

private def original {plan : Plan} {parents : List Parent} : Origin plan parents → TypedSource
  | .root specialized _ => specialized.function.typedBody
  | .contextual parent _ => parent.instance.origin.source
private def witnesses {plan : Plan} {parents : List Parent} : Origin plan parents → List Witness
  | .root _ _ => []
  | .contextual parent _ => parent.witnesses

inductive Error where
  | metadata (error : SourceCoreAllocationContexts.Error)
  | plan (error : SourceCompilationPlan.Error)
  | invalidContext (owner : Key) (active : Substitution)
  | invalidDeclaration (binder : Resolved.LocalId)
  | conflictingPrincipal (owner : Key) (active : Substitution) (binder : Resolved.LocalId)
  | incompleteInventory
  deriving Repr

/-- Membership in the actual executable plan or sealed parent-receipt list,
plus the exact runtime evidence factory result, is established once per
context. The original source is never replaced by the contextual compiler
ledger. -/
structure Context (program : CheckedProgram) (plan : Plan) (parents : List Parent) where private mk ::
  allocation : SourceCoreAllocationContexts.Certified plan parents
  caller : SourceSpecialization.SpecializedFunction
  callerFound : SourceCompilationPlan.exactSpecialization plan allocation.context.owner = .ok caller
  originalExact : caller.function.typedBody = original allocation.origin
  compilerExact : allocation.context.source = (original allocation.origin).applySubstitution allocation.context.active
  evidence : SourceCompilationPlan.EvidenceEnvironment
  evidenceResolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok evidence

namespace Context
variable {program : CheckedProgram} {plan : Plan} {parents : List Parent}
def owner (context : Context program plan parents) : Key := context.allocation.context.owner
def active (context : Context program plan parents) : Substitution := context.allocation.context.active
def originalSource (context : Context program plan parents) : TypedSource := original context.allocation.origin
def compilerSource (context : Context program plan parents) : TypedSource := context.allocation.context.source
def inherited (context : Context program plan parents) : List Witness := witnesses context.allocation.origin
def source (context : Context program plan parents) : TypedSource :=
  SourceTypedRuntime.rewriteLocalRequirements context.inherited (context.originalSource.applySubstitution context.active)
theorem compiler_source (context : Context program plan parents) :
    context.compilerSource = context.originalSource.applySubstitution context.active := context.compilerExact
end Context

private def context {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (origin : Origin plan parents) : Except Error (Context program plan parents) := do
  let allocation ← (SourceCoreAllocationContexts.certify origin).mapError Error.metadata
  match callerFound : SourceCompilationPlan.exactSpecialization plan allocation.context.owner with
  | .error error => throw (.plan error)
  | .ok caller =>
    if originalExact : caller.function.typedBody = original allocation.origin then
      if compilerExact : allocation.context.source = (original allocation.origin).applySubstitution allocation.context.active then
        match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions with
        | .error error => throw (.plan error)
        | .ok available => pure ⟨allocation, caller, callerFound, originalExact, compilerExact, available, resolved⟩
      else throw (.invalidContext allocation.context.owner allocation.context.active)
    else throw (.invalidContext allocation.context.owner allocation.context.active)

structure Principal {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (context : Context program plan parents) where private mk ::
  declaration : Declaration
  declared : declaration ∈ directDeclarations context.originalSource
  originalBinderDeclared : declaration.binder ∈ SourceCoreDataPlaces.declaredBinders context.originalSource
  binder : TypedBinder
  binderExact : binder = declaration.binder.applySubstitution context.active
  canonicalDeclared : ⟨binder, declaration.initializer⟩ ∈ declarations context.compilerSource
  allocationMember : binder ∈ context.allocation.context.binders
  originalNode : ExpressionNode
  originalFound : context.originalSource.lookupExpression? declaration.initializer = some originalNode
  originalParameters : List TypedBinder
  originalResult : Ty
  originalBody : List StatementId
  originalShape : originalNode.form = .lambda originalParameters originalResult originalBody
  node : ExpressionNode
  found : context.source.lookupExpression? declaration.initializer = some node
  parameters : List TypedBinder
  resultType : Ty
  body : List StatementId
  shape : node.form = .lambda parameters resultType body

private def principal {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (context : Context program plan parents) (declaration : Declaration)
    (declared : declaration ∈ directDeclarations context.originalSource) : Except Error (Principal context) := do
  let binder := declaration.binder.applySubstitution context.active
  if originalDeclared : declaration.binder ∈ SourceCoreDataPlaces.declaredBinders context.originalSource then
    if canonical : (⟨binder, declaration.initializer⟩ : Declaration) ∈ declarations context.compilerSource then
      if allocated : binder ∈ context.allocation.context.binders then
        match originalFound : context.originalSource.lookupExpression? declaration.initializer with
        | none => throw (.invalidDeclaration binder.id)
        | some originalNode =>
          match originalShape : originalNode.form with
          | .lambda originalParameters originalResult originalBody =>
            match found : context.source.lookupExpression? declaration.initializer with
            | none => throw (.invalidDeclaration binder.id)
            | some node =>
              match shape : node.form with
              | .lambda parameters resultType body =>
                pure ⟨declaration, declared, originalDeclared, binder, rfl, canonical, allocated,
                  originalNode, originalFound, originalParameters, originalResult, originalBody, originalShape,
                  node, found, parameters, resultType, body, shape⟩
              | _ => throw (.invalidDeclaration binder.id)
          | _ => throw (.invalidDeclaration binder.id)
      else throw (.invalidDeclaration binder.id)
    else throw (.invalidDeclaration binder.id)
  else throw (.invalidDeclaration binder.id)

namespace Principal
variable {program : CheckedProgram} {plan : Plan} {parents : List Parent} {context : Context program plan parents}
theorem allocation_origin (principal : Principal context) :
    SourceCoreAllocationContexts.BinderOrigin context.compilerSource principal.binder :=
  context.allocation.binder_origin principal.allocationMember

theorem lambdaMetadata (principal : Principal context) :
    ∃ node, context.source.lookupExpression? principal.declaration.initializer = some node ∧
      node.form = .lambda principal.parameters principal.resultType principal.body :=
  ⟨principal.node, principal.found, principal.shape⟩
end Principal

/-- Exact retained data controls duplicate reuse. In particular full contexts,
requirement witnesses, raw metadata and evidence are compared, not native
function types or instance counts. -/
structure Metadata where
  owner : Key
  active : Substitution
  originalSource : TypedSource
  compilerSource : TypedSource
  source : TypedSource
  inherited : List Witness
  evidence : SourceCompilationPlan.EvidenceEnvironment
  originalDeclaration : Declaration
  binder : TypedBinder
  originalNode : ExpressionNode
  node : ExpressionNode
  deriving DecidableEq

structure Entry (program : CheckedProgram) (plan : Plan) (parents : List Parent) where private mk ::
  context : Context program plan parents
  principal : Principal context

namespace Entry
variable {program : CheckedProgram} {plan : Plan} {parents : List Parent}
def metadata (entry : Entry program plan parents) : Metadata := {
  owner := entry.context.owner, active := entry.context.active
  originalSource := entry.context.originalSource, compilerSource := entry.context.compilerSource
  source := entry.context.source, inherited := entry.context.inherited, evidence := entry.context.evidence
  originalDeclaration := entry.principal.declaration, binder := entry.principal.binder
  originalNode := entry.principal.originalNode, node := entry.principal.node
}
def key (entry : Entry program plan parents) : Key × Substitution × Resolved.LocalId :=
  (entry.context.owner, entry.context.active, entry.principal.binder.id)

def matchesLayout (entry : Entry program plan parents) (key : SourceCoreAllocationLayouts.Key) : Prop :=
  key.owner = entry.context.owner ∧ key.active = entry.context.active ∧ key.binder = entry.principal.binder
instance (entry : Entry program plan parents) (key : SourceCoreAllocationLayouts.Key) : Decidable (entry.matchesLayout key) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem layout_binder_origin (entry : Entry program plan parents) {key : SourceCoreAllocationLayouts.Key}
    (matching : entry.matchesLayout key) : SourceCoreAllocationContexts.BinderOrigin entry.context.compilerSource key.binder := by
  rw [matching.2.2]
  exact entry.principal.allocation_origin
end Entry

structure Collected (program : CheckedProgram) (plan : Plan) (parents : List Parent) where private mk ::
  context : Context program plan parents
  principals : List (Principal context)
  complete : ∀ declaration ∈ directDeclarations context.originalSource,
    declaration ∈ principals.map (·.declaration)

private def collect {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (origin : Origin plan parents) : Except Error (Collected program plan parents) := do
  let context ← context origin
  let principals ← (directDeclarations context.originalSource).attach.mapM fun declaration =>
    principal context declaration.val declaration.property
  if complete : ∀ declaration ∈ directDeclarations context.originalSource,
      declaration ∈ principals.map (·.declaration) then
    pure ⟨context, principals, complete⟩
  else throw .incompleteInventory

/-- Equal keys may reuse only identical complete metadata. -/
def insert {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (rows : List (Entry program plan parents)) (candidate : Entry program plan parents) : Except Error (List (Entry program plan parents)) :=
  match rows.find? (fun row => decide (row.key = candidate.key)) with
  | none => .ok (rows ++ [candidate])
  | some existing =>
    if existing.metadata = candidate.metadata then .ok rows
    else .error (.conflictingPrincipal candidate.context.owner candidate.context.active candidate.principal.binder.id)

theorem insert_reuses {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    {rows : List (Entry program plan parents)} {candidate existing : Entry program plan parents}
    (found : rows.find? (fun row => decide (row.key = candidate.key)) = some existing)
    (equal : existing.metadata = candidate.metadata) : insert rows candidate = .ok rows := by
  simp only [insert, found, if_pos equal]

theorem insert_rejects_conflict {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    {rows : List (Entry program plan parents)} {candidate existing : Entry program plan parents}
    (found : rows.find? (fun row => decide (row.key = candidate.key)) = some existing)
    (different : existing.metadata ≠ candidate.metadata) :
    insert rows candidate = .error (.conflictingPrincipal candidate.context.owner candidate.context.active candidate.principal.binder.id) := by
  simp only [insert, found, if_neg different]

structure ContextKey where
  owner : Key
  active : Substitution
  originalSource : TypedSource
  inherited : List Witness
  deriving DecidableEq

def originKey {plan : Plan} {parents : List Parent} (origin : Origin plan parents) : ContextKey :=
  ⟨origin.owner, origin.active, original origin, witnesses origin⟩

def origins (plan : Plan) (parents : List Parent) : List (Origin plan parents) :=
  plan.specializations.attach.map (fun item => .root item.val item.property) ++
  parents.attach.map (fun item => .contextual item.val item.property)

structure Table (program : CheckedProgram) (plan : Plan) (parents : List Parent) where private mk ::
  collected : List (Collected program plan parents)
  contextsComplete : ∀ origin ∈ origins plan parents,
    originKey origin ∈ collected.map (fun row => originKey row.context.allocation.origin)
  entries : List (Entry program plan parents)
  unique : (entries.map (·.key)).Nodup
  covered : ∀ row ∈ collected, ∀ principal ∈ row.principals,
    (Entry.metadata ⟨row.context, principal⟩) ∈ entries.map (·.metadata)

private def fromPrepared (program : CheckedProgram) (plan : Plan) (parents : List Parent) :
    Except Error (Table program plan parents) := do
  let collected ← (origins plan parents).mapM collect
  let candidates := collected.flatMap fun row => row.principals.map fun principal => (⟨row.context, principal⟩ : Entry program plan parents)
  let entries ← candidates.foldlM insert []
  if complete : ∀ origin ∈ origins plan parents,
      originKey origin ∈ collected.map (fun row => originKey row.context.allocation.origin) then
    if unique : (entries.map (·.key)).Nodup then
      if covered : ∀ row ∈ collected, ∀ principal ∈ row.principals,
          (Entry.metadata ⟨row.context, principal⟩) ∈ entries.map (·.metadata) then
        pure ⟨collected, complete, entries, unique, covered⟩
      else throw .incompleteInventory
    else throw .incompleteInventory
  else throw .incompleteInventory

/-- The compatible artifact owns the executable plan and authenticated parent
receipts. Runtime evidence is resolved during this preparation only. -/
def prepare {checked : Checked} (base : SourceCoreCompatibleFunctions.Prepared checked) :
    Except Error (Table base.sourceProgram base.plan base.contexts) :=
  fromPrepared base.sourceProgram base.plan base.contexts

namespace Table
variable {program : CheckedProgram} {plan : Plan} {parents : List Parent}
def find? (table : Table program plan parents) (owner : Key) (active : Substitution)
    (binder : Resolved.LocalId) : Option (Entry program plan parents) :=
  table.entries.find? (fun entry => decide (entry.key = (owner, active, binder)))
def forLayout? (table : Table program plan parents) (key : SourceCoreAllocationLayouts.Key) : Option (Entry program plan parents) :=
  table.entries.find? (fun entry => decide (entry.matchesLayout key))

theorem direct_declaration_retained (table : Table program plan parents) {row : Collected program plan parents}
    (member : row ∈ table.collected) {declaration : Declaration}
    (declared : declaration ∈ directDeclarations row.context.originalSource) :
    ∃ principal ∈ row.principals, principal.declaration = declaration ∧
      (Entry.metadata ⟨row.context, principal⟩) ∈ table.entries.map (·.metadata) := by
  obtain ⟨principal, belongs, equal⟩ := List.mem_map.mp (row.complete declaration declared)
  exact ⟨principal, belongs, equal, table.covered row member principal belongs⟩

/-- Every root and every authenticated parent context retains each direct
lambda declaration, even when there are no reads or native instances. -/
theorem origin_declaration_retained (table : Table program plan parents)
    (origin : Origin plan parents) (member : origin ∈ origins plan parents)
    {declaration : Declaration} (declared : declaration ∈ directDeclarations (originKey origin).originalSource) :
    ∃ entry ∈ table.entries,
      entry.metadata.owner = origin.owner ∧ entry.metadata.active = origin.active ∧
      entry.metadata.originalSource = (originKey origin).originalSource ∧
      entry.metadata.inherited = (originKey origin).inherited ∧
      entry.metadata.originalDeclaration = declaration := by
  obtain ⟨row, rowMember, keyEqual⟩ := List.mem_map.mp (table.contextsComplete origin member)
  have sourceEqual := congrArg ContextKey.originalSource keyEqual
  have inheritedEqual := congrArg ContextKey.inherited keyEqual
  have ownerEqual := congrArg ContextKey.owner keyEqual
  have activeEqual := congrArg ContextKey.active keyEqual
  have declarationMember : declaration ∈ directDeclarations row.context.originalSource := by
    change declaration ∈ directDeclarations (original row.context.allocation.origin)
    rw [show original row.context.allocation.origin = (originKey origin).originalSource from sourceEqual]
    exact declared
  obtain ⟨principal, _, declarationEqual, retained⟩ := table.direct_declaration_retained rowMember declarationMember
  obtain ⟨entry, entryMember, metadataEqual⟩ := List.mem_map.mp retained
  refine ⟨entry, entryMember, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg Metadata.owner metadataEqual).trans (row.context.allocation.ownerExact.trans ownerEqual)
  · exact (congrArg Metadata.active metadataEqual).trans (row.context.allocation.activeExact.trans activeEqual)
  · exact (congrArg Metadata.originalSource metadataEqual).trans sourceEqual
  · exact (congrArg Metadata.inherited metadataEqual).trans inheritedEqual
  · exact (congrArg Metadata.originalDeclaration metadataEqual).trans declarationEqual

theorem forLayout?_authenticates (table : Table program plan parents) {key : SourceCoreAllocationLayouts.Key}
    {entry : Entry program plan parents} (found : table.forLayout? key = some entry) :
    entry ∈ table.entries ∧ entry.matchesLayout key := by
  have tested := List.find?_some found
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true tested⟩
end Table
end Solcore.Frontend.SourceCoreCallablePrincipals
