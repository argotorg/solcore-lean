import Solcore.Frontend.SourceCompilationPlan
import Solcore.Frontend.SourceCore.Lowering
import Solcore.Frontend.SourceCore.Data
import Solcore.Core.Internal.ConventionLaws
import Solcore.Core.LanguageResult
import Solcore.Frontend.SourceCore.Internal.FaultSites
import Solcore.Frontend.SourceCore.DataExpressions
import Solcore.Frontend.SourceCore.Internal.Entries
import Solcore.Frontend.SourceCore.DataPlaces

/-!
# Matches, evidence, contracts and general functions

Checked data patterns, authenticated evidence, finite local polymorphism, staging contracts, and
closed function instances over catalog data. Main declarations:
`SourceCoreGeneralFunctions.Function`, `SourceCoreGeneralFunctions.CallableContext`,
`SourceCoreLocalPolymorphism.Binding`, `SourceCoreStageContracts.Sidecar`.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreLocalPolymorphism
/-! Finite local-lambda instances use ordinary product bundles and optional
cells. The catalog retains the complete cumulative substitution, including
outer local contexts which may distinguish equal final function types.

This module supplies representation and metadata checks. Its candidate compiler
callback must authenticate local evidence and compile each lambda body; no
source evaluator is invoked here. Canonical executable-plan authentication and
the assembled Core checker remain responsibilities of the enclosing compiler.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreLocalPolymorphism

open SourceInference TypeSystem
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev Scope := SourceCoreBasic.Scope

namespace ProductBundle

inductive Pointwise {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Pointwise relation [] []
  | cons {head : α} {headType : β} {rest : List α} {restTypes : List β}
      (headTyped : relation head headType) (tailTyped : Pointwise relation rest restTypes) :
      Pointwise relation (head :: rest) (headType :: restTypes)

/-- Unit for no instances; a singleton is unchanged; larger bundles associate
to the right, matching source argument packing. -/
def type : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (ProductBundle.type rest)

def expression : List Core.Expr → Core.Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (expression rest)

def value : List Core.Value → Core.Value
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (ProductBundle.value rest)

/-- Bounds are checked statically. Empty bundles have no readable candidate. -/
def project? : List Core.Ty → Nat → Core.Expr → Option Core.Expr
  | [], _, _ => none
  | [_], 0, bundle => some bundle
  | [_], _ + 1, _ => none
  | _ :: _ :: _, 0, bundle => some (.first bundle)
  | _ :: next :: rest, index + 1, bundle =>
      project? (next :: rest) index (.second bundle)

theorem project?_exists {types : List Core.Ty} {index : Nat} {resultType : Core.Ty}
    (found : types[index]? = some resultType) (bundle : Core.Expr) :
    ∃ projected, project? types index bundle = some projected := by
  induction types generalizing index bundle with
  | nil => simp at found
  | cons head rest ih =>
      cases rest with
      | nil =>
          cases index with
          | zero => exact ⟨bundle, rfl⟩
          | succ index => simp at found
      | cons next tail =>
          cases index with
          | zero => exact ⟨.first bundle, rfl⟩
          | succ index => exact ih (by simpa using found) (.second bundle)

theorem type_wellFormed {definitions : Core.DataEnvironment} {types : List Core.Ty}
    (typed : ∀ type ∈ types, Core.Ty.WellFormed definitions type) :
    Core.Ty.WellFormed definitions (type types) := by
  induction types with
  | nil => exact .unit
  | cons head rest ih =>
      cases rest with
      | nil => exact typed head (by simp)
      | cons next tail =>
          exact .product (typed head (by simp)) (ih (by
            intro item member
            exact typed item (List.mem_cons_of_mem head member)))

theorem expression_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {expressions : List Core.Expr} {types : List Core.Ty}
    (typed : Pointwise (fun expression type => Core.HasType context expression type definitions) expressions types) :
    Core.HasType context (expression expressions) (type types) definitions := by
  induction typed with
  | nil => exact .unit
  | @cons head headType rest restTypes headTyped restTyped ih =>
      cases restTyped with
      | nil => exact headTyped
      | cons nextTyped tailTyped => exact .pair headTyped ih

theorem project_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {types : List Core.Ty} {index : Nat} {bundle projected : Core.Expr} {resultType : Core.Ty}
    (found : types[index]? = some resultType)
    (selected : project? types index bundle = some projected)
    (typed : Core.HasType context bundle (type types) definitions) :
    Core.HasType context projected resultType definitions := by
  induction types generalizing index bundle projected with
  | nil => simp at found
  | cons head rest ih =>
      cases rest with
      | nil =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              simp only [project?, Option.some.injEq] at selected
              subst resultType
              subst projected
              exact typed
          | succ index => simp at found
      | cons next tail =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              simp only [project?, Option.some.injEq] at selected
              subst resultType
              subst projected
              exact .first typed
          | succ index =>
              exact ih (by simpa using found) selected (.second typed)

theorem expression_evaluates {environment : Core.Environment} {store : Core.Store}
    {expressions : List Core.Expr} {values : List Core.Value}
    (evaluations : Pointwise (fun expression value => Core.Evaluates environment store expression value store)
      expressions values) :
    Core.Evaluates environment store (expression expressions) (value values) store := by
  induction evaluations with
  | nil => exact .unit
  | @cons head headValue rest restValues headEvaluation restEvaluations ih =>
      cases restEvaluations with
      | nil => exact headEvaluation
      | cons nextEvaluation tailEvaluations => exact .pair headEvaluation ih

end ProductBundle

inductive Error where
  | discovery (error : SourceSpecializationWorklist.Error)
  | projection (error : SourceCoreDataCatalog.Error)
  | metadata (error : SourceCoreBasic.Error)
  | missingCaller (caller : Key)
  | missingBinding (caller : Key) (binder : Resolved.LocalId)
  | duplicateBindings (caller : Key) (binder : Resolved.LocalId) (count : Nat)
  | bindingMetadataMismatch (binder : Resolved.LocalId)
  | initializerMetadataMismatch (id : ExpressionId)
  | openInstance (binder : Resolved.LocalId) (type : Ty)
  | missingInstance (binder : Resolved.LocalId) (substitution : Substitution)
  | duplicateInstances (binder : Resolved.LocalId) (substitution : Substitution) (count : Nat)
  | invalidProjection (index : Nat)
  | missingCallableContract (caller : Key) (initializer : ExpressionId) (context : Substitution)
  deriving Repr

structure Instance where
  origin : SourceCompilationPlan.LocalLambdaCatalogEntry
  parameterType : Core.Ty
  resultType : Core.Ty
  contractId : Option Core.Word := none
  deriving Repr

def Instance.type (candidate : Instance) : Core.Ty :=
  match candidate.contractId with
  | none => Core.TaggedFunction.functionType candidate.parameterType candidate.resultType
  | some _ => Core.CallableContract.functionType candidate.parameterType candidate.resultType

/-- Apply the cumulative context to the full table. Immutable original
occurrence metadata remains in `origin.source` for later scheme selection;
nested generalized binders retain their own quantifiers. -/
def Instance.source (candidate : Instance) : TypedSource :=
  candidate.origin.source.applySubstitution candidate.origin.substitution

/-- The body is compiled under the packed parameter followed by the original
lexical reference environment. Every instance keeps anonymous source identity. -/
def Instance.closure (candidate : Instance) (body : Core.Expr) : Core.Expr :=
  let tagged := Core.TaggedFunction.anonymous
    (.lambda candidate.parameterType (Core.LanguageResult.resultType candidate.resultType) body)
  match candidate.contractId with
  | none => tagged
  | some id => Core.CallableContract.wrap id tagged

theorem Instance.closure_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {candidate : Instance} {body : Core.Expr}
    (parameterWF : Core.Ty.WellFormed definitions candidate.parameterType)
    (resultWF : Core.Ty.WellFormed definitions candidate.resultType)
    (bodyTyped : Core.HasType (candidate.parameterType :: context) body
      (Core.LanguageResult.resultType candidate.resultType) definitions) :
    Core.HasType context (candidate.closure body) candidate.type definitions := by
  have tagged := Core.TaggedFunction.anonymous_hasType
    (Core.HasType.lambda parameterWF (Core.LanguageResult.resultType_wellFormed resultWF) bodyTyped)
  cases selected : candidate.contractId with
  | none => simpa [Instance.closure, Instance.type, selected] using tagged
  | some id => simpa [Instance.closure, Instance.type, selected] using Core.CallableContract.wrap_hasType id tagged

structure Binding where
  caller : Key
  source : TypedSource
  binder : TypedBinder
  initializer : ExpressionId
  instances : List Instance
  deriving Repr

structure Catalog where
  bindings : List Binding
  deriving Repr

/-- Attach artifact-owned descriptors after inventorying all original and
contextual origins. Every instance in the bundle retains its exact context. -/
def Catalog.withCallableContracts (catalog : Catalog)
    (idAt : Key → ExpressionId → Substitution → Option Core.Word) : Except Error Catalog := do
  let bindings ← catalog.bindings.mapM fun binding => do
    let instances ← binding.instances.mapM fun candidate => do
      let contract ← match idAt candidate.origin.caller candidate.origin.initializer candidate.origin.substitution with
        | some contract => pure contract
        | none => throw (.missingCallableContract candidate.origin.caller
            candidate.origin.initializer candidate.origin.substitution)
      pure { candidate with contractId := some contract }
    pure { binding with instances }
  pure { bindings }

/-- Candidate contexts must agree with every active outer-context metavariable.
Equal function types alone never choose a nested candidate. -/
def agreesOnContext (candidate active : Substitution) : Bool :=
  active.domain.all fun metavariable => decide (candidate.apply (.variable metavariable) = active.apply (.variable metavariable))

theorem agreesOnContext_spec {candidate active : Substitution}
    (accepted : agreesOnContext candidate active = true) (metavariable : TypeVarId)
    (member : metavariable ∈ active.domain) :
    candidate.apply (.variable metavariable) = active.apply (.variable metavariable) :=
  of_decide_eq_true (List.all_eq_true.mp accepted metavariable member)

def Binding.atContext (binding : Binding) (active : Substitution) : List Instance :=
  binding.instances.filter fun candidate => agreesOnContext candidate.origin.substitution active

def Binding.bundleType (binding : Binding) (active : Substitution) : Core.Ty :=
  ProductBundle.type ((binding.atContext active).map (·.type))

private def prepareInstance (projectType : Ty → Except Error Core.Ty) (entry : SourceCompilationPlan.LocalLambdaCatalogEntry) :
    Except Error Instance := do
  let source := entry.source.applySubstitution entry.substitution
  if source.owner ≠ entry.caller.declaration then
    throw (.metadata (.ownerMismatch entry.caller.declaration source.owner))
  if entry.binder.id.owner ≠ source.owner then
    throw (.metadata (.ownerMismatch source.owner entry.binder.id.owner))
  if entry.initializer.occurrence.owner ≠ source.owner then
    throw (.metadata (.ownerMismatch source.owner entry.initializer.occurrence.owner))
  let expected := entry.substitution.apply entry.binder.scheme.body
  unless expected.freeVariables.isEmpty do throw (.openInstance entry.binder.id expected)
  let (parameter, result) ← match expected with
    | .function parameter result => pure (parameter, result)
    | _ => throw (.initializerMetadataMismatch entry.initializer)
  let node ← match source.lookupExpression? entry.initializer with
    | some node => pure node
    | none => throw (.metadata (.missingExpression entry.initializer))
  let (parameters, returnType) ← match node.form with
    | .lambda parameters returnType _ => pure (parameters, returnType)
    | _ => throw (.initializerMetadataMismatch entry.initializer)
  if node.type ≠ expected || Ty.productMany (parameters.map (·.scheme.body)) ≠ parameter || returnType ≠ result then
    throw (.initializerMetadataMismatch entry.initializer)
  let parameterType ← projectType parameter
  let resultType ← projectType result
  pure { origin := entry, parameterType, resultType }

/-- Discover finite instances through the existing worklist. Unused direct
generalized lambdas are retained as empty bundles. This does not broaden the
worklist's supported generalized initializer forms or evidence policy. -/
def prepareWithProjection (projectType : Ty → Except Error Core.Ty) (plan : SourceSpecializationWorklist.Plan) (contextFuel : Option Nat := none) :
    Except Error Catalog := do
  let entries ← (SourceCompilationPlan.localLambdaCatalog plan contextFuel).mapError Error.discovery
  let instances ← entries.mapM (prepareInstance projectType)
  let mut bindings := []
  for specialized in plan.specializations do
    let source := specialized.function.typedBody
    if source.owner ≠ specialized.key.declaration then
      throw (.metadata (.ownerMismatch specialized.key.declaration source.owner))
    for node in source.nodes do
      match node with
      | .statement { form := .letDecl binder (some initializer), .. } =>
          unless binder.scheme.quantified.isEmpty do
            if binder.id.owner ≠ source.owner then throw (.metadata (.ownerMismatch source.owner binder.id.owner))
            if SourceSpecialization.isDirectLambdaInitializer source initializer then
              bindings := bindings ++ [{
                caller := specialized.key
                source
                binder
                initializer
                instances := instances.filter fun candidate =>
                  decide (candidate.origin.caller = specialized.key ∧ candidate.origin.binder.id = binder.id)
              }]
      | _ => pure ()
  pure ⟨bindings⟩

/-- The strict profile retains its existing metadata diagnostics and projected
representation. Compatible profiles use their own checked projection through
`prepareWithProjection`, sharing the same original instance discovery. -/
def prepare (checked : Checked) (plan : SourceSpecializationWorklist.Plan) (contextFuel : Option Nat := none) :
    Except Error Catalog :=
  prepareWithProjection (fun type => do
    let projected ← (checked.project type).mapError Error.projection
    pure projected.type) plan contextFuel

def Catalog.binding (catalog : Catalog) (caller : Key) (binder : Resolved.LocalId) : Except Error Binding :=
  match catalog.bindings.filter fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder) with
  | [] => .error (.missingBinding caller binder)
  | [entry] => .ok entry
  | entries => .error (.duplicateBindings caller binder entries.length)

/-- Generalized binders occupy one ordinary optional cell whose payload is the
finite contextual bundle. Monomorphic binders belong to the enclosing policy. -/
def lowerBinder (catalog : Catalog) (caller : Key) (active : Substitution) (source : TypedSource)
    (scope : Scope) (binder : TypedBinder) : Except Error Core.Ty := do
  if source.owner ≠ caller.declaration then throw (.metadata (.ownerMismatch caller.declaration source.owner))
  if binder.id.owner ≠ source.owner then throw (.metadata (.ownerMismatch source.owner binder.id.owner))
  if binder.comptime then throw (.metadata (.comptimeBinding binder.id))
  if scope.any (fun entry => decide (entry.1 = binder.id)) then throw (.metadata (.duplicateBinding binder.id))
  let binding ← catalog.binding caller binder.id
  if binding.binder.applySubstitution active ≠ binder then throw (.bindingMetadataMismatch binder.id)
  pure (binding.bundleType active)

/-- The callback compiles each raw tagged closure under the same lexical
reference environment. The bundle constructor itself allocates no cells. -/
def lowerInitializer (binding : Binding) (active : Substitution)
    (compileInstance : Instance → Except Error Core.Expr) : Except Error SourceCoreBasic.LoweredExpr := do
  let instances := binding.atContext active
  let closures ← instances.mapM compileInstance
  pure ⟨binding.bundleType active, Core.LanguageResult.success (ProductBundle.expression closures)⟩

def read (bundleType instanceType : Core.Ty) (reference projection : Core.Expr) (reason : Core.Word) : Core.Expr :=
  Core.LanguageResult.bind instanceType (Core.OptionalCell.read bundleType reference reason)
    (Core.LanguageResult.success projection)

theorem read_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {bundleType instanceType : Core.Ty} {reference projection : Core.Expr} (reason : Core.Word)
    (bundleWF : Core.Ty.WellFormed definitions bundleType)
    (instanceWF : Core.Ty.WellFormed definitions instanceType)
    (referenceTyped : Core.HasType context reference (Core.OptionalCell.referenceType bundleType) definitions)
    (projectionTyped : Core.HasType (bundleType :: context) projection instanceType definitions) :
    Core.HasType context (read bundleType instanceType reference projection reason)
      (Core.LanguageResult.resultType instanceType) definitions :=
  Core.LanguageResult.bind_hasType instanceWF
    (Core.OptionalCell.read_hasType reason bundleWF referenceTyped)
    (Core.LanguageResult.success_hasType projectionTyped)

theorem read_failure {environment : Core.Environment} {before after : Core.Store}
    {bundleType instanceType : Core.Ty} {reference projection : Core.Expr} {reason failure : Core.Word}
    (evaluation : Core.Evaluates environment before (Core.OptionalCell.read bundleType reference reason)
      (.inLeft bundleType (.word failure)) after) :
    Core.Evaluates environment before (read bundleType instanceType reference projection reason)
      (.inLeft instanceType (.word failure)) after :=
  Core.LanguageResult.bind_failure instanceType evaluation

theorem read_success {environment : Core.Environment} {before middle after : Core.Store}
    {bundleType instanceType : Core.Ty} {reference projection : Core.Expr} {reason : Core.Word}
    {bundle candidate : Core.Value}
    (evaluation : Core.Evaluates environment before (Core.OptionalCell.read bundleType reference reason)
      (.inRight .word bundle) middle)
    (projectionEvaluation : Core.Evaluates (bundle :: environment) middle projection candidate after) :
    Core.Evaluates environment before (read bundleType instanceType reference projection reason)
      (.inRight .word candidate) after :=
  Core.LanguageResult.bind_success instanceType evaluation
    (Core.LanguageResult.success_evaluates projectionEvaluation)

/-- Select by the exact cumulative scheme instance in the active context.
The original table supplies the pre-context raw type; the occurrence's current
raw and authoritative types must agree with the contextual selection. -/
def lowerRead (catalog : Catalog) (caller : Key) (active : Substitution) (source : TypedSource)
    (scope : Scope) (id : ExpressionId) (reason : Core.Word) : Except Error SourceCoreBasic.LoweredExpr := do
  if source.owner ≠ caller.declaration then throw (.metadata (.ownerMismatch caller.declaration source.owner))
  if id.occurrence.owner ≠ source.owner then throw (.metadata (.ownerMismatch source.owner id.occurrence.owner))
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (.metadata (.missingExpression id))
  let binder ← match node.form with
    | .reference _ (.local binder) => pure binder
    | _ => throw (.metadata (.unsupportedExpression id node.form))
  if binder.owner ≠ source.owner then throw (.metadata (.ownerMismatch source.owner binder.owner))
  let binding ← catalog.binding caller binder
  let original ← match binding.source.lookupExpression? id with
    | some node => pure node
    | none => throw (.metadata (.missingExpression id))
  match original.form with
  | .reference _ (.local originalBinder) =>
      if originalBinder ≠ binder || active.apply original.rawType ≠ node.rawType then
        throw (.bindingMetadataMismatch binder)
  | _ => throw (.bindingMetadataMismatch binder)
  let actual := active.apply original.rawType
  let child ← match SourceSpecialization.matchClosedSchemeInstance? (Scheme.apply active binding.binder.scheme) actual with
    | some child => pure child
    | none => throw (.bindingMetadataMismatch binder)
  let cumulative := child.compose active
  let candidates := (binding.atContext active).zipIdx.filter fun entry =>
    decide (entry.1.origin.substitution = cumulative)
  let (candidate, instanceIndex) ← match candidates with
    | [] => throw (.missingInstance binder cumulative)
    | [candidate] => pure candidate
    | candidates => throw (.duplicateInstances binder cumulative candidates.length)
  if node.type ≠ candidate.origin.substitution.apply binding.binder.scheme.body then
    throw (.bindingMetadataMismatch binder)
  let (index, payloadType) ← match SourceCoreLocalCell.lookup? scope binder with
    | some slot => pure slot
    | none => throw (.metadata (.missingBinding binder))
  (SourceCoreBasic.ensureType (.occurrence id.occurrence) (binding.bundleType active) payloadType).mapError Error.metadata
  let projection ← match ProductBundle.project? ((binding.atContext active).map (·.type)) instanceIndex (.var 0) with
    | some projection => pure projection
    | none => throw (.invalidProjection instanceIndex)
  pure ⟨candidate.type, read payloadType candidate.type (.var index) projection reason⟩

end Solcore.Frontend.SourceCoreLocalPolymorphism
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreLocalEvidence
/-! Authenticated qualified-local evidence for finite lambda instances.
Original requirement identities remain on body occurrences. Closed witnesses
replace their template assumption rows in the compiler's contextual ledger;
unbound obligations are retained. This module prepares compiler metadata only;
the enclosing compiler authenticates the executable plan before calling it.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreLocalEvidence

open SourceInference TypeSystem
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Instance := SourceCoreLocalPolymorphism.Instance
abbrev Binding := SourceCoreLocalPolymorphism.Binding
abbrev Witness := SourceTypedRuntime.LocalRequirementWitness

mutual
  def applyEvidence (substitution : Substitution) :
      TypedTraitResolution.Evidence → TypedTraitResolution.Evidence
    | .byImpl goal implementation premises =>
        .byImpl (TypedTraitResolution.applySubstitution substitution goal) implementation
          (applyEvidences substitution premises)
  def applyEvidences (substitution : Substitution) :
      List TypedTraitResolution.Evidence → List TypedTraitResolution.Evidence
    | [] => []
    | evidence :: rest => applyEvidence substitution evidence :: applyEvidences substitution rest
end

def applyPredicateEvidence (substitution : Substitution) : PredicateEvidence → PredicateEvidence
  | .assumption predicate => .assumption (TypedTraitResolution.applySubstitution substitution predicate)
  | .implementation evidence => .implementation (applyEvidence substitution evidence)

def applySolvedRequirement (substitution : Substitution) (row : SolvedRequirement) : SolvedRequirement :=
  { row with
    predicate := TypedTraitResolution.applySubstitution substitution row.predicate
    evidence := applyPredicateEvidence substitution row.evidence
  }

theorem applyPredicateEvidence_goal (substitution : Substitution) (evidence : PredicateEvidence) :
    (applyPredicateEvidence substitution evidence).goal =
      TypedTraitResolution.applySubstitution substitution evidence.goal := by
  cases evidence with
  | assumption goal => rfl
  | implementation evidence => cases evidence; rfl

theorem applySolvedRequirement_alignment (substitution : Substitution) (row : SolvedRequirement)
    (aligned : row.evidence.goal = row.predicate) :
    (applySolvedRequirement substitution row).evidence.goal =
      (applySolvedRequirement substitution row).predicate := by
  simpa [applySolvedRequirement, applyPredicateEvidence_goal] using
    congrArg (TypedTraitResolution.applySubstitution substitution) aligned

def rewriteRow (witnesses : List Witness) (row : SolvedRequirement) : SolvedRequirement :=
  match witnesses.find? (fun witness => decide (witness.templateRequirement = row.id)) with
  | none => row
  | some witness => { row with evidence := .implementation witness.evidence }

def rewriteLedger (substitution : Substitution) (witnesses : List Witness)
    (rows : List SolvedRequirement) : List SolvedRequirement :=
  rows.map fun row => rewriteRow witnesses (applySolvedRequirement substitution row)

@[simp] theorem rewriteRow_id (witnesses : List Witness) (row : SolvedRequirement) :
    (rewriteRow witnesses row).id = row.id := by
  unfold rewriteRow
  split <;> rfl

theorem rewriteLedger_ids (substitution : Substitution) (witnesses : List Witness)
    (rows : List SolvedRequirement) :
    (rewriteLedger substitution witnesses rows).map (·.id) = rows.map (·.id) := by
  simp [rewriteLedger, List.map_map, Function.comp_def, applySolvedRequirement]

inductive Error where
  | plan (error : SourceCompilationPlan.Error)
  | discovery (error : SourceSpecializationWorklist.Error)
  | originMismatch (key : Key)
  | bindingMismatch (binder : Resolved.LocalId)
  | instanceMismatch (binder : Resolved.LocalId)
  | parentMismatch (key : Key)
  | missingReference (binder : Resolved.LocalId)
  | missingExpression (id : ExpressionId)
  | duplicateTemplate (requirement : RequirementId)
  | templateRowMismatch (requirement : RequirementId)
  | occurrenceMismatch (id : ExpressionId)
  deriving Repr

structure Prepared where private mk ::
  private origin : Instance
  caller : SourceSpecialization.SpecializedFunction
  witnesses : List Witness

def Prepared.substitution (prepared : Prepared) : Substitution := prepared.origin.origin.substitution
def Prepared.source (prepared : Prepared) : TypedSource := prepared.caller.function.typedBody

/-- Retain the exact authenticated lambda instance for later metadata exports. -/
def Prepared.instance (prepared : Prepared) : Instance := prepared.origin

structure Reference where private mk ::
  id : ExpressionId
  cumulative : Substitution
  witnesses : List Witness
  original : ExpressionNode
  owned : List RequirementId

/-- Only authenticated ordinary scheme-instance requirements are removed.
Coercion-owned requirements and the complete coercion path remain. -/
def Reference.normalized (reference : Reference) : ExpressionNode :=
  { reference.original with
    requirements := reference.original.requirements.filter
      (fun requirement => !reference.owned.contains requirement)
  }

@[simp] theorem Reference.normalized_coercions (reference : Reference) :
    reference.normalized.coercions = reference.original.coercions := rfl

@[simp] theorem Reference.normalized_type (reference : Reference) :
    reference.normalized.type = reference.original.type := rfl

@[simp] theorem Reference.normalized_form (reference : Reference) :
    reference.normalized.form = reference.original.form := rfl

def exactCaller (plan : SourceSpecializationWorklist.Plan) (binding : Binding) :
    Except Error SourceSpecialization.SpecializedFunction := do
  let caller ← (SourceCompilationPlan.exactSpecialization plan binding.caller).mapError Error.plan
  if caller.function.typedBody ≠ binding.source then throw (.originMismatch binding.caller)
  let retained := binding.source.nodes.any fun
    | .statement { form := .letDecl binder (some initializer), .. } =>
        decide (binder = binding.binder ∧ initializer = binding.initializer)
    | _ => false
  unless retained do throw (.bindingMismatch binding.binder.id)
  pure caller

private def activeContext (caller : SourceSpecialization.SpecializedFunction) (parent : Option Prepared) :
    Except Error (Substitution × List Witness) := do
  match parent with
  | none => pure ([], [])
  | some parent =>
      if parent.caller.key ≠ caller.key || parent.origin.origin.source ≠ caller.function.typedBody then
        throw (.parentMismatch caller.key)
      pure (parent.substitution, parent.witnesses)

private def validateWitnesses (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (substitution : Substitution) (witnesses : List Witness) : Except Error Unit := do
  let mut seen := []
  for witness in witnesses do
    if seen.contains witness.templateRequirement then throw (.duplicateTemplate witness.templateRequirement)
    seen := witness.templateRequirement :: seen
    let row ← match caller.function.solvedRequirements.filter (fun row => decide (row.id = witness.templateRequirement)) with
      | [row] => pure (applySolvedRequirement substitution row)
      | _ => throw (.templateRowMismatch witness.templateRequirement)
    if row.predicate ≠ witness.predicate || SourceCompilationPlan.runtimeEvidenceGoal witness.evidence ≠ witness.predicate then
      throw (.templateRowMismatch witness.templateRequirement)
    match row.evidence with
    | .assumption predicate =>
        if predicate ≠ witness.predicate then throw (.templateRowMismatch witness.templateRequirement)
    | .implementation _ => throw (.templateRowMismatch witness.templateRequirement)
    (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures caller.key
      [witness.predicate] [witness.evidence]).mapError Error.plan

def contextualCaller (caller : SourceSpecialization.SpecializedFunction)
    (substitution : Substitution) (witnesses : List Witness) : SourceSpecialization.SpecializedFunction :=
  { caller with function := { caller.function with
      typedBody := caller.function.typedBody.applySubstitution substitution
      solvedRequirements := rewriteLedger substitution witnesses caller.function.solvedRequirements } }

/-- Authenticate one original reference under the enclosing local instance.
The receipt removes exactly its qualified-scheme requirements; caller-selected
raw Core code or a fabricated obligation list cannot create this receipt. -/
def authenticateReference (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (binding : Binding) (parent : Option Prepared) (id : ExpressionId) : Except Error Reference := do
  let caller ← exactCaller plan binding
  let (active, inherited) ← activeContext caller parent
  validateWitnesses program caller active inherited
  let contextual := contextualCaller caller active inherited
  let node ← match contextual.function.typedBody.lookupExpression? id with
    | some node => pure node
    | none => throw (.missingExpression id)
  if id.occurrence.owner ≠ caller.key.declaration then throw (.bindingMismatch binding.binder.id)
  match node.form with
  | .reference _ (.local binder) =>
      if binder ≠ binding.binder.id then throw (.bindingMismatch binding.binder.id)
  | _ => throw (.bindingMismatch binding.binder.id)
  let owned ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
    | some owned => pure owned
    | none => throw (.plan (.unsupportedRequirements node.requirements))
  let raw := { node with type := node.rawType, requirements := owned, coercions := [] }
  let available ← (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
    |>.mapError Error.plan
  let (child, witnesses) ← (SourceCompilationPlan.localRequirementWitnesses contextual available
    (binding.binder.applySubstitution active) raw).mapError Error.plan
  let cumulative := child.compose active
  validateWitnesses program caller cumulative (inherited ++ witnesses)
  pure ⟨id, cumulative, witnesses, node, owned⟩

/-- Authenticate a policy's local occurrence before it reads callee metadata.
The current row must be the original contextual row or one of the two exact
normalized views used by the output-coercion traversal. Other rows are retained.
Repeated normalization and traversal of an already raw row preserve that view. -/
def normalizeOccurrence (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (binding : Binding) (parent : Option Prepared) (source : TypedSource) (id : ExpressionId) :
    Except Error TypedSource := do
  if source.owner ≠ binding.caller.declaration then throw (.originMismatch binding.caller)
  let reference ← authenticateReference program plan binding parent id
  let current ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (.missingExpression id)
  let normalized := reference.normalized
  let ordinary ← match SourceCompilationPlan.ordinaryOwnedRequirements? normalized with
    | some ordinary => pure ordinary
    | none => throw (.plan (.unsupportedRequirements normalized.requirements))
  let raw := { normalized with type := normalized.rawType, requirements := ordinary, coercions := [] }
  if current = reference.original then
    pure { source with nodes := source.nodes.map fun
      | .expression old => if old.id = id then .expression normalized else .expression old
      | .statement old => .statement old }
  else if current = normalized || current = raw then pure source
  else throw (.occurrenceMismatch id)

/-- Prepare a lambda child's exact caller ledger. A concrete original use site
authenticates its local dictionary; the full contextual key is checked before
any template row is replaced. Requirement IDs and unbound obligations survive. -/
def prepare (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (candidate : Instance) (parent : Option Prepared := none) : Except Error Prepared := do
  let origin := candidate.origin
  let binding : Binding := ⟨origin.caller, origin.source, origin.binder, origin.initializer, []⟩
  let caller ← exactCaller plan binding
  if origin.solvedRequirements != caller.function.solvedRequirements ||
      origin.parameterSubstitution ≠ caller.parameterSubstitution then throw (.originMismatch origin.caller)
  let discovered ← (SourceSpecializationWorklist.localLambdaInstances binding.source).mapError Error.discovery
  unless discovered.contains origin.localInstance do throw (.instanceMismatch binding.binder.id)
  let (active, inherited) ← activeContext caller parent
  let matching := binding.source.nodes.filterMap fun
    | .expression node@{ form := .reference _ (.local binder), .. } =>
        if binder = binding.binder.id then
          match SourceSpecialization.matchClosedSchemeInstance? (Scheme.apply active binding.binder.scheme)
            (active.apply node.rawType) with
          | some child => if child.compose active = origin.substitution then some node.id else none
          | none => none
        else none
    | _ => none
  let id ← match matching with
    | id :: _ => pure id
    | [] => throw (.missingReference binding.binder.id)
  let reference ← authenticateReference program plan binding parent id
  if reference.cumulative ≠ origin.substitution then throw (.instanceMismatch binding.binder.id)
  let witnesses := inherited ++ reference.witnesses
  validateWitnesses program caller origin.substitution witnesses
  pure ⟨candidate, contextualCaller caller origin.substitution witnesses, witnesses⟩

/-- A bundle is created in its lexical environment, but a ground candidate
may have been discovered only at a read inside another generalized lambda.
Keep that read-parent authentication separate from the creation parent.
`authentic` records a successful invocation of the same checked factory; no
candidate caller or witness ledger is accepted directly. -/
structure Emission (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (candidate : Instance) (lexicalParent : Option Prepared) where private mk ::
  readParent : Option Prepared
  prepared : Prepared
  authentic : prepare program plan candidate readParent = .ok prepared

/-- Existing lexical preparation stays first. Alternative parents are finite
owned receipts, and each alternative is reauthenticated against this program,
plan and complete candidate key. The caller retains its lexical Core scope. -/
def prepareForEmission (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (candidate : Instance) (lexicalParent : Option Prepared) (parents : List Prepared) :
    Except Error (Emission program plan candidate lexicalParent) := do
  match original : prepare program plan candidate lexicalParent with
  | .ok prepared => pure ⟨lexicalParent, prepared, original⟩
  | .error originalError =>
    let mut found := none
    for parent in parents do
      if found.isNone then
        match authentic : prepare program plan candidate (some parent) with
        | .ok prepared => found := some (Emission.mk (some parent) prepared authentic)
        | .error _ => pure ()
    match found with
    | some emission => pure emission
    | none => throw originalError

end Solcore.Frontend.SourceCoreLocalEvidence
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreStageContracts
/-! Retained source staging contracts for Core compilation. These sealed
receipts preserve the original caller sidecar and the existing callable guard;
they neither evaluate source nor erase staging admission rules. The enclosing
artifact authenticates its canonical prepared plan. This module checks exact
plan lookup, source ownership, the analyzer's retained output, and callable
occurrence provenance within that plan.

`Guard.lower` is the static known-contract fragment: it evaluates the callee
first and skips arguments on rejection. Dynamic callable contract transport is
a separate representation boundary. These laws describe the existing metadata
validator and Core evaluation; the declarative source call rules currently do
not include this runtime stage guard. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreStageContracts

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev RuntimeError := SourceCompilationPlan.Error

inductive Error where
  | plan (error : RuntimeError)
  | analysis (error : SourceStageAnalysis.Error)
  | sidecarMismatch (key : Key)
  | ownerMismatch (expected actual : Resolved.DeclarationId)
  | missingExpression (id : ExpressionId)
  | duplicateExpression (id : ExpressionId) (count : Nat)
  | expectedLambda (id : ExpressionId)
  | openLambda (id : ExpressionId)
  | expectedIndirectCall (id : ExpressionId)
  | planMismatch
  | contextualCallerMismatch (key : Key)
  deriving Repr

/-- A retained original specialization and its exact analyzer output. Public
clients cannot substitute an edited stage table into this receipt. -/
structure Sidecar where private mk ::
  plan : Plan
  caller : SourceSpecialization.SpecializedFunction
  analyzed : SourceStageAnalysis.analyzeFunction caller.function = .ok caller.stageAnalysis

namespace Sidecar

def source (sidecar : Sidecar) : TypedSource := sidecar.caller.function.typedBody

theorem certificate (sidecar : Sidecar) :
    SourceStageAnalysis.FunctionAnalysisCertificate sidecar.caller.function sidecar.caller.stageAnalysis :=
  SourceStageAnalysis.analyzeFunction_success_certificate _ _ sidecar.analyzed

end Sidecar

/-- Metadata admission is checked before a contract is projected. Resolving
closed trait assumptions and authenticating the whole plan remain the owning
artifact's preparation responsibilities. -/
def prepareSidecar (plan : Plan) (key : Key) : Except Error Sidecar := do
  let caller ← (SourceCompilationPlan.exactSpecialization plan key).mapError Error.plan
  discard <| (SourceCompilationPlan.validateSpecializationMetadataWith true caller).mapError Error.plan
  match analyzed : SourceStageAnalysis.analyzeFunction caller.function with
  | .error error => .error (.analysis error)
  | .ok analysis =>
      if same : analysis = caller.stageAnalysis then
        .ok (.mk plan caller (same ▸ analyzed))
      else .error (.sidecarMismatch key)

def expression (sidecar : Sidecar) (id : ExpressionId) : Except Error ExpressionNode := do
  if id.occurrence.owner ≠ sidecar.source.owner then
    throw (.ownerMismatch sidecar.source.owner id.occurrence.owner)
  match sidecar.source.nodes.filterMap (fun
      | .expression node => if node.id = id then some node else none
      | .statement _ => none) with
  | [] => .error (.missingExpression id)
  | [node] => .ok node
  | nodes => .error (.duplicateExpression id nodes.length)

/-- The source types and flags stay together until the existing guard has been
decided. A source function type alone does not encode parameter comptime flags. -/
structure Contract where private mk ::
  plan : Plan
  parameters : List TypedBinder
  stagedResult : Bool
  owner : Key

namespace Contract

/-- Arbitrary source arity is retained; each flag includes an outer staged
source type, rather than just the binder's explicit marker. -/
def parameterStages (contract : Contract) : List Bool :=
  contract.parameters.map fun parameter => parameter.comptime ||
    SourceCompilationPlan.sourceTypeIsComptimeOnly parameter.scheme.body

def named (plan : Plan) (key : Key) : Except Error Contract := do
  let callee ← prepareSidecar plan key
  pure (.mk callee.plan callee.caller.function.typedBody.inputs
    (callee.caller.function.returnComptime ||
      SourceCompilationPlan.sourceTypeIsComptimeOnly callee.caller.function.inferredBodyType)
    callee.caller.key)

/-- Monomorphic original lambda contracts. Flexible local instances need a
separate authenticated contextual receipt before their flags can be projected. -/
def lambda (sidecar : Sidecar) (id : ExpressionId) : Except Error Contract := do
  let node ← expression sidecar id
  match node.form with
  | .lambda parameters resultType _ =>
      if parameters.any (fun parameter => !parameter.scheme.body.freeVariables.isEmpty) ||
          !resultType.freeVariables.isEmpty then
        throw (.openLambda id)
      pure (.mk sidecar.plan parameters (SourceCompilationPlan.sourceTypeIsComptimeOnly resultType) sidecar.caller.key)
  | _ => .error (.expectedLambda id)

/-- A generalized lambda is projected only through an authenticated complete
local context. The receipt must reconstruct this exact original caller,
including its retained sidecar and obligation ledger; a caller-selected type
substitution is insufficient. -/
def contextualLambda (sidecar : Sidecar) (prepared : SourceCoreLocalEvidence.Prepared)
    (id : ExpressionId) : Except Error Contract := do
  let original := sidecar.caller
  let expected := { original with function := { original.function with
    typedBody := sidecar.source.applySubstitution prepared.substitution
    solvedRequirements := SourceCoreLocalEvidence.rewriteLedger prepared.substitution
      prepared.witnesses original.function.solvedRequirements } }
  unless prepared.caller == expected do
    throw (.contextualCallerMismatch sidecar.caller.key)
  let node ← expression sidecar id
  match node.form with
  | .lambda parameters resultType _ =>
      let parameters := parameters.map (TypedBinder.applySubstitution prepared.substitution)
      let resultType := prepared.substitution.apply resultType
      if parameters.any (fun parameter => !parameter.scheme.body.freeVariables.isEmpty) ||
          !resultType.freeVariables.isEmpty then
        throw (.openLambda id)
      pure (.mk sidecar.plan parameters (SourceCompilationPlan.sourceTypeIsComptimeOnly resultType) sidecar.caller.key)
  | _ => .error (.expectedLambda id)

end Contract

/-- A static decision retains the exact original use occurrence, parameter
contract, and diagnostic. Stage rejection is a language result, not a Core
machine fault or an instruction to run the source evaluator. -/
structure Guard where private mk ::
  sidecar : Sidecar
  contract : Contract
  node : ExpressionNode
  arguments : List ExpressionId
  decision : Except RuntimeError Unit
  exact : SourceCompilationPlan.validateStagedCallableContract sidecar.caller node arguments
    contract.parameters contract.stagedResult contract.owner = decision

def prepareGuard (sidecar : Sidecar) (call : ExpressionId) (contract : Contract) : Except Error Guard := do
  unless sidecar.plan == contract.plan do throw .planMismatch
  let node ← expression sidecar call
  match node.form with
  | .call _ arguments (.indirect _) =>
      pure (.mk sidecar contract node arguments
        (SourceCompilationPlan.validateStagedCallableContract sidecar.caller node arguments
          contract.parameters contract.stagedResult contract.owner) rfl)
  | _ => .error (.expectedIndirectCall call)

namespace Guard

theorem decision_exact (guard : Guard) :
    SourceCompilationPlan.validateStagedCallableContract guard.sidecar.caller guard.node guard.arguments
      guard.contract.parameters guard.contract.stagedResult guard.contract.owner = guard.decision :=
  guard.exact

/-- `successBody` lives under the callee binder and owns argument evaluation.
The codebook maps the retained exact source diagnostic to a nonwrapping reason.
No source computation occurs when this decision is used by native execution. -/
def lower (guard : Guard) (resultType : Core.Ty) (callee successBody : Core.Expr)
    (reasonFor : RuntimeError → Core.Word) : Core.Expr :=
  Core.LanguageResult.bind resultType callee
    (match guard.decision with
    | .ok () => successBody
    | .error error => Core.LanguageResult.failure resultType (.word (reasonFor error)))

theorem lower_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {calleeType resultType : Core.Ty} {callee successBody : Core.Expr}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (wellFormed : Core.Ty.WellFormed definitions resultType)
    (calleeTyped : Core.HasType context callee (Core.LanguageResult.resultType calleeType) definitions)
    (bodyTyped : Core.HasType (calleeType :: context) successBody
      (Core.LanguageResult.resultType resultType) definitions) :
    Core.HasType context (guard.lower resultType callee successBody reasonFor)
      (Core.LanguageResult.resultType resultType) definitions := by
  apply Core.LanguageResult.bind_hasType wellFormed calleeTyped
  cases guard.decision with
  | ok value => cases value; exact bodyTyped
  | error error => exact Core.LanguageResult.failure_hasType wellFormed .word

theorem lower_callee_failure {environment : Core.Environment} {before after : Core.Store}
    {calleeType resultType : Core.Ty} {callee body : Core.Expr} {reason : Core.Word}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (evaluation : Core.Evaluates environment before callee (.inLeft calleeType (.word reason)) after) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor)
      (.inLeft resultType (.word reason)) after :=
  Core.LanguageResult.bind_failure resultType evaluation

theorem lower_callee_failure_iff {environment : Core.Environment} {before calleeStore after : Core.Store}
    {calleeType resultType : Core.Ty} {callee body : Core.Expr} {reason : Core.Word} {result : Core.Value}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (evaluation : Core.Evaluates environment before callee (.inLeft calleeType (.word reason)) calleeStore) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor) result after ↔
      result = .inLeft resultType (.word reason) ∧ after = calleeStore :=
  Core.LanguageResult.bind_failure_iff evaluation

theorem lower_rejected_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {calleeType resultType : Core.Ty} {callee body : Core.Expr} {error : RuntimeError}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (rejected : guard.decision = .error error)
    (wellFormed : Core.Ty.WellFormed definitions resultType)
    (calleeTyped : Core.HasType context callee (Core.LanguageResult.resultType calleeType) definitions) :
    Core.HasType context (guard.lower resultType callee body reasonFor)
      (Core.LanguageResult.resultType resultType) definitions := by
  apply Core.LanguageResult.bind_hasType wellFormed calleeTyped
  simp only [rejected]
  exact Core.LanguageResult.failure_hasType wellFormed .word

theorem lower_rejected {environment : Core.Environment} {before after : Core.Store}
    {resultType : Core.Ty} {callee body : Core.Expr} {value : Core.Value} {error : RuntimeError}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (rejected : guard.decision = .error error)
    (evaluation : Core.Evaluates environment before callee (.inRight .word value) after) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor)
      (.inLeft resultType (.word (reasonFor error))) after := by
  apply Core.LanguageResult.bind_success resultType evaluation
  simp only [rejected]
  exact Core.LanguageResult.failure_evaluates resultType .word

/-- A rejected known contract fixes the final heap to the callee's heap. The
argument/body expression is arbitrary and need not terminate. -/
theorem lower_rejected_iff {environment : Core.Environment} {before calleeStore after : Core.Store}
    {resultType : Core.Ty} {callee body : Core.Expr} {value result : Core.Value} {error : RuntimeError}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (rejected : guard.decision = .error error)
    (evaluation : Core.Evaluates environment before callee (.inRight .word value) calleeStore) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor) result after ↔
      result = .inLeft resultType (.word (reasonFor error)) ∧ after = calleeStore := by
  constructor
  · intro evaluated
    exact Core.evaluation_deterministic evaluated (lower_rejected guard reasonFor rejected evaluation)
  · rintro ⟨rfl, rfl⟩
    exact lower_rejected guard reasonFor rejected evaluation

theorem lower_accepted {environment : Core.Environment} {before middle after : Core.Store}
    {resultType : Core.Ty} {callee body : Core.Expr} {value result : Core.Value}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (accepted : guard.decision = .ok ())
    (calleeEvaluation : Core.Evaluates environment before callee (.inRight .word value) middle)
    (bodyEvaluation : Core.Evaluates (value :: environment) middle body result after) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor) result after := by
  apply Core.LanguageResult.bind_success resultType calleeEvaluation
  simpa only [accepted] using bodyEvaluation

end Guard

end Solcore.Frontend.SourceCoreStageContracts
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreStageCodebook
/-! Finite artifact-owned callable contracts. Contract IDs are ordinary Core
words and are independent of source named-function identity. The enclosing
artifact authenticates the prepared plan; sealed callable receipts authenticate
the retained source flags and cumulative contexts. This module evaluates no
source expressions. Its IDs need only existing Core word comparisons to dispatch.

The inventory covers compiled plan origins and discovered local instances.
External closure importing and declarative source staging-guard rules are
separate boundaries. Extra closed lambda origins in a retained source table
are harmless: the compiler emits a descriptor only for the exact origin it
actually compiles. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreStageCodebook

open SourceInference
abbrev Key := SourceCoreStageContracts.Key
abbrev Plan := SourceCoreStageContracts.Plan
abbrev Contract := SourceCoreStageContracts.Contract
abbrev Sidecar := SourceCoreStageContracts.Sidecar
abbrev Guard := SourceCoreStageContracts.Guard
abbrev RuntimeError := SourceCoreStageContracts.RuntimeError

inductive Origin where
  | named (key : Key)
  | lambda (owner : Key) (id : ExpressionId) (context : TypeSystem.Substitution)
  | builtin (function : BuiltinFunctionId)
  deriving Repr, DecidableEq

structure Limits where
  maxContracts : Nat := 4096
  maxDecisions : Nat := 65536
  deriving Repr

inductive Error where
  | contracts (error : SourceCoreStageContracts.Error)
  | localInstances (error : SourceCoreLocalPolymorphism.Error)
  | localEvidence (error : SourceCoreLocalEvidence.Error)
  | contractBudgetExhausted (limit : Nat)
  | decisionBudgetExhausted (limit : Nat)
  | contractIdSpaceExhausted (next : Nat)
  | zeroFirstId
  | ambiguousOrigin (origin : Origin)
  | duplicateId
  | duplicateDecision
  | missingCallsite (caller : Key) (id : ExpressionId)
  deriving Repr

structure Entry where private mk ::
  id : Core.Word
  origin : Origin
  parameterCount : Nat
  /-- Builtins bypass the old indirect staging validator. Their ordinary
  callable application still owns parameter-count/type checks. -/
  contract : Option Contract

structure Decision where private mk ::
  caller : Key
  call : ExpressionId
  entry : Entry
  argumentCount : Nat
  guard : Option Guard

namespace Decision

def answer (row : Decision) : Except RuntimeError Unit :=
  match row.guard with | some guard => guard.decision | none => .ok ()

def beforeArguments (row : Decision) : Except RuntimeError Unit := row.answer

/-- Unlike the stage guard, callable application checks full arity even for
an effectful-staging caller. This runs after arguments/coercions and before
parameter cells are allocated. -/
def afterArguments (row : Decision) : Except RuntimeError Unit :=
  if row.entry.parameterCount = row.argumentCount then .ok ()
  else .error (.argumentArityMismatch row.entry.parameterCount row.argumentCount)

theorem afterArguments_ok (row : Decision) (same : row.entry.parameterCount = row.argumentCount) :
    row.afterArguments = .ok () := by simp [afterArguments, same]

theorem afterArguments_mismatch (row : Decision) (different : row.entry.parameterCount ≠ row.argumentCount) :
    row.afterArguments = .error (.argumentArityMismatch row.entry.parameterCount row.argumentCount) := by
  simp [afterArguments, different]

def key (row : Decision) : Key × ExpressionId × Core.Word := (row.caller, row.call, row.entry.id)

theorem exact_guard (row : Decision) (guard : Guard) (same : row.guard = some guard) :
    row.answer = SourceCompilationPlan.validateStagedCallableContract guard.sidecar.caller guard.node guard.arguments
      guard.contract.parameters guard.contract.stagedResult guard.contract.owner := by
  simp only [answer, same]
  exact guard.decision_exact.symm

end Decision

structure Table where private mk ::
  entries : List Entry
  decisions : List Decision
  idsUnique : (entries.map (·.id)).Nodup
  originsUnique : (entries.map (·.origin)).Nodup
  decisionsUnique : (decisions.map Decision.key).Nodup

namespace Table

def idAt? (table : Table) (origin : Origin) : Option Core.Word :=
  (table.entries.find? (fun entry => decide (entry.origin = origin))).map (·.id)

def entryAt? (table : Table) (id : Core.Word) : Option Entry :=
  table.entries.find? (fun entry => decide (entry.id = id))

def decisionAt? (table : Table) (caller : Key) (call : ExpressionId) (id : Core.Word) : Option Decision :=
  table.decisions.find? (fun row => decide (row.key = (caller, call, id)))

def casesAt (table : Table) (caller : Key) (call : ExpressionId) : List Decision :=
  table.decisions.filter (fun row => decide (row.caller = caller ∧ row.call = call))

def contractCount (table : Table) : Nat := table.entries.length
def decisionCount (table : Table) : Nat := table.decisions.length

end Table

def insert (limits : Limits) (firstId : Nat) (entries : List Entry)
    (origin : Origin) (count : Nat) (contract : Option Contract) : Except Error (List Entry) := do
  if entries.any (fun entry => decide (entry.origin = origin)) then return entries
  if entries.length ≥ limits.maxContracts then throw (.contractBudgetExhausted limits.maxContracts)
  let id ← match Core.Word.ofNat? (firstId + entries.length) with
    | some id => pure id
    | none => throw (.contractIdSpaceExhausted (firstId + entries.length))
  pure (entries ++ [.mk id origin count contract])

private def lambdaIds (sidecar : Sidecar) : List ExpressionId :=
  sidecar.source.nodes.filterMap fun
    | .expression { id, form := .lambda _ _ _, .. } => some id
    | _ => none

def collectLambdas (limits : Limits) (firstId : Nat) (sidecar : Sidecar)
    (prepared : Option SourceCoreLocalEvidence.Prepared) (entries : List Entry) : Except Error (List Entry) := do
  let mut entries := entries
  let context := prepared.map (·.substitution) |>.getD []
  for id in lambdaIds sidecar do
    let answer := match prepared with
      | none => SourceCoreStageContracts.Contract.lambda sidecar id
      | some prepared => SourceCoreStageContracts.Contract.contextualLambda sidecar prepared id
    match answer with
    | .error (.openLambda _) => pure ()
    | .error error => throw (.contracts error)
    | .ok contract =>
        entries ← insert limits firstId entries (.lambda sidecar.caller.key id context)
          contract.parameters.length (some contract)
  pure entries

/-- Existing local discovery orders enclosing contexts before nested contexts.
Try the original caller and already authenticated contexts; every accepted
receipt checks the exact full cumulative instance and its evidence chain. -/
private def contextualReceipt (program : CheckedProgram) (plan : Plan)
    (parents : List SourceCoreLocalEvidence.Prepared) (candidate : SourceCoreLocalPolymorphism.Instance) :
    Except Error SourceCoreLocalEvidence.Prepared :=
  (SourceCoreLocalEvidence.prepareForEmission program plan candidate none parents).map (·.prepared)
    |>.mapError Error.localEvidence

/-- Storage order of source nodes need not be lexical parent order. Revisit
pending instances after each progress pass; every pass authenticates at least
one instance, so the instance count bounds this static dependency traversal. -/
private def contextualReceipts (program : CheckedProgram) (plan : Plan) : Nat →
    List SourceCoreLocalEvidence.Prepared → List SourceCoreLocalPolymorphism.Instance →
    Except Error (List SourceCoreLocalEvidence.Prepared)
  | _, parents, [] => pure parents
  | 0, _, _ :: _ => throw (.contractBudgetExhausted 0)
  | fuel + 1, parents, pending => do
      let mut parents := parents
      let mut remaining := []
      let mut firstError := none
      for candidate in pending do
        match contextualReceipt program plan parents candidate with
        | .ok prepared => parents := parents ++ [prepared]
        | .error error =>
            remaining := remaining ++ [candidate]
            if firstError.isNone then firstError := some error
      if remaining.length = pending.length then
        match firstError with
        | some error => throw error
        | none => throw (.contractBudgetExhausted 0)
      contextualReceipts program plan fuel parents remaining

def collectDecisions (limits : Limits) (sidecars : List Sidecar) (entries : List Entry) :
    Except Error (List Decision) := do
  let mut rows := []
  for sidecar in sidecars do
    for node in sidecar.source.nodes do
      match node with
      | .expression { id, form := .call _ arguments (.indirect _), .. } =>
          for entry in entries do
            if rows.length ≥ limits.maxDecisions then throw (.decisionBudgetExhausted limits.maxDecisions)
            let guard ← match entry.contract with
              | none => pure none
              | some contract =>
                  (SourceCoreStageContracts.prepareGuard sidecar id contract).map some |>.mapError Error.contracts
            rows := rows ++ [.mk sidecar.caller.key id entry arguments.length guard]
      | _ => pure ()
  pure rows

/-- Reuse the authenticated parent-order discovery for contextual metadata
inventories, including diagnostics and source-allocation preparation. -/
def prepareContexts (program : CheckedProgram) (plan : Plan)
    (candidates : List SourceCoreLocalPolymorphism.Instance) :
    Except Error (List SourceCoreLocalEvidence.Prepared) :=
  contextualReceipts program plan candidates.length [] candidates

/-- Construct once during artifact preparation. The IDs are positive words,
never wrapping; the immutable table certifies unique origins, IDs, and lookup
keys. The limits bound accepted origins and callsite/contract combinations. -/
def prepareWithProjection (program : CheckedProgram) (plan : Plan)
    (projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty)
    (limits : Limits := {}) (firstId : Nat := 1) : Except Error Table := do
  if firstId = 0 then throw .zeroFirstId
  let mut entries := []
  let mut sidecars := []
  for specialized in plan.specializations do
    let sidecar ← (SourceCoreStageContracts.prepareSidecar plan specialized.key).mapError Error.contracts
    sidecars := sidecars ++ [sidecar]
    let contract ← (SourceCoreStageContracts.Contract.named plan specialized.key).mapError Error.contracts
    entries ← insert limits firstId entries (.named specialized.key) contract.parameters.length (some contract)
    entries ← collectLambdas limits firstId sidecar none entries
  for function in BuiltinFunctionId.all do
    entries ← insert limits firstId entries (.builtin function) function.parameterTypes.length none
  let locals ← (SourceCoreLocalPolymorphism.prepareWithProjection projectType plan).mapError Error.localInstances
  let candidates := locals.bindings.flatMap (·.instances)
  if candidates.length > limits.maxContracts then throw (.contractBudgetExhausted limits.maxContracts)
  let contexts ← contextualReceipts program plan candidates.length [] candidates
  for prepared in contexts do
    let sidecar ← (SourceCoreStageContracts.prepareSidecar plan prepared.caller.key).mapError Error.contracts
    entries ← collectLambdas limits firstId sidecar (some prepared) entries
  let rows ← collectDecisions limits sidecars entries
  if ids : (entries.map (·.id)).Nodup then
    if origins : (entries.map (·.origin)).Nodup then
      if unique : (rows.map Decision.key).Nodup then
        pure (.mk entries rows ids origins unique)
      else throw .duplicateDecision
    else throw (.ambiguousOrigin (entries.head?.map (·.origin) |>.getD (.builtin .integerAdd)))
  else throw .duplicateId


/-- Strict-catalog compatibility entry. Both representations authenticate
original contracts through the same inventory and decision construction. -/
def prepare (program : CheckedProgram) (plan : Plan) (checked : SourceCoreDataCatalog.Checked)
    (limits : Limits := {}) (firstId : Nat := 1) : Except Error Table :=
  prepareWithProjection program plan (fun type => do
    let projected ← (checked.project type).mapError SourceCoreLocalPolymorphism.Error.projection
    pure projected.type) limits firstId

private theorem provenance_bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem provenance_forIn {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item, item ∈ items → ∀ state outcome, invariant state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant updated) : invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item items ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := provenance_bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

private def AuthenticContext (program : CheckedProgram) (plan : Plan)
    (item : SourceCoreLocalEvidence.Prepared) : Prop :=
  ∃ candidate parent, SourceCoreLocalEvidence.prepare program plan candidate parent = .ok item

private theorem contextualReceipt_authentic {program : CheckedProgram} {plan : Plan}
    {parents : List SourceCoreLocalEvidence.Prepared} {candidate : SourceCoreLocalPolymorphism.Instance}
    {item : SourceCoreLocalEvidence.Prepared}
    (accepted : contextualReceipt program plan parents candidate = .ok item) :
    AuthenticContext program plan item := by
  unfold contextualReceipt at accepted
  cases generated : SourceCoreLocalEvidence.prepareForEmission program plan candidate none parents with
  | error error => simp [generated, Except.map, Except.mapError] at accepted
  | ok emission =>
    have same : emission.prepared = item := by simpa [generated, Except.map, Except.mapError] using accepted
    exact ⟨candidate, emission.readParent, same ▸ emission.authentic⟩

private theorem contextualReceipts_authentic (program : CheckedProgram) (plan : Plan) (fuel : Nat)
    {parents output : List SourceCoreLocalEvidence.Prepared} {pending : List SourceCoreLocalPolymorphism.Instance}
    (initial : ∀ item ∈ parents, AuthenticContext program plan item)
    (accepted : contextualReceipts program plan fuel parents pending = .ok output) :
    ∀ item ∈ output, AuthenticContext program plan item := by
  induction fuel generalizing parents pending output with
  | zero =>
    cases pending with
    | nil => cases accepted; exact initial
    | cons candidate tail => cases accepted
  | succ fuel ih =>
    cases pending with
    | nil => cases accepted; exact initial
    | cons candidate tail =>
      rw [contextualReceipts] at accepted <;> try simp
      obtain ⟨state, loop, accepted⟩ := provenance_bind_ok accepted
      have generated := provenance_forIn loop
        (invariant := fun state => ∀ item ∈ state.1, AuthenticContext program plan item) initial ?_
      · dsimp only at accepted
        split at accepted
        · split at accepted <;> cases accepted
        · exact ih generated accepted
      · intro candidate member state outcome valid ran
        dsimp only at ran
        cases produced : contextualReceipt program plan state.1 candidate with
        | error error =>
          simp only [produced, pure, Except.pure] at ran
          split at ran <;> cases ran <;> exact ⟨_, rfl, valid⟩
        | ok item =>
          simp only [produced, pure, Except.pure] at ran
          cases ran
          refine ⟨_, rfl, ?_⟩
          intro next occurs
          rcases List.mem_append.mp occurs with old | fresh
          · exact valid next old
          · cases List.mem_singleton.mp fresh
            exact contextualReceipt_authentic produced

/-- Every returned context retains a successful invocation of the original
local-evidence factory, including its complete caller and ordered witnesses. -/
theorem prepareContexts_authentic {program : CheckedProgram} {plan : Plan}
    {candidates : List SourceCoreLocalPolymorphism.Instance} {prepared : List SourceCoreLocalEvidence.Prepared}
    (accepted : prepareContexts program plan candidates = .ok prepared)
    {item : SourceCoreLocalEvidence.Prepared} (member : item ∈ prepared) :
    ∃ candidate parent, SourceCoreLocalEvidence.prepare program plan candidate parent = .ok item :=
  contextualReceipts_authentic program plan candidates.length (by simp) accepted item member

end Solcore.Frontend.SourceCoreStageCodebook
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableContracts
/-! Translate authenticated finite source contracts to ordinary Core gates.
The source compiler selects an exact original callable origin; public function
values keep this descriptor hidden inside artifact-owned handles. This module
does not authenticate arbitrary Core closure code against a chosen source
origin, and does not expose a public runtime handle constructor.

The codebook keeps exact source diagnostics until the artifact assigns language
reason words. Native gate selection preserves those words and has no store
effects. Whole source meaning preservation and the dynamic stage-guard source
specification remain separate proof boundaries. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCallableContracts

open SourceInference
abbrev Key := SourceCoreStageCodebook.Key
abbrev Origin := SourceCoreStageCodebook.Origin
abbrev Table := SourceCoreStageCodebook.Table
abbrev Decision := SourceCoreStageCodebook.Decision
abbrev RuntimeError := SourceCoreStageCodebook.RuntimeError
abbrev Phase := Core.CallableContract.Phase

/-- The artifact's codebook assigns words once. Phase and contract ID remain
available when registering/restoring the exact caller/use/callee diagnostic. -/
abbrev ReasonAt := Key → ExpressionId → Core.Word → Phase → RuntimeError → Core.Word

inductive Error where
  | missingOrigin (origin : Origin)
  | missingCallsite (caller : Key) (call : ExpressionId)
  deriving Repr

structure Descriptor (table : Table) (origin : Origin) where private mk ::
  id : Core.Word
  found : table.idAt? origin = some id

def descriptor (table : Table) (origin : Origin) : Except Error (Descriptor table origin) :=
  match found : table.idAt? origin with
  | none => .error (.missingOrigin origin)
  | some id => .ok (.mk id found)

namespace Descriptor

def wrap {table : Table} {origin : Origin} (descriptor : Descriptor table origin) (function : Core.Expr) : Core.Expr :=
  Core.CallableContract.wrap descriptor.id function

theorem wrap_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {table : Table} {origin : Origin} {parameter result : Core.Ty} {function : Core.Expr}
    (descriptor : Descriptor table origin)
    (typed : Core.HasType context function (Core.TaggedFunction.functionType parameter result) definitions) :
    Core.HasType context (descriptor.wrap function) (Core.CallableContract.functionType parameter result) definitions :=
  Core.CallableContract.wrap_hasType descriptor.id typed

theorem wrap_evaluates {table : Table} {origin : Origin} {environment : Core.Environment}
    {before after : Core.Store} {function : Core.Expr} {value : Core.Value}
    (descriptor : Descriptor table origin)
    (evaluation : Core.Evaluates environment before function value after) :
    Core.Evaluates environment before (descriptor.wrap function) (.pair value (.word descriptor.id)) after :=
  Core.CallableContract.wrap_evaluates descriptor.id evaluation

end Descriptor

def phaseAnswer (row : Decision) : Phase → Except RuntimeError Unit
  | .beforeArguments => row.beforeArguments
  | .beforeApplication => row.afterArguments

def reason (row : Decision) (reasonAt : ReasonAt) (phase : Phase) : Option Core.Word :=
  match phaseAnswer row phase with
  | .ok () => none
  | .error error => some (reasonAt row.caller row.call row.entry.id phase error)

def gate (row : Decision) (reasonAt : ReasonAt) : Core.CallableContract.Gate := {
  contract := row.entry.id
  beforeArguments := reason row reasonAt .beforeArguments
  beforeApplication := reason row reasonAt .beforeApplication
}

theorem gate_reason (row : Decision) (reasonAt : ReasonAt) (phase : Phase) :
    (gate row reasonAt).reason phase = reason row reasonAt phase := by cases phase <;> rfl

theorem gate_contract (row : Decision) (reasonAt : ReasonAt) :
    (gate row reasonAt).contract = row.entry.id := rfl

theorem reason_accepted (row : Decision) (reasonAt : ReasonAt) (phase : Phase)
    (accepted : phaseAnswer row phase = .ok ()) : reason row reasonAt phase = none := by
  simp only [reason, accepted]

theorem reason_rejected (row : Decision) (reasonAt : ReasonAt) (phase : Phase) (error : RuntimeError)
    (rejected : phaseAnswer row phase = .error error) :
    reason row reasonAt phase = some (reasonAt row.caller row.call row.entry.id phase error) := by
  simp only [reason, rejected]

structure Callsite where private mk ::
  table : Table
  caller : Key
  call : ExpressionId
  reasonAt : ReasonAt
  present : table.casesAt caller call ≠ []

def prepareCallsite (table : Table) (caller : Key) (call : ExpressionId) (reasonAt : ReasonAt) : Except Error Callsite :=
  if present : table.casesAt caller call ≠ [] then .ok (.mk table caller call reasonAt present)
  else .error (.missingCallsite caller call)

namespace Callsite

def rows (site : Callsite) : List Decision := site.table.casesAt site.caller site.call
def gates (site : Callsite) : List Core.CallableContract.Gate := site.rows.map (fun row => gate row site.reasonAt)
def rowAt? (site : Callsite) (id : Core.Word) : Option Decision :=
  site.rows.find? (fun row => id == row.entry.id)

private theorem decision_rows (rows : List Decision) (reasonAt : ReasonAt) (phase : Phase) (unknown id : Core.Word) :
    Core.CallableContract.decision (rows.map (fun row => gate row reasonAt)) phase unknown id =
      match rows.find? (fun row => id == row.entry.id) with
      | none => some unknown
      | some row => reason row reasonAt phase := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases same : (id == row.entry.id) <;>
        simp only [List.map_cons, Core.CallableContract.decision, gate_contract, same,
          Bool.false_eq_true, ↓reduceIte, List.find?_cons, ih, gate_reason]

theorem decision_known (site : Callsite) (phase : Phase) (unknown id : Core.Word) (row : Decision)
    (found : site.rowAt? id = some row) :
    Core.CallableContract.decision site.gates phase unknown id = reason row site.reasonAt phase := by
  have evaluated := decision_rows site.rows site.reasonAt phase unknown id
  change site.rows.find? (fun row => id == row.entry.id) = some row at found
  simpa only [gates, found] using evaluated

theorem decision_unknown (site : Callsite) (phase : Phase) (unknown id : Core.Word)
    (missing : site.rowAt? id = none) :
    Core.CallableContract.decision site.gates phase unknown id = some unknown := by
  have evaluated := decision_rows site.rows site.reasonAt phase unknown id
  change site.rows.find? (fun row => id == row.entry.id) = none at missing
  simpa only [gates, missing] using evaluated

def lower (site : Callsite) (unknown : Core.Word) (result : Core.Ty) (callee arguments : Core.Expr) : Core.Expr :=
  Core.CallableContract.call site.gates unknown result callee arguments

theorem lower_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {parameter result : Core.Ty} {callee arguments : Core.Expr} (site : Callsite) (unknown : Core.Word)
    (wellFormed : Core.Ty.WellFormed definitions result)
    (calleeTyped : Core.HasType context callee
      (Core.LanguageResult.resultType (Core.CallableContract.functionType parameter result)) definitions)
    (argumentsTyped : Core.HasType context arguments (Core.LanguageResult.resultType parameter) definitions) :
    Core.HasType context (site.lower unknown result callee arguments) (Core.LanguageResult.resultType result) definitions :=
  Core.CallableContract.call_hasType site.gates unknown wellFormed calleeTyped argumentsTyped

theorem dispatch_known {environment : Core.Environment} {store : Core.Store} {expression : Core.Expr}
    (site : Callsite) (phase : Phase) (unknown id : Core.Word) (row : Decision)
    (found : site.rowAt? id = some row)
    (read : Core.Evaluates environment store expression (.word id) store) :
    Core.Evaluates environment store (Core.CallableContract.dispatch site.gates phase unknown expression)
      (Core.CallableContract.resultValue (reason row site.reasonAt phase)) store := by
  simpa only [site.decision_known phase unknown id row found] using
    Core.CallableContract.dispatch_evaluates site.gates phase unknown id read

theorem lower_stage_failure {environment : Core.Environment} {before after : Core.Store}
    {result : Core.Ty} {callee arguments : Core.Expr} {function : Core.Value} {id : Core.Word}
    (site : Callsite) (unknown : Core.Word) (row : Decision) (error : RuntimeError)
    (found : site.rowAt? id = some row) (rejected : row.beforeArguments = .error error)
    (evaluation : Core.Evaluates environment before callee (.inRight .word (.pair function (.word id))) after) :
    Core.Evaluates environment before (site.lower unknown result callee arguments)
      (.inLeft result (.word (site.reasonAt row.caller row.call row.entry.id .beforeArguments error))) after := by
  apply Core.CallableContract.call_stage_failure site.gates unknown evaluation
  rw [site.decision_known .beforeArguments unknown id row found]
  exact reason_rejected row site.reasonAt .beforeArguments error rejected

theorem lower_arity_failure {environment : Core.Environment} {before middle after : Core.Store}
    {result : Core.Ty} {callee arguments : Core.Expr} {function argument : Core.Value} {id : Core.Word}
    (site : Callsite) (unknown : Core.Word) (row : Decision) (error : RuntimeError)
    (found : site.rowAt? id = some row)
    (accepted : row.beforeArguments = .ok ()) (rejected : row.afterArguments = .error error)
    (calleeEvaluation : Core.Evaluates environment before callee (.inRight .word (.pair function (.word id))) middle)
    (argumentsEvaluation : Core.Evaluates (.unit :: .pair function (.word id) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inRight .word argument) after) :
    Core.Evaluates environment before (site.lower unknown result callee arguments)
      (.inLeft result (.word (site.reasonAt row.caller row.call row.entry.id .beforeApplication error))) after := by
  have stageAccepted : Core.CallableContract.decision site.gates .beforeArguments unknown id = none := by
    rw [site.decision_known .beforeArguments unknown id row found]
    exact reason_accepted row site.reasonAt .beforeArguments accepted
  have arityRejected : Core.CallableContract.decision site.gates .beforeApplication unknown id =
      some (site.reasonAt row.caller row.call row.entry.id .beforeApplication error) := by
    rw [site.decision_known .beforeApplication unknown id row found]
    exact reason_rejected row site.reasonAt .beforeApplication error rejected
  exact Core.CallableContract.call_arity_failure site.gates unknown calleeEvaluation stageAccepted argumentsEvaluation arityRejected

end Callsite

end Solcore.Frontend.SourceCoreCallableContracts
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableFaultSites
/-! Exact stage and invocation-arity diagnostics for the artifact codebook.
Tokens extend the existing program-wide diagnostic table without wrapping.
The original source occurrence supplies the span for contextual instances too. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCallableFaultSites
open SourceInference
abbrev Key := SourceCoreStageCodebook.Key
abbrev Table := SourceCoreStageCodebook.Table
abbrev Phase := Core.CallableContract.Phase
abbrev RuntimeError := SourceCoreStageCodebook.RuntimeError

structure Site where
  caller : Key
  call : ExpressionId
  contract : Core.Word
  phase : Phase
  error : RuntimeError
  reason : Core.Word
  diagnostic : SourceCoreFaultSites.Diagnostic
  deriving Repr

structure Program where
  sites : List Site
  unknown : Core.Word
  rootTable : SourceCoreFaultSites.Table
  deriving Repr

inductive Error where
  | reasonSpaceExhausted
  | missingCaller (key : Key)
  | missingCall (key : Key) (id : ExpressionId)
  deriving Repr

private def fresh (index : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? index with
  | some reason => .ok reason
  | none => .error .reasonSpaceExhausted

def prepare (plan : SourceCoreStageCodebook.Plan) (contracts : Table)
    (base : SourceCoreFaultSites.Table) (minimumReason : Nat := 0) : Except Error Program := do
  let used := base.reads.map (·.reason.val) ++ base.additional.map (·.1.val) ++
    [base.escapedReason.val]
  let start := max (used.foldl max 0 + 1) minimumReason
  let unknown ← fresh start
  let mut sites : List Site := []
  for row in contracts.decisions do
    let caller ← match plan.specializations.find? (fun entry => decide (entry.key = row.caller)) with
      | some caller => pure caller
      | none => throw (.missingCaller row.caller)
    let node ← match caller.function.typedBody.lookupExpression? row.call with
      | some node => pure node
      | none => throw (.missingCall row.caller row.call)
    for phase in ([.beforeArguments, .beforeApplication] : List Phase) do
      let answer := match phase with
        | .beforeArguments => row.beforeArguments
        | .beforeApplication => row.afterArguments
      match answer with
      | .ok _ => pure ()
      | .error error =>
          let reason ← fresh (start + 1 + sites.length)
          let diagnostic : SourceCoreFaultSites.Diagnostic :=
            { error, site := .occurrence row.call.occurrence, span := some node.span }
          sites := sites ++ [⟨row.caller, row.call, row.entry.id, phase, error, reason, diagnostic⟩]
  let unknownDiagnostic : SourceCoreFaultSites.Diagnostic :=
    { error := .deepSafetyInputsRejected, site := .declaration base.owner, span := none }
  pure { sites, unknown, rootTable := { base with
    additional := base.additional ++ [(unknown, unknownDiagnostic)] ++ sites.map (fun site => (site.reason, site.diagnostic)) } }

def Program.reasonAt (program : Program) (caller : Key) (call : ExpressionId)
    (contract : Core.Word) (phase : Phase) (error : RuntimeError) : Core.Word :=
  match program.sites.find? (fun site => decide (site.caller = caller ∧ site.call = call ∧
      site.contract = contract ∧ site.phase = phase ∧ site.error = error)) with
  | some site => site.reason
  | none => program.unknown

end Solcore.Frontend.SourceCoreCallableFaultSites
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreDataMatches
/-! Checked data patterns compiled to ordinary Core functions and sums. Pattern
attempts are pure: their successful result is a packed binder-value bundle.
Only a fully matched arm allocates the source binders. The scrutinee's hidden
source cell is allocated once, before testing the first arm. The callback owns
nested statement control and the surrounding compiler checks the full body.
Groups are transparent at the root and within tuple and constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataMatches

open SourceInference
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev ExpressionLowerer := SourceCoreDataExpressions.ExpressionLowerer
abbrev BodyLowerer := Nat → TypedSource → Scope → List StatementId → Core.Ty →
  (ExpressionId → Core.Word) → Core.Word → Except Error Core.Expr

structure Context where
  checked : Checked
  signatures : ProgramSignatures
  solvedRequirements : List SolvedRequirement

private def invalid : Error := .callPreparation .invalidPatternMetadata

/-- Unit/single/right-product representation of source-ordered binding values. -/
def bundleType : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (bundleType rest)

def bundle : List Core.Expr → Core.Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (bundle rest)

structure Pattern where
  type : Core.Ty
  bindings : List (TypedBinder × Core.Ty)
  requirements : List RequirementId
  matcher : Core.Expr
  deriving Repr

def Pattern.bindingTypes (pattern : Pattern) : List Core.Ty := pattern.bindings.map Prod.snd
def Pattern.resultType (pattern : Pattern) : Core.Ty := .sum .unit (bundleType pattern.bindingTypes)
def Pattern.functionType (pattern : Pattern) : Core.Ty := .function pattern.type pattern.resultType

/-- Every temporary successful child bundle is lexical only. Failed children
return absence immediately and never evaluate the later matcher applications. -/
def matchChildren (outputType : Core.Ty) : List Pattern → List Core.Expr → List Core.Expr → Core.Expr
  | [], _, accumulated => .inRight .unit (bundle accumulated)
  | pattern :: rest, value :: values, accumulated =>
      .caseE (.apply pattern.matcher value) (.inLeft outputType .unit)
        (matchChildren outputType rest (values.map (·.weakenAt 0))
          (accumulated.map (·.weakenAt 0) ++ pattern.bindingTypes.zipIdx.map
            (fun (_, index) => SourceCoreDataExpressions.projectPacked index pattern.bindingTypes (.var 0))))
  | _ :: _, [], _ => .inLeft outputType .unit

def projected (context : Context) (source : TypedSource) (type : TypeSystem.Ty) : Except Error Core.Ty :=
  SourceCoreGeneralTypes.projectType context.checked (.declaration source.owner) type

def unpackTypes : Nat → TypeSystem.Ty → Option (List TypeSystem.Ty)
  | 0, type => if type = .unit then some [] else none
  | 1, type => some [type]
  | count + 2, .product left right => do pure (left :: (← unpackTypes (count + 1) right))
  | _ + 2, _ => none

def childValues (types : List Core.Ty) : List Core.Expr :=
  types.zipIdx.map fun (_, index) => SourceCoreDataExpressions.projectPacked index types (.var 0)

/-- The shared literal validator consumes metadata only. Its temporary node
contains the expected type from the authenticated pattern tree, this literal's
own requirement, and the original literal spelling. `compilePattern` checks the
whole pattern's exact ordered requirement list independently. No expression
occurrence membership is inferred from this diagnostic carrier. -/
def literalMatcher (context : Context) (site : StatementId) (span : Syntax.SourceSpan)
    (type : TypeSystem.Ty) (literal : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution) :
    Except Error Core.Expr := do
  let node : ExpressionNode := {
    id := ⟨site.occurrence⟩, span, type, form := .integerLiteral literal resolution,
    requirements := [resolution.requirement]
  }
  let (coreType, equal) ← match type with
    | .constructor (.builtin .word) => do
      let valid ← (SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements node literal resolution)
        |>.mapError SourceCoreBasic.Error.literalEvidence
      pure (Core.Ty.word, Core.Expr.binary .wordEq (.var 0) (.word valid.value))
    | .constructor (.builtin .integer) => do
      let valid ← (SourceCoreElaboration.validateNativeIntegerLiteral context.solvedRequirements node literal resolution)
        |>.mapError SourceCoreBasic.Error.literalEvidence
      pure (Core.Ty.integer, Core.Expr.binary .integerEq (.var 0) (.integer valid.value))
    | _ => throw invalid
  pure (.lambda coreType (.sum .unit .unit)
    (.ifE equal (.inRight .unit .unit) (.inLeft .unit .unit)))

mutual
  def compileOne (context : Context) (source : TypedSource) (site : StatementId)
      (span : Syntax.SourceSpan) (scope : Scope) : Nat → TypeSystem.Ty → List MatchPatternInstruction →
        Except Error (Pattern × List MatchPatternInstruction)
    | 0, _, _ => throw (.traversalExhausted (.occurrence site.occurrence))
    | _ + 1, _, [] => throw invalid
    | fuel + 1, expected, instruction :: rest => do
      let type ← projected context source expected
      match instruction with
      | .wildcard => pure (⟨type, [], [], .lambda type (.sum .unit .unit) (.inRight .unit .unit)⟩, rest)
      | .binder binder =>
          unless binder.scheme.body = expected do throw invalid
          let actual ← SourceCoreGeneralTypes.lowerBinder context.checked source scope binder
          SourceCoreBasic.ensureType (.binder binder.id) type actual
          pure (⟨type, [(binder, type)], [], .lambda type (.sum .unit type) (.inRight .unit (.var 0))⟩, rest)
      | .integerLiteral literal resolution =>
          let matcher ← literalMatcher context site span expected literal resolution
          pure (⟨type, [], [resolution.requirement], matcher⟩, rest)
      | .tuple count =>
          let types ← match unpackTypes count expected with
            | some types => pure types
            | none => throw invalid
          let (children, rest) ← compileMany context source site span scope fuel types rest
          let bindings := children.flatMap (·.bindings)
          let outputType := bundleType (bindings.map Prod.snd)
          let types ← types.mapM (projected context source)
          pure (⟨type, bindings, children.flatMap (·.requirements),
            .lambda type (.sum .unit outputType)
              (matchChildren outputType children (childValues types) [])⟩, rest)
      | .constructor instantiation arity =>
          unless instantiation.resultType = expected && arity = instantiation.payloadTypes.length do throw invalid
          let constructor ← (context.checked.catalog.resolveConstructor context.signatures instantiation)
            |>.mapError (fun _ => invalid)
          SourceCoreBasic.ensureType (.occurrence site.occurrence) type (.namedData constructor.owner)
          let (children, rest) ← compileMany context source site span scope fuel instantiation.payloadTypes rest
          let bindings := children.flatMap (·.bindings)
          let outputType := bundleType (bindings.map Prod.snd)
          let payloadTypes ← instantiation.payloadTypes.mapM (projected context source)
          let definition ← match context.checked.catalog.definitions[constructor.owner.index]? with
            | some definition => pure definition
            | none => throw invalid
          let branches := definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
            if index = constructor.index then matchChildren outputType children (childValues payloadTypes) []
            else .inLeft outputType .unit
          pure (⟨type, bindings, children.flatMap (·.requirements),
            .lambda type (.sum .unit outputType)
              (.matchData constructor.owner (.sum .unit outputType) (.var 0) branches)⟩, rest)

  def compileMany (context : Context) (source : TypedSource) (site : StatementId)
      (span : Syntax.SourceSpan) (scope : Scope) : Nat → List TypeSystem.Ty → List MatchPatternInstruction →
        Except Error (List Pattern × List MatchPatternInstruction)
    | _, [], instructions => pure ([], instructions)
    | 0, _ :: _, _ => throw (.traversalExhausted (.occurrence site.occurrence))
    | fuel + 1, type :: types, instructions => do
        let (head, rest) ← compileOne context source site span scope fuel type instructions
        let (tail, rest) ← compileMany context source site span scope fuel types rest
        pure (head :: tail, rest)
end

def rootInstructions (context : Context) : MatchPatternSource → MatchPatternResolution →
    Except Error (List MatchPatternInstruction)
  | .wildcard _ _, .wildcard => pure [.wildcard]
  | .integerLiteral _ literal, .integerLiteral source resolution => do
      unless literal.value = source do throw invalid
      pure [.integerLiteral source resolution]
  | .binder _ name, .binder binder => do
      unless binder.name = name do throw invalid
      pure [.binder binder]
  | .constructor _ _ _ name count, .constructor instantiation instructions => do
      let signatures := context.signatures.dataTypes.filter (fun signature =>
        decide (signature.id = instantiation.constructor.dataType))
      let [signature] := signatures | throw invalid
      let [constructor] := signature.constructors.filter (fun constructor =>
        decide (constructor.id = instantiation.constructor)) | throw invalid
      unless constructor.name = name do throw invalid
      pure (.constructor instantiation count :: instructions)
  | .tuple _ count, .tuple instructions => pure (.tuple count :: instructions)
  | .group _ inner, resolution => rootInstructions context inner resolution
  | _, _ => throw invalid

structure CertifiedPattern (definitions : Core.DataEnvironment) where
  pattern : Pattern
  typed : Core.HasType [] pattern.matcher pattern.functionType definitions
  deriving Repr

/-- Authenticates the retained source root, complete nested prefix stream,
source-order requirements, lexical binder metadata, and generated Core type. -/
def compilePattern (context : Context) (fuel : Nat) (source : TypedSource) (scope : Scope)
    (site : StatementId) (span : Syntax.SourceSpan) (expected : TypeSystem.Ty)
    (pattern : TypedMatchPattern) : Except Error (CertifiedPattern context.checked.catalog.definitions) := do
  if site.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner site.occurrence.owner)
  unless pattern.type = expected do throw invalid
  let instructions ← rootInstructions context pattern.source pattern.resolution
  let (compiled, rest) ← compileOne context source site span scope fuel expected instructions
  unless rest.isEmpty && compiled.requirements = pattern.requirements do throw invalid
  unless (compiled.bindings.map (·.1.id)).Nodup && (compiled.bindings.map (·.1.name)).Nodup do throw invalid
  if accepted : Core.infer? [] compiled.matcher context.checked.catalog.definitions = some compiled.functionType then
    pure ⟨compiled, Core.infer_sound accepted⟩
  else throw invalid

/-- The raw successful bundle remains after the newly allocated source cells.
`body` already has those source cells in scope. -/
def bindArm (bindings : List (TypedBinder × Core.Ty)) (outputType : Core.Ty) (body : Core.Expr) : Core.Expr :=
  let types := bindings.map Prod.snd
  bindings.zipIdx.foldr (fun (binding, index) continuation =>
    Core.LocalSequence.letInitialized outputType binding.2
      (Core.LanguageResult.success (SourceCoreDataExpressions.projectPacked index types (.var index))) continuation)
    (body.weakenAt bindings.length)

/-- Select an arm from a pure matcher result. Both continuations are lowered
before inserting the matcher-result binder. -/
def attempt (pattern : Pattern) (outputType : Core.Ty) (body next : Core.Expr) : Core.Expr :=
  .caseE (.apply pattern.matcher (.var 0)) (next.weakenAt 0)
    (bindArm pattern.bindings outputType (body.weakenAt pattern.bindings.length))

theorem wildcard_evaluates (environment : Core.Environment) (store : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    Core.Evaluates (value :: environment) store
      (.apply (.lambda type (.sum .unit .unit) (.inRight .unit .unit)) (.var 0))
      (.inRight .unit .unit) store :=
  .apply .lambda (.var rfl) (.inRight .unit)

theorem binder_evaluates (environment : Core.Environment) (store : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    Core.Evaluates (value :: environment) store
      (.apply (.lambda type (.sum .unit type) (.inRight .unit (.var 0))) (.var 0))
      (.inRight .unit value) store :=
  .apply .lambda (.var rfl) (.inRight (.var rfl))

/-- A failed pattern returns immediately. No binding allocator, later pattern,
or selected-arm body occurs among the premises. -/
theorem matchChildren_failure {environment : Core.Environment} {store : Core.Store}
    {pattern : Pattern} {value : Core.Expr} (outputType : Core.Ty)
    (rest : List Pattern) (values accumulated : List Core.Expr)
    (failed : Core.Evaluates environment store (.apply pattern.matcher value)
      (.inLeft (bundleType pattern.bindingTypes) .unit) store) :
    Core.Evaluates environment store
      (matchChildren outputType (pattern :: rest) (value :: values) accumulated)
      (.inLeft outputType .unit) store :=
  .caseLeft failed (.inLeft .unit)

/-- Failure preserves the exact matcher store; only the next case executes. -/
theorem attempt_failure {environment : Core.Environment} {store finalStore : Core.Store}
    {pattern : Pattern} {outputType : Core.Ty} {body next : Core.Expr} {result : Core.Value}
    (failed : Core.Evaluates environment store (.apply pattern.matcher (.var 0))
      (.inLeft (bundleType pattern.bindingTypes) .unit) store)
    (nextEvaluation : Core.Evaluates (.unit :: environment) store (next.weakenAt 0) result finalStore) :
    Core.Evaluates environment store (attempt pattern outputType body next) result finalStore :=
  .caseLeft failed nextEvaluation

/-- Success executes the source-order binding allocator once and skips every
later arm. The body premise exposes the actual bundle and store boundary. -/
theorem attempt_success {environment : Core.Environment} {store finalStore : Core.Store}
    {pattern : Pattern} {outputType : Core.Ty} {body next : Core.Expr} {bindings result : Core.Value}
    (matched : Core.Evaluates environment store (.apply pattern.matcher (.var 0))
      (.inRight .unit bindings) store)
    (bodyEvaluation : Core.Evaluates (bindings :: environment) store
      (bindArm pattern.bindings outputType (body.weakenAt pattern.bindings.length)) result finalStore) :
    Core.Evaluates environment store (attempt pattern outputType body next) result finalStore :=
  .caseRight matched bodyEvaluation

/-- Lower one match statement to the caller's flow envelope. A surrounding
sequence discharges the match scope before evaluating its continuation. -/
def lowerWithReasons (context : Context) (lowerExpression : ExpressionLowerer) (lowerBody : BodyLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (id : StatementId)
    (resolution : MatchResolution) (resultType : Core.Ty) (reasonAt : ExpressionId → Core.Word)
    (internalReason : Core.Word) : Except Error Core.Expr := do
  match fuel with
  | 0 => throw (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1 =>
    let (node, statementType) ← SourceCoreGeneralTypes.readStatement context.checked source id
    unless statementType = .unit || statementType = resultType do throw invalid
    unless node.form = .matchWith resolution do throw invalid
    unless resolution.requirements = resolution.cases.flatMap (·.pattern.requirements) do throw invalid
    if resolution.hiddenScrutinee.owner ≠ source.owner then
      throw (.ownerMismatch source.owner resolution.hiddenScrutinee.owner)
    if scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) then
      throw (.duplicateBinding resolution.hiddenScrutinee)
    if resolution.scrutinee.occurrence.owner ≠ source.owner then
      throw (.ownerMismatch source.owner resolution.scrutinee.occurrence.owner)
    let scrutineeNode ← match source.lookupExpression? resolution.scrutinee with
      | some node => pure node
      | none => throw (.missingExpression resolution.scrutinee)
    let type ← projected context source scrutineeNode.type
    let scrutinee ← lowerExpression fuel source scope resolution.scrutinee reasonAt
    SourceCoreBasic.ensureType (.occurrence resolution.scrutinee.occurrence) type scrutinee.type
    let hiddenScope := (resolution.hiddenScrutinee, type) :: scope
    let arms ← resolution.cases.mapM fun arm => do
      let pattern ← compilePattern context fuel source hiddenScope id arm.span scrutineeNode.type arm.pattern
      let armScope := pattern.pattern.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) hiddenScope
      let body ← lowerBody fuel source armScope arm.body resultType reasonAt internalReason
      pure (pattern.pattern, body)
    let fallback ← match resolution.defaultBody with
      | none => pure (Core.LocalLoop.fallthrough resultType)
      | some body => lowerBody fuel source hiddenScope body resultType reasonAt internalReason
    let controlType := Core.LocalLoop.controlType resultType
    let branches := arms.foldr (fun (pattern, body) next =>
      attempt pattern controlType body next) (fallback.weakenAt 0)
    pure (Core.LocalSequence.letInitialized controlType type scrutinee.expression
      (.caseE (.loadCell (.var 0)) (Core.LanguageResult.failure controlType (.word internalReason)) branches))

structure Certified (context : Context) (environment : Core.Context) (resultType : Core.Ty) where
  expression : Core.Expr
  typed : Core.HasType environment expression (Core.LocalLoop.resultType resultType) context.checked.catalog.definitions
  deriving Repr

def lowerChecked (context : Context) (lowerExpression : ExpressionLowerer) (lowerBody : BodyLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (environment : Core.Context) (id : StatementId)
    (resolution : MatchResolution) (resultType : Core.Ty) (reasonAt : ExpressionId → Core.Word)
    (internalReason : Core.Word) : Except Error (Certified context environment resultType) := do
  let expression ← lowerWithReasons context lowerExpression lowerBody fuel source scope id resolution resultType reasonAt internalReason
  if accepted : Core.infer? environment expression context.checked.catalog.definitions = some (Core.LocalLoop.resultType resultType) then
    pure ⟨expression, Core.infer_sound accepted⟩
  else throw invalid

end Solcore.Frontend.SourceCoreDataMatches
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreEvidence
/-! Closed evidence is authenticated against the prepared source plan before
being erased from Core function signatures. Retained operator and coercion
methods use the same cached global cells as ordinary calls. This pass generates
Core code; no source evaluator is used at invocation. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreEvidence

open SourceInference TypeSystem
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev Context := SourceCoreFunctions.Context
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev Lowered := SourceCoreBasic.LoweredExpr
abbrev Child := SourceCoreFunctions.ExpressionLowerer
abbrev Key := SourceSpecialization.SpecializationKey

/-- Representation profiles project source metadata while this traversal owns
evidence authentication, call order and coercion code. Whole-entry checking
certifies the chosen representation's actual definitions. -/
abbrev Projector := SourceCoreElaboration.ErrorSite → Ty → Except Error Core.Ty

private def project (projectType : Projector) (node : ExpressionNode) (type : Ty) : Except Error Core.Ty :=
  projectType (.occurrence node.id.occurrence) type

private def signature (projectType : Projector) (context : Context) (node : ExpressionNode) (key : Key)
    (callables : SourceCoreFunctions.CallablePolicy) :
    Except Error (Nat × SourceCoreCalls.Signature) := do
  let actual ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
  if !callables.allowStaged &&
      (actual.function.returnComptime || actual.function.typedBody.inputs.any (·.comptime)) then
    throw (.unsupportedExpression node.id node.form)
  let (parameter, result) ← match actual.function.type with
    | .function parameter result => pure (parameter, result)
    | _ => throw (.callPreparation (.invalidFunctionType key actual.function.type))
  let (stored, index) ← match context.globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
    | [entry] => pure entry
    | [] => throw (.callPreparation (.missingSpecialization key))
    | entries => throw (.callPreparation (.duplicateSpecialization key entries.length))
  SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.parameterType (← project projectType node parameter)
  SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.resultType (← project projectType node result)
  pure (index, stored)

private def invoke (projectType : Projector) (context : Context) (scope : Scope) (node : ExpressionNode)
    (key : Key) (arguments : Lowered) (callables : SourceCoreFunctions.CallablePolicy) :
    Except Error Lowered := do
  let (index, selected) ← signature projectType context node key callables
  SourceCoreBasic.ensureType (.occurrence node.id.occurrence) selected.parameterType arguments.type
  pure ⟨selected.resultType, SourceCoreCalls.call selected
    (scope.length + context.administrativePrefix + index) arguments.expression context.internalReason⟩

private def methodKey (context : Context) (node : ExpressionNode)
    (method : ExecutableImplMethods.CheckedMethod) : Except Error Key :=
  (SourceCompilationPlan.exactCallKey context.plan context.owner node.id method.specialized.key)
    |>.mapError SourceCoreBasic.Error.callPreparation

def applyCoercions (program : CheckedProgram) (projectType : Projector) (context : Context)
    (caller : SourceSpecialization.SpecializedFunction) (available : SourceCompilationPlan.EvidenceEnvironment)
    (scope : Scope) (node : ExpressionNode) (callables : SourceCoreFunctions.CallablePolicy) :
    Lowered → List CoercionStep → Except Error Lowered
  | value, [] => pure value
  | value, step :: rest => do
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) (← project projectType node step.source) value.type
      let method ← (SourceCompilationPlan.checkedCoercionMethod program caller node available step)
        |>.mapError SourceCoreBasic.Error.callPreparation
      discard <| (SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method)
        |>.mapError SourceCoreBasic.Error.callPreparation
      let key ← methodKey context node method
      let result ← invoke projectType context scope node key value callables
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) (← project projectType node step.target) result.type
      applyCoercions program projectType context caller available scope node callables result rest

def withNode (source : TypedSource) (node : ExpressionNode) : TypedSource :=
  { source with nodes := source.nodes.map fun
      | .expression old => if old.id = node.id then .expression node else .expression old
      | .statement old => .statement old }

/-- The prepared plan authenticates closed evidence and selected helper edges.
Each special occurrence rechecks its ledger and endpoint types before emitting
ordinary Core calls, including output coercions and indirect argument coercions. -/
def lowerWithProjector (program : CheckedProgram) (projectType : Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : Context) (child : Child)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Core.Word) (callables : SourceCoreFunctions.CallablePolicy := {}) :
    Except Error (Option Lowered) := do
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (.missingExpression id)
  let hasIndirectCoercions := match node.form with
    | .call _ _ (.indirect metadata) => !metadata.argumentCoercions.isEmpty
    | _ => false
  let ordinary ← match node.form with
    | .call _ _ (.declaration _) | .reference _ (.declaration _) => pure []
    | _ => match SourceCompilationPlan.ordinaryOwnedRequirements? node with
        | some requirements => pure requirements
        | none => throw (.callPreparation (.unsupportedRequirements node.requirements))
  let isNativeLiteral := match node.form with | .integerLiteral .. => true | _ => false
  -- A method caller can own authenticated closed assumptions even when this
  -- particular helper call/reference requires no dictionary of its own.
  let authenticatesCaller := !caller.assumptions.isEmpty && (match node.form with
    | .call _ _ (.declaration _) | .reference _ (.declaration _) => true
    | _ => false)
  if node.coercions.isEmpty && !hasIndirectCoercions && (node.requirements.isEmpty || isNativeLiteral) &&
      !authenticatesCaller then
    return none
  unless node.hasValidCoercionPath do throw (.coercionsPresent id)
  if caller.key ≠ context.owner then throw (.ownerMismatch context.owner.declaration caller.key.declaration)
  let available ← (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
    |>.mapError SourceCoreBasic.Error.callPreparation
  let raw := {node with type := node.rawType, requirements := ordinary, coercions := []}
  let result ← match node.form with
    | .call callee arguments (.declaration instantiation) => do
        (SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let evidence ← (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let target ← (SourceCompilationPlan.exactInstantiationKey context.plan instantiation).mapError SourceCoreBasic.Error.callPreparation
        let key ← (SourceCompilationPlan.exactCallKey context.plan context.owner id target).mapError SourceCoreBasic.Error.callPreparation
        let selected ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
        (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key selected.assumptions evidence)
          |>.mapError SourceCoreBasic.Error.callPreparation
        if arguments.length ≠ selected.function.typedBody.inputs.length then
          throw (.callPreparation (.argumentArityMismatch selected.function.typedBody.inputs.length arguments.length))
        let arguments ← arguments.mapM fun argument => child fuel source scope argument reasonAt
        invoke projectType context scope raw key (SourceCoreCalls.packArguments arguments) callables
    | .reference _ (.declaration instantiation) => do
        let evidence ← (SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let target ← (SourceCompilationPlan.exactInstantiationKey context.plan instantiation).mapError SourceCoreBasic.Error.callPreparation
        let key ← (SourceCompilationPlan.exactReferenceKey context.plan context.owner id target).mapError SourceCoreBasic.Error.callPreparation
        let selected ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
        (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key selected.assumptions evidence)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let (index, stored) ← signature projectType context raw key callables
        let identity ← match Core.Word.ofNat? (index + 1) with
          | some identity => pure identity
          | none => throw (.unsupportedExpression id node.form)
        let expression ← callables.decorateCallable context source node (.named key)
          stored.parameterType stored.resultType
          (SourceCoreFunctions.namedReference stored (scope.length + context.administrativePrefix + index)
            identity context.internalReason)
        pure ⟨callables.functionType stored.parameterType stored.resultType, expression⟩
    | .call callee arguments (.indirect metadata) => do
        (SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let callee ← child fuel source scope callee reasonAt
        let arguments ← arguments.mapM fun argument => child fuel source scope argument reasonAt
        let packed ← applyCoercions program projectType context caller available scope node callables
          (SourceCoreCalls.packArguments arguments) metadata.argumentCoercions
        let resultType ← project projectType node node.rawType
        let parameterType ← project projectType node metadata.argumentTypeAfterCoercion
        SourceCoreBasic.ensureType (.occurrence id.occurrence) parameterType packed.type
        SourceCoreBasic.ensureType (.occurrence id.occurrence)
          (callables.functionType parameterType resultType) callee.type
        let expression ← callables.callCallable context source node resultType callee.expression packed.expression
        pure ⟨resultType, expression⟩
    | .unary operator operand => do
        if ordinary.isEmpty then child fuel (withNode source raw) scope id reasonAt
        else
          let selected ← (SourceCompilationPlan.checkedUnaryOperatorMethod program caller raw available operator)
            |>.mapError SourceCoreBasic.Error.callPreparation
          discard <| (SourceCompilationPlan.operatorMethodRuntimeEvidence program caller raw selected)
            |>.mapError SourceCoreBasic.Error.callPreparation
          let key ← methodKey context raw selected.method
          let operand ← child fuel source scope operand reasonAt
          invoke projectType context scope raw key operand callables
    | .binary left operator right => do
        if ordinary.isEmpty then child fuel (withNode source raw) scope id reasonAt
        else
          let selected ← (SourceCompilationPlan.checkedBinaryOperatorMethod program caller raw available operator)
            |>.mapError SourceCoreBasic.Error.callPreparation
          discard <| (SourceCompilationPlan.operatorMethodRuntimeEvidence program caller raw selected)
            |>.mapError SourceCoreBasic.Error.callPreparation
          let key ← methodKey context raw selected.method
          let arguments ← [left, right].mapM fun argument => child fuel source scope argument reasonAt
          invoke projectType context scope raw key (SourceCoreCalls.packArguments arguments) callables
    | _ => child fuel (withNode source raw) scope id reasonAt
  SourceCoreBasic.ensureType (.occurrence id.occurrence) (← project projectType node node.rawType) result.type
  let result ← applyCoercions program projectType context caller available scope node callables result node.coercions
  SourceCoreBasic.ensureType (.occurrence id.occurrence) (← project projectType node node.type) result.type
  pure (some result)

/-- Compatibility entry using the strict catalog's own projection. -/
def lowerWithCaller (program : CheckedProgram) (checked : Checked)
    (caller : SourceSpecialization.SpecializedFunction) (context : Context) (child : Child)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Core.Word) (callables : SourceCoreFunctions.CallablePolicy := {}) :
    Except Error (Option Lowered) :=
  lowerWithProjector program (SourceCoreGeneralTypes.projectType checked) caller context child fuel source scope id reasonAt callables

/-- Ordinary occurrences use the exact authenticated plan caller. Contextual
local lambdas supply an authenticated rebinding of the same caller ledger to
`lowerWithCaller`; helper edges and selected globals still use the same plan. -/
def lower (program : CheckedProgram) (checked : Checked) (context : Context) (child : Child)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Core.Word) (callables : SourceCoreFunctions.CallablePolicy := {}) :
    Except Error (Option Lowered) := do
  let caller ← (SourceCompilationPlan.exactSpecialization context.plan context.owner)
    |>.mapError SourceCoreBasic.Error.callPreparation
  lowerWithCaller program checked caller context child fuel source scope id reasonAt callables

end Solcore.Frontend.SourceCoreEvidence
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreGeneralFunctions
/-! Closed function instances and catalog data share ordinary Core execution.
Preparation authenticates the plan, compiles reachable closures once, and checks
each assembled entry against the actual recursive data definitions. This slice
supports finite contextual local-lambda bundles and structural place assignments. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreGeneralFunctions

open SourceInference
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Signature := SourceCoreCalls.Signature

inductive Error where
  | plan (error : SourceCompilationPlan.Error)
  | catalog (error : SourceCoreDataCatalog.Error)
  | lowering (error : SourceCoreBasic.Error)
  | diagnostics (error : SourceCoreDataPlaceFaultSites.Error)
  | localInstances (error : SourceCoreLocalPolymorphism.Error)
  | callableContracts (error : SourceCoreStageCodebook.Error)
  | callableDiagnostics (error : SourceCoreCallableFaultSites.Error)
  | invalidFunctionType (key : Key)
  | resultMetadataMismatch (key : Key)
  | assumptionsUnsupported (key : Key)
  | stagedResultUnsupported (key : Key)
  | missingGlobal (key : Key)
  | missingDiagnostics (key : Key)
  | expectedStatementRoot (id : ExpressionId)
  deriving Repr

structure Function where
  specialized : SourceSpecialization.SpecializedFunction
  signature : Signature
  inputs : List (TypedBinder × Core.Ty)
  deriving Repr

/-- Representation hooks retain the common contextual traversal, evidence
validation and control flow. The enclosing artifact checks generated code under
its actual data definitions, including any source-allocation marker suffix. -/
structure Representation where
  expressions : SourceCoreFunctions.Policy
  allowStaged : Bool := false
  loops : List SolvedRequirement → SourceCoreAssignmentFaultSites.Table →
    SourceCoreDataPlaceFaultSites.Program → Key → SourceCoreFunctions.ExpressionLowerer →
    SourceCoreLoops.Policy
  rawLambdaBodyAt : Key → TypeSystem.Substitution → SourceCoreFunctions.RawLambdaBodyHook :=
    fun _ _ => expressions.rawLambdaBody
  rawLambdaExpressionAt : Key → TypeSystem.Substitution → SourceCoreFunctions.RawLambdaExpressionHook :=
    fun _ _ => expressions.rawLambdaExpression
  /-- The assembled checker validates this hook after all named parameter
  cells have been bound. Its body still has the original raw argument slot. -/
  rawNamedBody : Function → Core.Expr → Except SourceCoreBasic.Error Core.Expr :=
    fun _ body => pure body
  /-- Preserve per-occurrence metadata after selecting a generalized local
  bundle. This does not change its representation type or select evidence. -/
  localReadView : Key → TypeSystem.Substitution → TypedSource → SourceCoreBasic.Scope →
    ExpressionId → SourceCoreBasic.LoweredExpr → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr :=
    fun _ _ _ _ _ lowered => pure lowered
  allocatorAt : Key → TypeSystem.Substitution → Option SourceCoreSourceCells.Allocator :=
    fun _ _ => expressions.sourceCells
  loopsWithSourceCells : Option SourceCoreSourceCells.Allocator →
    List SolvedRequirement → SourceCoreAssignmentFaultSites.Table →
    SourceCoreDataPlaceFaultSites.Program → Key → SourceCoreFunctions.ExpressionLowerer →
    SourceCoreLoops.Policy := fun cells solved assignments diagnostics owner expression =>
      {loops solved assignments diagnostics owner expression with sourceCells := cells}

def Representation.atContext (representation : Representation) (owner : Key)
    (active : TypeSystem.Substitution) : Representation :=
  {representation with expressions := {representation.expressions with
    sourceCells := representation.allocatorAt owner active
    rawLambdaBody := representation.rawLambdaBodyAt owner active
    rawLambdaExpression := representation.rawLambdaExpressionAt owner active}}

private def prepareInputs (representation : Representation) (source : TypedSource) :
    SourceCoreBasic.Scope → List TypedBinder → Except Error (List (TypedBinder × Core.Ty))
  | _, [] => pure []
  | scope, binder :: rest => do
      let type ← (representation.expressions.lowerBinder source scope binder).mapError Error.lowering
      let remaining ← prepareInputs representation source ((binder.id, type) :: scope) rest
      pure ((binder, type) :: remaining)

def prepareFunctionWithRepresentation (program : CheckedProgram) (representation : Representation) (specialized : SourceSpecialization.SpecializedFunction) :
    Except Error Function := do
  let function := specialized.function
  discard <| (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program specialized.key specialized.assumptions)
    |>.mapError Error.plan
  if function.returnComptime && !representation.allowStaged then throw (.stagedResultUnsupported specialized.key)
  let (parameter, result) ← match function.type with
    | .function parameter result => pure (parameter, result)
    | _ => throw (.invalidFunctionType specialized.key)
  if result ≠ function.inferredBodyType then throw (.resultMetadataMismatch specialized.key)
  let site := SourceCoreElaboration.ErrorSite.declaration specialized.key.declaration
  let parameterType ← (representation.expressions.projectType site parameter).mapError Error.lowering
  let resultType ← (representation.expressions.projectType site result).mapError Error.lowering
  let inputs ← prepareInputs representation function.typedBody [] function.typedBody.inputs
  pure { specialized, inputs, signature := { key := specialized.key, parameterType, resultType } }

/-- The strict catalog uses the same compiler entry as other representations. -/
def strictRepresentation (checked : Checked) (signatures : ProgramSignatures) : Representation := {
  expressions := SourceCoreGeneralTypes.policy checked signatures
  allowStaged := checked.catalog.callableContracts
  loops := fun solvedRequirements assignments diagnostics owner expression => {
      lowerExpression := expression
      readStatement := SourceCoreGeneralTypes.readStatement checked
      lowerBinder := SourceCoreGeneralTypes.lowerBinder checked
      lowerAssignment := SourceCoreGeneralTypes.lowerAssignment checked
      lowerMatch := some (SourceCoreDataMatches.lowerWithReasons
        { checked, signatures, solvedRequirements })
      assignEqual := some fun expression fuel source scope site assignment rhs output next reasonAt =>
        SourceCoreDataPlaces.lower checked signatures expression fuel source scope site assignment .equal
          (some rhs) output next reasonAt
          (diagnostics.placeReason owner site assignment.target.root none) Core.Word.zero
          (fun type => diagnostics.placeReason owner site assignment.target.root (some type))
      assignValue := some fun expression fuel source scope site assignment operator rhs output next reasonAt =>
        SourceCoreDataPlaces.lower checked signatures expression fuel source scope site assignment operator
          (some rhs) output next reasonAt
          (diagnostics.placeReason owner site assignment.target.root none)
          (assignments.reasonAt site assignment.target.root (.value operator))
          (fun type => diagnostics.placeReason owner site assignment.target.root (some type))
      assignBitNotWithExpression := some fun expression fuel source scope site assignment output next reasonAt =>
        SourceCoreDataPlaces.lower checked signatures expression fuel source scope site assignment .equal
          none output next reasonAt
          (diagnostics.placeReason owner site assignment.target.root none)
          (assignments.reasonAt site assignment.target.root .bitNot)
          (fun type => diagnostics.placeReason owner site assignment.target.root (some type))
    }
}

def bodyLowererWithRepresentation (representation : Representation)
    (solvedRequirements : List SolvedRequirement) (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (owner : Key)
    (lowerBinder : TypedSource → SourceCoreBasic.Scope → TypedBinder → Except SourceCoreBasic.Error Core.Ty :=
      representation.expressions.lowerBinder) : SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {
      representation.loopsWithSourceCells representation.expressions.sourceCells
        solvedRequirements assignments diagnostics owner expression with
      sourceCells := representation.expressions.sourceCells
      lowerBinder
    } fuel source scope statements result reasonAt fellThrough escaped

/-- Existing strict callers retain their catalog and diagnostics API. -/
def bodyLowerer (checked : Checked) (signatures : ProgramSignatures)
    (solvedRequirements : List SolvedRequirement) (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (owner : Key)
    (lowerBinder : TypedSource → SourceCoreBasic.Scope → TypedBinder → Except SourceCoreBasic.Error Core.Ty :=
      SourceCoreGeneralTypes.lowerBinder checked) : SourceCoreFunctions.BodyLowerer :=
  bodyLowererWithRepresentation (strictRepresentation checked signatures)
    solvedRequirements assignments diagnostics owner lowerBinder

private def localError (id : ExpressionId) (node : ExpressionNode)
    (error : SourceCoreLocalPolymorphism.Error) : SourceCoreBasic.Error :=
  match error with
  | .metadata error => error
  | _ => .unsupportedExpression id node.form

/-- The production binder policy, retained in static receipts connecting an
accepted function body to its exact contextual statement traversal. -/
def contextualBinder (representation : Representation) (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : Key) (active : TypeSystem.Substitution) (source : TypedSource)
    (scope : SourceCoreBasic.Scope) (binder : TypedBinder) : Except SourceCoreBasic.Error Core.Ty :=
  if binder.scheme.quantified.isEmpty then representation.expressions.lowerBinder source scope binder
  else (SourceCoreLocalPolymorphism.lowerBinder locals owner active source scope binder).mapError fun
    | .metadata error => error
    | _ => .polymorphicBinding binder.id

def contextualSource (program : CheckedProgram) (plan : Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : Key)
    (parent : Option SourceCoreLocalEvidence.Prepared) (source : TypedSource) (id : ExpressionId) :
    Except SourceCoreBasic.Error TypedSource := do
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (.missingExpression id)
  match node.form with
  | .reference _ (.local binder) =>
      if locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) then
        let binding ← (locals.binding owner binder).mapError (localError id node)
        (SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent source id).mapError fun
          | .plan error => .callPreparation error
          | .missingExpression missing => .missingExpression missing
          | _ => .unsupportedExpression id node.form
      else pure source
  | _ => pure source

/-- Authenticated callable metadata shared by the generated representation
and every indirect callsite in one prepared artifact. -/
structure CallableContext where
  table : SourceCoreStageCodebook.Table
  diagnostics : SourceCoreCallableFaultSites.Program

/-- The callable representation used by the general compiler. Keeping this
policy visible lets lowering proofs authenticate the actual emitted wrapper. -/
def callablePolicy (native : Option CallableContext) (active : TypeSystem.Substitution) :
    SourceCoreFunctions.CallablePolicy :=
  match native with
  | none => {}
  | some native => {
      functionType := Core.CallableContract.functionType
      allowStaged := true
      decorateCallable := fun context _ node origin parameter result raw => do
        let origin := match origin with
          | .named key => SourceCoreStageCodebook.Origin.named key
          | .lambda id => .lambda context.owner id active
          | .builtin function => .builtin function
        let descriptor ← (SourceCoreCallableContracts.descriptor native.table origin).mapError fun _ =>
          SourceCoreBasic.Error.unsupportedExpression node.id node.form
        pure (match raw with
          | .inRight .word value => Core.LanguageResult.success (descriptor.wrap value)
          | _ => Core.LanguageResult.bind (Core.CallableContract.functionType parameter result) raw
              (Core.LanguageResult.success (descriptor.wrap (.var 0))))
      callCallable := fun context _ node result callee arguments => do
        match node.form with
        | .call _ _ (.indirect _) =>
            let site ← (SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
              native.diagnostics.reasonAt).mapError fun _ =>
                SourceCoreBasic.Error.unsupportedExpression node.id node.form
            pure (site.lower native.diagnostics.unknown result callee arguments)
        | .call _ _ (.builtinFunction function) =>
            let descriptor ← (SourceCoreCallableContracts.descriptor native.table (.builtin function)).mapError fun _ =>
              SourceCoreBasic.Error.unsupportedExpression node.id node.form
            pure (Core.CallableContract.call [⟨descriptor.id, none, none⟩]
              native.diagnostics.unknown result callee arguments)
        | _ => throw (.unsupportedExpression node.id node.form) }

/-- Contextual local instances re-enter the shared expression traversal with
concrete metadata. Every closure captures the same lexical references; the
bundle is constructed before the generalized binding's cell is allocated. -/
def lowerContextualExpression (program : CheckedProgram) (representation : Representation)
    (signatures : ProgramSignatures) (locals : SourceCoreLocalPolymorphism.Catalog)
    (candidateParents : List SourceCoreLocalEvidence.Prepared)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (context : SourceCoreFunctions.Context)
    (native : Option CallableContext)
    (parent : Option SourceCoreLocalEvidence.Prepared) (skipInitializer : Option ExpressionId) :
    SourceCoreFunctions.ExpressionLowerer
  | 0, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, source, scope, id, reasonAt => do
      let active := parent.map SourceCoreLocalEvidence.Prepared.substitution |>.getD []
      let representation := representation.atContext context.owner active
      let callables := callablePolicy native active
      let caller ← match parent with
        | some prepared => pure prepared.caller
        | none => (SourceCompilationPlan.exactSpecialization context.plan context.owner)
            |>.mapError SourceCoreBasic.Error.callPreparation
      let bind := contextualBinder representation locals context.owner active
      let lowerBody := bodyLowererWithRepresentation representation context.solvedRequirements assignments diagnostics context.owner bind
      let policy := { representation.expressions with
        callables
        snapshotLambda := fun lambda => skipInitializer ≠ some lambda
        lowerBinder := bind
        readExpression := fun source id => do
          let source ← contextualSource program context.plan locals context.owner parent source id
          representation.expressions.readExpression source id
        lowerSpecial? := some fun current child budget source scope id reasonAt => do
          let source ← contextualSource program current.plan locals current.owner parent source id
          let node ← match source.lookupExpression? id with
            | some node => pure node
            | none => throw (.missingExpression id)
          let initialized := locals.bindings.find? fun binding =>
            decide (binding.caller = current.owner ∧ binding.initializer = id)
          if let some initialized := initialized.filter (fun _ => skipInitializer ≠ some id) then
            let binding ← (locals.binding current.owner initialized.binder.id).mapError (localError id node)
            let lowered ← (SourceCoreLocalPolymorphism.lowerInitializer binding active fun candidate => do
              let emission ← (SourceCoreLocalEvidence.prepareForEmission program current.plan candidate parent candidateParents).mapError fun _ =>
                SourceCoreLocalPolymorphism.Error.initializerMetadataMismatch id
              let prepared := emission.prepared
              let childContext := { current with solvedRequirements := prepared.caller.function.solvedRequirements }
              let lowered ← (lowerContextualExpression program representation signatures locals candidateParents assignments diagnostics childContext native
                (some prepared) (some id) (min budget fuel) prepared.source scope id reasonAt)
                |>.mapError SourceCoreLocalPolymorphism.Error.metadata
              (SourceCoreBasic.ensureType (.occurrence id.occurrence) candidate.type lowered.type)
                |>.mapError SourceCoreLocalPolymorphism.Error.metadata
              match lowered.expression with
              | .inRight .word closure => pure closure
              | _ => throw (.initializerMetadataMismatch id)).mapError (localError id node)
            return some lowered
          let evidence ← SourceCoreEvidence.lowerWithProjector program representation.expressions.projectType caller current child budget source scope id reasonAt callables
          if let some lowered := evidence then return some lowered
          match node.form with
          | .reference _ (.local binder) =>
              if locals.bindings.any (fun binding => decide (binding.caller = current.owner ∧ binding.binder.id = binder)) then
                let lowered ← (SourceCoreLocalPolymorphism.lowerRead locals current.owner active source scope id (reasonAt id))
                  |>.mapError (localError id node)
                let viewed ← representation.localReadView current.owner active source scope id lowered
                SourceCoreBasic.ensureType (.occurrence id.occurrence) lowered.type viewed.type
                return some viewed
              else return none
          | _ => return none }
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) context source scope id reasonAt
termination_by fuel => fuel

def compileClosureWithRepresentation (program : CheckedProgram) (representation : Representation) (signatures : ProgramSignatures) (plan : Plan)
    (globals : List Signature) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (locals : SourceCoreLocalPolymorphism.Catalog) (native : Option CallableContext)
    (fuel : Nat) (function : Function) : Except Error Core.Expr := do
  let representation := representation.atContext function.signature.key []
  let source := function.specialized.function.typedBody
  let candidateParents ← (SourceCoreStageCodebook.prepareContexts program plan
    (locals.bindings.flatMap (·.instances))).mapError Error.callableContracts
  let own ← match diagnostics.base.find? function.signature.key with
    | some own => pure own
    | none => throw (.missingDiagnostics function.signature.key)
  let statements ← source.roots.mapM fun
    | .statement id => pure id
    | .expression id => throw (.expectedStatementRoot id)
  let context : SourceCoreFunctions.Context := {
    plan, globals, owner := function.signature.key, administrativePrefix := 1
    solvedRequirements := function.specialized.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let lowerBody := bodyLowererWithRepresentation representation function.specialized.function.solvedRequirements own.assignments
    diagnostics function.signature.key (contextualBinder representation locals function.signature.key [])
  let body ← (lowerBody
    (lowerContextualExpression program representation signatures locals candidateParents own.assignments diagnostics context native none none)
    fuel source (function.inputs.reverse.map (fun (binder, type) => (binder.id, type))) statements
    function.signature.resultType (diagnostics.reasonAt function.signature.key)
    own.fellThroughReason own.table.escapedReason).mapError Error.lowering
  let body ← match representation.expressions.sourceCells with
    | none => pure (SourceCoreFunctions.bindParameters function.inputs function.signature.resultType body)
    | some allocate => (SourceCoreSourceCells.bindParameters allocate source [] function.inputs
        function.signature.resultType SourceCoreFunctions.argumentProjection body).mapError Error.lowering
  let body ← (representation.rawNamedBody function body).mapError Error.lowering
  pure (.lambda function.signature.parameterType (Core.LanguageResult.resultType function.signature.resultType) body)

def assembleCall (globals : List Signature) (functions : List Function) (closures : List Core.Expr)
    (key : Key) (arguments : SourceCoreBasic.LoweredExpr) : Except Error Core.Expr := do
  let (function, index) ← match functions.zipIdx.find? (fun entry => decide (entry.1.signature.key = key)) with
    | some found => pure found
    | none => throw (.missingGlobal key)
  (SourceCoreBasic.ensureType (.declaration function.signature.key.declaration)
    function.signature.parameterType arguments.type).mapError Error.lowering
  let invoked := SourceCoreCalls.call function.signature index arguments.expression Core.Word.zero
  pure (SourceCoreRecursiveEntry.allocateGlobals globals.reverse
    (SourceCoreRecursiveEntry.installFunctions closures invoked))

private def assemble (globals : List Signature) (functions : List Function) (closures : List Core.Expr)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) {checked : Checked}
    (request : SourceCoreGeneralEntry.BodyRequest checked) : Except Error SourceCoreGeneralEntry.LoweredBody := do
  let arguments := SourceCoreCalls.packArguments (request.inputs.zipIdx.map fun (input, index) =>
    ⟨input.type, Core.OptionalCell.read input.type
      (.var (globals.length + (request.inputs.length - 1 - index))) Core.Word.zero⟩)
  let expression ← assembleCall globals functions closures request.specialized.key arguments
  pure {
    expression
    faultSites := diagnostics.rootTable
  }

/-- A supplied catalog is checked before lowering; the entry checker certifies
the assembled closures, helpers, and seed call under those exact definitions. -/
def prepareWithCatalog (program : CheckedProgram) (plan : Plan) (checked : Checked) (fuel : Nat) :
    Except (SourceCoreGeneralEntry.CompileError Error) (SourceCoreGeneralEntry.PreparedProgram checked) := do
  let plan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError
    (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.plan)
  let locals ← (SourceCoreLocalPolymorphism.prepare checked plan).mapError
    (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.localInstances)
  let representation := strictRepresentation checked program.signatures
  let functions ← (plan.specializations.reverse.mapM (prepareFunctionWithRepresentation program representation)).mapError
    SourceCoreGeneralEntry.CompileError.lowering
  let globals := functions.map (·.signature)
  match plan.seedKeys with
  | [] => pure { plan, entries := [] }
  | first :: _ =>
      let diagnostics ← (SourceCoreDataPlaceFaultSites.prepare checked program.signatures plan first).mapError
        (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.diagnostics)
      let native ← if checked.catalog.callableContracts then do
          let table ← (SourceCoreStageCodebook.prepare program plan checked).mapError
            (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.callableContracts)
          let callableDiagnostics ← (SourceCoreCallableFaultSites.prepare plan table diagnostics.rootTable).mapError
            (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.callableDiagnostics)
          pure (some { table, diagnostics := callableDiagnostics : CallableContext })
        else pure none
      let locals ← match native with
        | none => pure locals
        | some native => (locals.withCallableContracts (fun caller initializer active =>
            native.table.idAt? (.lambda caller initializer active))).mapError (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.localInstances)
      let diagnostics := match native with
        | none => diagnostics
        | some native => { diagnostics with rootTable := native.diagnostics.rootTable }
      let closures ← (functions.mapM (compileClosureWithRepresentation program representation program.signatures plan globals diagnostics locals native fuel)).mapError
        SourceCoreGeneralEntry.CompileError.lowering
      SourceCoreGeneralEntry.prepareValidated plan checked fuel (fun _ request =>
        assemble globals functions closures diagnostics request) true

private theorem input_bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem input_mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem prepareInputs_receipt {representation : Representation} {source : TypedSource}
    {scope : SourceCoreBasic.Scope} {binders : List TypedBinder} {inputs : List (TypedBinder × Core.Ty)}
    (accepted : prepareInputs representation source scope binders = .ok inputs) :
    inputs.map Prod.fst = binders ∧
      ∀ index binding, inputs[index]? = some binding →
        representation.expressions.lowerBinder source
          ((inputs.take index).reverse.map (fun entry => (entry.1.id, entry.2)) ++ scope) binding.1 =
            .ok binding.2 := by
  induction binders generalizing scope inputs with
  | nil =>
    simp only [prepareInputs, pure, Except.pure, Except.ok.injEq] at accepted
    subst inputs
    exact ⟨rfl, by simp⟩
  | cons binder binders ih =>
    rw [prepareInputs] at accepted
    obtain ⟨type, projected, accepted⟩ := input_bind_ok accepted
    obtain ⟨remaining, generated, accepted⟩ := input_bind_ok accepted
    cases accepted
    obtain ⟨same, preceding⟩ := ih generated
    refine ⟨by simp [same], ?_⟩
    intro index binding found
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      cases found
      simpa using input_mapError_ok projected
    | succ index =>
      have next := preceding index binding (by simpa using found)
      simpa [List.take_succ_cons, List.reverse_cons, List.map_append, List.append_assoc] using next

/-- Actual function preparation keeps each binder and its original position.
Each native type was returned by the real binder compiler with precisely the
previously prepared prefix in scope. No packed-parameter equality is inferred. -/
theorem prepareFunctionWithRepresentation_inputs
    {program : CheckedProgram} {representation : Representation}
    {specialized : SourceSpecialization.SpecializedFunction} {named : Function}
    (accepted : prepareFunctionWithRepresentation program representation specialized = .ok named) :
    named.specialized = specialized ∧
      named.inputs.map Prod.fst = specialized.function.typedBody.inputs ∧
      ∀ index binding, named.inputs[index]? = some binding →
        representation.expressions.lowerBinder specialized.function.typedBody
          ((named.inputs.take index).reverse.map (fun entry => (entry.1.id, entry.2))) binding.1 =
            .ok binding.2 := by
  unfold prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := input_bind_ok accepted
  cases discarded
  by_cases staged : (specialized.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : specialized.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ specialized.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨parameterType, _, accepted⟩ := input_bind_ok accepted
      obtain ⟨resultType, _, accepted⟩ := input_bind_ok accepted
      obtain ⟨inputs, prepared, accepted⟩ := input_bind_ok accepted
      cases accepted
      obtain ⟨same, preceding⟩ := prepareInputs_receipt prepared
      exact ⟨rfl, same, by simpa using preceding⟩

end Solcore.Frontend.SourceCoreGeneralFunctions
end

section
-- leanmerge: from Solcore.Frontend.SourceCorePlanCatalog
/-! Discover the closed representations used by the authenticated specialization
plan. Catalog discovery is a compilation pass and never evaluates source IR. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCorePlanCatalog

abbrev Plan := SourceSpecializationWorklist.Plan

def sourceTypes (source : SourceInference.TypedSource) : List TypeSystem.Ty :=
  source.inputs.map (·.scheme.body) ++
  (SourceCoreDataPlaces.declaredBinders source).map (·.scheme.body) ++
  source.nodes.map (fun | .expression node => node.type | .statement node => node.type)

def planTypes (plan : Plan) : List TypeSystem.Ty :=
  (plan.specializations.flatMap fun specialized =>
    specialized.function.type :: specialized.function.inferredBodyType ::
      sourceTypes specialized.function.typedBody).filter SourceCoreDataCatalog.closed

inductive Error where
  | plan (error : SourceCompilationPlan.Error)
  | catalog (error : SourceCoreDataCatalog.Error)
  | localInstances (error : SourceSpecializationWorklist.Error)
  | lowering (error : SourceCoreGeneralEntry.CompileError SourceCoreGeneralFunctions.Error)
  deriving Repr

structure Prepared where
  checked : SourceCoreDataCatalog.Checked
  program : SourceCoreGeneralEntry.PreparedProgram checked
  deriving Repr

def prepare (program : CheckedProgram) (plan : Plan) (fuel : Nat)
    (callableContracts : Bool := false) : Except Error Prepared := do
  let executablePlan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError Error.plan
  let locals ← (SourceCompilationPlan.localLambdaCatalog executablePlan).mapError Error.localInstances
  let localTypes := locals.flatMap fun candidate => sourceTypes (candidate.source.applySubstitution candidate.substitution)
  let checked ← (SourceCoreDataCatalog.prepare program.signatures fuel
    (planTypes executablePlan ++ localTypes.filter SourceCoreDataCatalog.closed).eraseDups callableContracts).mapError Error.catalog
  let prepared ← (SourceCoreGeneralFunctions.prepareWithCatalog program plan checked fuel).mapError Error.lowering
  pure ⟨checked, prepared⟩

end Solcore.Frontend.SourceCorePlanCatalog
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreSession
/-! Owned source values over a typed Core session. The public carrier cannot
contain Core code or references. Function handles are minted only when exporting
a checked native result; they resolve to the original tagged function and its
captured locations in the session heap. This fresh/session-reuse boundary does
not yet import arbitrary pre-existing typed-source closures or heaps. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreSession

open SourceInference TypeSystem
abbrev DataContext := SourceCoreDataValues.Context
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev Key := SourceSpecialization.SpecializationKey

abbrev ArtifactAuthority := SourceCorePublicValues.ArtifactAuthority
abbrev SessionAuthority := SourceCorePublicValues.SessionAuthority
abbrev ExportGeneration := SourceCorePublicValues.ExportGeneration
abbrev Handle := SourceCorePublicValues.Handle
abbrev Value := SourceCorePublicValues.Value

@[match_pattern] abbrev Value.unit := SourceCorePublicValues.Value.unit
@[match_pattern] abbrev Value.bool := SourceCorePublicValues.Value.bool
@[match_pattern] abbrev Value.word := SourceCorePublicValues.Value.word
@[match_pattern] abbrev Value.integer := SourceCorePublicValues.Value.integer
@[match_pattern] abbrev Value.product := SourceCorePublicValues.Value.product
@[match_pattern] abbrev Value.constructed := SourceCorePublicValues.Value.constructed
@[match_pattern] abbrev Value.mapping := SourceCorePublicValues.Value.mapping
@[match_pattern] abbrev Value.proxy := SourceCorePublicValues.Value.proxy
@[match_pattern] abbrev Value.function := SourceCorePublicValues.Value.function
abbrev Value.type (value : Value) : Ty := SourceCorePublicValues.Value.type value
abbrev Value.decEq := SourceCorePublicValues.Value.decEq
abbrev Value.listDecEq := SourceCorePublicValues.Value.listDecEq
abbrev Value.entriesDecEq := SourceCorePublicValues.Value.entriesDecEq

abbrev PathStep := SourceCoreDataValues.PathStep

inductive ErrorCode where
  | data (error : SourceCoreDataValues.ErrorCode)
  | foreignArtifact | foreignSession | unknownHandle
  | handleTypeMismatch (expected actual : Ty)
  | invalidNativeValue (expected actual : Core.Ty)
  | missingEntry (key : Key)
  | argumentCountMismatch (expected actual : Nat)
  deriving Repr, DecidableEq

structure Error where
  path : List PathStep := []
  code : ErrorCode
  deriving Repr, DecidableEq

private def Error.at (step : PathStep) (error : Error) : Error :=
  { error with path := step :: error.path }
private def fromData (error : SourceCoreDataValues.Error) : Error := ⟨error.path, .data error.code⟩
private def fromCatalog (error : SourceCoreDataCatalog.Error) : Error := ⟨[], .data (.catalog error)⟩

private structure TypedValue (definitions : Core.DataEnvironment) (world : Core.StoreTyping)
    (value : Core.Value) (type : Core.Ty) : Type where
  typed : Core.RuntimeValueHasType world value type definitions

private structure TypedEnvironment (definitions : Core.DataEnvironment) (world : Core.StoreTyping)
    (environment : Core.Environment) : Type where
  typed : Core.RuntimeEnvironmentHasTypes world environment (environment.map Core.Value.type) definitions

mutual
  /-- Internal validation of finite value trees. References check the existing
  world; closures check captured values and their actual bodies. This operation
  is never an external closure-registration API. -/
  private def validateAt (definitions : Core.DataEnvironment) (world : Core.StoreTyping) :
      (value : Core.Value) → (type : Core.Ty) → Except Error (TypedValue definitions world value type)
    | .unit, .unit => pure ⟨.unit⟩
    | .bool _, .bool => pure ⟨.bool⟩
    | .word _, .word => pure ⟨.word⟩
    | .integer _, .integer => pure ⟨.integer⟩
    | .pair left right, .product leftType rightType => do
        let left ← (validateAt definitions world left leftType).mapError (Error.at .productLeft)
        let right ← (validateAt definitions world right rightType).mapError (Error.at .productRight)
        pure ⟨.pair left.typed right.typed⟩
    | .inLeft annotation payload, .sum leftType rightType => do
        if same : annotation = rightType then
          let payload ← validateAt definitions world payload leftType
          pure ⟨by cases same; exact .inLeft payload.typed⟩
        else throw ⟨[], .invalidNativeValue (.sum leftType rightType) (.sum payload.type annotation)⟩
    | .inRight annotation payload, .sum leftType rightType => do
        if same : annotation = leftType then
          let payload ← validateAt definitions world payload rightType
          pure ⟨by cases same; exact .inRight payload.typed⟩
        else throw ⟨[], .invalidNativeValue (.sum leftType rightType) (.sum annotation payload.type)⟩
    | .constructed constructor payload, .namedData id => do
        if same : constructor.owner = id then
          match found : definitions.lookupConstructorPayloadType? constructor with
          | none => throw ⟨[], .data (.invalidConstructor constructor)⟩
          | some payloadType =>
              let payload ← (validateAt definitions world payload payloadType).mapError (Error.at (.constructorPayload 0))
              pure ⟨same ▸ Core.RuntimeValueHasType.constructed found payload.typed⟩
        else throw ⟨[], .data (.invalidConstructor constructor)⟩
    | .cellRef annotation location, .cell payload =>
        if same : annotation = payload then
          if found : world[location]? = some payload then
            pure ⟨by cases same; exact .cellRef found⟩
          else throw ⟨[], .data .externalReferenceUnsupported⟩
        else throw ⟨[], .data .externalReferenceUnsupported⟩
    | .closure input output body captured, .function parameter result => do
        if same : input = parameter ∧ output = result then
          let validation ← validateEnvironment definitions world captured
          if inferred : Core.infer? (input :: captured.map Core.Value.type) body definitions = some output then
            pure ⟨by rcases same with ⟨rfl, rfl⟩; exact .closure validation.typed (Core.infer_sound inferred)⟩
          else throw ⟨[], .invalidNativeValue (.function parameter result) (.function input output)⟩
        else throw ⟨[], .invalidNativeValue (.function parameter result) (.function input output)⟩
    | .hostFunction .., _ => throw ⟨[], .data .externalHostUnsupported⟩
    | value, type => throw ⟨[], .invalidNativeValue type value.type⟩
  termination_by value _ => sizeOf value
  decreasing_by all_goals simp_wf; omega

  private def validateEnvironment (definitions : Core.DataEnvironment) (world : Core.StoreTyping) :
      (environment : Core.Environment) → Except Error (TypedEnvironment definitions world environment)
    | [] => pure ⟨.nil⟩
    | head :: tail => do
        let head ← validateAt definitions world head head.type
        let tail ← validateEnvironment definitions world tail
        pure ⟨.cons head.typed tail.typed⟩
  termination_by environment => sizeOf environment
  decreasing_by all_goals simp_wf; omega
end

private structure Slot (context : DataContext) (world : Core.StoreTyping) where
  handle : Handle
  value : Core.Value
  projection : Core.Ty
  generated : context.checked.catalog.project handle.sourceType = .ok projection
  typed : Core.RuntimeValueHasType world value projection context.checked.catalog.definitions

private abbrev Registry (context : DataContext) (world : Core.StoreTyping) := List (Slot context world)

private def Slot.weaken {context : DataContext} {world future : Core.StoreTyping}
    (extension : Core.WorldExtends world future) (slot : Slot context world) : Slot context future :=
  { slot with typed := slot.typed.weaken extension }
private def Registry.weaken {context : DataContext} {world future : Core.StoreTyping}
    (extension : Core.WorldExtends world future) (registry : Registry context world) : Registry context future :=
  registry.map (Slot.weaken extension)

private def resolve {context : DataContext} {world : Core.StoreTyping}
    (artifact : ArtifactAuthority) (session : SessionAuthority) (registry : Registry context world) (expected : Ty) (handle : Handle) :
    Except Error Core.Value := do
  unless handle.belongsToArtifact artifact do throw ⟨[], .foreignArtifact⟩
  unless handle.belongsToSession session do throw ⟨[], .foreignSession⟩
  let slot ← match registry.find? fun slot => decide (slot.handle = handle) with
    | none => throw ⟨[], .unknownHandle⟩
    | some slot => pure slot
  unless handle.sourceType = expected do throw ⟨[], .handleTypeMismatch expected handle.sourceType⟩
  pure slot.value

private def identity (context : DataContext) (type : Ty) : Except Error Core.DataTypeId := do
  match ← (context.checked.catalog.project type).mapError fromCatalog with
  | .namedData id => pure id
  | actual => throw ⟨[], .data (.coreShapeMismatch (.namedData ⟨0⟩) actual)⟩

mutual
  private def encodeRaw {context : DataContext} {world : Core.StoreTyping} :
      Nat → ArtifactAuthority → SessionAuthority → Registry context world → Ty → Value → Except Error Core.Value
    | 0, _, _, _, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, registry, expected, value => do
        match expected, value with
        | .comptime inner, value => encodeRaw fuel artifact session registry inner value
        | .function .., .function handle => resolve artifact session registry expected handle
        | .constructor (.builtin .unit), .unit => pure .unit
        | .constructor (.builtin .bool), .bool value => pure (.bool value)
        | .constructor (.builtin .word), .word value => pure (.word value)
        | .constructor (.builtin .integer), .integer value => pure (.integer value)
        | .product leftType rightType, .product left right => do
            let left ← (encodeRaw fuel artifact session registry leftType left).mapError (Error.at .productLeft)
            let right ← (encodeRaw fuel artifact session registry rightType right).mapError (Error.at .productRight)
            pure (.pair left right)
        | .mapping key value, .mapping actualKey actualValue entries => do
            unless actualKey = key ∧ actualValue = value do
              throw ⟨[], .data (.mappingMetadataMismatch key value actualKey actualValue)⟩
            encodeEntries fuel artifact session registry key value (← identity context expected) entries 0
        | .proxy inner, .proxy actual => do
            unless actual = inner do throw ⟨[], .data (.proxyIdentityMismatch inner actual)⟩
            pure (.constructed ⟨← identity context expected, 0⟩ .unit)
        | expected, .constructed metadata payloads => do
            unless metadata.resultType = expected do throw ⟨[], .data (.sourceTypeMismatch expected metadata.resultType)⟩
            let tag ← (context.checked.catalog.resolveConstructor context.signatures metadata).mapError fromCatalog
            let canonical ← (SourceCoreDataValues.constructorMetadata context expected tag).mapError fromData
            unless metadata = canonical do throw ⟨[], .data .constructorMetadataMismatch⟩
            let payload ← encodePayloads fuel artifact session registry metadata.payloadTypes payloads 0
            pure (.constructed tag payload)
        | expected, value => throw ⟨[], .data (.sourceTypeMismatch expected value.type)⟩

  private def encodePayloads {context : DataContext} {world : Core.StoreTyping} (fuel : Nat)
      (artifact : ArtifactAuthority) (session : SessionAuthority) (registry : Registry context world) (types : List Ty) (values : List Value)
      (index : Nat) : Except Error Core.Value := do
    if types.length ≠ values.length then throw ⟨[], .data (.payloadCountMismatch types.length values.length)⟩
    match fuel, types, values with
    | _, [], [] => pure .unit
    | 0, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, [type], [value] =>
        (encodeRaw fuel artifact session registry type value).mapError (Error.at (.constructorPayload index))
    | fuel + 1, type :: types, value :: values => do
        let value ← (encodeRaw fuel artifact session registry type value).mapError (Error.at (.constructorPayload index))
        pure (.pair value (← encodePayloads fuel artifact session registry types values (index + 1)))
    | _, _, _ => throw ⟨[], .data (.payloadCountMismatch types.length values.length)⟩

  private def encodeEntries {context : DataContext} {world : Core.StoreTyping} :
      Nat → ArtifactAuthority → SessionAuthority → Registry context world → Ty → Ty → Core.DataTypeId → List (Value × Value) →
      Nat → Except Error Core.Value
    | _, _, _, _, _, _, id, [], _ => pure (.constructed ⟨id, 0⟩ .unit)
    | 0, _, _, _, _, _, _, _ :: _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, registry, keyType, valueType, id, (key, value) :: rest, index => do
        let key ← (encodeRaw fuel artifact session registry keyType key).mapError (Error.at (.mappingKey index))
        let value ← (encodeRaw fuel artifact session registry valueType value).mapError (Error.at (.mappingValue index))
        let rest ← encodeEntries fuel artifact session registry keyType valueType id rest (index + 1)
        pure (.constructed ⟨id, 1⟩ (.pair (.pair key value) rest))
end

private def register {context : DataContext} {world : Core.StoreTyping}
    (_artifact : ArtifactAuthority) (session : SessionAuthority) (generation : ExportGeneration) (registry : Registry context world)
    (sourceType : Ty) (value : Core.Value) : Except Error (Handle × Registry context world) := do
  match registry.find? fun slot => decide (slot.handle.sourceType = sourceType ∧ slot.value = value) with
  | some slot => pure (slot.handle, registry)
  | none =>
      let projection ← (SourceCoreGeneralEntry.projectType context.checked sourceType).mapError fromCatalog
      let validation ← validateAt context.checked.catalog.definitions world value projection.type
      let handle : Handle := session.issue generation registry.length sourceType
      pure (handle, registry ++ [⟨handle, value, projection.type, projection.generated, validation.typed⟩])

mutual
  private def decodeRaw {context : DataContext} {world : Core.StoreTyping} :
      Nat → ArtifactAuthority → SessionAuthority → ExportGeneration → Registry context world → Ty → Core.Value →
      Except Error (Value × Registry context world)
    | 0, _, _, _, _, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, generation, registry, expected, value => do
        match expected, value with
        | _, .cellRef .. => throw ⟨[], .data .externalReferenceUnsupported⟩
        | _, .hostFunction .. => throw ⟨[], .data .externalHostUnsupported⟩
        | .comptime inner, value => decodeRaw fuel artifact session generation registry inner value
        | .function .., value =>
            let (handle, registry) ← register artifact session generation registry expected value
            pure (.function handle, registry)
        | _, .closure .. => throw ⟨[], .data .functionHandleRequired⟩
        | .constructor (.builtin .unit), .unit => pure (.unit, registry)
        | .constructor (.builtin .bool), .bool value => pure (.bool value, registry)
        | .constructor (.builtin .word), .word value => pure (.word value, registry)
        | .constructor (.builtin .integer), .integer value => pure (.integer value, registry)
        | .product leftType rightType, .pair left right => do
            let (left, registry) ← (decodeRaw fuel artifact session generation registry leftType left).mapError (Error.at .productLeft)
            let (right, registry) ← (decodeRaw fuel artifact session generation registry rightType right).mapError (Error.at .productRight)
            pure (.product left right, registry)
        | .mapping key value, core => do
            let (entries, registry) ← decodeEntries fuel artifact session generation registry key value
              (← identity context expected) core 0
            pure (.mapping key value entries, registry)
        | .proxy inner, .constructed tag .unit => do
            unless tag = ⟨← identity context expected, 0⟩ do throw ⟨[], .data (.invalidConstructor tag)⟩
            pure (.proxy inner, registry)
        | expected, .constructed tag payload => do
            let metadata ← (SourceCoreDataValues.constructorMetadata context expected tag).mapError fromData
            let (payloads, registry) ← decodePayloads fuel artifact session generation registry metadata.payloadTypes payload 0
            pure (.constructed metadata payloads, registry)
        | expected, value =>
            let projected ← (context.checked.catalog.project expected).mapError fromCatalog
            throw ⟨[], .data (.coreShapeMismatch projected value.type)⟩

  private def decodePayloads {context : DataContext} {world : Core.StoreTyping} :
      Nat → ArtifactAuthority → SessionAuthority → ExportGeneration → Registry context world → List Ty → Core.Value → Nat →
      Except Error (List Value × Registry context world)
    | _, _, _, _, registry, [], .unit, _ => pure ([], registry)
    | 0, _, _, _, _, _, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, generation, registry, [type], value, index => do
        let (value, registry) ← (decodeRaw fuel artifact session generation registry type value).mapError (Error.at (.constructorPayload index))
        pure ([value], registry)
    | fuel + 1, artifact, session, generation, registry, type :: types, .pair value tail, index => do
        let (value, registry) ← (decodeRaw fuel artifact session generation registry type value).mapError (Error.at (.constructorPayload index))
        let (tail, registry) ← decodePayloads fuel artifact session generation registry types tail (index + 1)
        pure (value :: tail, registry)
    | _, _, _, _, _, _, _, _ => throw ⟨[], .data .constructorMetadataMismatch⟩

  private def decodeEntries {context : DataContext} {world : Core.StoreTyping} :
      Nat → ArtifactAuthority → SessionAuthority → ExportGeneration → Registry context world → Ty → Ty → Core.DataTypeId → Core.Value → Nat →
      Except Error (List (Value × Value) × Registry context world)
    | 0, _, _, _, _, _, _, _, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, generation, registry, keyType, valueType, id, core, index => do
        match core with
        | .constructed tag .unit =>
            unless tag = ⟨id, 0⟩ do throw ⟨[], .data (.invalidConstructor tag)⟩
            pure ([], registry)
        | .constructed tag (.pair (.pair key value) tail) => do
            unless tag = ⟨id, 1⟩ do throw ⟨[], .data (.invalidConstructor tag)⟩
            let (key, registry) ← (decodeRaw fuel artifact session generation registry keyType key).mapError (Error.at (.mappingKey index))
            let (value, registry) ← (decodeRaw fuel artifact session generation registry valueType value).mapError (Error.at (.mappingValue index))
            let (tail, registry) ← (decodeEntries fuel artifact session generation registry keyType valueType id tail (index + 1)).mapError (Error.at .mappingTail)
            pure ((key, value) :: tail, registry)
        | _ => throw ⟨[], .data .constructorMetadataMismatch⟩
end

private structure Encoded {context : DataContext} (world : Core.StoreTyping) (sourceType : Ty) where
  value : Core.Value
  type : Core.Ty
  generated : context.checked.catalog.project sourceType = .ok type
  typed : Core.RuntimeValueHasType world value type context.checked.catalog.definitions

private def encode {context : DataContext} {world : Core.StoreTyping} (fuel : Nat)
    (artifact : ArtifactAuthority) (session : SessionAuthority) (registry : Registry context world) (expected : Ty) (value : Value) :
    Except Error (Encoded (context := context) world expected) := do
  let projection ← (SourceCoreGeneralEntry.projectType context.checked expected).mapError fromCatalog
  let core ← encodeRaw fuel artifact session registry expected value
  let validation ← validateAt context.checked.catalog.definitions world core projection.type
  pure ⟨core, projection.type, projection.generated, validation.typed⟩

private structure Exported {context : DataContext} (world : Core.StoreTyping)
    (artifact : ArtifactAuthority) (session : SessionAuthority) (fuel : Nat) (expected : Ty) (core : Core.Value) where
  value : Value
  registry : Registry context world
  reencoded : encodeRaw fuel artifact session registry expected value = .ok core

/-- The exact re-encoding guard proves that exporting a function handle retains
its complete identity tag, code and captured reference tree inside the owned
registry. Source data substitutions and mapping order are authenticated too. -/
private def exportValue {context : DataContext} {world : Core.StoreTyping} (fuel : Nat)
    (artifact : ArtifactAuthority) (session : SessionAuthority) (generation : ExportGeneration) (registry : Registry context world)
    (expected : Ty) (core : Core.Value) :
    Except Error (Exported (context := context) world artifact session fuel expected core) := do
  let (value, registry) ← decodeRaw fuel artifact session generation registry expected core
  match recovered : encodeRaw fuel artifact session registry expected value with
  | .error error => throw error
  | .ok encoded =>
      if same : encoded = core then
        pure ⟨value, registry, by simpa only [same] using recovered⟩
      else throw ⟨[], .data .nonCanonicalCoreValue⟩

/-- The constructor is sealed. Preparation authenticates the actual plan and
checks each native entry once; cached consumers may inspect those checked
entries without rebuilding them. No owned identity exists until open. -/
structure Recipe where private mk ::
  private context : DataContext
  private prepared : SourceCoreGeneralEntry.PreparedProgram context.checked
  deriving Repr

def Recipe.checked (recipe : Recipe) : Checked := recipe.context.checked
def Recipe.program (recipe : Recipe) : SourceCoreGeneralEntry.PreparedProgram recipe.checked := recipe.prepared

def Recipe.prepare (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (checked : Checked) (compilationFuel : Nat) :
    Except (SourceCoreGeneralEntry.CompileError SourceCoreGeneralFunctions.Error) Recipe := do
  let prepared ← SourceCoreGeneralFunctions.prepareWithCatalog program plan checked compilationFuel
  pure ⟨⟨checked, program.signatures⟩, prepared⟩

def Recipe.prepareAutomatic (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (compilationFuel : Nat) (callableContracts : Bool := true) : Except SourceCorePlanCatalog.Error Recipe := do
  let prepared ← SourceCorePlanCatalog.prepare program plan compilationFuel callableContracts
  pure ⟨⟨prepared.checked, program.signatures⟩, prepared.program⟩

/-- An owned artifact uses a cached, authenticated recipe. -/
structure Artifact where private mk ::
  private identity : ArtifactAuthority
  private context : DataContext
  private program : SourceCoreGeneralEntry.PreparedProgram context.checked

/-- Opening the same recipe again creates a separate owned artifact. This only
mints an identity and copies the cached entries; no compiler is run here. -/
def Recipe.open (recipe : Recipe) : IO Artifact :=
  return ⟨← SourceCorePublicValues.ArtifactAuthority.mint, recipe.context, recipe.prepared⟩

def Artifact.prepare (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (checked : Checked) (compilationFuel : Nat) :
    IO (Except (SourceCoreGeneralEntry.CompileError SourceCoreGeneralFunctions.Error) Artifact) := do
  match Recipe.prepare program plan checked compilationFuel with
  | .error error => pure (.error error)
  | .ok recipe => pure (.ok (← recipe.open))

/-- Discover all closed catalog representations from the authenticated plan. -/
def Artifact.prepareAutomatic (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (compilationFuel : Nat) : IO (Except SourceCorePlanCatalog.Error Artifact) := do
  match Recipe.prepareAutomatic program plan compilationFuel with
  | .error error => pure (.error error)
  | .ok recipe => pure (.ok (← recipe.open))

def Artifact.keys (artifact : Artifact) : List Key := artifact.program.entries.map (·.key)

/-- A persistent version of one owned execution session. Heap cells and
registry values are private; copying this value does not mint another identity. -/
structure Session (artifact : Artifact) where private mk ::
  private identity : SessionAuthority
  private world : Core.StoreTyping
  private store : Core.Store
  private stored : Core.RuntimeStoreHasTypes world store artifact.context.checked.catalog.definitions
  private registry : Registry artifact.context world

def Artifact.newSession (artifact : Artifact) : IO (Session artifact) := do
  pure ⟨← artifact.identity.newSession, [], [], .nil _, []⟩

def Session.heapSize {artifact : Artifact} (session : Session artifact) : Nat := session.store.length
def Session.functionCount {artifact : Artifact} (session : Session artifact) : Nat := session.registry.length

inductive FunctionIdentity where
  | anonymous
  | named (identity : Core.Word)
  deriving Repr, DecidableEq

/-- Inspect only the source identity tag of an owned function. Equality of the
public carrier compares lookup capabilities; source function equality continues
to use the original anonymous/named tag inside Core. -/
def Session.functionIdentity? {artifact : Artifact} (session : Session artifact) (handle : Handle) :
    Option FunctionIdentity :=
  match resolve artifact.identity session.identity session.registry handle.sourceType handle with
  | .ok (.pair (.pair (.inLeft .word .unit) (.closure ..)) (.word _)) => some .anonymous
  | .ok (.pair (.pair (.inRight .unit (.word identity)) (.closure ..)) (.word _)) => some (.named identity)
  | .ok (.pair (.inLeft .word .unit) (.closure ..)) => some .anonymous
  | .ok (.pair (.inRight .unit (.word identity)) (.closure ..)) => some (.named identity)
  | _ => none

/-- Pure proof boundary for a public value: its private encoding is typed in
the session's current world and comes from resolving owned handles and deeply
authenticating source metadata. -/
def Session.Authenticates {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (sourceType : Ty) (value : Value) : Prop :=
  ∃ core type,
    encodeRaw fuel artifact.identity session.identity session.registry sourceType value = .ok core ∧
    artifact.context.checked.catalog.project sourceType = .ok type ∧
    Core.RuntimeValueHasType session.world core type artifact.context.checked.catalog.definitions

structure Authentication {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (sourceType : Ty) (value : Value) : Type where private mk ::
  typed : session.Authenticates fuel sourceType value

/-- Deep public validation returns a certificate, never a raw Core closure.
It checks ownership, function type, constructor metadata and every child value. -/
def Session.authenticate {artifact : Artifact} (session : Session artifact) (fuel : Nat)
    (sourceType : Ty) (value : Value) : Except Error (Authentication session fuel sourceType value) := do
  let projection ← (SourceCoreGeneralEntry.projectType artifact.context.checked sourceType).mapError fromCatalog
  match accepted : encodeRaw fuel artifact.identity session.identity session.registry sourceType value with
  | .error error => throw error
  | .ok core =>
      let validation ← validateAt artifact.context.checked.catalog.definitions session.world core projection.type
      pure ⟨⟨core, projection.type, accepted, projection.generated, validation.typed⟩⟩

private structure Frame (definitions : Core.DataEnvironment) (initial : Core.StoreTyping)
    (context : Core.Context) where
  world : Core.StoreTyping
  store : Core.Store
  environment : Core.Environment
  extension : Core.WorldExtends initial world
  stored : Core.RuntimeStoreHasTypes world store definitions
  typed : Core.RuntimeEnvironmentHasTypes world environment context definitions

private def Frame.push {definitions : Core.DataEnvironment} {initial : Core.StoreTyping} {context : Core.Context}
    (frame : Frame definitions initial context) (type : Core.Ty) (value : Core.Value)
    (typed : Core.RuntimeValueHasType frame.world value type definitions) :
    Frame definitions initial (Core.OptionalCell.referenceType type :: context) := by
  let payloadType := Core.OptionalCell.cellType type
  have extension : Core.WorldExtends frame.world (frame.world ++ [payloadType]) := ⟨_, rfl⟩
  exact {
    world := frame.world ++ [payloadType], store := frame.store ++ [.inRight .unit value]
    environment := .cellRef payloadType frame.store.length :: frame.environment
    extension := frame.extension.trans extension
    stored := frame.stored.allocate (.inRight typed)
    typed := .cons (.cellRef (by simp [← frame.stored.length_eq])) (frame.typed.weaken extension)
  }

private def arguments {artifact : Artifact} (session : Session artifact) (fuel : Nat)
    {context : Core.Context} (index : Nat)
    (frame : Frame artifact.context.checked.catalog.definitions session.world context) :
    (inputs : List (SourceCoreGeneralEntry.Input artifact.context.checked)) → List Value →
    Except Error (Frame artifact.context.checked.catalog.definitions session.world
      (SourceCoreGeneralEntry.inputContext inputs ++ context))
  | [], [] => pure (by simpa [SourceCoreGeneralEntry.inputContext] using frame)
  | input :: inputs, value :: values => do
      let encoded ← encode fuel artifact.identity session.identity (session.registry.weaken frame.extension) input.sourceType value
      have same : encoded.type = input.type := Except.ok.inj (encoded.generated.symm.trans input.projection.generated)
      let next ← arguments session fuel (index + 1)
        (frame.push input.type encoded.value (same ▸ encoded.typed)) inputs values
      pure (by simpa [SourceCoreGeneralEntry.inputContext, List.reverse_cons, List.append_assoc] using next)
  | inputs, values => throw ⟨[], .argumentCountMismatch (index + inputs.length) (index + values.length)⟩

structure Checkpoint (artifact : Artifact) where private mk ::
  private origin : Session artifact
  private identity : SessionAuthority
  private sourceType : Ty
  private type : Core.Ty
  private generated : artifact.context.checked.catalog.project sourceType = .ok type
  private world : Core.StoreTyping
  private state : Core.State
  private stored : Core.RuntimeStoreHasTypes world state.store artifact.context.checked.catalog.definitions
  private typed : Core.StateHasType state (Core.LanguageResult.resultType type) artifact.context.checked.catalog.definitions
  private registry : Registry artifact.context world
  private extension : Core.WorldExtends origin.world world

/-- Append initialized parameter cells to the existing typed heap. Existing
closures keep their actual captures and all previous cell locations. -/
def Session.start {artifact : Artifact} (session : Session artifact) (key : Key)
    (values : List Value) (boundaryFuel : Nat := 1024) : Except Error (Checkpoint artifact) := do
  let entry ← match artifact.program.findEntry? key with
    | none => throw ⟨[], .missingEntry key⟩
    | some entry => pure entry
  if entry.inputs.length ≠ values.length then
    throw ⟨[], .argumentCountMismatch entry.inputs.length values.length⟩
  let initial : Frame artifact.context.checked.catalog.definitions session.world [] :=
    ⟨session.world, session.store, [], .refl _, session.stored, .nil⟩
  let frame ← arguments session boundaryFuel 0 initial entry.inputs values
  have environmentTyped : Core.RuntimeEnvironmentHasTypes frame.world frame.environment
      (SourceCoreGeneralEntry.inputContext entry.inputs) artifact.context.checked.catalog.definitions := by
    simpa using frame.typed
  pure {
    origin := session, identity := session.identity, sourceType := entry.sourceResultType, type := entry.resultType
    generated := entry.result.generated, world := frame.world
    state := .initial entry.body frame.environment frame.store, stored := frame.stored
    typed := .eval frame.stored environmentTyped entry.bodyTyped .nil
    registry := session.registry.weaken frame.extension
    extension := frame.extension
  }

structure Completion (artifact : Artifact) where private mk ::
  value : Value
  sourceType : Ty
  session : Session artifact
  boundaryFuel : Nat
  authenticated : session.Authenticates boundaryFuel sourceType value
  private origin : Session artifact
  private extension : Core.WorldExtends origin.world session.world

inductive Outcome (artifact : Artifact) where
  | succeeded (completion : Completion artifact)
  | failed (reason : Core.Word) (session : Session artifact)
  | outOfFuel (checkpoint : Checkpoint artifact)
  | exportError (error : Error) (session : Session artifact)

private def complete {artifact : Artifact} (checkpoint : Checkpoint artifact) (generation : ExportGeneration)
    (fuel boundaryFuel : Nat) (value : Core.Value) (store : Core.Store)
    (finished : Core.runStateful fuel checkpoint.state = .done value store) : Outcome artifact := by
  let world := store.map Core.Value.type
  have stored : Core.RuntimeStoreHasTypes world store artifact.context.checked.catalog.definitions := by
    obtain ⟨_, _, path⟩ := Core.runStateful_sound finished
    obtain ⟨future, _, typed⟩ := path.preserve_store_world checkpoint.typed checkpoint.stored
    simpa only [typed.world_eq, Core.State.final, Core.State.store] using typed
  have extension : Core.WorldExtends checkpoint.world world := by
    obtain ⟨_, _, path⟩ := Core.runStateful_sound finished
    obtain ⟨future, extension, typed⟩ := path.preserve_store_world checkpoint.typed checkpoint.stored
    simpa only [typed.world_eq, Core.State.final, Core.State.store] using extension
  have typed : Core.RuntimeValueHasType world value (Core.LanguageResult.resultType checkpoint.type)
      artifact.context.checked.catalog.definitions := by
    obtain ⟨future, typedStore, typedValue⟩ := Core.well_typed_runStateful_preserves_result_type checkpoint.typed finished
    simpa only [typedStore.world_eq] using typedValue
  let registry := checkpoint.registry.weaken extension
  let session : Session artifact := ⟨checkpoint.identity, world, store, stored, registry⟩
  exact match decoded : Core.LanguageResult.decode? value with
  | none => False.elim (by
      obtain ⟨outcome, found, _⟩ := Core.LanguageResult.decode?_runtime_typed typed
      rw [decoded] at found
      cases found)
  | some outcome =>
      have related : outcome.RuntimeHasType world checkpoint.type artifact.context.checked.catalog.definitions := by
        obtain ⟨actual, found, related⟩ := Core.LanguageResult.decode?_runtime_typed typed
        rw [decoded] at found
        cases found
        exact related
      match outcome with
      | .failed reason => .failed reason session
      | .succeeded payload =>
          match exportValue boundaryFuel artifact.identity checkpoint.identity generation registry checkpoint.sourceType payload with
          | .error error => .exportError error session
          | .ok exported =>
              let session : Session artifact := ⟨checkpoint.identity, world, store, stored, exported.registry⟩
              .succeeded ⟨exported.value, checkpoint.sourceType, session, boundaryFuel,
                ⟨payload, checkpoint.type, exported.reencoded, checkpoint.generated, related⟩,
                checkpoint.origin, checkpoint.extension.trans extension⟩

private def suspend {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (state : Core.State) (executed : Core.runStateful fuel checkpoint.state = .outOfFuel state) : Checkpoint artifact := by
  let world := state.store.map Core.Value.type
  have extension : Core.WorldExtends checkpoint.world world := by
    obtain ⟨future, extension, stored⟩ :=
      Core.well_typed_runStateful_preserves_checkpoint_world checkpoint.typed checkpoint.stored executed
    simpa only [stored.world_eq] using extension
  have stored : Core.RuntimeStoreHasTypes world state.store artifact.context.checked.catalog.definitions := by
    obtain ⟨future, _, stored⟩ :=
      Core.well_typed_runStateful_preserves_checkpoint_world checkpoint.typed checkpoint.stored executed
    simpa only [stored.world_eq] using stored
  exact {
    origin := checkpoint.origin, identity := checkpoint.identity, sourceType := checkpoint.sourceType, type := checkpoint.type
    generated := checkpoint.generated, world, state, stored
    typed := Core.well_typed_runStateful_preserves_checkpoint_type checkpoint.typed executed
    registry := checkpoint.registry.weaken extension
    extension := checkpoint.extension.trans extension
  }

/-- Obtain a genuine native exhaustion checkpoint, without exporting a result
or minting an identity. Successful and failed completions return none. -/
def Checkpoint.suspend? {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) :
    Option (Checkpoint artifact) :=
  match executed : Core.runStateful fuel checkpoint.state with
  | .outOfFuel state => some (suspend checkpoint fuel state executed)
  | _ => none

/-- Execution and resumption use only the saved native machine state. Every
branch carries either a typed checkpoint or a certified extended session heap.
An export error can reject source metadata; it is not a machine fault. -/
def Checkpoint.resume {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (boundaryFuel : Nat := 1024) : IO (Outcome artifact) := do
  match executed : Core.runStateful fuel checkpoint.state with
  | .done value store => pure (complete checkpoint (← SourceCorePublicValues.ExportGeneration.mint) fuel boundaryFuel value store executed)
  | .fault _error _faultState =>
      pure (False.elim (Core.well_typed_runStateful_never_faults checkpoint.typed executed))
  | .outOfFuel state =>
      pure (.outOfFuel (suspend checkpoint fuel state executed))

def Session.run {artifact : Artifact} (session : Session artifact) (key : Key) (values : List Value)
    (fuel : Nat) (boundaryFuel : Nat := 1024) : IO (Except Error (Outcome artifact)) := do
  match session.start key values boundaryFuel with
  | .error error => pure (.error error)
  | .ok checkpoint => pure (.ok (← checkpoint.resume fuel boundaryFuel))

theorem Completion.typed {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value :=
  completion.authenticated

/-- Input allocation and every subsequent native step retain the old world's
location types. This certificate includes all resumptions since start. -/
theorem Completion.world_extension {artifact : Artifact} (completion : Completion artifact) :
    Core.WorldExtends completion.origin.world completion.session.world := completion.extension

theorem Checkpoint.world_extension {artifact : Artifact} (checkpoint : Checkpoint artifact) :
    Core.WorldExtends checkpoint.origin.world checkpoint.world := checkpoint.extension

/-- Native result/state typing for each finite amount of fuel. -/
def Checkpoint.NativeSafe {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) : Prop :=
  (Core.runStateful fuel checkpoint.state).HasType (Core.LanguageResult.resultType checkpoint.type)
    artifact.context.checked.catalog.definitions

theorem Checkpoint.native_safe {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) :
    checkpoint.NativeSafe fuel := Core.well_typed_runStateful_has_type checkpoint.typed fuel

def Checkpoint.NativeResumes {artifact : Artifact} (checkpoint next : Checkpoint artifact)
    (spent additional : Nat) : Prop :=
  Core.runStateful additional next.state = Core.runStateful (spent + additional) checkpoint.state

theorem Checkpoint.suspend?_fuel_resume {artifact : Artifact} {checkpoint next : Checkpoint artifact}
    {spent : Nat} (exhausted : checkpoint.suspend? spent = some next) (additional : Nat) :
    checkpoint.NativeResumes next spent additional := by
  unfold Checkpoint.suspend? at exhausted
  split at exhausted
  · cases exhausted
    exact Core.runStateful_resume (by assumption) additional
  · cases exhausted

/-- The heap invariant is a pure Core theorem; fresh token allocation is not
a premise of runtime type safety. -/
theorem Session.heap_typed {artifact : Artifact} (session : Session artifact) :
    Core.RuntimeStoreHasTypes session.world session.store artifact.context.checked.catalog.definitions :=
  session.stored

end Solcore.Frontend.SourceCoreSession
end
