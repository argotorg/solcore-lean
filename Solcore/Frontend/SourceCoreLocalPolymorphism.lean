import Solcore.Frontend.SourceCompilationPlan.LocalInstances
import Solcore.Frontend.SourceCoreBasic
import Solcore.Frontend.SourceCoreDataCatalog
import Solcore.Core.TaggedFunction

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
  deriving Repr

structure Instance where
  origin : SourceCompilationPlan.LocalLambdaCatalogEntry
  parameterType : Core.Ty
  resultType : Core.Ty
  deriving Repr

def Instance.type (candidate : Instance) : Core.Ty :=
  Core.TaggedFunction.functionType candidate.parameterType candidate.resultType

/-- Apply the cumulative context to the full table. Immutable original
occurrence metadata remains in `origin.source` for later scheme selection;
nested generalized binders retain their own quantifiers. -/
def Instance.source (candidate : Instance) : TypedSource :=
  candidate.origin.source.applySubstitution candidate.origin.substitution

/-- The body is compiled under the packed parameter followed by the original
lexical reference environment. Every instance keeps anonymous source identity. -/
def Instance.closure (candidate : Instance) (body : Core.Expr) : Core.Expr :=
  Core.TaggedFunction.anonymous
    (.lambda candidate.parameterType (Core.LanguageResult.resultType candidate.resultType) body)

theorem Instance.closure_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {candidate : Instance} {body : Core.Expr}
    (parameterWF : Core.Ty.WellFormed definitions candidate.parameterType)
    (resultWF : Core.Ty.WellFormed definitions candidate.resultType)
    (bodyTyped : Core.HasType (candidate.parameterType :: context) body
      (Core.LanguageResult.resultType candidate.resultType) definitions) :
    Core.HasType context (candidate.closure body) candidate.type definitions :=
  Core.TaggedFunction.anonymous_hasType
    (.lambda parameterWF (Core.LanguageResult.resultType_wellFormed resultWF) bodyTyped)

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

private def prepareInstance (checked : Checked) (entry : SourceCompilationPlan.LocalLambdaCatalogEntry) :
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
  let parameterType ← (checked.project parameter).mapError Error.projection
  let resultType ← (checked.project result).mapError Error.projection
  pure ⟨entry, parameterType.type, resultType.type⟩

/-- Discover finite instances through the existing worklist. Unused direct
generalized lambdas are retained as empty bundles. This does not broaden the
worklist's supported generalized initializer forms or evidence policy. -/
def prepare (checked : Checked) (plan : SourceSpecializationWorklist.Plan) (contextFuel : Option Nat := none) :
    Except Error Catalog := do
  let entries ← (SourceCompilationPlan.localLambdaCatalog plan contextFuel).mapError Error.discovery
  let instances ← entries.mapM (prepareInstance checked)
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
