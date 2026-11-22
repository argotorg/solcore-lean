import Solcore.SourceSemantics.CoreLowering.AcceptedBuiltins

/-!
# Accepted bodies: constructors

Constructor applications as compiler sites of named-row bodies, which the compiler lowers to the
constructor's tag and metadata header over its packed arguments, and the cell-aware head of such
an application.

Main declarations:
- `CellAwareInvocationAcceptedConstructorSites.ConstructorSite`, a constructor application as a
  compiler site;
- `CellAwareInvocationAcceptedConstructors.preserves` and
  `CellAwareInvocationAcceptedConstructors.reflects`, the cell-aware head of an application.
-/

section
/-! Constructor applications in named-row bodies as compiler sites. A site has
no coercions or requirements, is not a generalized initializer and lies in a
row without evidence assumptions, so the named policy's special callback
declines it and its read policy is the compatible reader, as at a tuple. Its
parameter substitution is closed, so the typing's admissible instantiation is
valid at the runtime context. `constructorSite?` recognizes one on an actually
compiled row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConstructorSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy)

/-- A constructor application with a closed parameter substitution in a
named-row body. -/
structure ConstructorSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) (instantiation : DataConstructorInstantiation)
    (ids : List ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : node.form = .constructor instantiation ids
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  assumptions : named.specialized.assumptions = []
  ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id : ExpressionId}
  {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}

theorem contextual (site : ConstructorSite prepared named source id instantiation ids) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, site.found, site.form]

private theorem ordinary_nil {node : ExpressionNode} (requirements : node.requirements = [])
    (coercions : node.coercions = []) : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [requirements, coercions]
  rfl

private theorem evidence_none (site : ConstructorSite prepared named source id instantiation ids)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, ordinary_nil site.requirements site.coercions, site.found,
    site.form, site.requirements, site.coercions, site.assumptions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The named policy's special callback declines a constructor application. -/
theorem special (site : ConstructorSite prepared named source id instantiation ids) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  simp [site.form]

theorem read (site : ConstructorSite prepared named source id instantiation ids) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

private theorem ranges_of_all {substitution : TypeSystem.ParameterSubstitution}
    (closed : substitution.all (fun entry => SourceCoreDataCatalog.closed entry.2) = true) :
    CompatibleSourceInstantiationClosure.ClosedParameterRange substitution := by
  intro parameter replacement member
  exact List.all_eq_true.mp closed (parameter, replacement) member

/-- Proof-producing recognition of a constructor application of the row. -/
def constructorSite? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) :
    Option (Σ' (instantiation : DataConstructorInstantiation) (ids : List ExpressionId),
      ConstructorSite prepared named source id instantiation ids) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match form : node.form with
    | .constructor instantiation ids =>
      if closed : instantiation.parameterSubstitution.all (fun entry => SourceCoreDataCatalog.closed entry.2) then
        match coercions : node.coercions, requirements : node.requirements with
        | [], [] =>
          match initializer : prepared.base.locals.bindings.find? (fun binding =>
              decide (binding.caller = named.signature.key ∧ binding.initializer = id)) with
          | some _ => none
          | none =>
            match assumptions : named.specialized.assumptions with
            | [] => some ⟨instantiation, ids, ⟨node, found, form, coercions, requirements, initializer,
                assumptions, ranges_of_all closed⟩⟩
            | _ :: _ => none
        | _, _ => none
      else none
    | _ => none

/-- A constructor site depends on its row only through the row's key and its
empty assumptions. -/
def transport {first second : SourceCoreGeneralFunctions.Function}
    (keyEq : first.signature.key = second.signature.key) (assumptions : second.specialized.assumptions = [])
    (site : ConstructorSite prepared first source id instantiation ids) :
    ConstructorSite prepared second source id instantiation ids where
  node := site.node
  found := site.found
  form := site.form
  coercions := site.coercions
  requirements := site.requirements
  notInitializer := keyEq ▸ site.notInitializer
  assumptions := assumptions
  ranges := site.ranges

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConstructorSites
end

section
/-! The cell-aware head of a constructor application. A Source trace of the
application determines the actual construction: its arguments' reached state,
and the constructed value at the compiler's tag and header, or the arguments'
failure. The typing's admissible instantiation and the site's closed
substitution make the metadata valid, which refutes the metadata fault. Native
completion reconstructs the staged trace in the same way. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConstructors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedPreparedStagedConstructorHeadBounds (Point)
open CompatibleExpressionConstructors (construct_rename construct_success construct_failure)
universe u

private theorem values_rep {checked : SourceCoreCompatibleCatalog.Checked} {receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel checked receiving functions)
      mapping world types natives sources payloads) :
    ValuesRep checked receiving functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
  {instantiation : DataConstructorInstantiation} {ids : List ExpressionId} {tag : ConstructorId}
  {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
  (receipt : CompatibleExpressionConstructors.Header (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source id node instantiation tag header codes)
  (form : node.form = .constructor instantiation ids)
  (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "headCode" => SourceCoreBasic.LoweredExpr.mk (Core.Ty.namedData (Core.ConstructorId.owner tag))
  (SourceCoreCompatibleDataExpressions.construct tag header
    (SourceCoreBasic.LoweredExpr.expression (SourceCoreCalls.packArguments codes)))

include extension receipt in
private theorem constructed_represents {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value}
    {values : List Value}
    (payloads : DataExpressionSequence.Values model mapping world instantiation.payloadTypes
      (codes.map (·.type)) sources values) :
    RecursiveStageMeaning.ResultRepresentsFor model mapping world node.type (.namedData tag.owner) faults
      (.value (.constructed instantiation sources)) (.inRight .word (.constructed tag (.pair (.word header)
        (packValues values)))) := by
  rw [receipt.sourceType]
  exact .value (.constructed (receipt.original.extend extension)
    (extension.signatures.trans (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registryOwner)
    receipt.selected (receipt.sourceType ▸ receipt.metadata.projected) receipt.registered (values_rep payloads))

include bridge functions extension faults unique selectedBodies runtime covers receipt form ranges in
/-- A Source trace of a constructor application determines the actual
construction, the arguments' reached state and the constructed value. -/
theorem preserves {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation (Point scope id headCode)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique receipt.metadata.found form receipt.metadata.coercions typed
  have valid := CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges
  have originalTrace := trace
  rcases CallableIndexedOwnedPreparedStagedConstructorSourceInversion.children unique receipt.metadata.found form
      valid trace with
    ⟨sequenceSize, sources, sameSize, outcomeEq, sourceTrace⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, payloads, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
      CellAwareInvocationExpressionSequence.preserves_values bridge size sequence unique typing childMeaning
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
        sourceTrace within
    refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues values))), finalStore, finalMap,
      finalWorld, ?_, constructed_represents functions extension faults receipt payloads, finalHeaps, maps, worlds, frame,
      heapMetadata, effect, reached, related, ?_⟩
    · rw [construct_rename]
      exact construct_success tag header evaluated
    · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
        locals typed originalTrace frame
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
      CellAwareInvocationExpressionSequence.preserves_fault bridge size sequence unique typing childMeaning
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
        sourceTrace within
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
    · rw [construct_rename]
      exact construct_failure tag header evaluated
    · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
        locals typed originalTrace frame

include bridge functions extension faults unique selectedBodies runtime covers receipt form ranges in
/-- Native completion of a constructor application reconstructs its staged
Source execution: the arguments', and the construction at their values. -/
theorem reflects {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation (Point scope id headCode)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique receipt.metadata.found form receipt.metadata.coercions typed
  have valid := CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges
  rw [construct_rename] at completed
  obtain ⟨sequenceSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, sourceTrace, sequenceResult, finalHeaps,
      maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
    CellAwareInvocationExpressionSequence.reflects bridge size sequence unique typing childMeaning
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
      childEvaluation smaller
  have occurrence : Staging.Recursive.Occurrence invocation child (.constructor instantiation ids) :=
    ⟨_, lookupExpression?_sound receipt.metadata.found, form, receipt.metadata.requirements,
      receipt.metadata.coercions⟩
  cases sequenceResult with
  | @values sources values payloads =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (construct_success tag header childEvaluation.sound)
    have trace := Staging.Recursive.Size.Expression.constructorValue occurrence valid sourceTrace
    exact ⟨_, _, after, finalMap, finalWorld, trace, constructed_represents functions extension faults receipt payloads,
      finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related,
      SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
        locals typed trace frame⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (construct_failure tag header childEvaluation.sound)
    have trace := Staging.Recursive.Size.Expression.constructorFault occurrence sourceTrace
    exact ⟨_, _, after, finalMap, finalWorld, trace, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, effect, reached, related,
      SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
        locals typed trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedConstructors
end
