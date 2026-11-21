import Solcore.SourceSemantics.CoreLowering.AcceptedConversions

/-!
# Accepted bodies: builtin closures

The seven integer closures and the word opcodes as compiler sites of named-row bodies: a
reference to a closure, which the compiler lowers to the closure's contracted value, and a call of
a closure, which it lowers to the contracted call of that value on its packed arguments; and the
cell-aware head of such a call.

Main declarations:
- `CellAwareInvocationAcceptedBuiltinSites.BuiltinSite` and
  `CellAwareInvocationAcceptedBuiltinSites.of_accepted`, a closure call's receipt;
- `CellAwareInvocationAcceptedBuiltinSites.value_of_accepted`, a closure reference's receipt;
- `CellAwareInvocationAcceptedBuiltins.preserves` and
  `CellAwareInvocationAcceptedBuiltins.reflects`, the cell-aware head of a closure call.
-/

section
/-! Calls of builtin closures in named-row bodies as compiler sites. A call site
has no coercions or requirements, is not a generalized initializer and lies in a
row without evidence assumptions, so the named policy's special callback
declines it and its read policy is the compatible reader, as at a conversion.
Its builtin is a closure of the inventory (`BuiltinFunctionId.conversion?` is
`none`): the compiler lowers and packs its arguments and calls the closure's
contracted value under the builtin's descriptor (`of_accepted`). A reference to
a closure on its own lowers to that value (`value_of_accepted`).
`builtinSite?` recognizes a call on an actually compiled row. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedBuiltinSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site)

/-- A call of a builtin closure in a named-row body. -/
structure BuiltinSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id callee : ExpressionId) (ids : List ExpressionId) (function : BuiltinFunctionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : node.form = .call callee ids (.builtinFunction function)
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  assumptions : named.specialized.assumptions = []
  closure : function.conversion? = none

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id callee : ExpressionId}
  {ids : List ExpressionId} {function : BuiltinFunctionId}

theorem contextual (site : BuiltinSite prepared named source id callee ids function) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, site.found, site.form]

private theorem ordinary_nil {node : ExpressionNode} (requirements : node.requirements = [])
    (coercions : node.coercions = []) : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [requirements, coercions]
  rfl

private theorem evidence_none (site : BuiltinSite prepared named source id callee ids function)
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

/-- The named policy's special callback declines a call of a closure. -/
theorem special (site : BuiltinSite prepared named source id callee ids function) (rootFuel : Nat)
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

theorem read (site : BuiltinSite prepared named source id callee ids function) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

/-- An accepted call of a closure lowers and packs its arguments and emits the
contracted call of the closure's value on their pack. -/
theorem of_accepted (site : BuiltinSite prepared named source id callee ids function) (rootFuel : Nat)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) (fuel + 1) (context prepared named) source scope id reasonAt = .ok lowered) :
    Nonempty (CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) (.initial checked) source scope id callee ids function
      reasonAt lowered) :=
  CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.of_functions prepared.ancestry.graph.inputs.callable []
    (by
      show SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [] = _
      rw [prepared.ancestry.graph.inputs.callableSelected])
    site.found site.form (fun child budget => special compiled site rootFuel child budget scope reasonAt)
    (read compiled site rootFuel) site.closure accepted

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty} {done : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok done) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- An accepted reference to a builtin closure lowers to the closure's
contracted value, at the type that the compatible reader projects. -/
theorem value_of_accepted (site : Site prepared named source id) (rootFuel : Nat) {name : String}
    (form : site.node.form = .reference name (.builtinFunction function))
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) source scope id reasonAt = .ok lowered) :
    Nonempty (CellAwareBuiltinValueCertificates.Header prepared source id lowered) ∧
      CompatibleExpressionReads.Metadata checked source id site.node lowered.type := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, site.found,
        bind, Except.bind, pure, Except.pure] at accepted
      have bypass := CellAwareNamedExpressionPolicies.special compiled site rootFuel
        (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
            (namedLowerBody compiled) (min budget fuel) (context prepared named)
            childSource childScope childId childReasonAt) (fuel + 1) scope reasonAt
      simp only [show (namedPolicy compiled rootFuel).lowerSpecial? = some
        (CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel) from rfl] at accepted
      rw [bypass] at accepted
      simp only [form, CellAwareNamedExpressionPolicies.read compiled site rootFuel] at accepted
      obtain ⟨pair, read, rest⟩ := bind_ok accepted
      obtain ⟨other, type⟩ := pair
      have metadata := CompatibleExpressionReads.metadata_of_read read
      have same := Option.some.inj (metadata.found.symm.trans site.found)
      subst other
      simp only [form] at rest
      obtain ⟨code, reference, rest⟩ := bind_ok rest
      obtain ⟨done, sameType, rest⟩ := bind_ok rest
      cases done
      cases rest
      have typeEq := ensureType_ok sameType
      subst typeEq
      exact ⟨CellAwareBuiltinValueCertificates.of_reference prepared rfl site.found form
        metadata.requirements metadata.coercions reference, metadata⟩
    · simp [owner, bind, Except.bind] at accepted

/-- Proof-producing recognition of a call of a closure of the row. -/
def builtinSite? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) :
    Option (Σ' (callee : ExpressionId) (ids : List ExpressionId) (function : BuiltinFunctionId),
      BuiltinSite prepared named source id callee ids function) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match form : node.form with
    | .call callee ids (.builtinFunction function) =>
      match closure : function.conversion? with
      | some _ => none
      | none =>
        match coercions : node.coercions, requirements : node.requirements with
        | [], [] =>
          match initializer : prepared.base.locals.bindings.find? (fun binding =>
              decide (binding.caller = named.signature.key ∧ binding.initializer = id)) with
          | some _ => none
          | none =>
            match assumptions : named.specialized.assumptions with
            | [] => some ⟨callee, ids, function,
                ⟨node, found, form, coercions, requirements, initializer, assumptions, closure⟩⟩
            | _ :: _ => none
        | _, _ => none
    | _ => none

/-- A closure call site depends on its row only through the row's key and its
empty assumptions. -/
def transport {first second : SourceCoreGeneralFunctions.Function}
    (keyEq : first.signature.key = second.signature.key) (assumptions : second.specialized.assumptions = [])
    (site : BuiltinSite prepared first source id callee ids function) :
    BuiltinSite prepared second source id callee ids function where
  node := site.node
  found := site.found
  form := site.form
  coercions := site.coercions
  requirements := site.requirements
  notInitializer := keyEq ▸ site.notInitializer
  assumptions := assumptions
  closure := site.closure

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedBuiltinSites
end

section
/-! The cell-aware head of a call of a builtin closure. The closure's
contracted value and both gates of the contract are pure, so the call runs its
arguments once in the same invocation, at the native environment that the
contract prefixes, and applies the closure at the heap and store that they
reach, which the primitive keeps. An argument's failure is the call's own.
Preservation uses the arguments' meaning below the grade, and reflection at the
native size of the argument pack. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedBuiltins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
open BuiltinCalls.Protocol
open GenericExpressionMeaning (agree_prefix rename_prefix)
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

private theorem prefixed_typed {definitions : DataEnvironment} {world : StoreTyping}
    {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (function : BuiltinFunctionId) (identity contract : Word) :
    RuntimeEnvironmentHasTypes world (.unit :: contractedValue function identity contract actual :: actual)
      (.unit :: CallableContract.functionType (SourceCoreInteger.builtinParameter function)
        (SourceCoreInteger.builtinResult function) :: actualContext) definitions := by
  have closureTyped := SourceCoreInteger.builtinClosure_hasType (scope := actualContext) (definitions := definitions) function
  cases closureTyped with
  | lambda _ _ body => exact .cons .unit (.cons (.pair (.pair (.inRight .word) (.closure typed body)) .word) typed)

private theorem contracted_rename (function : BuiltinFunctionId) (identity contract : Word) (ξ : Renaming) :
    (contracted function identity contract).rename ξ = contracted function identity contract := by
  cases function <;> first | rfl | (rename_i op; cases op <;> rfl)

private theorem call_rename (function : BuiltinFunctionId) (identity contract unknown : Word)
    (arguments : Expr) (ξ : Renaming) :
    (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (contracted function identity contract) arguments).rename ξ =
    CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (contracted function identity contract) (arguments.rename ξ) := by
  simp [CallableContract.call, LanguageResult.bind, CallableContract.dispatch, CallableContract.guardResult,
    CallableContract.Gate.reason, LanguageResult.success, LanguageResult.failure,
    contracted_rename, Expr.rename, Renaming.lift]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
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
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
  {ids : List ExpressionId} {function : BuiltinFunctionId} {codes : List SourceCoreBasic.LoweredExpr}
  {identity contract unknown : Word}
  (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
    (SourceCoreInteger.builtinResult function))
  (form : node.form = .call callee ids (.builtinFunction function))
  (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "headCode" => SourceCoreBasic.LoweredExpr.mk (SourceCoreInteger.builtinResult function)
  (CallableContract.call [CallableContract.Gate.mk contract none none] unknown (SourceCoreInteger.builtinResult function)
    (contracted function identity contract) (SourceCoreBasic.LoweredExpr.expression (SourceCoreCalls.packArguments codes)))

include bridge functions observations faults unique selectedBodies runtime covers metadata form nativeTypes in
/-- A Source trace of a call of a closure determines the actual contracted
call, the arguments' reached state and the closure's result. -/
theorem preserves {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids function.parameterTypes codes)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation (Point scope id headCode)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨typing, sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types
    unique metadata.found form metadata.coercions typed
  have prefixed := prefixed_typed actualTyped function identity contract
  have agreesPrefix : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: contractedValue function identity contract actual :: actual) :=
    agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
  have originalTrace := trace
  rcases CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.children unique metadata.found form trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, sameSize, sourceTrace, applied⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, payloads, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
      CellAwareInvocationExpressionSequence.preserves_values bridge size sequence unique typing childMeaning
        environments heaps locals agreesPrefix prefixed initial admitted authority physical owner ownerFrame
        sourceTrace within
    have represented := values_rep payloads
    rw [nativeTypes] at represented
    have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
    obtain ⟨value, sameOutcome, sameHeap, _grade, primitive⟩ :=
      CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions observations represented applied
    subst outcome
    subst after
    rw [rename_prefix, rename_prefix] at evaluated
    obtain ⟨actualResult, nativeResult, actualPrimitive, resultRep, completed⟩ := contracted_preserves
      (identity := identity) (contract := contract) (unknown := unknown) inputs evaluated
    have same := actualPrimitive.functional primitive
    subst actualResult
    refine ⟨.inRight .word nativeResult, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
    · rw [call_rename]; exact completed
    · rw [sourceResult]
      exact .value (CompatibleBuiltinMeaning.result_represents inputs primitive resultRep)
    · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
        locals typed originalTrace frame
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
      CellAwareInvocationExpressionSequence.preserves_fault bridge size sequence unique typing childMeaning
        environments heaps locals agreesPrefix prefixed initial admitted authority physical owner ownerFrame
        sourceTrace within
    rw [rename_prefix, rename_prefix] at evaluated
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
    · rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store)
        (gates_accept contract unknown .beforeArguments) evaluated
    · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
        locals typed originalTrace frame

include bridge functions observations faults unique selectedBodies runtime covers metadata form nativeTypes in
/-- Native completion of a call of a closure reconstructs its staged Source
execution: the arguments', and the closure's application at their values. -/
theorem reflects {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids function.parameterTypes codes)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation (Point scope id headCode)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨typing, sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types
    unique metadata.found form metadata.coercions typed
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.builtinFunction function)) :=
    ⟨node, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have prefixed := prefixed_typed actualTyped function identity contract
  have agreesPrefix : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: contractedValue function identity contract actual :: actual) :=
    agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
  rw [call_rename] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedBuiltinCallBounds.contracted_arguments_sized completed
  have shifted := argumentEvaluation
  rw [← rename_prefix, ← rename_prefix] at shifted
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
    CellAwareInvocationExpressionSequence.reflects bridge size sequence unique typing childMeaning
      environments heaps locals agreesPrefix prefixed initial admitted authority physical owner ownerFrame shifted
      smaller
  cases represented with
  | @values sources values payloads =>
    have represented := values_rep payloads
    rw [nativeTypes] at represented
    have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
    obtain ⟨sourceValue, nativeValue, primitive, resultRep, same, sameStore⟩ :=
      contracted_reflects inputs argumentEvaluation.sound completed.sound
    subst value
    subst finalStore
    have trace := Staging.Recursive.Size.Expression.builtinApplied occurrence sourceTrace
      (Staging.Recursive.Size.Applies.builtin primitive)
    refine ⟨_, _, argumentsHeap, finalMap, finalWorld, trace, ?_, finalHeaps,
      maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
    · rw [sourceResult]
      exact .value (CompatibleBuiltinMeaning.result_represents inputs primitive resultRep)
    · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
        locals typed trace frame
  | fault matched =>
    have failed := CallableContract.call_argument_failure
      (result := SourceCoreInteger.builtinResult function) [⟨contract, none, none⟩] unknown
      (contracted_evaluates function identity contract actual store)
      (gates_accept contract unknown .beforeArguments) argumentEvaluation.sound
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
    have trace := Staging.Recursive.Size.Expression.builtinArgumentsFault occurrence sourceTrace
    refine ⟨_, _, argumentsHeap, finalMap, finalWorld, trace, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
    exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers
      locals typed trace frame

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedBuiltins
end
