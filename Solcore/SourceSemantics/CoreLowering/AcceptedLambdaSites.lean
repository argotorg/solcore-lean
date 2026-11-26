import Solcore.SourceSemantics.CoreLowering.AcceptedNamedValues

/-!
# Accepted bodies: lambdas

A lambda of a named-row body, such as the argument of
`apply(lam (x: word) -> word { return x; }, 7)`. The named policy lowers it
through the ordinary lambda branch of `SourceCoreFunctions.lowerExpressionWithPolicy`:
the parameter cells, the body at the lambda's own fuel, the copies of the
captures at each call, both indexed lambda hooks, the decoration with the
descriptor of the callable codebook's `.lambda` row and the copies of the
captures at creation, since the named policy snapshots every lambda it forms.
This module gives the lambda site, the compiler's receipt of such a site and
the lifting of the Source's lambda rule to the staged atomic value. Nothing
uses them yet: the nested expression family takes them with the closure leaf.

Main declarations: `CellAwareInvocationAcceptedLambdaSites.LambdaSite` and
`lambdaSite?`, the site; `CellAwareLambdaCertificates.Receipt` and
`Receipt.of_site`, the receipt, and `Receipt.produced`, the older route's
static lambda code at the receipt; and `lambda_value`, `lambda_no_fault`,
`staged`, `lambda_rule`, `lambda_lift` and `lambda_lift_fault` of
`CellAwareInvocationAcceptedLambdaLifting`, the Source side.
-/

section
/-! Lambdas of named-row bodies as compiler sites. A lambda site has no
coercions or requirements, is not a generalized initializer and lies in a row
without evidence assumptions, so the named policy's special callback declines
it and its read policy is the compatible reader, as for a named function value.
Its parameters are runtime and its result type is not comptime-only: the call
guard of an indirect call binds the closure the lambda forms to its own
parameters, with a staged result exactly when its result type is comptime-only
(`CallableLedger.Binds.closure`), so the guard accepts every call of it at its
arity. A lambda that is a generalized local's initializer takes the callback's
special path instead (`GeneralizedLocalInitializerCompilation.of_named_policy`)
and is no lambda site. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedLambdaSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

/-- A runtime parameter: not marked comptime, of a type that is not
comptime-only (`Staging.CallGuard.RequiresComptime` fails for it unforced). -/
def RuntimeParameter (parameter : TypedBinder) : Prop :=
  parameter.comptime = false ∧ ¬ Staging.ComptimeOnlyType parameter.scheme.body

/-- A lambda of a named-row body. -/
structure LambdaSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  found : source.lookupExpression? id = some node
  form : node.form = .lambda parameters result body
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  runtimeParameters : ∀ parameter ∈ parameters, RuntimeParameter parameter
  runtimeResult : ¬ Staging.ComptimeOnlyType result
  assumptions : named.specialized.assumptions = []

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id : ExpressionId}

theorem contextual (site : LambdaSite prepared named source id) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, site.found, site.form]

private theorem evidence_none (site : LambdaSite prepared named source id)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  have owned : SourceCompilationPlan.ordinaryOwnedRequirements? site.node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [site.requirements, site.coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, site.found, site.form, owned, site.requirements, site.coercions,
    bind, Except.bind, pure, Except.pure]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The named policy's special callback declines a lambda site: it is no
generalized initializer, needs no evidence and is no local read. -/
theorem special (site : LambdaSite prepared named source id) (rootFuel : Nat)
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

theorem read (site : LambdaSite prepared named source id) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

/-- The executable check of `RuntimeParameter` on every parameter. -/
def runtimeParameters? (parameters : List TypedBinder) : Bool :=
  parameters.all fun parameter => !parameter.comptime && !SourceStageAnalysis.typeIsComptimeOnly parameter.scheme.body

/-- A passed check gives `RuntimeParameter` of every parameter. -/
theorem runtimeParameters?_sound {parameters : List TypedBinder} (passed : runtimeParameters? parameters = true) :
    ∀ parameter ∈ parameters, RuntimeParameter parameter := by
  intro parameter member
  have each := List.all_eq_true.mp passed parameter member
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at each
  refine ⟨each.1, fun comptimeOnly => ?_⟩
  have marked := (SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff _).mpr comptimeOnly
  rw [each.2] at marked
  cases marked

/-- A result type the executable check passes is not comptime-only. -/
theorem runtimeResult_sound {result : TypeSystem.Ty}
    (passed : SourceStageAnalysis.typeIsComptimeOnly result = false) : ¬ Staging.ComptimeOnlyType result := by
  intro comptimeOnly
  have marked := (SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff _).mpr comptimeOnly
  rw [passed] at marked
  cases marked

/-- Proof-producing recognition of a lambda site. -/
def lambdaSite? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) : Option (LambdaSite prepared named source id) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match form : node.form with
    | .lambda parameters result body =>
      match coercions : node.coercions, requirements : node.requirements with
      | [], [] =>
        match initializer : prepared.base.locals.bindings.find? (fun binding =>
            decide (binding.caller = named.signature.key ∧ binding.initializer = id)) with
        | some _ => none
        | none =>
          if runtime : runtimeParameters? parameters = true then
            if staged : SourceStageAnalysis.typeIsComptimeOnly result = false then
              match assumptions : named.specialized.assumptions with
              | [] => some ⟨node, parameters, result, body, found, form, coercions, requirements, initializer,
                  runtimeParameters?_sound runtime, runtimeResult_sound staged, assumptions⟩
              | _ :: _ => none
            else none
          else none
      | _, _ => none
    | _ => none

/-- A lambda site depends on its row only through the row's key and its empty
assumptions. -/
def transport {first second : SourceCoreGeneralFunctions.Function}
    (keyEq : first.signature.key = second.signature.key) (assumptions : second.specialized.assumptions = [])
    (site : LambdaSite prepared first source id) : LambdaSite prepared second source id where
  node := site.node
  parameters := site.parameters
  result := site.result
  body := site.body
  found := site.found
  form := site.form
  coercions := site.coercions
  requirements := site.requirements
  notInitializer := keyEq ▸ site.notInitializer
  runtimeParameters := site.runtimeParameters
  runtimeResult := site.runtimeResult
  assumptions := assumptions

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedLambdaSites
end

section
/-! The compiler receipt of a lambda site. The named policy's lambda branch
checks the node's function type against the parameter bundle and the result,
projects both, binds the parameter cells, lowers the body at its own fuel,
copies the captures at each call, applies the template hook and the indexed
expression hook, which selects the codebook's `.lambda` row and snapshots the
creation frame, decorates the result with that row's descriptor and copies the
captures at creation: the named policy snapshots every lambda
(`PolicyRecipe.snapshotLambda`). The receipt keeps the actual lambda branch
receipt (`CallableIndexedLambdaCertificates.Certificate`) at the named policy,
the descriptor and the emitted code. `Receipt.produced` gives the older route's
static code of the same lambda (`CallableIndexedLambdaValues.Code`, inside a
`CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced`) at any Source
context and evidence, from a native typing of the emitted code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLambdaCertificates
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context allocator)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareInvocationAcceptedLambdaSites (LambdaSite)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word} (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok descriptor => exact ⟨descriptor⟩

/-- The decorated lambda before its creation-time copies, as
`CallableIndexedLambdaValues.Code.expression`: the anonymous tagged closure
over the snapshot of the creation frame, wrapped with the descriptor word. -/
def decorated {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (compilation : SourceCoreFunctions.Context) (scope : SourceCoreLocalCell.Scope) (origin : Word)
    (parameter result : Ty) (rawBody : Expr) : Expr :=
  LanguageResult.success (CallableContract.wrap origin (TaggedFunction.anonymous
    (SourceCoreCallableIndexedAncestry.snapshotLambda prepared.ancestry.graph.table prepared.ancestry.layout.frame
      origin (SourceCoreCallableIndexedAncestry.creationReferenceIndex compilation scope) parameter result rawBody)))

/-- A lambda's static code decorates the same expression. -/
theorem decorated_code {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : CallableIndexedLambdaValues.Code prepared function scope administrative viewRelation) :
    code.expression = decorated prepared code.compilation scope code.descriptor.id code.receipt.parameterCore
      code.receipt.resultCore code.receipt.rawBody := rfl

variable {whole : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

/-- The compiler receipt of a lambda site: the node and its lambda header,
the compatible metadata of the node at the lowered type, the site's runtime
parameters and result, the actual lambda branch receipt at the named policy,
the descriptor of the codebook's `.lambda` row of the site, the native function
type and the emitted code, the creation-time copies of the decorated lambda
through the row's marked allocator. -/
structure Receipt (generation : Compilation whole.indexed named diagnostics code) (rootFuel fuel : Nat)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node lowered.type
  form : node.form = .lambda parameters result body
  runtimeParameters : ∀ parameter ∈ parameters, CellAwareInvocationAcceptedLambdaSites.RuntimeParameter parameter
  runtimeResult : ¬ Staging.ComptimeOnlyType result
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
    (namedLowerBody generation) (fuel + 1) (context whole.indexed named) source scope id reasonAt = .ok lowered
  certificate : CallableIndexedLambdaCertificates.Certificate (namedPolicy generation rootFuel)
    (namedLowerBody generation) fuel (context whole.indexed named) source scope id node parameters result body
    lowered.type reasonAt lowered
  descriptor : SourceCoreCallableContracts.Descriptor whole.indexed.ancestry.graph.inputs.callable.table
    (.lambda named.signature.key id [])
  nativeType : lowered.type = CallableContract.functionType certificate.parameterCore certificate.resultCore
  emitted : SourceCoreSourceCells.copyScope (some (allocator whole.indexed named)) source scope (fun index => index)
    (decorated whole.indexed (context whole.indexed named) scope descriptor.id certificate.parameterCore
      certificate.resultCore certificate.rawBody) = .ok lowered.expression

private theorem read_of_accepted {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result statements)
    (special : DecoratedFunctionCode.SpecialPasses policy body fuel compilation source scope id reasonAt)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id
      reasonAt = .ok lowered) :
    id.occurrence.owner = source.owner ∧ ∃ pair, policy.readExpression source id = .ok pair := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · refine ⟨owner, ?_⟩
    change (match policy.lowerSpecial? with
      | none => pure none
      | some lower => lower compilation (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation
            childSource childScope childId childReasonAt) (fuel + 1) source scope id reasonAt) = .ok none at special
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted special
    all_goals try rw [special] at accepted
    all_goals
      simp only [form] at accepted
      obtain ⟨pair, read, _remaining⟩ := bind_ok accepted
      exact ⟨pair, read⟩
  · simp [owner, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted

/-- A lambda site of a named row and its accepted lowering under the named
policy supply the receipt. -/
theorem Receipt.of_site (generation : Compilation whole.indexed named diagnostics code) (rootFuel : Nat)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (site : LambdaSite whole.indexed named source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
      (namedLowerBody generation) (fuel + 1) (context whole.indexed named) source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt generation rootFuel fuel source scope id reasonAt lowered) := by
  have special : DecoratedFunctionCode.SpecialPasses (namedPolicy generation rootFuel) (namedLowerBody generation)
      fuel (context whole.indexed named) source scope id reasonAt :=
    CellAwareInvocationAcceptedLambdaSites.special generation site rootFuel _ _ scope reasonAt
  obtain ⟨owner, ⟨readNode, reported⟩, read⟩ := read_of_accepted site.found site.form special accepted
  have metadata := CompatibleExpressionReads.metadata_of_read
    ((CellAwareInvocationAcceptedLambdaSites.read generation site rootFuel).symm ▸ read)
  cases Option.some.inj (metadata.found.symm.trans site.found)
  obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted special owner site.found read site.form
    accepted
  have typeEq : lowered.type = reported := congrArg SourceCoreBasic.LoweredExpr.type certificate.emitted
  subst typeEq
  have callables := CellAwareNamedCallPorts.callable_policy generation (rootFuel := rootFuel)
  have checkedType := certificate.checked
  rw [callables] at checkedType
  have nativeType := ensure_type checkedType
  have hook : SourceCoreCallableIndexedAncestry.expressionHook whole.indexed.ancestry named.signature.key []
      (context whole.indexed named) source scope site.node certificate.parameterCore certificate.resultCore
      (.lambda certificate.parameterCore (LanguageResult.resultType certificate.resultCore) certificate.rawBody) =
        .ok certificate.rawLambda :=
    certificate.expressionHook
  obtain ⟨origin, rawBody, selected, raw, _, _, _, rawEmitted⟩ :=
    CallableIndexedFormation.expressionHook_receipt whole.indexed.ancestry hook
  rw [(lookupExpression?_sound site.found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  have sameOrigin : origin = descriptor.id := Option.some.inj (selected.symm.trans descriptor.found)
  have bodyEq : certificate.rawBody = rawBody := (Expr.lambda.inj raw).2.2
  have decoration := certificate.decoration
  rw [callables] at decoration
  have expected := ActualCallablePolicy.lambda_decoration whole.indexed.ancestry.graph.inputs.callable []
    (context whole.indexed named) source site.node id certificate.parameterCore certificate.resultCore
    (TaggedFunction.anonymous certificate.rawLambda) descriptor
  have expression := Except.ok.inj (decoration.symm.trans expected)
  have snapshot := certificate.snapshot
  change SourceCoreSourceCells.copyScope (some (allocator whole.indexed named)) source scope (fun index => index)
    certificate.expression = .ok certificate.snapshotted at snapshot
  have emitted : SourceCoreSourceCells.copyScope (some (allocator whole.indexed named)) source scope
      (fun index => index) (decorated whole.indexed (context whole.indexed named) scope descriptor.id
        certificate.parameterCore certificate.resultCore certificate.rawBody) = .ok lowered.expression := by
    rw [congrArg SourceCoreBasic.LoweredExpr.expression certificate.emitted, ← snapshot, expression, rawEmitted,
      sameOrigin, ← bodyEq]
    rfl
  exact ⟨⟨site.node, site.parameters, site.result, site.body, metadata, site.form, site.runtimeParameters,
    site.runtimeResult, accepted, certificate, descriptor, nativeType, emitted⟩⟩

/-- The node's Source type projects to the native function type. -/
theorem Receipt.projection {generation : Compilation whole.indexed named diagnostics code} {rootFuel fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt generation rootFuel fuel source scope id reasonAt lowered) :
    whole.compatible.checked.catalog.project receipt.node.type =
      .ok (CallableContract.functionType receipt.certificate.parameterCore receipt.certificate.resultCore) :=
  receipt.nativeType ▸ receipt.metadata.projected

/-- The node's Source type is the function type of every closure with the
receipt's lambda header. -/
theorem Receipt.source_type {generation : Compilation whole.indexed named diagnostics code} {rootFuel fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt generation rootFuel fuel source scope id reasonAt lowered) {function : Dynamic.Closure}
    (parameters : function.parameters = receipt.parameters) (result : function.resultType = receipt.result) :
    receipt.node.type = FunctionValues.sourceType function := by
  rw [receipt.certificate.sourceType, ← receipt.certificate.parameterTypes, FunctionValues.sourceType, parameters,
    result]

/-- The receipt gives the older route's static code of the same lambda at any
Source context and evidence: the site chosen by the producer's certificate
(`CallableIndexedLambdaGeneration.of_certificate`) with the row's body and
policy recipes at its own compilation and root fuel and the issued assignment
inventory, without a joint body. The native typing of the emitted code is the
one input the receipt does not carry; its Source is the row's own. -/
theorem Receipt.produced {generation : Compilation whole.indexed named diagnostics code} {rootFuel fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt generation rootFuel fuel source scope id reasonAt lowered)
    (profile : whole.compatible.checked.catalog.callableContracts = true)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
    (sourceEq : source = CallableIndexedNamedGeneration.source named)
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    {administrative : Core.Context}
    (typed : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      nativeType whole.indexed.layouts.definitions) :
    ∃ produced : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced (compiled := whole) named
        receipt.parameters receipt.result receipt.body sourceContext evidence scope administrative id lowered,
      produced.site.code.policy = namedPolicy generation rootFuel ∧
      produced.site.code.lowerBody = namedLowerBody generation ∧ produced.site.code.fuel = fuel ∧
      produced.site.code.view = source ∧ produced.site.code.reasonAt = reasonAt ∧
      produced.site.code.node = receipt.node ∧ HEq produced.site.code.receipt receipt.certificate := by
  obtain ⟨nativeType, nativeTyped⟩ := typed
  have callables := CellAwareNamedCallPorts.callable_policy generation (rootFuel := rootFuel)
  have typed := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native whole.indexed
    receipt.certificate receipt.metadata.found rfl callables nativeTyped
  subst sourceEq
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, sameFuel, sameView, sameReason, _sameSource, sameNode,
      sameReceipt⟩ :=
    CallableIndexedLambdaGeneration.of_certificate whole.indexed sourceContext evidence [] receipt.certificate
      receipt.accepted profile (LambdaMetadataViews.MetadataView.refl _) receipt.metadata.found receipt.form
      receipt.metadata.found rfl rfl rfl rfl callables rfl rfl typed
  have recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe generation site.code := sameBody
  have policy : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe generation rootFuel
      site.code.policy := by
    rw [samePolicy]
    exact GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel
  have binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy named site.code := by
    unfold CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy
    rw [samePolicy]
    rfl
  exact ⟨⟨diagnostics, code, generation, site, identifier, emitted, binderPolicy, recipe,
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes generation recipe policy site.compilation,
    CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained.of_recipes generation issued recipe policy
      site.compilation⟩, samePolicy, sameBody, sameFuel, sameView, sameReason, sameNode, sameReceipt⟩

/-- An older-route lambda site of the row at the same occurrence carries the
receipt's descriptor word. -/
theorem Receipt.code_descriptor {generation : Compilation whole.indexed named diagnostics code}
    {rootFuel fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt generation rootFuel fuel source scope id reasonAt lowered)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {captured : Dynamic.Environment} {administrative : Core.Context}
    (site : CallableIndexedLambdaGeneration.Site whole.indexed named parameters result statements sourceContext
      evidence captured scope administrative)
    (identifier : site.code.id = id) : site.code.descriptor.id = receipt.descriptor.id := by
  have found := site.code.descriptor.found
  generalize site.code.descriptor.id = word at found ⊢
  rw [site.compilation, site.active, identifier] at found
  exact Option.some.inj (found.symm.trans receipt.descriptor.found)

end Solcore.SourceSemantics.CoreLowering.CellAwareLambdaCertificates
end

section
/-! The Source side of a lambda site. The Source's lambda rule
(`Dynamic.ExpressionFormEvaluates.lambda`) is an atomic form: it forms the
closure over a copy of the creation environment (`Dynamic.EnvironmentCopies`)
at the current Source context and evidence, and no rule faults at a lambda.
Every original Source execution of an uncoerced lambda node and every staged
trace of one is therefore that closure, and the staged atomic value rule
carries it unchanged, as for a builtin or named function value. The lemmas
take the node's facts, which a site and a receipt both give; the liftings take
the site. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedLambdaLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareInvocationAcceptedLambdaSites (LambdaSite)

/-- The closure the Source's lambda rule forms for a lambda header. -/
def closure (parameters : List TypedBinder) (result : TypeSystem.Ty) (body : List StatementId)
    (source : TypedSource) (captured : Dynamic.Environment) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Dynamic.Closure where
  parameters := parameters
  resultType := result
  body := body
  source := source
  captured := captured
  context := context
  evidence := evidence

/-- At the row's own Source, it is the older route's generated closure. -/
theorem closure_generation (named : SourceCoreGeneralFunctions.Function) (parameters : List TypedBinder)
    (result : TypeSystem.Ty) (body : List StatementId) (captured : Dynamic.Environment)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    closure parameters result body (CallableIndexedNamedGeneration.source named) captured context evidence =
      CallableIndexedLambdaGeneration.closure named parameters result body context evidence captured := rfl

variable {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {body : List StatementId}

private theorem node_eq (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    {other : ExpressionNode} (contains : ContainsExpression source id other) : other = node :=
  Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)

private theorem not_local (form : node.form = .lambda parameters result body) {name : String}
    {binder : Resolved.LocalId} (reference : node.form = .reference name (.local binder)) : False := by
  rw [form] at reference
  cases reference

variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}

/-- An original Source execution of an uncoerced lambda node is the closure
over a copy of the creation environment. -/
theorem lambda_value (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) (coercions : node.coercions = []) {value : Dynamic.Value}
    (evaluation : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    ∃ captured, value = .closure (closure parameters result body source captured context evidence) ∧
      Dynamic.EnvironmentCopies source environment before captured after := by
  cases evaluation with
  | intro contains raw path =>
    have same := node_eq unique found contains
    subst same
    rw [coercions] at path
    cases path
    rw [form] at raw
    cases raw with
    | lambda _ snapshot => exact ⟨_, rfl, snapshot⟩
  | _ =>
    exact (not_local form ((congrArg ExpressionNode.form
      (node_eq unique found ‹ContainsExpression _ _ _›)).symm.trans ‹_›)).elim

/-- No Source rule faults at an uncoerced lambda node. -/
theorem lambda_no_fault (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) (coercions : node.coercions = [])
    {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before id reason after) :
    False := by
  cases failed with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found)
  | form contains raw =>
    have same := node_eq unique found contains
    subst same
    rw [form] at raw
    cases raw
  | coercion contains _ path =>
    have same := node_eq unique found contains
    subst same
    rw [coercions] at path
    cases path
  | _ =>
    exact not_local form ((congrArg ExpressionNode.form
      (node_eq unique found ‹ContainsExpression _ _ _›)).symm.trans ‹_›)

variable {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}

private theorem no_stage (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (coercions : node.coercions = []) {failedScope : Staging.Recursive.Scope} {call : ExpressionId}
    {reason : Staging.CallGuard.Fault}
    (trace : Staging.Recursive.Expression program registry scope context environment before id
      (.fault (.stage failedScope call reason)) after) : False := by
  have occurs : ∀ {shape requirements}, Staging.Recursive.Occurrence scope id shape requirements →
      shape = .lambda parameters result body := by
    intro shape requirements occurrence
    obtain ⟨other, contains, same, _, _⟩ := occurrence
    exact same.symm.trans ((congrArg ExpressionNode.form (node_eq unique found contains)).trans form)
  cases trace
  all_goals first
    | (cases occurs ‹Staging.Recursive.Occurrence _ _ _ _›; done)
    | (cases occurs ‹Staging.Recursive.Occurrence _ _ _ _›; cases ‹Staging.Recursive.arrayChildren _ = some _›)
    | exact absurd ((congrArg ExpressionNode.coercions (node_eq unique found ‹ContainsExpression _ _ _›)).trans
        coercions) ‹_›
    | exact not_local form ((congrArg ExpressionNode.form
        (node_eq unique found ‹ContainsExpression _ _ _›)).symm.trans ‹_›)

/-- Every staged trace of an uncoerced lambda node is the Source's lambda rule:
the closure over a copy of the creation environment, at the scope's evidence. -/
theorem staged (unique : NodeOccurrencesUnique scope.source) (found : scope.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) (coercions : node.coercions = [])
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Expression program registry scope context environment before id outcome after) :
    ∃ captured, outcome = .value (.closure (closure parameters result body scope.source captured context
        scope.evidence)) ∧ Dynamic.EnvironmentCopies scope.source environment before captured after := by
  cases outcome with
  | value value =>
    obtain ⟨captured, rfl, copies⟩ := lambda_value unique found form coercions trace.value_plain
    exact ⟨captured, rfl, copies⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact (lambda_no_fault unique found form coercions trace.semanticFault_plain).elim
    | stage failedScope call reason => exact (no_stage unique found form coercions trace).elim

/-- A copy of the creation environment gives the sized staged atomic value of
an uncoerced lambda node without requirements, as the reflection of its native
formation needs. -/
theorem lambda_rule (found : scope.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) (coercions : node.coercions = [])
    (requirements : node.requirements = []) {captured : Dynamic.Environment}
    (copies : Dynamic.EnvironmentCopies scope.source environment before captured after) :
    Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize []) scope context environment
      before id (.value (.closure (closure parameters result body scope.source captured context scope.evidence)))
      after := by
  apply Staging.Recursive.Size.Expression.atomicValue (lookupExpression?_sound found)
    (form ▸ Staging.Recursive.AtomicForm.lambda _ _ _) coercions
  rw [form, requirements]
  exact Dynamic.ExpressionFormEvaluates.lambda rfl copies

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function}

/-- A sized value execution of a lambda site is the staged atomic value. -/
theorem lambda_lift (unique : NodeOccurrencesUnique scope.source) (site : LambdaSite prepared named scope.source id)
    {size : Nat} {value : Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
      before id value after) :
    Staging.Recursive.Expression program registry scope context environment before id (.value value) after :=
  Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound site.found)
    (by rw [site.form]; exact .lambda _ _ _) site.coercions
    (fun _ _ same => not_local site.form same) (.value trace.sound)

/-- A lambda site has no sized fault execution, so its fault lifting holds
vacuously. -/
theorem lambda_lift_fault (unique : NodeOccurrencesUnique scope.source)
    (site : LambdaSite prepared named scope.source id) {size : Nat} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment
      before id reason after) :
    Staging.Recursive.Expression program registry scope context environment before id
      (.fault (.semantic reason)) after :=
  (lambda_no_fault unique site.found site.form site.coercions trace.sound).elim

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedLambdaLifting
end
