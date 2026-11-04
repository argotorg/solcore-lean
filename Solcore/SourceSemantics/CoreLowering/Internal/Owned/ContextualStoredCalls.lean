import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds

/-!
# Owned callables: contextual stored calls

Type and origin receipts of contextual stored calls, member call bounds and stored expression heads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSamePolicyCompilerLeafReceipts
/-! Genuine extra leaves use the actual root policy at each child fuel.
Lambda joint bodies and indirect children retain their literal compiler factory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSamePolicyCompilerLeafReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedPreparedOrdinaryLambdaFormation
open CallableIndexedOwnedContextualCompilerPolicyProfiles

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
      rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- The same-policy certificate chooses one Site, whose genuine dependent
collector inputs build its joint body. The root policy is never reselected. -/
theorem lambda_of_accepted_with_inputs
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    {childFuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source caller.named) view)
    (sourceFound : (source caller.named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result statements)
    (rawType : sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements sourceContext evidence []))
    (rawOrdinary : Dynamic.OrdinaryRequirementLayout sourceNode.requirements sourceNode.coercions [])
    (rawCoercions : sourceNode.coercions = [])
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions)
    (inputProperty : ∀ {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered),
      CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller produced → Prop)
    (siteInputs : ∀ produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered,
      produced.diagnostics = diagnostics → produced.namedCode = namedCode → HEq produced.compilation compilation →
      produced.site.code.policy = root.selected.policy → produced.site.code.lowerBody = root.selected.lowerBody →
      produced.site.code.fuel = childFuel → produced.site.code.view = view → produced.site.code.reasonAt = reasonAt →
      ∃ inputs : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller produced,
        inputProperty produced inputs) :
    ∃ certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) view scope id node parameters result statements reported reasonAt lowered,
      ∃ receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
          sourceContext evidence scope id lowered,
        receipt.formation.produced.site.code.policy = root.selected.policy ∧
        receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody ∧
        receipt.formation.produced.site.code.fuel = childFuel ∧
        receipt.formation.produced.site.code.view = view ∧
        receipt.formation.produced.site.code.reasonAt = reasonAt ∧
        HEq receipt.formation.produced.site.code.receipt certificate ∧
        ∃ inputs : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller receipt.formation.produced,
          inputProperty receipt.formation.produced inputs ∧
          receipt.formation.expressionSyntax = inputs.expressionSyntax ∧
          receipt.formation.certificates = inputs.certificates ∧
          receipt.formation.body.readFuel = inputs.readFuel ∧
          HEq receipt.formation.body.toContext inputs.entry := by
  have pointwise := lambda_policy root (scope := scope) (reasonAt := reasonAt) found (form.trans sourceForm) requirements coercions ordinary
  have special : DecoratedFunctionCode.SpecialPasses root.selected.policy root.selected.lowerBody childFuel
      (context compiled.indexed caller.named) view scope id reasonAt := by
    exact pointwise.special _ _
  obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted special owner found
    (pointwise.read.trans read) (form.trans sourceForm) accepted
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, sameFuel, sameView, sameReason, sameSourceNode,
      _sameNode, sameCertificate⟩ :=
    of_certificate compiled.indexed sourceContext evidence [] certificate accepted profile viewOfSource sourceFound
      sourceForm found form root.sourceCells root.rawLambdaBody root.rawLambdaExpression root.callables root.projectType
      (by rw [root.compilerPolicy.snapshotLambda]) typed
  have compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named site.code := by
    apply CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes (rootFuel := rootFuel) compilation
      (sameBody.trans root.selected.recipe) _ site.compilation
    rw [samePolicy]
    exact root.compilerPolicy
  have issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained caller.named site.code := by
    apply CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained.of_recipes (rootFuel := rootFuel)
      compilation issued (sameBody.trans root.selected.recipe) _ site.compilation
    rw [samePolicy]
    exact root.compilerPolicy
  let produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered :=
    ⟨diagnostics, namedCode, compilation, site, identifier, emitted,
      (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans root.selected.binder,
      sameBody.trans root.selected.recipe, compilerPolicy, issuedRecipe⟩
  obtain ⟨inputs, chosen⟩ := siteInputs produced rfl rfl (HEq.refl compilation) samePolicy sameBody sameFuel sameView sameReason
  obtain ⟨body, entryEq, readFuelEq⟩ := at_site produced.compilation produced.site produced.recipe
    (Program.ofChecked compiled.sourceProgram) inputs.entry inputs.frame inputs.expressionSyntax inputs.certificates
    inputs.readFuel inputs.diagnosticPolicy inputs.issued.invalidOperand inputs.issued.invalidUnary
    inputs.issued.invalidProjection inputs.issued.missingDefault inputs.edited inputs.avoids inputs.unique
    inputs.sameLedger inputs.syntaxTransport inputs.expressions inputs.syntaxTree inputs.viewSyntax inputs.projection
    inputs.static inputs.nativeTyped
  let formation : Formation caller sourceContext evidence scope id lowered := {
    parameters := parameters, result := result, statements := statements, produced := produced
    expressionSyntax := inputs.expressionSyntax, certificates := inputs.certificates, issued := inputs.issued
    diagnosticPolicy := inputs.diagnosticPolicy, body := body
    bodyView := fun _ reached => CallableLambdaBodyReachability.expression_lookup inputs.edited inputs.avoids reached
    bodyReasons := inputs.bodyReasons
    declarations := inputs.declarations
    sourceType := sameSourceNode ▸ rawType, ordinary := sameSourceNode ▸ rawOrdinary, coercions := sameSourceNode ▸ rawCoercions }
  let receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
      sourceContext evidence scope id lowered := ⟨formation, rfl, rfl, HEq.refl compilation⟩
  exact ⟨certificate, receipt, samePolicy, sameBody, sameFuel, sameView, sameReason, sameCertificate,
    inputs, chosen, rfl, rfl, readFuelEq, heq_of_eq entryEq⟩

/- The original endpoint forgets only the selected input companion. -/
theorem lambda_of_accepted
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    {childFuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source caller.named) view)
    (sourceFound : (source caller.named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result statements)
    (rawType : sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements sourceContext evidence []))
    (rawOrdinary : Dynamic.OrdinaryRequirementLayout sourceNode.requirements sourceNode.coercions [])
    (rawCoercions : sourceNode.coercions = [])
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions)
    (siteInputs : ∀ produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered,
      produced.diagnostics = diagnostics → produced.namedCode = namedCode → HEq produced.compilation compilation →
      produced.site.code.policy = root.selected.policy → produced.site.code.lowerBody = root.selected.lowerBody →
      produced.site.code.fuel = childFuel → produced.site.code.view = view → produced.site.code.reasonAt = reasonAt →
      Nonempty (CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.SiteInputs caller produced)) :
    ∃ certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) view scope id node parameters result statements reported reasonAt lowered,
      ∃ receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
          sourceContext evidence scope id lowered,
        receipt.formation.produced.site.code.policy = root.selected.policy ∧
        receipt.formation.produced.site.code.lowerBody = root.selected.lowerBody ∧
        receipt.formation.produced.site.code.fuel = childFuel ∧
        receipt.formation.produced.site.code.view = view ∧
        receipt.formation.produced.site.code.reasonAt = reasonAt ∧
        HEq receipt.formation.produced.site.code.receipt certificate := by
  obtain ⟨certificate, receipt, samePolicy, sameBody, sameFuel, sameView, sameReason, sameCertificate,
      _inputs, _chosen⟩ :=
    lambda_of_accepted_with_inputs root issued sourceContext evidence profile viewOfSource sourceFound sourceForm
      rawType rawOrdinary rawCoercions found form owner requirements coercions ordinary read accepted typed
      (fun _ _ => True) (fun produced diagnosticsEq codeEq compilationEq policyEq bodyEq fuelEq viewEq reasonEq => by
        obtain ⟨inputs⟩ := siteInputs produced diagnosticsEq codeEq compilationEq policyEq bodyEq fuelEq viewEq reasonEq
        exact ⟨inputs, trivial⟩)
  exact ⟨certificate, receipt, samePolicy, sameBody, sameFuel, sameView, sameReason, sameCertificate⟩

/-- The actual indirect invocation retains the physical children, raw row and
prepared callsite under the same root policy at its child fuel. -/
theorem indirect_of_accepted
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (factory : CallableIndexedOwnedIndirectCompilerReceipts.Factory caller diagnostics namedCode compilation
      source sourceContext evidence scope administrative certificates)
    {childFuel : Nat} {id callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none)
    (typed : ExpressionHasType source sourceContext id node.type) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) source scope id reasonAt = .ok lowered) :
    Nonempty (CallableIndexedOwnedIndirectCompilerReceipts.Receipt compiled.indexed.ancestry.graph.inputs.callable [] factory
      (policy := root.selected.policy) (body := root.selected.lowerBody) (fuel := childFuel)
      (id := id) (callee := callee) (ids := ids) (metadata := metadata) (reasonAt := reasonAt) (lowered := lowered)) := by
  have pointwise := indirect_policy root (scope := scope) (reasonAt := reasonAt) found form requirements coercions arguments ordinary
  exact CallableIndexedOwnedIndirectCompilerReceipts.Receipt.of_functions factory _ [] found form typed unique
    pointwise.special pointwise.read root.callables accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSamePolicyCompilerLeafReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallTypeReceipts
/-! Actual successful callee posts retain a positive static closure member, the genuine
raw Source type and the native compiler type at the same reached state. These
finite projections derive the ordered Source and native aggregate equalities
needed by receiving-model stored calls. Physical binder arity and stage gates
remain independent receipts. The body registry stays distinct from outer
payload metadata; no hidden Code equality or registry rebasing is inferred. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallTypeReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualTypedClosureReceipts (StaticMember)
open CallableIndexedOwnedContextualCellOrigins
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)
open CallableIndexedOwnedStoredNativePackReceipts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {native : Core.Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Core.Ty}

/-- The original contextual producer retains each canonical binder projection,
for ordinary and principal members alike. Only the positive member is used. -/
theorem member_projected_bindings
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 :=
  member.projected_bindings

/-- Original Tree indices retain both physical ordered vector lengths. Packed
type equality is not used to recover either length or binder arity. -/
theorem tree_counts {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes) :
    ids.length = types.length ∧ ids.length = codes.length := by
  induction tree with
  | nil => exact ⟨rfl, rfl⟩
  | single _ _ => exact ⟨rfl, rfl⟩
  | cons _ _ _ ih => exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

section Call
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {heap : Dynamic.Heap} {calleeNode : ExpressionNode}

/-- Genuine raw closure typing aligns the original parent argument row with
this member's Source binders. The parent's actual empty output path fixes the
raw result type. No native signature or descriptor determines a Source type. -/
theorem source_aggregates
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeTyped : Dynamic.ValueHasType context heap (.closure function) calleeNode.type)
    (member : StaticMember headers keys bodyRegistry faults mapping world
      function native bindings parameterCore resultCore) :
    ExpressionsHaveTypes source context ids sourceTypes ∧
    TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) ∧
    compiler.original.type = function.resultType := by
  generalize reportedEq : compiler.original.type = reported at parentTyped
  cases parentTyped with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans compiler.found)
    subst actualNode
    rw [compiler.originalForm] at raw
    cases raw with
    | indirectCall calleeTyping argumentsTyping application =>
      have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
        unique calleeFound calleeTyping
      rw [reported] at calleeTyped
      have closure := Dynamic.ValueHasType.closure_function_inv calleeTyped
      have row := CallableIndexedOwnedContextualInitializedClosureReceipts.source_types_at_tree
        unique tree argumentsTyping
      have bundle := CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle
        application compiler.argumentCoercions
      have sourceBundle : TypeSystem.Ty.productMany sourceTypes =
          TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) := by
        rw [← row]
        exact bundle.trans (closure.1.trans (congrArg TypeSystem.Ty.productMany member.source_binders.symm))
      have result := requirements.outputPath.foldl_target
      rw [parent.coercions, List.foldl_nil] at result
      exact ⟨row ▸ argumentsTyping, sourceBundle, result.symm.trans closure.2.1⟩

/-- Actual native typing aligns the compiler's two types with the retained
member. Only runtime typing is needed here, so body and payload registries
are not identified to invoke a one-registry representation helper. -/
theorem native_parameters
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore)
    (typed : RuntimeValueHasType world native compiler.calleeCode.type compiled.indexed.layouts.definitions) :
    compiler.parameterType = parameterCore ∧ compiler.resultType = resultCore := by
  have accepted := compiler.callableType
  rw [actualFunctionType] at accepted
  have selected := member.native_type
  exact callable_parameters (accepted.trans (typed.type_eq.symm.trans selected))

/-- The positive member and all aggregates belong to the original caller's
actual compiler vector. This receipt deliberately carries no stage verdict or
binder-count equality, which need separate genuine acceptance facts. -/
structure TypedCallAt : Prop where
  member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore
  arguments : ExpressionsHaveTypes source context ids sourceTypes
  sourceCount : ids.length = sourceTypes.length
  compilerCount : ids.length = compiler.codes.length
  sourceBundle : TypeSystem.Ty.productMany sourceTypes =
    TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body))
  nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
    SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)
  rawResult : compiler.original.type = function.resultType
  nativeParameter : compiler.parameterType = parameterCore
  nativeResult : compiler.resultType = resultCore
  rawCalleeView : SourceCoreRawMetadata.runtimeType calleeNode.type =
    SourceCoreRawMetadata.runtimeType (FunctionValues.sourceType function)

/-- Positive classification projects the real static member and its syntax/owner;
actual raw typing and native typing then derive the required aggregate facts.
The original callee node is supplied by its real Source lookup. -/
theorem at_typed_callee
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeTyped : Dynamic.ValueHasType context heap (.closure function) calleeNode.type)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (payload : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      calleeNode.type (.closure function) native compiler.calleeCode.type) :
    ∃ bindings parameterCore resultCore,
      TypedCallAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := faults)
        (mapping := mapping) (world := world) (function := function) (native := native)
        (bindings := bindings) (parameterCore := parameterCore) (resultCore := resultCore)
        (context := context) (sourceTypes := sourceTypes) (calleeNode := calleeNode) compiler := by
  obtain ⟨bindings, parameterCore, resultCore, member, _nativeView, rawView⟩ :=
    (CallableIndexedOwnedContextualCalleeOriginReadReceipts.callable_at profile payload
      (.closure function)).closure_member
  obtain ⟨arguments, sourceBundle, rawResult⟩ :=
    source_aggregates compiler parent tree unique parentTyped calleeFound calleeTyped member
  have nativeTypes := native_parameters compiler actualFunctionType member payload.runtime_hasType
  have bindingPack := member.parameter_core profile
  have nativeBundle := (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
    (compiler.packedType.symm.trans (nativeTypes.1.trans bindingPack))
  have counts := tree_counts tree
  exact ⟨bindings, parameterCore, resultCore,
    member, arguments, counts.1, counts.2, sourceBundle, nativeBundle, rawResult,
    nativeTypes.1, nativeTypes.2, rawView⟩

/-- The genuine successful child post supplies raw closure typing and positive
payload at its exact reached state. Admission and cells remain at that same
witness; this static adapter performs no callee evaluation or invocation. -/
theorem at_callee_post
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    {index : ProtectedStateTransition.Index}
    (reached : callerProtocol.State index)
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile calleeNode.type compiler.calleeCode.type
      (.value (.closure function)) (.inRight .word native) reached) :
    ∃ bindings parameterCore resultCore,
      TypedCallAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := faults)
        (mapping := index.mapping) (world := index.world) (function := function) (native := native)
        (bindings := bindings) (parameterCore := parameterCore) (resultCore := resultCore)
        (context := context) (sourceTypes := sourceTypes) (calleeNode := calleeNode) compiler ∧
      CallableIndexedOwnedSourceAdmission.Admission bridge context reached ∧
      CellOrigins headers keys bodyRegistry registry faults profile
        index.mapping index.world index.heap index.store := by
  have successful := post.at_value
  obtain ⟨bindings, parameterCore, resultCore, typed⟩ :=
    at_typed_callee compiler parent tree unique parentTyped calleeFound successful.2.1 profile
      actualFunctionType successful.2.2
  exact ⟨bindings, parameterCore, resultCore, typed, successful.1, post.cells⟩

end Call
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallTypeReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
/-! Original indirect Source typing fixes the raw callee and argument bundle
before selecting any runtime function leaf. Empty compiler output coercions
retain the same raw result. Physical argument count remains independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}

include compiler in
/-- These facts come from the accepted parent and its actual ordered compiler
Tree. No closure representation, application trace or body law is used. -/
theorem original_rows
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode) :
    ∃ parameter result,
      calleeNode.type = .function parameter result ∧
      ExpressionsHaveTypes source context ids sourceTypes ∧
      TypeSystem.Ty.productMany sourceTypes = parameter ∧
      compiler.original.type = result := by
  generalize reportedEq : compiler.original.type = reported at parentTyped
  cases parentTyped with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans compiler.found)
    subst actualNode
    rw [compiler.originalForm] at raw
    cases raw with
    | indirectCall calleeTyping argumentsTyping application =>
      have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
        unique calleeFound calleeTyping
      have row := CallableIndexedOwnedContextualInitializedClosureReceipts.source_types_at_tree
        unique tree argumentsTyping
      have bundle := CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle
        application compiler.argumentCoercions
      have result := requirements.outputPath.foldl_target
      rw [parent.coercions, List.foldl_nil] at result
      exact ⟨_, _, reported, row ▸ argumentsTyping, by simpa only [← row] using bundle, result.symm⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAcceptedIndirectPhysicalArity
/-! An accepted second gate recovers physical arity from its actual selected
codebook row. Closure and named parameter counts use original contract binding.
Packed Source or native types are not used to recover list lengths. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAcceptedIndirectPhysicalArity
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)

section Row
variable {sidecar : SourceCoreStageContracts.Sidecar}
  {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {row : SourceCoreStageCodebook.Decision} {contract unknown : Word}

/-- The original selected decision, rather than the callee's type, fixes this
accepted physical argument count. Unknown descriptors cannot supply it. -/
theorem selected_count
    (selected : Selected sidecar site callee ids metadata node row)
    (found : site.rowAt? contract = some row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown contract = none) :
    row.entry.parameterCount = ids.length := by
  rw [site.decision_known .beforeApplication unknown contract row found] at accepted
  by_cases same : row.entry.parameterCount = row.argumentCount
  · exact same.trans selected.argument_count
  · have rejected := SourceCoreCallableContracts.reason_rejected row site.reasonAt
      .beforeApplication _ (row.afterArguments_mismatch same)
    rw [rejected] at accepted
    cases accepted
end Row

section Closure
variable {sidecar : SourceCoreStageContracts.Sidecar}
  {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.Closure} {native : Value} {unknown : Word}

/-- The real closure binding identifies the retained contract's ordered
parameters; successful gate selection then supplies their physical count. -/
theorem closure_count
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.closure function) native)
    (selected : Selected sidecar site callee ids metadata node dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none) :
    function.parameters.length = ids.length := by
  have retained := CallableIndexedOwnedStoredIndirectCallBounds.selected_contract dispatch selected
  have count : dispatch.row.entry.parameterCount = function.parameters.length := by
    cases dispatch.bound with
    | closure parameters _ =>
      exact (selected.parameter_count retained).trans (congrArg List.length parameters)
  exact count.symm.trans (selected_count selected dispatch.found accepted)
end Closure

section Named
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {function : Dynamic.GlobalFunction} {sidecar : SourceCoreStageContracts.Sidecar}
  {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {native : Value} {unknown : Word}

/-- Full named Source authority and the same caller preparation identify the
actual Header parameters before the accepted gate recovers their length. -/
theorem named_count
    (sourceAt : NamedSourceAt header rawD function)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : Selected sidecar site callee ids metadata node dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none) :
    header.function.parameters.length = ids.length :=
  (CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count sourceAt caller dispatch selected).symm.trans
    (selected_count selected dispatch.found accepted)
end Named
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAcceptedIndirectPhysicalArity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredMemberCallBounds
/-! Positive ordinary or principal stored members construct their actual
callable origin and initialized callee post. The same selected carrier tag,
ordered argument receipts and genuine strict joint continuations feed the
original whole-call proofs. The member's hidden code is never reclassified. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredMemberCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedStoredClosureArgumentReceipts
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Only the positive constructor is projected. Its actual Source authority,
code and history produce origin for exactly its retained native carrier. -/
theorem member_stage_origin {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Core.Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : Member headers keys registry faults mapping world function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases member with
  | ordinary _ captured code history support _ _ _ _ _ _ _ =>
    exact CallableIndexedOwnedOrdinaryLambdaSupport.Support.stage_origin captured code support history
  | principal _ captured code history support _ _ _ _ _ _ _ =>
    exact CallableIndexedOwnedMethodLambdaSupport.Support.stage_origin captured code support history

variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {certificate : GenericExpressionMeaning.Certificate}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {captureScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world captureScope function.captured capturedActual)
  (code : Code compiled.indexed function captureScope captured.administrative)
  (history : History code)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared code)

local notation "carrier" => CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual
local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

section Static
variable {context : SourceSemantics.Context}
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)

include selected unique parentTyped in
/-- The original Source row and selected physical vector retain ordered
binder equality, count and native packing independently of any body law. -/
theorem argument_rows :
    ExpressionsHaveTypes source context ids (code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) ∧
    ids.length = code.receipt.loweredParameters.length ∧
    SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) := by
  obtain ⟨_parameter, _result, _types, _calleeTyped, argumentsTyped, _application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  have row := CallableIndexedOwnedContextualInitializedClosureReceipts.source_types_at_tree
    unique selected.children argumentsTyped
  have counts := congrArg List.length selected.nativeTypes
  simp only [List.length_map] at counts
  exact ⟨row ▸ argumentsTyped, compiler.ordered_children.1.trans counts,
    congrArg SourceCoreCompatibleCatalog.packTypes selected.nativeTypes⟩

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (member : Member headers keys registry faults mapping world function
    (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
    code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)

include member caller in
/-- Caller preparation transports the retained positive member origin to the
same exact plan and table used by the original callsite. -/
theorem member_origin_at_caller :
    CallableLedger.OriginRep sidecar.plan prepared.site.table (.closure function) carrier := by
  have plan := (CallContractCertificates.sidecar_of_accepted caller).1
  simpa only [plan, prepared.table] using (member_stage_origin member)

include member selected caller sidecarSource in
/-- Original codebook rows construct Dispatch. Its actual carrier word fixes
only the descriptor ID, preserving the member's distinct hidden code. The
same selected first decision reconstructs the authentic Source guard. -/
theorem dispatch_at_member :
    ∃ _dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site
        prepared.site.call ids (.closure function) carrier,
      Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function) := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  have atSite := stages.accepted
  rw [← prepared.table] at atSite
  have contains : ContainsExpression sidecar.source prepared.site.call compiler.original := by
    rw [sidecarSource, prepared.call]
    exact lookupExpression?_sound compiler.found
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection atSite caller contains compiler.originalForm
  have origin := member_origin_at_caller (prepared := prepared) (member := member) (caller := caller)
  have binding : ∃ contract, (CallableLedger.frame sidecar).Binds (.closure function) contract := by
    generalize carrier_eq : carrier = native at origin
    cases origin with
    | closure _ _ _ actualOrigin => exact ⟨_, actualOrigin.binds⟩
  obtain ⟨_contract, bound⟩ := binding
  obtain ⟨dispatch⟩ := CallableLedger.dispatch rows origin bound
  have descriptor : dispatch.contract = code.descriptor.id :=
    (Core.Value.word.inj (Core.Value.pair.inj dispatch.shape).2).symm
  have decision : CallableContract.decision prepared.site.gates .beforeArguments
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
    rw [descriptor]
    exact selected.stageAccepted
  have noReason := (prepared.site.decision_known .beforeArguments
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
    dispatch.contract dispatch.row dispatch.found).symm.trans decision
  have passed : dispatch.row.beforeArguments = .ok () := by
    cases answer : dispatch.row.beforeArguments with
    | ok accepted => cases accepted; rfl
    | error error =>
      have rejected := SourceCoreCallableContracts.reason_rejected dispatch.row prepared.site.reasonAt
        .beforeArguments error answer
      rw [rejected] at noReason
      cases noReason
  exact ⟨dispatch, dispatch.accepted_iff.mp passed⟩
end Static

section LiveCallee
variable {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (stored : CallableIndexedOwnedContextualInitializedClosureReceipts.StoredAt headers keys registry faults
    mapping world heap store location function
    (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual) code.receipt.loweredParameters
    code.receipt.parameterCore code.receipt.resultCore)
  {readFuel : Nat} {readReason : Word} {readCode : Expr}
  (read : CompatibleExpressionReads.Certificate readFuel (.initial compiled.compatible.checked)
    source scope callee readReason readCode)
  (sameCode : compiler.calleeCode.expression = readCode)
  (sameType : compiler.calleeCode.type = read.type)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (binding : CompatibleExpressionReads.StaticBinding read context)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (lookup : Dynamic.Environment.LooksUp environment read.binder location)
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
  (admitted : Admission bridge context initial)

include stored read sameCode sameType extension binding unique parentTyped environments heaps locals agrees lookup admitted in
/-- The actual initialized read derives its own Source trace, full ValuePost
and retained positive association at the identical caller tuple. -/
theorem callee_at_stored :
    ∃ sourceSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment heap callee (.closure function) heap ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := read.node) (context := context)
        bridge functions compiler initial (.closure function) heap carrier store mapping world ∧
      CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
        function carrier code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨_parameter, _result, _types, calleeTyped, _argumentsTyped, _application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique read.metadata.found calleeTyped
  have readTyped : ExpressionHasType source context callee read.node.type := by
    rw [reported]
    exact calleeTyped
  obtain ⟨sourceSize, sourceTrace, post, association, _selection, _stored⟩ :=
    CallableIndexedOwnedContextualInitializedClosureReceipts.callee_post
      (certificate := read) (bridge := bridge) (compiler := compiler) (initial := initial) (evidence := evidence)
      (profile := profile) (extension := extension) (binding := binding) (unique := unique)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (stored := stored) (lookup := lookup) (sameCode := sameCode) (sameNode := rfl)
      (sameType := sameType) (sourceTyped := readTyped) (admitted := admitted)
  exact ⟨sourceSize, sourceTrace, post, association⟩

variable (parent : SourceParent compiler)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include selected stored read sameCode sameType extension binding unique parentTyped environments heaps locals agrees lookup admitted
  parent wellFormed runtime covers typed caller sidecarSource in
/-- Both positive member alternatives feed one original whole preservation
proof at their actual callee post. Strict argument and body continuations
remain universal inputs; the returned pool, effects and admission stay causal. -/
theorem preserves_at_stored (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment heap ids function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment heap id outcome after ∧
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨_sourceSize, sourceTrace, post, association⟩ := callee_at_stored
    (bridge := bridge) (profile := profile) (compiler := compiler)
    (stored := stored) (read := read) (sameCode := sameCode) (sameType := sameType) (extension := extension)
    (binding := binding) (unique := unique) (parentTyped := parentTyped) (environments := environments)
    (heaps := heaps) (locals := locals) (agrees := agrees) (lookup := lookup)
    (initial := initial) (admitted := admitted)
  obtain ⟨calleeEvaluation, _represented, calleeHeaps, maps, worlds, frame, metadata,
    reached, related, _calleeAdmission⟩ := post
  obtain ⟨_sourceArguments, binderCount, nativeBundle⟩ := argument_rows
    (compiler := compiler) (prepared := prepared) (code := code) (selected := selected)
    (unique := unique) (parentTyped := parentTyped)
  obtain ⟨dispatch, accepted⟩ := dispatch_at_member
    (compiler := compiler) (prepared := prepared) (captured := captured) (code := code)
    (history := history) (selected := selected) (member := stored.1)
    (caller := caller) (sidecarSource := sidecarSource)
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  exact CallableIndexedOwnedStoredIndirectCallBounds.preserves_selected
    bridge profile compiler prepared parent selected.children unique parentTyped wellFormed runtime covers
    environments locals agrees typed initial admitted reached related maps worlds frame metadata
    association calleeHeaps binderCount rfl nativeBundle selected.rawResult selected.nativeResult
    stages caller sidecarSource dispatch accepted sourceTrace calleeEvaluation
    budget children below suffix argumentsWithin callWithin

include selected stored read sameCode sameType extension binding unique parentTyped environments heaps locals agrees lookup admitted
  parent wellFormed runtime covers typed caller sidecarSource in
/-- Finite native whole-call reflection retains its actual application grade
and returns an independent Source grade with the same caller post. -/
theorem reflects_at_stored (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {value : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment heap id outcome after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨_sourceSize, sourceTrace, post, association⟩ := callee_at_stored
    (bridge := bridge) (profile := profile) (compiler := compiler)
    (stored := stored) (read := read) (sameCode := sameCode) (sameType := sameType) (extension := extension)
    (binding := binding) (unique := unique) (parentTyped := parentTyped) (environments := environments)
    (heaps := heaps) (locals := locals) (agrees := agrees) (lookup := lookup)
    (initial := initial) (admitted := admitted)
  obtain ⟨calleeEvaluation, _represented, calleeHeaps, maps, worlds, frame, metadata,
    reached, related, _calleeAdmission⟩ := post
  obtain ⟨_sourceArguments, binderCount, nativeBundle⟩ := argument_rows
    (compiler := compiler) (prepared := prepared) (code := code) (selected := selected)
    (unique := unique) (parentTyped := parentTyped)
  obtain ⟨dispatch, accepted⟩ := dispatch_at_member
    (compiler := compiler) (prepared := prepared) (captured := captured) (code := code)
    (history := history) (selected := selected) (member := stored.1)
    (caller := caller) (sidecarSource := sidecarSource)
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  exact CallableIndexedOwnedStoredIndirectCallBounds.reflects_selected
    bridge profile compiler prepared parent selected.children unique parentTyped wellFormed runtime covers
    environments locals agrees typed initial admitted reached related maps worlds frame metadata
    association calleeHeaps binderCount rfl nativeBundle selected.rawResult selected.nativeResult
    stages caller sidecarSource dispatch accepted sourceTrace calleeEvaluation
    budget children below completed within
end LiveCallee
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredMemberCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualPrincipalStoredCallReceipts
/-! Actual contextual principal formation supplies the positive member used by
the shared stored-call adapters. Method authority, Source origin, leading
bundle and same-body PrincipalAt remain genuine retained fields. The original
Selection supplies its exact escaped-control row; live reads stay explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualPrincipalStoredCallReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedOwnedContextualLambdaProvenance (PrincipalAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
  (owner : OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {parentScope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source parentScope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared code)

section ExistingMember
variable (history : History code)
  (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
  (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
  (nativeTyped : RuntimeValueHasType world (value code captured.embedding history.native actual)
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (provenance : PrincipalAt code support)

include selected origin globals leading referenceIndex nativeTyped provenance in
/-- The real principal branch retains its complete same-Code provenance and
uses the original selected compiler row, without rank or authority recovery. -/
theorem member_from_selection :
    Member headers keys registry faults mapping world function
      (value code captured.embedding history.native actual) code.receipt.loweredParameters
      code.receipt.parameterCore code.receipt.resultCore :=
  Member.principal owner captured code history support origin globals leading referenceIndex
    nativeTyped provenance selected.escaped

variable {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Nat}
  (reference : ReferenceRepresents mapping world location target
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore))
  (sourceRead : Dynamic.Heap.Reads heap location ⟨FunctionValues.sourceType function, some (.closure function), none⟩)
  (nativeRead : store.read? target = some (.inRight .unit (value code captured.embedding history.native actual)))

include selected origin globals leading referenceIndex nativeTyped provenance reference sourceRead nativeRead in
/-- Only actual initialized Source/native cell reads are attached. This
positive receipt feeds both shared whole-call directions at their real state. -/
theorem stored_from_selection :
    CallableIndexedOwnedContextualInitializedClosureReceipts.StoredAt headers keys registry faults
      mapping world heap store location function (value code captured.embedding history.native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
  ⟨member_from_selection (captured := captured) (code := code) (support := support) (owner := owner)
    (selected := selected) (history := history) (origin := origin) (globals := globals) (leading := leading)
    (referenceIndex := referenceIndex) (nativeTyped := nativeTyped) (provenance := provenance),
    target, reference, sourceRead, nativeRead⟩

include selected origin globals leading referenceIndex nativeTyped provenance in
/-- The shared positive projection preserves the principal's actual callable
origin at exactly its retained native carrier and original table. -/
theorem stage_origin_from_selection :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) (value code captured.embedding history.native actual) := by
  exact CallableIndexedOwnedContextualStoredMemberCallBounds.member_stage_origin
    (member_from_selection (captured := captured) (code := code) (support := support) (owner := owner)
      (selected := selected) (history := history) (origin := origin) (globals := globals) (leading := leading)
      (referenceIndex := referenceIndex) (nativeTyped := nativeTyped) (provenance := provenance))
end ExistingMember

section Formation
variable {heap : Dynamic.Heap} {store : Store}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (provenance : PrincipalAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)

include selected packet profile provenance inclusion in
/-- One original contextual principal formation returns its exact Source
trace, native trace, receiving-model value and positive member. The history,
leading bundle and Source origin come from the same actual initial packet. The
member is the formed closure over the copies of its captured cells. -/
theorem formation_member_from_selection
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) heap store
        owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      Member headers keys registry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  exact CallableIndexedOwnedContextualStoredClosureAssociationReceipts.principal_formation_member
    (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (provenance := provenance)
    (functions := functions) (inclusion := inclusion) (escaped := selected.escaped)
    heaps copied ordinary coercions
end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualPrincipalStoredCallReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallOriginPosts
/-! Pointwise stored calls retain positive cells and result origins at the
original returned caller. Source admission comes from the original whole
Source trace, its real initial admission and cumulative frame preservation.
The receiving model is the positive model throughout; neither an erased
representation nor a completed body law supplies a stronger result.
Preservation derives its application leaf from strict body children, while
reflection reuses the receiving-model endpoint. The joint child/body family
and per-input live callee invariant remain separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallOriginPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredClosureInvocation (Association)
open CallableIndexedOwnedStoredClosureArgumentReceipts
open CallableIndexedOwnedStoredIndirectCallBounds
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins post_at_same_state)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section Result
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context}
  {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {canonical : Environment}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)

/-- Every effect and the stronger post belong to the same returned caller.
The closure body registry is kept independently of outer payload metadata. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
    finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
  CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧
    PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile compiler.original.type lowered.type outcome value reached

/-- The model-generic producer already derives PostAdmission from its actual
whole Source trace. Its positive heap and result attach to that exact witness;
this projection performs no invocation or restoration. -/
theorem of_result_at {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ForModel.ResultAt (registry := registry) (faults := faults) (context := context)
      bridge (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      compiler first outcome after value finalStore finalMap finalWorld) :
    ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (context := context) bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, cells, maps, worlds, frame, metadata, reached, related, admitted⟩ := result
  exact ⟨represented, cells, maps, worlds, frame, metadata, reached, related,
    post_at_same_state bridge profile reached admitted cells represented⟩

/-- Forgetting only the stronger facets reconstructs the original causal
result, with the very same returned state, pool and independent effects. -/
theorem ResultAt.forget {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (context := context) bridge profile compiler first outcome after value finalStore finalMap finalWorld) :
    ForModel.ResultAt (registry := registry) (faults := faults) (context := context)
      bridge (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, cells, maps, worlds, frame, metadata, reached, related, post⟩ := result
  exact ⟨represented, cells, maps, worlds, frame, metadata, reached, related, post.admission⟩

/-- Sequential use receives the same successful caller together with its raw
value type, deep heap admission, all rows, positive cells and native payload. -/
theorem ResultAt.at_value {raw : Dynamic.Value} {native : Value}
    {after : Dynamic.Heap} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (context := context) bridge profile compiler first (.value raw) after (.inRight .word native)
      finalStore finalMap finalWorld) :
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates first reached ∧ Admission bridge context reached ∧
      Dynamic.ValueHasType context after raw compiler.original.type ∧
      CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
      CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry registry faults profile
        finalMap finalWorld compiler.original.type raw native lowered.type := by
  obtain ⟨_, _, _, _, _, _, reached, related, post⟩ := result
  have successful := post.at_value
  exact ⟨reached, related, successful.1, successful.2.1, post.cells, successful.2.2⟩
end Result

section Selected
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (firstAdmission : Admission bridge context first)
  (calleeState : callerProtocol.State ⟨scope, mapping, world, calleeHeap, store, canonical⟩)
  (calleeRelated : callerProtocol.Relates first calleeState)
  (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
  (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
  (calleeMetadata : Dynamic.HeapMetadataExtend before calleeHeap)
  {function : Dynamic.Closure} {calleeNative : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults mapping world function calleeNative bindings parameterCore resultCore)
  (heaps : CellOrigins headers keys bodyRegistry registry faults profile mapping world calleeHeap store)
  (binderCount : ids.length = bindings.length)
  (sourceBundle : TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)))
  (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
    SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
  rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation in
/-- The application leaf is derived internally from the actual admitted ordered
arguments and strict body children. The original whole call and single caller
restoration then return the same positive cells/result and Source admission. -/
theorem preserves_selected
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar prepared.site callee ids metadata compiler.original dispatch.row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (context := context) bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have original : ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      ForModel.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        compiler first outcome after value finalStore finalMap finalWorld := by
    apply ForModel.preserves_selected_with_application bridge
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed first firstAdmission
      calleeState calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata (Association.native_typed association)
      heaps rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation selected budget children suffix argumentsWithin callWithin
    intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
      argumentState argumentAdmission maps worlds frame metadata calleeTyped extension representedValues
      middleHeaps rawTyped packing bundle argumentsSize callSize outcome after argumentsTrace called _sameSuffix callWithin
    have nativeCount : (compiler.codes.map (·.type)).length = bindings.length := by
      simpa only [List.length_map] using compiler.ordered_children.1.symm.trans binderCount
    have valuesCount : _ = bindings.length := representedValues.length.1.symm.trans nativeCount
    have representedArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings representedValues
      valuesCount sourceBundle nativeBundle
    have future := association.extend maps worlds
    have rawArity := arity_of_association future representedArguments
    obtain ⟨result, finalStore, evaluated, finalMap, finalWorld, resultRep, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, _baseReached, _baseRelated, _stable, returned, _samePool, lastRelated⟩ :=
      CallableIndexedOwnedAdmittedStoredClosureInvocation.preserves_at bridge
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        wellFormed runtime future argumentState argumentAdmission calleeTyped extension representedArguments middleHeaps
        rawTyped packing bundle rawArity budget below called callWithin
    exact ⟨result, finalStore, finalMap, finalWorld,
      application_gate dispatch selected ((Association.binding_count association).symm.trans binderCount.symm)
        native.diagnostics.unknown,
      evaluated, resultRep, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, lastRelated⟩
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceTrace, evaluated, result⟩ := original
  exact ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceTrace, evaluated,
    of_result_at bridge profile compiler first result⟩

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
  rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation in
/-- Reflection reuses the receiving-model whole parent exactly once. Its
independently constructed Source grade and exact returned caller are retained. -/
theorem reflects_selected
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar prepared.site callee ids metadata compiler.original dispatch.row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (context := context) bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result⟩ :=
    CallableIndexedOwnedStoredIndirectCallForModelReflection.reflects_selected
      bridge (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed first firstAdmission
      calleeState calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
      rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation selected budget children below completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace,
    of_result_at bridge profile compiler first result⟩
end Selected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallOriginPosts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureWriteReceipts
/-! Actual writes update positive contextual closure receipts at the same
Source/native cell. Writes to other cells preserve their live reads using
the genuine injective location map. Administrative transport supplies neither
of these facts. This module covers ordinary initialized closure cells. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureWriteReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedOwnedContextualInitializedClosureReceipts (StoredAt payload_member)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {native : Core.Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

/-- One original initialized write returns its full heap/frame receipts and
the new positive payload at the actual written cell. Its Source declaration
type is authenticated independently of the projected native function type. -/
theorem written_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {heap after : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {target : Core.Location} {cell : Dynamic.Cell}
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world heap store)
    (reference : ReferenceRepresents mapping world location target (CallableContract.functionType parameter result))
    (read : Dynamic.Heap.Reads heap location cell)
    (cellType : cell.type = FunctionValues.sourceType function)
    (member : Member headers keys registry faults mapping world function native bindings parameter result)
    (written : Dynamic.Heap.Writes heap location (some (.closure function)) after) :
    ∃ updated, store.write? target (.inRight .unit native) = some updated ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
        mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated ∧
      Dynamic.HeapMetadataExtend heap after ∧
      StoredAt headers keys registry faults mapping world after updated location function native bindings parameter result := by
  have represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world cell.type (.closure function) native (CallableContract.functionType parameter result) :=
    cellType.symm ▸ payload_member profile member
  obtain ⟨updated, coreWritten, finalHeaps, administrative⟩ :=
    GenericHeap.HeapRepresents.write_initialized heaps reference read represented written
  obtain ⟨old, _oldValue, _oldPayload, oldRead, _, _, oldRelated⟩ := heaps.cells reference.mapped
  have same := oldRead.functional read
  subst old
  have ordinary := oldRelated.ordinary
  obtain ⟨previous, previousRead, afterRead⟩ := written.reads_updated
  have same := previousRead.functional read
  subst previous
  have initialized : Dynamic.Heap.Reads after location
      ⟨FunctionValues.sourceType function, some (.closure function), none⟩ := by
    simpa only [cellType, ordinary] using afterRead
  exact ⟨updated, coreWritten, finalHeaps, administrative, .of_write written,
    member, target, reference, initialized, Store.write?_reads_written coreWritten⟩

/-- Source/native writes to a different mapped cell retain this same member
and its actual reads. Injectivity derives distinct physical targets; a frame
preservation receipt alone does not protect mapped payloads. -/
theorem preserves_other
    {heap after : Dynamic.Heap} {store updated : Store}
    {location other : Dynamic.Location} {target : Core.Location} {payload : Ty}
    {replacement : Option Dynamic.Value} {replacementNative : Core.Value}
    (injective : LocationMap.Injective mapping)
    (reference : ReferenceRepresents mapping world location target payload)
    (stored : StoredAt headers keys registry faults mapping world heap store other function native bindings parameter result)
    (different : other ≠ location)
    (written : Dynamic.Heap.Writes heap location replacement after)
    (coreWritten : store.write? target replacementNative = some updated) :
    StoredAt headers keys registry faults mapping world after updated other function native bindings parameter result := by
  obtain ⟨member, otherTarget, otherReference, sourceRead, nativeRead⟩ := stored
  have differentIndices : other.index ≠ location.index := by
    intro same
    apply different
    cases other
    cases location
    simp_all
  have differentTargets : otherTarget ≠ target := by
    intro same
    exact differentIndices (injective (same ▸ otherReference.mapped) reference.mapped)
  exact ⟨member, otherTarget, otherReference, written.preserves_other different sourceRead,
    (Store.write?_preserves_other coreWritten differentTargets).trans nativeRead⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureWriteReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredExpressionHeads
/-! A selected initialized local call supplies the admitted expression head
from its original whole Source trace or native completion. The original Source
children retain their own grades. Positive live cells are required separately
at every input state; argument execution only extends the already-read callable
association. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedStoredClosureArgumentReceipts
open CallableIndexedOwnedContextualStoredMemberCallBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section Source
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {location : Dynamic.Location}
  {function : Dynamic.Closure} {native : Core.Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
  {readFuel : Nat} {readReason : Word} {readCode : Expr}
  (read : CompatibleExpressionReads.Certificate readFuel (.initial compiled.compatible.checked)
    source scope callee readReason readCode)
  (stored : CallableIndexedOwnedContextualInitializedClosureReceipts.StoredAt headers keys registry faults
    mapping world heap store location function native bindings parameter result)
  (lookup : Dynamic.Environment.LooksUp environment read.binder location)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (heapTyped : Dynamic.HeapWellTyped context heap)
  (parentTyped : ExpressionHasType source context id compiler.original.type)

include parent read stored lookup unique wellFormed runtime covers locals heapTyped parentTyped in
/-- A finite inversion keeps the original measured children. The initialized
Source read is constructed directly from its actual cell; no diagnostic read
producer or body execution is called to identify these children. -/
theorem suffix_of_source {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment heap id outcome after) :
    ∃ calleeSize argumentsSize callSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
        context evidence source environment heap callee (.closure function) heap ∧
      SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment heap ids function
        argumentsSize callSize outcome after ∧
      calleeSize < size ∧ argumentsSize < size ∧ callSize ≤ size := by
  have known : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap callee (.closure function) heap := by
    have formTrace : Dynamic.ExpressionFormEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
        source environment heap read.node.form [] [] (.closure function) heap :=
      read.form ▸ Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup
        stored.2.choose_spec.2.1 rfl rfl
    exact .intro (lookupExpression?_sound read.metadata.found)
      (by rw [read.metadata.requirements, read.metadata.coercions]; exact formTrace)
      (by rw [read.metadata.coercions]; exact .nil)
  have align : ∀ {childOutcome childHeap},
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence source
        environment heap callee childOutcome childHeap →
      childOutcome = .value (.closure function) ∧ childHeap = heap := by
    intro childOutcome childHeap child
    exact CompatibleExpressionReads.source_outcome_unique unique
      (lookupExpression?_sound read.metadata.found) read.form read.metadata.coercions
      lookup stored.2.choose_spec.2.1 rfl child (.value known)
  obtain ⟨_parameter, _result, types, _calleeTyped, argumentsTyped, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  have count : types.length = metadata.argumentCount := by
    cases application with
    | intro count _ _ _ => exact count.symm
  have independent := CallableIndirectCallSourceBounds.indirect_inv_sized
    compiler.found compiler.originalForm parent.coercions unique trace
  cases independent with
  | calleeFault child smaller =>
    obtain ⟨same, _⟩ := align (.fault child.sound)
    cases same
  | notCallable child invalid smaller =>
    obtain ⟨same, _⟩ := align (.value child.sound)
    cases same
    exact False.elim (invalid trivial)
  | argumentsFault first callable children firstSmall childrenSmall =>
    obtain ⟨same, sameHeap⟩ := align (.value first.sound)
    cases same; cases sameHeap
    exact ⟨_, _, 0, first, .argumentFault children, firstSmall, childrenSmall, Nat.zero_le _⟩
  | sourceArity first children mismatch firstSmall childrenSmall =>
    exact False.elim (mismatch parent.arity.symm)
  | argumentCoercionFault first children sameArity pack failed firstSmall childrenSmall coercionSmall =>
    rw [compiler.argumentCoercions] at failed
    cases failed
  | applied layout first children packed converted unpacked sameArity appliedArity called firstSmall childrenSmall coercionSmall callSmall =>
    obtain ⟨same, sameHeap⟩ := align (.value first.sound)
    cases same; cases sameHeap
    rw [compiler.argumentCoercions] at converted
    cases converted
    have sameArguments := Dynamic.ValuesPack.injective_of_length_eq packed unpacked
      ((arguments_count_of_source_admission wellFormed runtime covers locals heapTyped
        argumentsTyped count children).trans appliedArity.symm)
    cases sameArguments
    exact ⟨_, _, _, first, SourceSuffix.of_call children (.value called),
      firstSmall, childrenSmall, Nat.le_of_lt callSmall⟩
  | applicationFault first children packed converted unpacked sameArity appliedArity called firstSmall childrenSmall coercionSmall callSmall =>
    obtain ⟨same, sameHeap⟩ := align (.value first.sound)
    cases same; cases sameHeap
    rw [compiler.argumentCoercions] at converted
    cases converted
    have sameArguments := Dynamic.ValuesPack.injective_of_length_eq packed unpacked
      ((arguments_count_of_source_admission wellFormed runtime covers locals heapTyped
        argumentsTyped count children).trans appliedArity.symm)
    cases sameArguments
    exact ⟨_, _, _, first, SourceSuffix.of_call children (.fault called),
      firstSmall, childrenSmall, Nat.le_of_lt callSmall⟩
end Source

/-- A static call head retains its actual lowering, caller sidecar and local
read certificates. It stores no callee, argument or body execution law. -/
structure Receipt (context : SourceSemantics.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  policy : SourceCoreFunctions.Policy
  body : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  compilation : SourceCoreFunctions.Context
  callee : ExpressionId
  ids : List ExpressionId
  metadata : IndirectCallResolution
  reasonAt : ExpressionId → Word
  compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered
  prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable
  parent : SourceParent compiler
  readFuel : Nat
  readReason : Word
  readCode : Expr
  read : CompatibleExpressionReads.Certificate readFuel (.initial compiled.compatible.checked)
    source scope callee readReason readCode
  sameCode : compiler.calleeCode.expression = readCode
  sameType : compiler.calleeCode.type = read.type
  binding : CompatibleExpressionReads.StaticBinding read context
  sidecar : SourceCoreStageContracts.Sidecar
  caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar
  sidecarSource : sidecar.source = source

def Head (context : SourceSemantics.Context) (source : TypedSource) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (Receipt (compiled := compiled) context source scope id lowered)

/-- This positive input witness is indexed by the actual current heap/store.
The selected external Code shares binder and result indices with the retained
member. Its descriptor word may align without identifying hidden Codes. -/
structure LiveAt {context : SourceSemantics.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Receipt (compiled := compiled) context source scope id lowered)
    (certificate : GenericExpressionMeaning.Certificate)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (environment : Dynamic.Environment) where
  function : Dynamic.Closure
  captureScope : SourceCoreLocalCell.Scope
  capturedActual : Environment
  captured : Captures compiled.indexed mapping world captureScope function.captured capturedActual
  code : Code compiled.indexed function captureScope captured.administrative
  history : History code
  selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) head.compiler head.prepared code
  location : Dynamic.Location
  stored : CallableIndexedOwnedContextualInitializedClosureReceipts.StoredAt headers keys registry faults
    mapping world heap store location function
    (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
    code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore
  lookup : Dynamic.Environment.LooksUp environment head.read.binder location

section Meaning
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- Availability of a retained live member is a state invariant, independent
of execution meaning. Every instance must supply its own real cell reads.
Administrative map/frame extension alone does not establish this invariant. -/
def LiveFor : Prop :=
  ∀ {scope id lowered}, (head : Receipt (compiled := compiled) context source scope id lowered) →
  ∀ {mapping world administrative environment canonical heap store},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store →
    Dynamic.EnvironmentAgrees heap context.locals environment →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩,
    Admission bridge context initial →
    Nonempty (LiveAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      head certificate mapping world heap store environment)

include extension unique wellFormed runtime covers in
/-- Original full Source inversion constructs the suffix internally. The
single common producer then returns exactly the admitted head spine at the
same caller witness, preserving argument faults and strict child grades. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (live : LiveFor (registry := registry) (faults := faults) (context := context)
      (source := source) (certificate := certificate) bridge profile)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults child)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source
      (Head (compiled := compiled) context source) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    heap store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨head⟩ := certified
  have sameNode : node = head.compiler.original := Option.some.inj (found.symm.trans head.compiler.found)
  subst node
  obtain ⟨current⟩ := live head environments heaps locals initial admitted
  obtain ⟨_calleeSize, argumentsSize, callSize, _originalCallee, suffix,
      _calleeSmaller, argumentsSmaller, callWithin⟩ := suffix_of_source
    (compiler := head.compiler) (parent := head.parent) (read := head.read)
    (stored := current.stored) (lookup := current.lookup) (unique := unique)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (locals := locals) (heapTyped := admitted.heap) (parentTyped := sourceTyped) trace
  obtain ⟨_constructedSourceSize, value, finalStore, finalMap, finalWorld, _constructedSource,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedContextualStoredMemberCallBounds.preserves_at_stored
      (bridge := bridge) (profile := profile) (compiler := head.compiler) (prepared := head.prepared)
      (captured := current.captured) (code := current.code) (history := current.history)
      (selected := current.selected) (stored := current.stored) (read := head.read)
      (sameCode := head.sameCode) (sameType := head.sameType) (extension := extension)
      (binding := head.binding) (unique := unique) (parentTyped := sourceTyped)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (lookup := current.lookup) (initial := initial) (admitted := admitted)
      (parent := head.parent) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      (typed := typed) (caller := head.caller) (sidecarSource := head.sidecarSource)
      budget children below suffix (Nat.le_trans (Nat.le_of_lt argumentsSmaller) within)
      (Nat.le_trans callWithin within)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩

include extension unique wellFormed runtime covers in
/-- Native reflection calls the same common producer once. Its independently
measured Source grade and exact reached admission are the head result. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (live : LiveFor (registry := registry) (faults := faults) (context := context)
      (source := source) (certificate := certificate) bridge profile)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults child)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source
      (Head (compiled := compiled) context source) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    heap store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨head⟩ := certified
  have sameNode : node = head.compiler.original := Option.some.inj (found.symm.trans head.compiler.found)
  subst node
  obtain ⟨current⟩ := live head environments heaps locals initial admitted
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
      represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedContextualStoredMemberCallBounds.reflects_at_stored
      (bridge := bridge) (profile := profile) (compiler := head.compiler) (prepared := head.prepared)
      (captured := current.captured) (code := current.code) (history := current.history)
      (selected := current.selected) (stored := current.stored) (read := head.read)
      (sameCode := head.sameCode) (sameType := head.sameType) (extension := extension)
      (binding := head.binding) (unique := unique) (parentTyped := sourceTyped)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (lookup := current.lookup) (initial := initial) (admitted := admitted)
      (parent := head.parent) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      (typed := typed) (caller := head.caller) (sidecarSource := head.sidecarSource)
      budget children below completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
end Meaning
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredExpressionHeads
end
