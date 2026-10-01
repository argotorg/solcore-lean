import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedRetainedNamedValues
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews

/-! Indexed anonymous leaves retain the source formation inputs, static
compiler receipts, real mapped captures and the independently carried lexical
history. A source context or dictionary is never recovered from a native type.
The relation has no field requiring execution of the lambda body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedHistory
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Identity := @CallableIndexedRetainedNamedValues.Identity
abbrev identity_faithful := @CallableIndexedRetainedNamedValues.identity_faithful

structure Code {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (function : Dynamic.Closure) (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  compilation : SourceCoreFunctions.Context
  active : TypeSystem.Substitution
  view : TypedSource
  viewOfSource : LambdaMetadataViews.MetadataView function.source view
  id : ExpressionId
  sourceNode : ExpressionNode
  sourceFound : function.source.lookupExpression? id = some sourceNode
  sourceForm : sourceNode.form = .lambda function.parameters function.resultType function.body
  node : ExpressionNode
  found : view.lookupExpression? id = some node
  form : node.form = sourceNode.form
  reported : Core.Ty
  reasonAt : ExpressionId → Word
  lowered : SourceCoreBasic.LoweredExpr
  receipt : CallableIndexedLambdaCertificates.Certificate policy lowerBody fuel compilation view scope id node
    function.parameters function.resultType function.body reported reasonAt lowered
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
    compilation view scope id reasonAt = .ok lowered
  allocationError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  allocationProfile : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
    prepared.ancestry.layout.frame prepared.base.globals.length
    (prepared.layouts.allocatorAt compilation.owner active allocationError))
  manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates compilation.owner active
  expressionProfile : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner active
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active
  descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner id active)
  projection : checked.catalog.project (FunctionValues.sourceType function) = .ok
    (CallableContract.functionType receipt.parameterCore receipt.resultCore)
  typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
    (LanguageResult.resultType (CallableContract.functionType receipt.parameterCore receipt.resultCore)) prepared.layouts.definitions

def Code.referenceIndex {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) : Nat :=
  SourceCoreCallableIndexedAncestry.creationReferenceIndex code.compilation scope

def Code.body {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) : Expr :=
  SourceCoreCallableIndexedFrames.withFrame (.var (code.referenceIndex + 2))
    (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table prepared.ancestry.layout.frame
      code.descriptor.id (.var 1) (.loadCell (.var (code.referenceIndex + 2)))) (code.receipt.rawBody.weakenAt 1)

theorem Code.emitted {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) :
    code.lowered.expression = LanguageResult.success (code.descriptor.wrap (TaggedFunction.anonymous
      (.letE (.loadCell (.var code.referenceIndex))
        (.lambda code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore) code.body)))) := by
  have hook := code.receipt.expressionHook
  rw [code.expressionProfile] at hook
  obtain ⟨origin, body, selected, raw, _, _, _, emitted⟩ := CallableIndexedFormation.expressionHook_receipt prepared.ancestry hook
  have sameBody := Expr.lambda.inj raw
  have nodeId := (lookupExpression?_sound code.found).2
  rw [nodeId] at selected
  have sameOrigin : origin = code.descriptor.id := Option.some.inj (selected.symm.trans code.descriptor.found)
  have bodyEq : code.receipt.rawBody = body := sameBody.2.2
  have decorated := code.receipt.decoration
  rw [code.callables] at decorated
  have expected := ActualCallablePolicy.lambda_decoration prepared.ancestry.graph.inputs.callable code.active
    code.compilation code.view code.node code.id code.receipt.parameterCore code.receipt.resultCore
    (TaggedFunction.anonymous code.receipt.rawLambda) code.descriptor
  have decoration := Except.ok.inj (decorated.symm.trans expected)
  apply (congrArg SourceCoreBasic.LoweredExpr.expression code.receipt.emitted).trans
  change code.receipt.expression = _
  rw [decoration, emitted, sameOrigin, ← bodyEq]
  rfl

/-- The full actual environment is retained. Only lexical cell references are
compared with canonical slots; extra native captures are not discarded. -/
structure Captures {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (scope : SourceCoreLocalCell.Scope)
    (source : Dynamic.Environment) (actual : Core.Environment) where
  administrative : Core.Context
  canonical : Core.Environment
  actualContext : Core.Context
  embedding : Renaming
  represented : DataHeap.EnvRepresents (storageCatalog checked.catalog) mapping world administrative scope source canonical prepared.layouts.definitions
  agrees : ReadOnly.EnvironmentsAgree embedding canonical actual
  respects : Renaming.Respects embedding (SourceCoreLocalCell.coreContext scope ++ administrative) actualContext
  typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions

def Captures.extend {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {actual : Core.Environment}
    (captured : Captures prepared mapping world scope source actual)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Captures prepared futureMapping futureWorld scope source actual :=
  {captured with represented := captured.represented.extend maps worlds, typed := captured.typed.weaken worlds}

/-- Generation-site alignment belongs to the carried source execution state.
An index that merely decodes successfully does not supply this receipt. Source
context and evidence remain the exact inputs stored in `function`. -/
structure History {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) where
  native : NativeFrame
  ghost : GhostFrame
  metadata : MetadataState
  carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table native ghost (some metadata)
  source : metadata.metadata.source = function.source
  owner : metadata.metadata.owner = code.compilation.owner
  active : metadata.nativeActive = code.active

def value {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (embedding : Renaming)
    (native : NativeFrame) (actual : Core.Environment) : Core.Value :=
  .pair (.pair (.inLeft .word .unit)
    (.closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
      (code.body.rename embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native :: actual))) (.word code.descriptor.id)

inductive Represents {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | retained {sourceType source native type}
      (related : CallableIndexedRetainedNamedValues.Represents prepared world sourceType source native type) :
      Represents prepared mapping world sourceType source native type
  | lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
      (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) prepared.layouts.definitions) :
      Represents prepared mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

def model {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ mapping world => Represents prepared mapping world
  projection := by
    intro registry mapping world sourceType source native type related
    cases related with
    | retained prior => exact (CallableIndexedRetainedNamedValues.model prepared profile).projection (registry := registry) (mapping := mapping) prior
    | lambda _ code _ _ => exact code.projection
  runtime_hasType := by
    intro registry mapping world sourceType source native type related
    cases related with
    | retained prior => exact (CallableIndexedRetainedNamedValues.model prepared profile).runtime_hasType (registry := registry) (mapping := mapping) prior
    | lambda _ _ _ typed => exact typed
  source_function := by
    intro registry mapping world sourceType source native type related
    cases related with
    | retained prior => exact (CallableIndexedRetainedNamedValues.model prepared profile).source_function (registry := registry) (mapping := mapping) prior
    | lambda => exact .closure _
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type related registries maps worlds
    cases related with
    | retained prior => exact .retained ((CallableIndexedRetainedNamedValues.model prepared profile).extend prior registries maps worlds)
    | lambda captured code history typed => exact .lambda (captured.extend maps worlds) code history (typed.weaken worlds)

theorem observations {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionObservations checked.catalog (model prepared profile) (Identity prepared) := by
  intro registry mapping world sourceType source native type related
  cases related with
  | retained prior => exact CallableIndexedRetainedNamedValues.observations prepared profile (mapping := mapping) prior
  | lambda captured code history _ => exact .contractedAnonymous _ _ _ _ _ profile

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) : FunctionRuntimeViews (model prepared profile) := by
  intro registry mapping world parameter result source native type related
  cases related with
  | retained prior => exact prior.runtime_view
  | lambda => exact (Dynamic.ValueRuntimeType.closure _).matches

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
