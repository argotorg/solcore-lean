import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInstances
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedMaterialization
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadView
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAppliedSourceOrigins

/-! Materialized local functions retain their real compiler row, Source
instantiation, lexical capture and read-time view. The relation records no
execution law for the body and does not identify the two native contexts.
The body evidence is the actual accepted tree, without a finite lexical profile. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)

structure Materialization (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure)
    (viewRelation : TypedSource → TypedSource → Prop := LambdaMetadataViews.MetadataView) where
  descriptor : Dynamic.GeneralizedClosure
  binding : SourceCoreLocalPolymorphism.Binding
  lexical : TypeSystem.Substitution
  inputs : Inputs
  candidate : SourceCoreLocalPolymorphism.Instance
  raw : Expr
  packet : Packet inputs candidate raw
  indexed : Indexed compiled.indexed packet
  body : Nonempty (GeneralizedLocalAcceptedBody.Receipt packet)
  sameLexical : indexed.lexical = lexical
  owner : inputs.current.owner = binding.caller
  initializer : inputs.initializer = binding.initializer
  candidateSource : candidate.origin.source = binding.source
  candidateBinder : candidate.origin.binder.id = binding.binder.id
  descriptorInitializer : descriptor.initializer = binding.initializer
  origin : Origin compiled.indexed descriptor binding lexical
  descriptorUnique : NodeOccurrencesUnique descriptor.source
  sourceCaptures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
    descriptor.captured descriptor.binder descriptor.initializer descriptor
  context : Solcore.SourceSemantics.Context
  callerEvidence : Dynamic.EvidenceEnvironment
  produced : Dynamic.EvidenceEnvironment
  actualType : TypeSystem.Ty
  requirements : List RequirementId
  semantic : TypeSystem.Substitution
  instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
    actualType requirements semantic produced
  materialized : function = descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
  actual : Environment
  captured : Captures compiled.indexed mapping world inputs.scope function.captured actual
  capturedDeclarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.context
  frameLocation : Core.Location
  frameReference : captured.canonical[GeneralizedLocalInstanceValues.referenceIndex indexed]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation)
  code : Code compiled.indexed function inputs.scope captured.administrative viewRelation
  compilation : code.compilation = GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared
  active : code.active = packet.original.emission.prepared.substitution
  lowered : code.lowered = packet.original.lowered
  codeId : code.id = inputs.initializer
  policy : code.policy = GeneralizedLocalLambdaCompilation.policy inputs packet.original.emission.prepared packet.fuel
  lowerBody : code.lowerBody = GeneralizedLocalLambdaCompilation.lowerBody inputs packet.original.emission.prepared
  fuel : code.fuel = packet.fuel
  descriptorId : code.descriptor.id = indexed.descriptor.id
  certificate : HEq code.receipt packet.certificate
  view : code.view = packet.original.emission.prepared.source
  reasons : code.reasonAt = inputs.reasonAt
  rawTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value code captured.embedding origin.native actual)
    candidate.type compiled.indexed.layouts.definitions
  ownership : LocalIdentityOwnership function.source
  issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs
  unique : NodeOccurrencesUnique function.source

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure}
  {viewRelation : TypedSource → TypedSource → Prop}

def Materialization.extend (material : Materialization compiled mapping world function viewRelation)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Materialization compiled futureMapping futureWorld function viewRelation :=
  { material with captured := material.captured.extend maps worlds
                  rawTyped := material.rawTyped.weaken worlds }

/-- Weakening view evidence retains the same stored packet and every capture. -/
def Materialization.weaken_view {after : TypedSource → TypedSource → Prop}
    (material : Materialization compiled mapping world function viewRelation)
    (weaken : ∀ source view, viewRelation source view → after source view) :
    Materialization compiled mapping world function after :=
  { material with code := material.code.weaken_view weaken }

theorem Materialization.frame_reference (material : Materialization compiled mapping world function viewRelation) :
    material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type material.frameLocation) := by
  simpa only [Code.referenceIndex, material.compilation, GeneralizedLocalInstanceValues.referenceIndex]
    using material.frameReference

/-- Canonical provenance belongs to the compiler view. The independently
substituted runtime Source is carried by the actual paired history. -/
theorem Materialization.compiler_source_receipt (material : Materialization compiled mapping world function viewRelation) :
    LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      material.code.compilation.owner material.code.active material.code.view := by
  have authentic : LambdaSourceAlignment.SourceReceipt material.inputs.program material.inputs.current.plan
      material.candidate.origin.caller material.packet.original.emission.prepared.substitution
      material.packet.original.emission.prepared.source :=
    .contextual material.packet.original.emission.authentic
  simpa only [material.indexed.program, material.indexed.plan, ← material.indexed.owner,
    material.compilation, material.active, material.view, GeneralizedLocalLambdaCompilation.context] using authentic

/-- Compatibility for clients whose actual source is the canonical compiler
view. General applied origins use the independent paired-source producer. -/
theorem Materialization.source_receipt_of_eq (material : Materialization compiled mapping world function viewRelation)
    (same : function.source = material.code.view) :
    LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      material.code.compilation.owner material.code.active function.source := by
  rw [same]
  exact material.compiler_source_receipt

abbrev Materialization.source_receipt := @Materialization.source_receipt_of_eq

theorem Materialization.native_type (material : Materialization compiled mapping world function viewRelation) :
    material.candidate.type = CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore := by
  have same := GeneralizedLocalMaterializedCode.value_eq material.indexed material.code material.lowered
    material.captured.embedding material.origin.native material.actual
  have shape := Value.closure.inj (Value.pair.inj (Value.pair.inj same).1).2
  have result := (Ty.sum.inj shape.2.1).2
  rw [shape.1, result]
  exact material.indexed.nativeType

/-- The compiler-selected read wrapper and the captured reference remain
available after the read has returned and the caller has changed. -/
structure View (material : Materialization compiled mapping world function viewRelation) where
  owner : SourceCoreLocalPolymorphism.Key
  active : TypeSystem.Substitution
  source : TypedSource
  scope : SourceCoreLocalCell.Scope
  expression : ExpressionId
  original : SourceCoreBasic.LoweredExpr
  lowered : SourceCoreBasic.LoweredExpr
  accepted : SourceCoreCallableIndexedAncestry.lowerView compiled.indexed.ancestry owner active source scope
    expression original = .ok lowered
  id : Word
  referenceIndex : Nat
  emitted : lowered.expression = SourceCoreCallableIndexedAncestry.viewLower compiled.indexed.ancestry.layout.frame
    material.code.receipt.parameterCore material.code.receipt.resultCore id material.code.descriptor.id
    referenceIndex original.expression
  callerNative : NativeFrame
  callerGhost : GhostFrame
  caller : MetadataState
  carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    callerNative callerGhost (some caller)
  recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs callerGhost
    material.origin.ghost caller material.origin.metadata id material.code.descriptor.id
  initializer : material.descriptor.initializer = recipe.read.entry.view.principal.initializer
  scheme : material.descriptor.binder.scheme = recipe.read.binder.scheme
  actualType : material.actualType = recipe.read.node.rawType
  embedding : Renaming
  environment : Environment
  location : Core.Location
  reference : environment[embedding referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location)
  lexicalReference : material.captured.canonical[material.code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location)

theorem View.materialized_pair {material : Materialization compiled mapping world function viewRelation} (view : View material) :
    CallableAppliedDynamicSourceMaterialization.Pair compiled.indexed.ancestry.graph.inputs
      (.appliedView view.id material.code.descriptor.id view.callerGhost material.origin.ghost)
      (view.recipe.read.after material.origin.metadata) function.source := by
  have captures : Dynamic.GeneralizedClosureCaptures material.descriptor.definitionContext material.descriptor.source
      material.descriptor.captured material.descriptor.binder view.recipe.read.entry.view.principal.initializer
      material.descriptor := by
    rw [← view.initializer]
    exact material.sourceCaptures
  have result := material.origin.materialize view.recipe captures material.descriptorUnique
    material.instantiation view.scheme view.actualType
  simpa only [← material.materialized] using result.1

def View.native {material : Materialization compiled mapping world function viewRelation} (view : View material) : Value :=
  GeneralizedLocalReadView.value compiled.indexed.ancestry.layout.frame
    material.code.receipt.parameterCore material.code.receipt.resultCore view.id material.code.descriptor.id
    view.referenceIndex view.embedding view.callerNative (.inLeft .word .unit)
    (.closure material.code.receipt.parameterCore (LanguageResult.resultType material.code.receipt.resultCore)
      (material.code.body.rename material.captured.embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual))
    view.environment

def View.extend {material : Materialization compiled mapping world function viewRelation} (view : View material)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    View (material.extend maps worlds) :=
  { view with }

def View.weaken_view {after : TypedSource → TypedSource → Prop}
    {material : Materialization compiled mapping world function viewRelation} (view : View material)
    (weaken : ∀ source target, viewRelation source target → after source target) :
    View (material.weaken_view weaken) := { view with }

theorem View.weaken_view_native {after : TypedSource → TypedSource → Prop}
    {material : Materialization compiled mapping world function viewRelation} (view : View material)
    (weaken : ∀ source target, viewRelation source target → after source target) :
    (view.weaken_view weaken).native = view.native := rfl

inductive Association (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping)
    {viewRelation : optParam (TypedSource → TypedSource → Prop) LambdaMetadataViews.MetadataView} :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | viewed {function : Dynamic.Closure} (material : Materialization compiled mapping world function viewRelation)
      (view : View material)
      (typed : RuntimeValueHasType world view.native
        (CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Association compiled mapping world (viewRelation := viewRelation) function view.native material.code.receipt.loweredParameters
        material.code.receipt.parameterCore material.code.receipt.resultCore

variable {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

def Association.AtFrame
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result)
    (location : Core.Location) : Prop :=
  match member with
  | .viewed _ view _ => view.location = location

theorem Association.projection
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result) :
    compiled.compatible.checked.catalog.project (FunctionValues.sourceType function) =
      .ok (CallableContract.functionType parameter result) := by
  cases member with
  | viewed material _ _ => exact material.code.projection

theorem Association.runtime_hasType
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result) :
    RuntimeValueHasType world native (CallableContract.functionType parameter result) compiled.indexed.layouts.definitions := by
  cases member with
  | viewed _ _ typed => exact typed

def Association.extend
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association compiled futureMapping futureWorld (viewRelation := viewRelation) function native bindings parameter result := by
  cases member with
  | viewed material view typed =>
    exact .viewed (material.extend maps worlds) (view.extend maps worlds) (typed.weaken worlds)

def Association.weaken_view {after : TypedSource → TypedSource → Prop}
    (member : Association compiled mapping world (viewRelation := viewRelation)
      function native bindings parameter result)
    (weaken : ∀ source view, viewRelation source view → after source view) :
    Association compiled mapping world (viewRelation := after) function native bindings parameter result := by
  cases member with
  | viewed material view typed =>
    exact .viewed (material.weaken_view weaken) (view.weaken_view weaken) typed

theorem Association.stage_origin
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases member with
  | viewed material view _ =>
    have captures : Dynamic.GeneralizedClosureCaptures material.descriptor.definitionContext
        material.descriptor.source material.descriptor.captured material.descriptor.binder
        view.recipe.read.entry.view.principal.initializer material.descriptor := by
      rw [← view.initializer]
      exact material.sourceCaptures
    let payload : Value := match view.native with
      | .pair payload _ => payload
      | _ => .unit
    have result := GeneralizedLocalAppliedSourceOrigins.materialized material.origin view.recipe
      captures material.descriptorUnique material.instantiation view.scheme view.actualType payload
    simpa only [← material.materialized, payload, View.native, GeneralizedLocalReadView.value] using result.2


theorem Association.observation
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    CompatibleEquality.Observation compiled.compatible.checked.catalog registry identities
      (CallableContract.functionType parameter result) (.closure function) native := by
  cases member with
  | viewed _ _ _ => exact .contractedAnonymous _ _ _ _ _ profile

theorem Association.source_binders
    (member : Association compiled mapping world (viewRelation := viewRelation) function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  cases member with
  | viewed material _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) material.code)).symm

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
