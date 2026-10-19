import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedMaterialization
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadView
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins

/-! Materialized local functions retain their real compiler row, Source
instantiation, lexical capture and read-time view. The relation records no
execution law for the body and does not identify the two native contexts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)

structure Materialization (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) where
  descriptor : Dynamic.GeneralizedClosure
  binding : SourceCoreLocalPolymorphism.Binding
  lexical : TypeSystem.Substitution
  inputs : Inputs
  candidate : SourceCoreLocalPolymorphism.Instance
  raw : Expr
  packet : Packet inputs candidate raw
  indexed : Indexed compiled.indexed packet
  bodyProfile : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
    packet.original.emission.prepared.source inputs.initializer
  sameLexical : indexed.lexical = lexical
  owner : inputs.current.owner = binding.caller
  initializer : inputs.initializer = binding.initializer
  candidateSource : candidate.origin.source = binding.source
  candidateBinder : candidate.origin.binder.id = binding.binder.id
  descriptorSource : descriptor.source = binding.source
  descriptorInitializer : descriptor.initializer = binding.initializer
  binderScheme : descriptor.binder.scheme = binding.binder.scheme
  origin : Origin compiled.indexed descriptor binding lexical
  namedLexical : lexical = []
  namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩
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
  code : Code compiled.indexed function inputs.scope captured.administrative
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
  source : function.source = packet.original.emission.prepared.source
  rawTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value code captured.embedding origin.native actual)
    candidate.type compiled.indexed.layouts.definitions
  ownership : LocalIdentityOwnership function.source
  issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs
  unique : NodeOccurrencesUnique function.source

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure}

def Materialization.extend (material : Materialization compiled mapping world function)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Materialization compiled futureMapping futureWorld function :=
  { material with captured := material.captured.extend maps worlds
                  rawTyped := material.rawTyped.weaken worlds }

theorem Materialization.frame_reference (material : Materialization compiled mapping world function) :
    material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type material.frameLocation) := by
  simpa only [Code.referenceIndex, material.compilation, GeneralizedLocalInstanceValues.referenceIndex]
    using material.frameReference

theorem Materialization.source_receipt (material : Materialization compiled mapping world function) :
    LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      material.code.compilation.owner material.code.active function.source :=
  GeneralizedLocalMaterializedCode.source_receipt material.indexed material.code
    material.compilation material.active material.source

theorem Materialization.native_type (material : Materialization compiled mapping world function) :
    material.candidate.type = CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore := by
  have same := GeneralizedLocalMaterializedCode.value_eq material.indexed material.code material.lowered
    material.captured.embedding material.origin.native material.actual
  have shape := Value.closure.inj (Value.pair.inj (Value.pair.inj same).1).2
  have result := (Ty.sum.inj shape.2.1).2
  rw [shape.1, result]
  exact material.indexed.nativeType

/-- The compiler-selected read wrapper and the captured reference remain
available after the read has returned and the caller has changed. -/
structure View (material : Materialization compiled mapping world function) where
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

theorem View.materialized_pair {material : Materialization compiled mapping world function} (view : View material) :
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

def View.native {material : Materialization compiled mapping world function} (view : View material) : Value :=
  GeneralizedLocalReadView.value compiled.indexed.ancestry.layout.frame
    material.code.receipt.parameterCore material.code.receipt.resultCore view.id material.code.descriptor.id
    view.referenceIndex view.embedding view.callerNative (.inLeft .word .unit)
    (.closure material.code.receipt.parameterCore (LanguageResult.resultType material.code.receipt.resultCore)
      (material.code.body.rename material.captured.embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual))
    view.environment

def View.extend {material : Materialization compiled mapping world function} (view : View material)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    View (material.extend maps worlds) :=
  { view with }

inductive Association (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | viewed {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
      (view : View material)
      (typed : RuntimeValueHasType world view.native
        (CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Association compiled mapping world function view.native material.code.receipt.loweredParameters
        material.code.receipt.parameterCore material.code.receipt.resultCore

variable {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

def Association.AtFrame
    (member : Association compiled mapping world function native bindings parameter result)
    (location : Core.Location) : Prop :=
  match member with
  | .viewed _ view _ => view.location = location

theorem Association.projection
    (member : Association compiled mapping world function native bindings parameter result) :
    compiled.compatible.checked.catalog.project (FunctionValues.sourceType function) =
      .ok (CallableContract.functionType parameter result) := by
  cases member with
  | viewed material _ _ => exact material.code.projection

theorem Association.runtime_hasType
    (member : Association compiled mapping world function native bindings parameter result) :
    RuntimeValueHasType world native (CallableContract.functionType parameter result) compiled.indexed.layouts.definitions := by
  cases member with
  | viewed _ _ typed => exact typed

def Association.extend
    (member : Association compiled mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association compiled futureMapping futureWorld function native bindings parameter result := by
  cases member with
  | viewed material view typed =>
    exact .viewed (material.extend maps worlds) (view.extend maps worlds) (typed.weaken worlds)

theorem Association.stage_origin
    (member : Association compiled mapping world function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases member with
  | viewed material view _ =>
    have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
      compiled.indexed.ancestry.graph.inputs.callableSelected
    have sourceReceipt := material.source_receipt
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at sourceReceipt
    exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted material.code.descriptor
      sourceReceipt material.code.viewOfSource material.unique material.code.found
      (material.code.form.trans material.code.sourceForm) _

theorem Association.observation
    (member : Association compiled mapping world function native bindings parameter result)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    CompatibleEquality.Observation compiled.compatible.checked.catalog registry identities
      (CallableContract.functionType parameter result) (.closure function) native := by
  cases member with
  | viewed _ _ _ => exact .contractedAnonymous _ _ _ _ _ profile

theorem Association.source_binders
    (member : Association compiled mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  cases member with
  | viewed material _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) material.code)).symm

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
