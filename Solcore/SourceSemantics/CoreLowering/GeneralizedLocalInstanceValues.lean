import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorOrigin
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfile
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDiagnosticIssuer

/-! Stored generalized instances retain their literal compiler packet, mapped
captures and actual lexical snapshot. They become ordinary Source closures
only when a read supplies its real substitution and evidence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
  {packet : Packet inputs candidate raw}

def referenceIndex (_indexed : Indexed prepared packet) : Nat :=
  SourceCoreCallableIndexedAncestry.creationReferenceIndex
    (GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared) inputs.scope

def body (indexed : Indexed prepared packet) : Core.Expr :=
  SourceCoreCallableIndexedFrames.withFrame (.var (referenceIndex indexed + 2))
    (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table prepared.ancestry.layout.frame
      indexed.descriptor.id (.var 1) (.loadCell (.var (referenceIndex indexed + 2))))
    (packet.certificate.rawBody.weakenAt 1)

def value (indexed : Indexed prepared packet) (embedding : Renaming)
    (native : NativeFrame) (actual : Core.Environment) : Core.Value :=
  .pair (.pair (.inLeft .word .unit)
    (.closure packet.certificate.parameterCore (LanguageResult.resultType packet.certificate.resultCore)
      ((body indexed).rename embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native :: actual)))
    (.word indexed.descriptor.id)

/-- Creation retains a static native typing derivation and its actual capture
representation. There is no Source body execution or future read dictionary. -/
inductive Represents (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) : Dynamic.GeneralizedClosure →
      SourceCoreLocalPolymorphism.Binding → Substitution → SourceCoreLocalPolymorphism.Instance → Core.Value → Prop where
  | retained {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
      {lexical : Substitution} {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
      {raw : Core.Expr} {actual : Core.Environment}
      (packet : Packet inputs candidate raw) (indexed : Indexed prepared packet)
      (bodyProfile : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
        packet.original.emission.prepared.source inputs.initializer)
      (sameLexical : indexed.lexical = lexical)
      (owner : inputs.current.owner = binding.caller)
      (initializer : inputs.initializer = binding.initializer)
      (candidateSource : candidate.origin.source = binding.source)
      (candidateBinder : candidate.origin.binder.id = binding.binder.id)
      (descriptorSource : function.source = binding.source)
      (origin : Origin prepared function binding lexical)
      (namedLexical : lexical = [])
      (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
      (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
      (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
      (ownership : LocalIdentityOwnership function.source)
      (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
      (frameLocation : Core.Location)
      (frameReference : captured.canonical[referenceIndex indexed]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
      (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
        raw candidate.type prepared.layouts.definitions)
      (runtimeTyped : RuntimeValueHasType world (value indexed captured.embedding origin.native actual)
        candidate.type prepared.layouts.definitions) :
      Represents prepared mapping world function binding lexical candidate
        (value indexed captured.embedding origin.native actual)

def model (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions where
  locals := prepared.base.locals
  Origin := fun function binding lexical => Nonempty (Origin prepared function binding lexical)
  Represents := Represents prepared
  runtime_hasType := by
    intro mapping world function binding lexical candidate native represented
    cases represented with
    | retained _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ typed => exact typed
  extend := by
    intro mapping futureMapping world futureWorld function binding lexical candidate native represented maps worlds
    cases represented with
    | retained packet indexed bodyProfile lexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer frameLocation frameReference typed runtimeTyped =>
        exact .retained packet indexed bodyProfile lexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata (captured.extend maps worlds) declarations ownership issuer frameLocation frameReference typed
          (runtimeTyped.weaken worlds)

/-- The literal snapshot lambda reads the actual lexical reference and leaves
the whole native store unchanged. -/
theorem formation_evaluates (indexed : Indexed prepared packet)
    {mapping : LocationMap} {world : StoreTyping} {source : Dynamic.Environment} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope source actual)
    {native : NativeFrame} {store : Store} {location : Core.Location}
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native)) :
    Evaluates actual store (raw.rename captured.embedding) (value indexed captured.embedding native actual) store := by
  conv => arg 3; rw [indexed.emitted]
  exact .pair (.pair (.inLeft .unit) (.letE (.loadCell (.var (captured.agrees reference)) read) .lambda)) .word

/-- Runtime typing is derived from the accepted raw expression and its actual
execution in this same store. It does not assume an instance body law. -/
theorem formation (indexed : Indexed prepared packet)
    (bodyProfile : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
      packet.original.emission.prepared.source inputs.initializer)
    {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {actual : Core.Environment}
    (sameLexical : indexed.lexical = lexical) (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (candidateSource : candidate.origin.source = binding.source)
    (candidateBinder : candidate.origin.binder.id = binding.binder.id)
    (descriptorSource : function.source = binding.source)
    (origin : Origin prepared function binding lexical)
    (namedLexical : lexical = [])
    (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
      (ownership : LocalIdentityOwnership function.source)
      (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding) (value indexed captured.embedding origin.native actual) store ∧
    Represents prepared mapping world function binding lexical candidate
      (value indexed captured.embedding origin.native actual) := by
  have evaluated := formation_evaluates indexed captured reference read
  obtain ⟨future, _, finalStored, outputTyped⟩ :=
    evaluation_preserves_type evaluated (typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  exact ⟨evaluated, .retained packet indexed bodyProfile sameLexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer location reference typed outputTyped⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues
