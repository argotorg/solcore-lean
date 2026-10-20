import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBody
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues

/-! Creation retains the actual instance packet and accepted body instead of a
finite body profile. The original capture mapping and snapshot location remain
explicit through heap extension. No later body execution is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInstances
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInstanceValues (referenceIndex value)
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}

/-- All rows of one initializer can retain the same genuine snapshot location.
The body receipt is derived from this packet's own contextual compiler call. -/
inductive Framed (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) (location : Core.Location) :
    SourceCoreLocalPolymorphism.Instance → Core.Value → Prop where
  | retained {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
      {raw : Core.Expr} {actual : Core.Environment}
      (packet : Packet inputs candidate raw) (indexed : Indexed prepared packet)
      (body : Nonempty (GeneralizedLocalAcceptedBody.Receipt packet))
      (sameLexical : indexed.lexical = lexical)
      (owner : inputs.current.owner = binding.caller)
      (initializer : inputs.initializer = binding.initializer)
      (candidateSource : candidate.origin.source = binding.source)
      (candidateBinder : candidate.origin.binder.id = binding.binder.id)
      (descriptorSource : function.source = binding.source)
      (origin : Origin prepared function binding lexical)
      (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
      (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
      (ownership : LocalIdentityOwnership function.source)
      (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
      (reference : captured.canonical[referenceIndex indexed]? =
        some (.cellRef prepared.ancestry.layout.frame.type location))
      (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
        raw candidate.type prepared.layouts.definitions)
      (runtimeTyped : RuntimeValueHasType world (value indexed captured.embedding origin.native actual)
        candidate.type prepared.layouts.definitions) :
      Framed prepared mapping world function binding lexical location candidate
        (value indexed captured.embedding origin.native actual)

theorem Framed.runtime_hasType {location : Core.Location}
    (framed : Framed prepared mapping world function binding lexical location candidate native) :
    RuntimeValueHasType world native candidate.type prepared.layouts.definitions := by
  cases framed
  assumption

theorem Framed.extend {location : Core.Location}
    (framed : Framed prepared mapping world function binding lexical location candidate native)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Framed prepared futureMapping futureWorld function binding lexical location candidate native := by
  cases framed with
  | retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      descriptorSource origin captured declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      descriptorSource origin (captured.extend maps worlds) declarations ownership issuer reference
      typed (runtimeTyped.weaken worlds)

def Represents (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution)
    (candidate : SourceCoreLocalPolymorphism.Instance) (native : Core.Value) : Prop :=
  ∃ location, Framed prepared mapping world function binding lexical location candidate native

def model (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions where
  locals := prepared.base.locals
  Origin := fun function binding lexical => Nonempty (Origin prepared function binding lexical)
  Represents := Represents prepared
  runtime_hasType := by
    intro mapping world function binding lexical candidate native represented
    obtain ⟨_, framed⟩ := represented
    exact framed.runtime_hasType
  extend := by
    intro mapping futureMapping world futureWorld function binding lexical candidate native represented maps worlds
    obtain ⟨location, framed⟩ := represented
    exact ⟨location, framed.extend maps worlds⟩

/-- Creation evaluates the literal snapshot closure in the same store and
derives runtime typing from the accepted native type and capture environment.
It does not execute or restrict the instance body. -/
theorem formation_at_frame {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed prepared packet)
    {actual : Core.Environment}
    (sameLexical : indexed.lexical = lexical) (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (candidateSource : candidate.origin.source = binding.source)
    (candidateBinder : candidate.origin.binder.id = binding.binder.id)
    (descriptorSource : function.source = binding.source)
    (origin : Origin prepared function binding lexical)
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
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (value indexed captured.embedding origin.native actual) store ∧
    Framed prepared mapping world function binding lexical location candidate
      (value indexed captured.embedding origin.native actual) := by
  have evaluated := GeneralizedLocalInstanceValues.formation_evaluates indexed captured reference read
  obtain ⟨future, _, finalStored, outputTyped⟩ :=
    evaluation_preserves_type evaluated (typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  exact ⟨evaluated, .retained packet indexed (GeneralizedLocalAcceptedBody.of_packet packet)
    sameLexical owner initializer candidateSource candidateBinder descriptorSource origin captured
    declarations ownership issuer reference typed outputTyped⟩

/-- Previously profiled instances embed with their same packet and actual body,
without changing the value, captured environment or native world. -/
theorem of_profiled
    (represented : GeneralizedLocalInstanceValues.Represents prepared mapping world
      function binding lexical candidate native) :
    Represents prepared mapping world function binding lexical candidate native := by
  cases represented with
  | retained packet indexed _ sameLexical owner initializer candidateSource candidateBinder descriptorSource
      origin _ _ captured declarations ownership issuer location reference typed runtimeTyped =>
    exact ⟨location, .retained packet indexed (GeneralizedLocalAcceptedBody.of_packet packet)
      sameLexical owner initializer candidateSource candidateBinder descriptorSource origin captured
      declarations ownership issuer reference typed runtimeTyped⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInstances
