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
inductive Snapshot (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) (location : Core.Location) (attachment : Prop) :
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
      (attached : attachment)
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
      Snapshot prepared mapping world function binding lexical location attachment candidate
        (value indexed captured.embedding origin.native actual)

/-- The original API retains its exact source attachment. General creation
uses the same snapshot representation with its authentic paired history. -/
abbrev Framed (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) (location : Core.Location) :=
  Snapshot prepared mapping world function binding lexical location (function.source = binding.source)

variable {attachment : Prop}

theorem Snapshot.runtime_hasType {location : Core.Location}
    (framed : Snapshot prepared mapping world function binding lexical location attachment candidate native) :
    RuntimeValueHasType world native candidate.type prepared.layouts.definitions := by
  cases framed
  assumption

theorem Snapshot.extend {location : Core.Location}
    (framed : Snapshot prepared mapping world function binding lexical location attachment candidate native)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Snapshot prepared futureMapping futureWorld function binding lexical location attachment candidate native := by
  cases framed with
  | retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      attached origin captured declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      attached origin (captured.extend maps worlds) declarations ownership issuer reference
      typed (runtimeTyped.weaken worlds)

abbrev Framed.runtime_hasType := @Snapshot.runtime_hasType
abbrev Framed.extend := @Snapshot.extend

def RepresentsWith (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) (attachment : Prop)
    (candidate : SourceCoreLocalPolymorphism.Instance) (native : Core.Value) : Prop :=
  ∃ location, Snapshot prepared mapping world function binding lexical location attachment candidate native

def Represents (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution)
    (candidate : SourceCoreLocalPolymorphism.Instance) (native : Core.Value) : Prop :=
  RepresentsWith prepared mapping world function binding lexical (function.source = binding.source) candidate native

/-- Both the original and general attachment use this one instance model.
Every snapshot independently retains the actual origin, code and captures. -/
def modelWith (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (attachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → Substitution → Prop) :
    GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions where
  locals := prepared.base.locals
  Origin := fun function binding lexical => Nonempty (Origin prepared function binding lexical)
  Represents := fun mapping world function binding lexical =>
    RepresentsWith prepared mapping world function binding lexical (attachment function binding lexical)
  runtime_hasType := by
    intro mapping world function binding lexical candidate native represented
    obtain ⟨_, framed⟩ := represented
    exact framed.runtime_hasType
  extend := by
    intro mapping futureMapping world futureWorld function binding lexical candidate native represented maps worlds
    obtain ⟨location, framed⟩ := represented
    exact ⟨location, framed.extend maps worlds⟩

def model (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions :=
  modelWith prepared (fun function binding _ => function.source = binding.source)

/-- The actual Origin.Pair, rather than equality with a canonical table,
attaches independently substituted Source to every stored snapshot. -/
def trackedModel (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions :=
  modelWith prepared (fun _ _ _ => True)

theorem Snapshot.forget_attachment {location : Core.Location}
    (framed : Snapshot prepared mapping world function binding lexical location attachment candidate native) :
    Snapshot prepared mapping world function binding lexical location True candidate native := by
  cases framed with
  | retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      _ origin captured declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      True.intro origin captured declarations ownership issuer reference typed runtimeTyped

/-- Creation evaluates the literal snapshot closure in the same store and
derives runtime typing from the accepted native type and capture environment.
It does not execute or restrict the instance body. -/
theorem formation_at_frame_with {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed prepared packet)
    {actual : Core.Environment}
    (sameLexical : indexed.lexical = lexical) (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (candidateSource : candidate.origin.source = binding.source)
    (candidateBinder : candidate.origin.binder.id = binding.binder.id)
    (attachment : Prop) (attached : attachment)
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
    Snapshot prepared mapping world function binding lexical location attachment candidate
      (value indexed captured.embedding origin.native actual) := by
  have evaluated := GeneralizedLocalInstanceValues.formation_evaluates indexed captured reference read
  obtain ⟨future, _, finalStored, outputTyped⟩ :=
    evaluation_preserves_type evaluated (typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  exact ⟨evaluated, .retained packet indexed (GeneralizedLocalAcceptedBody.of_packet packet)
    sameLexical owner initializer candidateSource candidateBinder attached origin captured
    declarations ownership issuer reference typed outputTyped⟩

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
  exact formation_at_frame_with indexed sameLexical owner initializer candidateSource candidateBinder
    (function.source = binding.source) descriptorSource origin captured declarations ownership issuer
    typed stored reference read

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
