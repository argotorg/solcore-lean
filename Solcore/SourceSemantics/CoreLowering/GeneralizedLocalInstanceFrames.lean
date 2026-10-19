import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows

/-! The actual snapshot reference is retained through storage and heap
extension. This is creation evidence; a shared reference is never inferred
from equal native payload types or source binder identifiers. -/
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
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : Substitution} {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}

inductive Framed (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) (frameLocation : Core.Location) :
    SourceCoreLocalPolymorphism.Instance → Core.Value → Prop where
  | retained {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
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
      (frameReference : captured.canonical[referenceIndex indexed]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
      (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
        raw candidate.type prepared.layouts.definitions)
      (runtimeTyped : RuntimeValueHasType world (value indexed captured.embedding origin.native actual)
        candidate.type prepared.layouts.definitions) :
      Framed prepared mapping world function binding lexical frameLocation candidate
        (value indexed captured.embedding origin.native actual)

theorem Framed.forget {location : Core.Location}
    (framed : Framed prepared mapping world function binding lexical location candidate native) :
    Represents prepared mapping world function binding lexical candidate native := by
  cases framed with
  | retained packet indexed profile sameLexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed profile sameLexical owner initializer candidateSource candidateBinder descriptorSource
      origin namedLexical namedMetadata captured declarations ownership issuer location reference typed runtimeTyped

theorem Framed.extend {location : Core.Location}
    (framed : Framed prepared mapping world function binding lexical location candidate native)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Framed prepared futureMapping futureWorld function binding lexical location candidate native := by
  cases framed with
  | retained packet indexed profile sameLexical owner initializer candidateSource candidateBinder descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed profile sameLexical owner initializer candidateSource candidateBinder descriptorSource
      origin namedLexical namedMetadata (captured.extend maps worlds) declarations ownership issuer reference typed (runtimeTyped.weaken worlds)

theorem formation_at_frame {inputs : Inputs} {raw : Core.Expr} {packet : Packet inputs candidate raw}
    (indexed : Indexed prepared packet)
    (bodyProfile : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
      packet.original.emission.prepared.source inputs.initializer)
    {actual : Core.Environment}
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
    Framed prepared mapping world function binding lexical location candidate
      (value indexed captured.embedding origin.native actual) := by
  have evaluated := formation_evaluates indexed captured reference read
  obtain ⟨future, _, finalStored, outputTyped⟩ :=
    evaluation_preserves_type evaluated (typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  exact ⟨evaluated, .retained packet indexed bodyProfile sameLexical owner initializer candidateSource candidateBinder descriptorSource
    origin namedLexical namedMetadata captured declarations ownership issuer reference typed outputTyped⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues

namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
open Core Frontend SourceInference TypeSystem GeneralHeap
open SourceCoreLocalPolymorphism GeneralizedLocalInstanceValues

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
  {location : Dynamic.Location} {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store finalStore : Store}

def Located.Frames (located : Located (model prepared) function binding lexical location mapping world heap store)
    (frameLocation : Core.Location) : Prop :=
  ProductBundle.Pointwise (Framed prepared mapping world function binding lexical frameLocation)
    (binding.atContext lexical) located.values

theorem Located.Frames.transport
    {previous : Located (model prepared) function binding lexical location mapping world heap store}
    {next : Located (model prepared) function binding lexical location futureMapping futureWorld after finalStore}
    {frameLocation : Core.Location} (frames : previous.Frames frameLocation)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (sameValues : next.values = previous.values) : next.Frames frameLocation := by
  change ProductBundle.Pointwise _ _ _
  rw [sameValues]
  change ProductBundle.Pointwise _ _ _ at frames
  generalize binding.atContext lexical = selected at frames ⊢
  generalize previous.values = payload at frames ⊢
  induction frames with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extend maps worlds) ih

theorem Located.preserves_framed
    (located : Located (model prepared) function binding lexical location mapping world heap store)
    {frameLocation : Core.Location} (frames : located.Frames frameLocation)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate prepared.base.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical prepared.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ native, Framed prepared mapping world function binding lexical frameLocation receipt.candidate native ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : prepared.base.locals.binding binding.caller binding.binder.id = .ok binding := located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨target, referenceAt, reference⟩ := environments.lookup_visible lookup receipt.slot
  have sameTarget : target = located.target := Option.some.inj (reference.mapped.symm.trans located.reference.mapped)
  subst target
  have payload : receipt.payloadType = binding.bundleType lexical := by
    simpa [OptionalCell.cellType] using Option.some.inj (reference.typed.symm.trans located.reference.typed)
  have bundleType : binding.bundleType active = binding.bundleType lexical := by
    have checked := receipt.bundleType
    rw [sameBinding] at checked
    exact checked.trans payload
  have sameRows : receipt.binding.atContext active = binding.atContext lexical := by
    rw [sameBinding]
    exact (GeneralizedLocalBundleContexts.atContext_eq_of_bundleType context binding bundleType.symm).symm
  have rows : ProductBundle.Pointwise (Framed prepared mapping world function binding lexical frameLocation)
      (receipt.binding.atContext active) located.values := sameRows ▸ frames
  obtain ⟨native, framed, evaluated⟩ := GeneralizedLocalBundleReadMeaning.preserves receipt rows referenceAt located.nativeRead
  exact ⟨native, framed, (readOnly receipt).evaluation_rename evaluated agrees⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
