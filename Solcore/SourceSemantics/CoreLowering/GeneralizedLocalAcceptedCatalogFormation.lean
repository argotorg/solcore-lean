import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInstances
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalOrigins

/-! The actual compiler catalog supplies candidate origins at creation and at
a later read. Snapshot formation uses the same Packet, captured environment
and stored frame; no independent candidate Source or binder equality is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCatalogFormation
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInstanceValues (referenceIndex value)
open GeneralizedLocalAcceptedInstances (Snapshot)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

theorem read_origins {caller : SourceCoreLocalPolymorphism.Key} {active : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals
      caller active source scope id reason lowered) :
    receipt.candidate.origin.caller = caller ∧
      receipt.candidate.origin.source = receipt.binding.source ∧
      receipt.candidate.origin.binder = receipt.binding.binder ∧
      receipt.candidate.origin.initializer = receipt.binding.initializer :=
  SelectedCompilationLocalOrigins.at_context compiled receipt.bindingFound
    (List.mem_of_getElem? receipt.candidate_at)

theorem formation_at_frame {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {candidate : SourceCoreLocalPolymorphism.Instance}
    {inputs : Inputs} {raw : Core.Expr} {packet : Packet inputs candidate raw}
    (indexed : Indexed compiled.indexed packet) {actual : Core.Environment}
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext lexical)
    (sameLexical : indexed.lexical = lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin compiled.indexed function binding lexical)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding lexical location True candidate
      (value indexed captured.embedding origin.native actual) := by
  obtain ⟨_, source, binder, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  exact GeneralizedLocalAcceptedInstances.formation_at_frame_with indexed sameLexical owner initializer
    source (congrArg TypedBinder.id binder) True True.intro origin captured declarations ownership issuer
    typed stored reference read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCatalogFormation
