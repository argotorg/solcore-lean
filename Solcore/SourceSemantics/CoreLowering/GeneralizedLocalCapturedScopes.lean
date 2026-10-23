import Solcore.Frontend.ResidualLexicalScopes
import Solcore.SourceSemantics.CoreLowering.ResidualScopeReachability
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalClosedAllocation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleContexts
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedCatalogFormation

/-! Actual allocation records its lexical residual scope in the existing
Snapshot. A later accepted read adds the chosen lambda's own keys and supplies
scope coverage for the exact body compiled by the retained Packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalAcceptedInstances (Snapshot)
open GeneralizedLocalBundleContexts (ContextExtension)

structure Attachment (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) : Prop
    extends GeneralizedLocalReachedAllocation.Attachment function binding lexical where
  captured : CapturedResidualScope binding.source binding.initializer
    binding.binder.scheme.quantified lexical.domain

/-- Strengthening proof evidence preserves this same compiled packet, captured
frame, native value and heap location. -/
theorem retain_scope {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (snapshot : Snapshot prepared mapping world function binding lexical location
      (GeneralizedLocalReachedAllocation.Attachment function binding lexical) candidate native)
    (captured : CapturedResidualScope binding.source binding.initializer
      binding.binder.scheme.quantified lexical.domain) :
    Snapshot prepared mapping world function binding lexical location
      (Attachment function binding lexical) candidate native := by
  cases snapshot with
  | retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      attached origin frame declarations ownership issuer reference typed runtimeTyped =>
    exact .retained packet indexed body sameLexical owner initializer candidateSource candidateBinder
      ⟨attached, captured⟩ origin frame declarations ownership issuer reference typed runtimeTyped

/-- The scope attached at an actual initialized statement comes from its own
invocation entry and direct lexical path. -/
theorem retain_at_statement {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (snapshot : Snapshot prepared mapping world function binding lexical location
      (GeneralizedLocalReachedAllocation.Attachment function binding lexical) candidate native)
    {roots : List NodeId} (entry : ResidualEntryCovered binding.source roots lexical.domain)
    {id : StatementId} (path : LocalLambdaLexicalPath binding.source roots (.statement id))
    {statement : StatementNode}
    (found : binding.source.lookupNode? id.occurrence = some (.statement statement))
    (form : statement.form = .letDecl binding.binder (some binding.initializer)) :
    Snapshot prepared mapping world function binding lexical location
      (Attachment function binding lexical) candidate native :=
  retain_scope snapshot (entry.capture path found form)

/-- Loop initializer and post items retain scope from their actual enclosing
loop occurrence, including when the surrounding invocation is contextual. -/
theorem retain_at_header {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (snapshot : Snapshot prepared mapping world function binding lexical location
      (GeneralizedLocalReachedAllocation.Attachment function binding lexical) candidate native)
    {roots : List NodeId} (entry : ResidualEntryCovered binding.source roots lexical.domain)
    {id : StatementId} (path : LocalLambdaLexicalPath binding.source roots (.statement id))
    {statement : StatementNode}
    (found : binding.source.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    (member : .letDecl binding.binder (some binding.initializer) ∈ initializers ++ post) :
    Snapshot prepared mapping world function binding lexical location
      (Attachment function binding lexical) candidate native :=
  retain_scope snapshot (ResidualScopeReachability.capture_header entry path found form member)

private theorem expression_before {source : TypedSource} {substitution : Substitution}
    {id : ExpressionId} {node : ExpressionNode}
    (accepted : (source.applySubstitution substitution).lookupExpression? id = some node) :
    ∃ original, source.lookupNode? id.occurrence = some (.expression original) ∧
      original.applySubstitution substitution = node := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode? at accepted
  simp only [TypedSource.applySubstitution, List.find?_map] at accepted
  have predicate :
      ((fun candidate => decide (candidate.occurrenceId = id.occurrence)) ∘
        Node.applySubstitution substitution) =
      (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [predicate] at accepted
  cases found : source.lookupNode? id.occurrence with
  | none => simp only [TypedSource.lookupNode?] at found; simp [found] at accepted
  | some candidate =>
    have selected := found
    unfold TypedSource.lookupNode? at selected
    cases candidate with
    | statement statement => simp [selected, Node.applySubstitution] at accepted
    | expression original =>
      refine ⟨original, rfl, ?_⟩
      simpa only [selected, Option.map_some, Node.applySubstitution, Option.some.injEq] using accepted

/-- The accepted matcher covers every own quantifier; its actual cumulative
candidate also retains every key in the saved lexical context. -/
theorem read_keys {catalog : SourceCoreLocalPolymorphism.Catalog}
    {caller : SourceCoreLocalPolymorphism.Key} {active lexical : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    (extension : ContextExtension lexical active) :
    ∀ metavariable, metavariable ∈ receipt.binding.binder.scheme.quantified ∨
      metavariable ∈ lexical.domain → metavariable ∈ receipt.candidate.origin.substitution.domain := by
  intro metavariable member
  rw [receipt.candidate_key, Substitution.mem_domain_compose_iff]
  rcases member with own | saved
  · right
    have domain : receipt.child.domain = receipt.binding.binder.scheme.quantified :=
      (SourceSpecialization.matchClosedSchemeInstance?_sound receipt.matched).2.2.1
    exact domain.symm ▸ own
  · exact .inl (extension.domain metavariable saved)

/-- The same Packet fixes the body list after specialization. This producer
uses the stored scope and actual accepted read, without a source-wide equality
or a law about arbitrary future contexts. -/
theorem body_at_read (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : SourceCoreLocalPolymorphism.Key} {active lexical : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals
      caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure}
    (attached : Attachment function receipt.binding lexical)
    (extension : ContextExtension lexical active)
    {inputs : Inputs} {raw : Core.Expr} (packet : Packet inputs receipt.candidate raw)
    (initializer : inputs.initializer = receipt.binding.initializer) :
    ResidualEntryCovered receipt.binding.source (packet.statements.map NodeId.statement)
      packet.original.emission.prepared.substitution.domain := by
  obtain ⟨_, source, _, _⟩ := GeneralizedLocalAcceptedCatalogFormation.read_origins receipt
  have accepted := packet.found
  rw [GeneralizedLocalLambdaEmissionFacts.Emission.source, source, initializer] at accepted
  obtain ⟨original, found, same⟩ := expression_before accepted
  have form := packet.form
  rw [← same] at form
  cases original with
  | mk id span type actual requirements coercions localStart =>
    cases actual <;> simp only [ExpressionNode.applySubstitution,
      ExpressionForm.applySubstitution] at form <;> try contradiction
    rename_i parameters result body
    have bodyEq : body = packet.statements := (ExpressionForm.lambda.inj form).2.2
    rw [GeneralizedLocalLambdaEmissionFacts.Emission.substitution, ← bodyEq]
    exact attached.captured.body (read_keys receipt extension) found rfl

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedScopes
