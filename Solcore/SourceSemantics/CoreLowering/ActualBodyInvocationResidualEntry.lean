import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalReadMaterialization
import Solcore.SourceSemantics.CoreLowering.NamedInvocationResidualEntry
import Solcore.SourceSemantics.SourceSpecializationLocalLexicalSubstitutionChildren

/-! The existing actual invocation carries scope evidence for its original
cached body. Named calls derive it from their root receipt; contextual calls
retain the evidence produced by the real stored read. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableLambdaBodyReachability CallableBodyMetadataViews
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

/-- The same final-plan source precedes the native flexible action. -/
def Index.originalSource : Index compiled bodyRelation → TypedSource
  | @Index.named _ _ callable _ _ _ _ => callable.specialized.function.typedBody
  | .contextual material _ => material.candidate.origin.source

/-- This proof component is produced at named entry or at the actual contextual
read. It does not alter the invocation's native or Source representation. -/
def Index.ResidualEntry : Index compiled bodyRelation → Prop
  | .named _ _ => True
  | .contextual material _ => SelectedCompilationLocalReadMaterialization.Entry material

theorem Index.original_receipt (index : Index compiled bodyRelation) :
    ∃ row, SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan index.owner = .ok row ∧
      row.function.typedBody = index.originalSource := by
  cases index with
  | named receipt selected => exact ⟨_, selected, rfl⟩
  | contextual material view =>
    obtain ⟨row, selected, source, _, _⟩ :=
      LambdaSourceAlignment.prepared_source material.packet.original.emission.authentic
    rw [material.indexed.plan] at selected
    refine ⟨row, ?_, source⟩
    simpa only [Index.owner, material.compilation, GeneralizedLocalLambdaCompilation.context,
      material.indexed.owner] using selected

theorem Index.compiler_original (index : Index compiled bodyRelation) :
    index.compilerSource = index.originalSource.applySubstitution index.active := by
  cases index with
  | named receipt selected => exact (EmptySourceSubstitution.source _).symm
  | contextual material view =>
    exact SelectedCompilationLocalSourceReceipts.compiler_source material

theorem Index.ResidualEntry.covered {index : Index compiled bodyRelation}
    (entry : index.ResidualEntry) :
    ResidualEntryCovered index.originalSource (index.statements.map NodeId.statement)
      index.active.domain := by
  cases index with
  | named receipt selected => exact receipt.residual_entry
  | contextual material view =>
    exact SelectedCompilationLocalReadMaterialization.Entry.covered entry

theorem Index.reaches_original (index : Index compiled bodyRelation) {node : NodeId}
    (path : Reaches index.compilerSource (index.statements.map NodeId.statement) node) :
    Reaches index.originalSource (index.statements.map NodeId.statement) node := by
  apply (reaches_substitution index.active).mp
  rwa [← index.compiler_original]

/-- Both the invocation and the selected candidate resolve the same real key
in the final plan. This fixes the binding source before either substitution. -/
theorem Index.binding_original (index : Index compiled bodyRelation)
    {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (owner : binding.caller = index.owner) :
    binding.source = index.originalSource := by
  obtain ⟨candidateOwner, candidateSource, _, _⟩ :=
    SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨target, targetFound, targetSource, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, candidateOwner, owner] at targetFound
  obtain ⟨original, originalFound, originalSource⟩ := index.original_receipt
  have same : target = original := Except.ok.inj (targetFound.symm.trans originalFound)
  exact (targetSource.trans candidateSource).symm.trans (same ▸ originalSource)

/-- Runtime statement lookup extends the original lexical path through the
actual substitution, without comparing unrelated table entries. -/
theorem Index.statement_lexical_child (index : Index compiled bodyRelation)
    {id : StatementId} {node : StatementNode} {child : NodeId}
    (path : LocalLambdaLexicalPath index.originalSource
      (index.statements.map NodeId.statement) (.statement id))
    (found : index.compilerSource.lookupStatement? id = some node)
    (edge : child ∈ node.form.references) :
    LocalLambdaLexicalPath index.originalSource (index.statements.map NodeId.statement) child := by
  rw [index.compiler_original] at found
  exact path.statement_child_of_substitution found edge

/-- A non-lambda expression extends the same original lexical path. Lambda
bodies start with their own actual invocation-entry evidence. -/
theorem Index.expression_lexical_child (index : Index compiled bodyRelation)
    {id : ExpressionId} {node : ExpressionNode} {child : NodeId}
    (path : LocalLambdaLexicalPath index.originalSource
      (index.statements.map NodeId.statement) (.expression id))
    (found : index.compilerSource.lookupExpression? id = some node)
    (nonLambda : ∀ parameters result body, node.form ≠ .lambda parameters result body)
    (edge : child ∈ node.form.references) :
    LocalLambdaLexicalPath index.originalSource (index.statements.map NodeId.statement) child := by
  rw [index.compiler_original] at found
  exact path.expression_child_of_substitution found nonLambda edge

/-- A body site keeps the executed compiler path and the original lexical
path together. The constructors below follow the actual roots and lookups. -/
structure Index.Site (index : Index compiled bodyRelation) (node : NodeId) : Prop where
  reached : index.Reached node
  lexical : LocalLambdaLexicalPath index.originalSource
    (index.statements.map NodeId.statement) node

theorem Index.site_root (index : Index compiled bodyRelation) {id : StatementId}
    (member : id ∈ index.statements) : index.Site (.statement id) :=
  ⟨index.body_root member, .root (List.mem_map.mpr ⟨id, member, rfl⟩)⟩

theorem Index.Site.statement_child {index : Index compiled bodyRelation}
    {id : StatementId} (site : index.Site (.statement id))
    {node : StatementNode} (found : index.compilerSource.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Site child :=
  ⟨.statement site.reached found edge,
    index.statement_lexical_child site.lexical found edge⟩

theorem Index.Site.expression_child {index : Index compiled bodyRelation}
    {id : ExpressionId} (site : index.Site (.expression id))
    {node : ExpressionNode} (found : index.compilerSource.lookupExpression? id = some node)
    (nonLambda : ∀ parameters result body, node.form ≠ .lambda parameters result body)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Site child :=
  ⟨.expression site.reached found edge,
    index.expression_lexical_child site.lexical found nonLambda edge⟩

/-- Source execution and native compilation share the reached statement.
This transports the same site through a genuine Source child step. -/
theorem Index.Site.statement_source_child {index : Index compiled ReachedView}
    {id : StatementId} (site : index.Site (.statement id))
    {node : StatementNode} (found : index.source.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Site child := by
  apply site.statement_child _ edge
  exact (index.reached_view.statement (.inr site.reached)).symm.trans found

theorem Index.Site.expression_source_child {index : Index compiled ReachedView}
    {id : ExpressionId} (site : index.Site (.expression id))
    {node : ExpressionNode} (found : index.source.lookupExpression? id = some node)
    (nonLambda : ∀ parameters result body, node.form ≠ .lambda parameters result body)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Site child := by
  obtain ⟨actual, selected, _, form⟩ :=
    index.reached_view.expression_back (.inr site.reached) found
  apply site.expression_child selected
  · simpa only [form] using nonLambda
  · simpa only [form] using edge

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
