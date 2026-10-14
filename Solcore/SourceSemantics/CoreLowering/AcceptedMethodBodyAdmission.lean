import Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyReceipts

/-! A genuine method instantiation supplies original Source typing for the
actual cached body. Its accepted statement and expression actions construct
the existing method certificate, preserving its full synthetic specialization. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyAdmission
open Core Frontend SourceInference
open AcceptedMethodBodyReceipts
open AcceptedNamedBodyFlow AcceptedNamedExpressionFlow
open CallablePreparedMethodSelection (Cached)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots (DirectSource)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedScopedMethodAdmission (SourceCertificate)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

/-- Final-plan provenance already retains the full successful method recheck
and specialization. Head matching is not needed to recover its typed body;
formation of every actual raw replacement remains a separate premise. -/
theorem instantiates_of_selection
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (selected : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      method.specialized.parameterSubstitution) :
    ∃ definition, definition ∈ (Program.ofChecked compiled.sourceProgram).methods ∧
      definition.id = selected.declaration.id ∧
      Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
        selected.implementation selected.declaration selected.trait definition
        method.specialized.parameterSubstitution
        (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) := by
  obtain ⟨retained, member, idEq, completeEq⟩ := selected.retained checked
  let receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method :=
    ⟨selected, retained, member, idEq, completeEq⟩
  have owner : retained.checked.declaration = selected.implementation.id := by
    rw [← completeEq]
    exact checkFunctionBody_success_declaration selected.bodyChecked
  have traitLookup := selected.traitLookup
  unfold ProgramSignatures.trait? at traitLookup
  have traitMember := List.mem_of_find?_eq_some traitLookup
  have traitOwner : selected.declaration.traitMethod.trait = selected.trait.id := by
    exact (of_decide_eq_true (List.find?_some
      (p := fun trait : ProgramTraitSignature => decide (trait.id = selected.declaration.traitMethod.trait))
      traitLookup)).symm
  have domain : method.specialized.parameterSubstitution.map Prod.fst = selected.implementation.parameters :=
    SourceSpecialization.specializeFunction_parameterDomain selected.specialized
  have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
      method.specialized.parameterSubstitution selected.implementation.parameters :=
    ⟨parameters, by rw [SourceSemantics.ParameterSubstitution.domain, domain]⟩
  refine ⟨MethodDefinition.ofChecked retained, List.mem_map.mpr ⟨retained, member, rfl⟩,
    idEq.trans selected.methodId, ?_⟩
  apply Dynamic.TraitMethodInstantiates.intro selected.implementationMember selected.methodMember
    traitMember traitOwner (List.mem_map.mpr ⟨retained, member, rfl⟩)
    (idEq.trans selected.methodId) owner exactSubstitution range
  · exact receipt.body
  · exact receipt.result.1
  · change declarationContext compiled.sourceProgram.signatures method.specialized.function.typedBody.owner []
      method.specialized.assumptions method.specialized.function.solvedRequirements = _
    rw [receipt.owner, receipt.assumptions, receipt.ledger]
    change declarationContext compiled.sourceProgram.signatures selected.implementation.id [] _ _ =
      declarationContext compiled.sourceProgram.signatures retained.checked.declaration [] _ _
    rw [owner]
    rfl

theorem roots : statements (source cached) = cached.compilation.statements := by
  unfold statements source CallableIndexedNamedGeneration.source
  rw [RecursiveNamedPreparedSourceFrames.compiled_roots_eq cached.compilation]
  simp only [List.filterMap_map]
  induction cached.compilation.statements with
  | nil => rfl
  | cons first rest ih =>
    simpa only [List.filterMap_cons, Function.comp_apply] using congrArg (List.cons first) ih

/-- Source typing follows the full original trait-method substitution. Neither
cache membership nor equality of native result types supplies these facts. -/
theorem source_typing
    {implementation : ProgramImplementationSignature} {declaration : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : TypeSystem.ParameterSubstitution}
    (instantiated : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      implementation declaration trait definition substitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ context final facts,
      StatementsHaveType (source cached) {returnType := cached.named.specialized.function.inferredBodyType}
        context cached.compilation.statements final facts ∧
      NodeOccurrencesUnique (source cached) ∧ LocalIdentityOwnership (source cached) := by
  obtain ⟨types, context, facts, typed⟩ := instantiated.certificate wellFormed
  have sameSource : (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method).source =
      source cached := by
    simp only [source, CallableIndexedNamedGeneration.source, cached.same,
      CallableCoercionMethodInstantiation.bodyInstance]
  have sameResult : (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method).resultType =
      cached.named.specialized.function.inferredBodyType := by
    rw [cached.same]
    rfl
  have body := typed.typing.body_typed
  rw [sameSource, sameResult] at body
  obtain ⟨final, body, _roots, _complete⟩ := body
  change StatementsHaveType (source cached)
    {returnType := cached.named.specialized.function.inferredBodyType}
    context (statements (source cached)) final facts at body
  rw [roots cached] at body
  exact ⟨context, final, facts, body,
    sameSource ▸ typed.graph_closed.wellFormed.nodeOccurrencesUnique,
    sameSource ▸ typed.local_identity_ownership⟩

/-- Open structure and generalized locals remain attached to the same emitted
method body. They are static boundaries, not assumed execution behavior. -/
inductive Unsupported (receipt : BodyAt cached) where
  | structure (openBranch : receipt.tree.closed = false)
  | generalized (binding : Binding (policy cached) (source cached))
      (member : binding ∈ receipt.tree.bindings) (quantified : binding.binder.scheme.quantified ≠ [])

/-- Every reached expression grammar is derived from the actual compiler trace.
Finite original forms and child membership only exclude its retained boundaries. -/
theorem of_instantiated
    {implementation : ProgramImplementationSignature} {declaration : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : TypeSystem.ParameterSubstitution}
    (instantiated : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      implementation declaration trait definition substitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression)
    (closed : receipt.tree.closed = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []) :
    Nonempty (SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨context, final, facts, typed, unique, ownership⟩ := source_typing cached instantiated wellFormed
  have binders := AcceptedNamedBodyBindings.of_monomorphic receipt.tree (read cached)
    unique ownership typed monomorphic
  have grammar : ∀ child ∈ receipt.tree.children,
      GeneralSyntax (source cached) child.expression (DirectSite table.rows) := by
    intro child member
    exact child_syntax cached table wellFormed metadata covered reachedForms arguments initializers
      child.accepted (children child member)
  have body := receipt.tree.scan (read cached) closed unique ownership grammar binders typed
  rw [← roots cached] at body
  exact ⟨⟨forms, ⟨metadata, body⟩⟩⟩

/-- The source certificate or remaining structural boundary belongs to the
same actual method body. No successful shape check is assumed globally. -/
theorem of_receipt
    {implementation : ProgramImplementationSignature} {declaration : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : TypeSystem.ParameterSubstitution}
    (instantiated : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      implementation declaration trait definition substitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression) :
    Nonempty (SourceCertificate compiled cached.named table.rows) ∨ Nonempty (Unsupported cached receipt) := by
  classical
  cases closed : receipt.tree.closed with
  | false => exact .inr ⟨.structure closed⟩
  | true =>
    by_cases mono : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []
    · exact .inl (of_instantiated cached instantiated wellFormed table receipt forms metadata covered
        reachedForms arguments initializers children closed mono)
    · have generalized : ∃ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified ≠ [] := by
        apply Classical.byContradiction
        intro absent
        apply mono
        intro binding member
        apply Classical.byContradiction
        intro different
        exact absent ⟨binding, member, different⟩
      obtain ⟨binding, member, different⟩ := generalized
      exact .inr ⟨.generalized binding member different⟩

/-- The genuine selector retained by final preparation feeds the same existing
method certificate without inventing an ordinary declaration or Source call. -/
theorem of_selection
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (selected : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      method.specialized.parameterSubstitution)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression)
    (closed : receipt.tree.closed = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []) :
    Nonempty (SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨definition, _member, _id, instantiated⟩ := instantiates_of_selection checked selected parameters range
  exact of_instantiated cached instantiated wellFormed table receipt forms metadata covered
    reachedForms arguments initializers children closed monomorphic

end Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyAdmission
