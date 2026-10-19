import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors

/-! The same data-only syntax admission feeds existing evidence-aware scoped
bodies. A finite requirements check preserves the stronger metadata profile
needed by that family, including grammar-supported nodes outside the body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
open CallableIndexedOwnedPreparedNamedScopedAdmission (SourceAdmission Admission)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)

def OrdinaryRequirements (node : ExpressionNode) : Prop :=
  match node.form with
  | .integerLiteral _ _ => True
  | .call _ _ (.declaration _) => True
  | _ => node.requirements = []

instance (node : ExpressionNode) : Decidable (OrdinaryRequirements node) := by
  unfold OrdinaryRequirements
  split <;> infer_instance

private theorem ordinary_requirements {node : ExpressionNode} (checked : OrdinaryRequirements node) :
    node.requirements = [] ∨ (∃ literal resolution, node.form = .integerLiteral literal resolution) ∨
      ∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation) := by
  unfold OrdinaryRequirements at checked
  split at checked
  · exact .inr (.inl ⟨_, _, by assumption⟩)
  · exact .inr (.inr ⟨_, _, _, by assumption⟩)
  · exact .inl checked

def Requirements (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node →
    node.requirements = [] ∨ (∃ literal resolution, node.form = .integerLiteral literal resolution) ∨
      ∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation)

/-- This check covers every actual expression in the original finite table.
Unused operator nodes cannot silently acquire a weaker metadata restriction. -/
def requirements? (source : TypedSource) : Option (PLift (Requirements source)) :=
  if checked : source.nodes.all (fun node => match node with
      | .expression expression => decide (OrdinaryRequirements expression)
      | .statement _ => true) = true then
    some ⟨by
      intro id node found
      have member := (lookupExpression?_sound found).1
      have selected := List.all_eq_true.mp checked (.expression node) member
      exact ordinary_requirements (by simpa only [decide_eq_true_eq] using selected)⟩
  else none

structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) where
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  sourceAdmission : SourceAdmission compiled named named.specialized.function.typedBody
    (statements named.specialized.function.typedBody) named.specialized.function.inferredBodyType table.rows
  requirements : Requirements named.specialized.function.typedBody

/-- No semantic catalog or classically selected Header is an executable input.
The cache table, original syntax and evidence restriction are certified together. -/
def certifySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (named : SourceCoreGeneralFunctions.Function) (fuel : Nat) :
    Option (Certificate compiled named) := do
  let checked ← CallableIndexedOwnedPreparedNamedCatalogAdmission.certifySource compiled wellFormed
    named named.specialized.function.typedBody (statements named.specialized.function.typedBody)
    named.specialized.function.inferredBodyType fuel
  let ⟨requirements⟩ ← requirements? named.specialized.function.typedBody
  pure ⟨checked.table, checked.sourceAdmission, requirements⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {index : Nat} {named : SourceCoreGeneralFunctions.Function}
  (selected : compiled.indexed.base.functions[index]? = some named)
  (same : named.specialized = row)
  (certificate : Certificate compiled named)

include prepared aligned selected same certificate in
theorem at_header : Admission prepared header certificate.table.rows :=
  source_at_header prepared aligned selected same certificate.sourceAdmission

include prepared aligned selected same certificate in
theorem metadata_at_header :
    CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite certificate.table.rows) := by
  have admission := at_header prepared aligned selected same certificate
  refine ⟨?_, admission.metadata.coercions, admission.metadata.initializer,
    admission.metadata.arguments, admission.metadata.localRead⟩
  intro id _tree node found
  rw [(header_data prepared aligned).1, cached_named prepared selected same] at found
  exact certificate.requirements id node found

include prepared aligned selected same certificate in
/-- Actual accepted statement compilation supplies the receipt; the source
checker supplies only its static shape. -/
theorem receipt : Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header) :=
  CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted aligned.accepted
    (at_header prepared aligned selected same certificate).body.shape aligned.projection

/-- Existing complete ordinary inventories cover the actual scanned cache;
all direct support, metadata and statement syntax are constructed internally. -/
def of_receipt {inputs : List (Input compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers rows))
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (bodyReceipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      (headers rows) keys bodyRegistry header (RecursiveNamedPreparedStageScopes.registry actual)
      bodyReceipt (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  have admission := at_header prepared aligned selected same certificate
  have table := table_aligned_of_complete rows complete certificate.table
  have syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source
      (fun id => CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        header.function.source id (DirectSite certificate.table.rows))
      header.context (.statements true header.function.body) header.function.resultType := by
    obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
    exact admission.body.syntax header.unique typed
  exact CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors.of_actual prepared aligned
    ready diagnostic receiver wellFormed (fun _ site => site.supported table)
    (metadata_at_header prepared aligned selected same certificate) rows complete zero member
    bodyReceipt actual syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceAdmission
