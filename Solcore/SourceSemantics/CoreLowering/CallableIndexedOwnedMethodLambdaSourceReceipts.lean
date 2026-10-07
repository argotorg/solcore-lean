import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal
import Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceAdmission

/-! A selected method retains its genuine trait authority and full dictionary.
Its emitted compiler principal supplies a factory-created lambda site without
an ordinary function Header. Exact plan preparation authenticates that site's
Source graph and original stage descriptor. Body support and runtime captures
remain separate receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSourceReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)

/-- The same selected method has canonical compiler Source provenance. Its
independent Source authority remains the original method selector. -/
theorem source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      principal.named.signature.key [] principal.sourceBody.source := by
  rw [← principal.source_eq]
  exact .original principal.record

/-- Original whole-program validity and genuine trait instantiation establish
occurrence uniqueness for this exact selected method graph. -/
theorem source_unique (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    NodeOccurrencesUnique principal.sourceBody.source := by
  obtain ⟨implementation, methodSignature, trait, definition, substitution, instantiated⟩ :=
    principal.source_instantiation
  obtain ⟨inputTypes, context, facts, certificate⟩ := instantiated.certificate wellFormed
  exact certificate.graph_closed.wellFormed.nodeOccurrencesUnique

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context evidence environment scope administrative)

/-- The actual factory site retains its complete source and empty cumulative
substitution; neither is inferred from native callable typing. -/
theorem site_provenance
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      site.code.compilation.owner site.code.active
      (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context evidence environment).source ∧
    NodeOccurrencesUnique
      (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context evidence environment).source := by
  constructor
  · rw [site.compilation, site.active]
    exact .original principal.record
  · change NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named)
    rw [principal.source_eq]
    exact source_unique principal wellFormed

/-- The real selected hook supplies the site's entire carried compiler seed.
The dictionary and lexical generation inputs remain those in the site. -/
theorem site_history :
    ∃ hook, compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook ∧
      ∃ history : History site.code,
        history.native = SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table hook ∧
        history.ghost = .named hook ∧ history.metadata = CallableIndexedNamedGeneration.state principal.named := by
  exact site.history principal.cached.compilation principal.record

variable {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope environment actual)
  (actualSite : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context evidence environment scope captured.administrative)
  (history : History actualSite.code)

/-- Original table preparation authenticates the actual emitted descriptor
and the same full lambda Source. Captures and carried history stay explicit. -/
theorem origin_of_site
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context evidence environment))
      (CallableIndexedLambdaValues.value actualSite.code captured.embedding history.native actual) := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  obtain ⟨source, unique⟩ := site_provenance principal actualSite wellFormed
  exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted actualSite.code.descriptor
    source actualSite.code.viewOfSource unique actualSite.code.found
    (actualSite.code.form.trans actualSite.code.sourceForm) _

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSourceReceipts
