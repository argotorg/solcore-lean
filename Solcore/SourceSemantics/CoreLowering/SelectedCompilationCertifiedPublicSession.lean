import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramSupportIssuer
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalogFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogPublicAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionRegistry

/-! A checked program certificate issues one automatic catalog and its complete
physical support. Later public starts retain the same Source heap and history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

structure Issued (recipe : SourceCoreIndexedSession.Recipe) where
  prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe
  catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog recipe.compiled
  initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed
  support : SelectedCompilationPhysicalProgramSupport.Support recipe.compiled
    (headers catalog.rows) (keys recipe.compiled) initial

variable {recipe : SourceCoreIndexedSession.Recipe}

/-- The authentic selected public entry supplies the diagnostic receiver. The
checker receipt keeps its original budget when the support is issued. -/
theorem of_checked
    (certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Issued recipe) := by
  obtain ⟨initial, _sameEntry, registry, received⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry recipe.compiled entry
      recipe.compiled.compatible.checked.staticRegistry (.refl _)
  obtain ⟨catalog, ⟨support⟩⟩ := SelectedCompilationProgramSupportIssuer.issue certificate bodies prepared received registry member checked
  exact ⟨⟨prepared, catalog, initial, support⟩⟩

abbrev Issued.State (issued : Issued recipe)
    (anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) :=
  RecursiveNamedPublicPhysicalSessionState.State issued.catalog.rows anchor issued.initial
    issued.support.profile recipe session entries

/-- The real current history supplies the native state used by the front door.
The original entry's full instantiation determines the actual first cache row. -/
theorem Issued.recover_start_entry (issued : Issued recipe)
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : issued.State anchor session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    {entry : Dynamic.ProgramEntry} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan entry.instantiation = .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked recipe.compiled.sourceProgram) entry state.heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store,
      CallableNamedMetadata.Matches request.header.named.specialized entry.instantiation := by
  exact SelectedCompilationCatalogFrontdoor.recover_start_entry issued.catalog issued.support.bodyTyping.signatures issued.prepared state.atRecipe
    state.history.semantic.current.1 state.atSession target valid ordinaryReturn ordinaryParameters call.started

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
