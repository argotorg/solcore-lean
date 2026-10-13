import Solcore.SourceSemantics.CoreLowering.AcceptedNamedScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.CompilerProgramStaticProfile
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedRefinedBodyAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedMethods
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedNamed
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedScopedFactories

/-! Every actual cache position receives its genuine compiler origin. Flat
profiles close the retained statement and expression receipts, after which
the existing full program certificate is assembled internally. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramAdmission
open Core Frontend SourceInference
open CompilerProgramStaticProfile
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedOrdinarySyntaxTable (Table)
open CallableIndexedOwnedPreparedProgramAdmission (RootCertificate RowCertificate Certificate)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

private theorem no_lambdas {named : SourceCoreGeneralFunctions.Function}
    {rows : List SourceSpecialization.SpecializedFunction}
    (absent : ∀ node ∈ named.specialized.function.typedBody.nodes, LambdaAllowed none node) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate compiled named rows false := by
  constructor
  intro node member
  have original := absent node member
  cases node with
  | statement statement => exact True.intro
  | expression expression =>
    cases form : expression.form
    case lambda parameters result body =>
      simp only [LambdaAllowed, form] at original
      cases original
    all_goals simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, form]

private theorem scoped_of_header
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) (same : named.specialized = row)
    {rows : List SourceSpecialization.SpecializedFunction}
    (profile : Scoped compiled named rows false)
    (supported : ∀ instantiation, DirectSite rows instantiation → Supported compiled.indexed.base.plan instantiation)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    Nonempty (RowCertificate compiled named rows false) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  obtain ⟨source, body, _result⟩ :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned
  rw [namedEq] at source body
  let expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source rows false true true := by
    rw [source, namedEq]
    exact profile.expressions
  have flatBody : AcceptedCompilerBodyProfile.Profile header.function.source expressions.Reached := by
    change AcceptedCompilerBodyProfile.Profile header.function.source
      (fun id => id ∈ AcceptedCompilerExpressionProfile.supportedIds header.function.source false true true)
    rw [source]
    exact profile.body
  have returns : AcceptedCompilerBodyProfile.HasReturn header.function.source header.function.body := by
    rw [source, body]
    exact profile.returns
  obtain ⟨receipt, ready⟩ := AcceptedNamedBodyRefinement.of_header prepared aligned
  obtain ⟨closed, monomorphic, children⟩ := AcceptedCompilerBodyProfile.facts receipt.tree
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) flatBody ready (.inr returns)
  have admission := SelectedCompilationAcceptedNamed.of_receipt prepared aligned receipt
    expressions.metadata supported expressions.covered closed monomorphic
    (by
      intro child member residual
      obtain ⟨residual⟩ := residual
      exact residual.impossible_constructors expressions.metadata expressions.constructorForms expressions.noInitializer
        expressions.constructorArguments expressions.constructorMetadata expressions.requirements expressions.indexOperands expressions.constructorRanges (children child member)) certified
  exact ⟨⟨.scoped (AcceptedNamedBodyAdmission.source_of_header prepared aligned selected same admission),
    no_lambdas profile.lambdas⟩⟩

private theorem factory_of_header
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) (same : named.specialized = row)
    {rows : List SourceSpecialization.SpecializedFunction}
    (profile : Factory compiled named rows)
    (supported : ∀ instantiation, DirectSite rows instantiation → Supported compiled.indexed.base.plan instantiation)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    Nonempty (RowCertificate compiled named rows false) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  obtain ⟨source, body, _result⟩ :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned
  rw [namedEq] at source body
  let expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source rows true := by
    rw [source, namedEq]
    exact profile.expressions
  have ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
      (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed prepared.named).owner ∧
        binding.initializer = profile.expression)) = none := by
    rw [namedEq]
    exact profile.ordinary
  obtain ⟨produced, statementEq, expressionEq⟩ :=
    SelectedCompilationAcceptedFactories.produced_of_returning prepared aligned
      (by rw [body]; exact profile.roots) (by rw [source]; exact profile.outerFound) profile.outerForm
      (by rw [source]; exact profile.found) profile.form profile.requirements profile.coercions ordinary
      (by rw [source]; exact profile.returnFound) profile.returnForm certified
  obtain ⟨factory⟩ := AcceptedNamedFactoryAdmission.source_of_header prepared aligned selected same produced.certificate
  have reached : expressions.Reached produced.certificate.returnExpression := by
    change produced.certificate.returnExpression ∈ AcceptedCompilerExpressionProfile.supportedIds header.function.source true
    rw [expressionEq, source]
    exact profile.innerReached
  obtain ⟨closure⟩ := AcceptedNamedClosureAdmission.of_produced prepared aligned produced
    expressions.metadata supported expressions.covered expressions.directForms expressions.noInitializer
    expressions.directArguments reached
  obtain ⟨closure⟩ := AcceptedNamedClosureAdmission.source_of_header prepared selected same closure
  rw [statementEq] at closure
  refine ⟨⟨.formation factory, ⟨?_⟩⟩⟩
  intro node member
  have covered := profile.lambdas node member
  cases node with
  | statement statement => exact True.intro
  | expression expression =>
    cases form : expression.form
    case lambda parameters result body =>
      simp only [LambdaAllowed, form, Option.some.injEq] at covered
      subst expression
      rw [profile.form] at form
      cases form
      simpa only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, profile.form] using
        (show Nonempty (CallableIndexedOwnedPreparedClosureAdmission.BodyCertificate compiled named rows false
          [profile.statement]) from ⟨.ordinary closure⟩)
    all_goals simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, form]

private theorem scoped_factory_of_header
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) (same : named.specialized = row)
    {rows : List SourceSpecialization.SpecializedFunction}
    (profile : ScopedFactory compiled named rows)
    (supported : ∀ instantiation, DirectSite rows instantiation → Supported compiled.indexed.base.plan instantiation)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    Nonempty (RowCertificate compiled named rows false) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  obtain ⟨source, body, _result⟩ :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned
  rw [namedEq] at source body
  let expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source rows false true true := by
    rw [source, namedEq]
    exact profile.expressions
  have ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
      (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed prepared.named).owner ∧
        binding.initializer = profile.expression)) = none := by
    rw [namedEq]
    exact profile.ordinary
  have bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids profile.statements := by
    change AcceptedCompilerBodySubsetProfile.Profile header.function.source
      (AcceptedCompilerExpressionProfile.supportedIds header.function.source false true true) profile.statements
    rw [source]
    exact profile.body
  obtain ⟨⟨factory⟩, ⟨closure⟩⟩ := SelectedCompilationAcceptedScopedFactories.of_returning prepared aligned
    (by rw [body]; exact profile.roots) (by rw [source]; exact profile.outerFound) profile.outerForm
    (by rw [source]; exact profile.found) profile.form profile.requirements profile.coercions
    ordinary expressions bodyProfile supported certified
  obtain ⟨factory⟩ := AcceptedNamedScopedFactoryAdmission.source_of_header prepared aligned selected same factory
  obtain ⟨closure⟩ := AcceptedNamedScopedFactoryAdmission.closure_of_header prepared selected same closure
  refine ⟨⟨.scopedFactory factory, ⟨?_⟩⟩⟩
  intro node member
  have covered := profile.lambdas node member
  cases node with
  | statement statement => exact True.intro
  | expression expression =>
    cases form : expression.form
    case lambda parameters result statements =>
      simp only [LambdaAllowed, form, Option.some.injEq] at covered
      subst expression
      rw [profile.form] at form
      cases form
      simpa only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, profile.form] using
        (show Nonempty (CallableIndexedOwnedPreparedClosureAdmission.BodyCertificate compiled named rows false
          profile.statements) from ⟨.scoped closure⟩)
    all_goals simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, form]

private theorem ordinary_row {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (eligible : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible compiled named.specialized)
    {rows : List SourceSpecialization.SpecializedFunction} (profile : Ordinary compiled named rows)
    (supported : ∀ instantiation, DirectSite rows instantiation → Supported compiled.indexed.base.plan instantiation)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled) :
    Nonempty (RowCertificate compiled named rows false) := by
  obtain ⟨prepared, _indexEq, namedEq⟩ :=
    CallableIndexedOwnedPreparedOrdinaryCachedInputs.of_cached_origin_at compiled selected rfl eligible.origin
  obtain ⟨header, aligned⟩ := SelectedCompilationHeaders.retained_header prepared
    (values := .initial compiled.compatible.checked) bodies eligible.range
    eligible.ordinaryReturn eligible.ordinaryParameters
    (by
      rw [namedEq]
      exact SelectedCompilationCatalog.retained_target
        compiled bodies.signatures selected eligible.origin)
  have certified := SelectedCompilationHeaders.certificate_at prepared bodies eligible.range aligned
  cases profile with
  | «scoped» profile => exact scoped_of_header prepared aligned selected rfl profile supported certified
  | factory profile => exact factory_of_header prepared aligned selected rfl profile supported certified
  | scopedFactory profile => exact scoped_factory_of_header prepared aligned selected rfl profile supported certified

private theorem method_origin {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) (excluded : NoOrdinary compiled named) :
    ∃ method : ExecutableImplMethods.CheckedMethod,
      Nonempty (CallableCoercionBodyProvenance.Selection compiled.sourceProgram method) ∧
      named.specialized = method.specialized := by
  have origin := CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
    named.specialized (RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl)
  generalize same : named.specialized = row at origin
  cases origin with
  | ordinary original =>
    obtain ⟨request, signature, generic, member, _, _, specialized⟩ := original
    have fields := RecursiveNamedSpecializationBodyFacts.identities specialized
    have declaration : named.specialized.declaration = signature.id := by
      rw [same]
      exact fields.2.2.trans fields.1.symm
    exact False.elim (excluded signature member declaration)
  | @method method selection => exact ⟨method, ⟨selection⟩, rfl⟩

private theorem method_row {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (table : Table compiled)
    (catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled)
    (excluded : NoOrdinary compiled named)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) named.specialized.parameterSubstitution)
    (forms : CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.DirectSource named.specialized.function.typedBody)
    (profile : Scoped compiled named table.rows true) :
    Nonempty (CallableIndexedOwnedPreparedScopedMethodAdmission.SourceCertificate compiled named table.rows) := by
  obtain ⟨method, ⟨selection⟩, same⟩ := method_origin selected excluded
  obtain ⟨diagnostics, code, generated, ⟨compilation⟩⟩ :=
    CallableIndexedNamedGeneration.compiled_at compiled.indexed selected
  let cached : CallablePreparedMethodSelection.Cached compiled method.specialized :=
    ⟨index, named, diagnostics, code, selected, same, generated, compilation⟩
  obtain ⟨receipt, ready⟩ := AcceptedMethodBodyReceipts.of_cached cached
  have returns : AcceptedCompilerBodyProfile.HasReturn (AcceptedMethodBodyReceipts.source cached)
      cached.compilation.statements := by
    rw [← AcceptedMethodBodyAdmission.roots cached]
    exact profile.returns
  obtain ⟨closed, monomorphic, children⟩ := AcceptedCompilerBodyProfile.facts receipt.tree
    (AcceptedMethodBodyReceipts.read cached) profile.body ready (.inr returns)
  have formation := catalog.formed.formed selection.implementation selection.implementationMember
    selection.declaration selection.methodMember
  exact SelectedCompilationAcceptedMethods.of_selection cached checked selection formation.parameters
    (by rw [← same]; exact range) bodies table receipt forms profile.expressions.metadata
    profile.expressions.covered profile.expressions.directForms profile.expressions.directArguments
    profile.expressions.noInitializer children closed monomorphic

/-- Actual indices select flat profiles; equality preserves the complete named
carrier, not just its key or result representation. -/
theorem profile_at {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (profile : StaticProfile compiled) (selected : compiled.indexed.base.functions[index]? = some named) :
    Nonempty (Row compiled named profile.table.rows) := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp selected
  have actual := profile.rows ⟨index, bound⟩
  simpa only [same] using actual

/-- The existing complete certificate is built from all actual cache positions.
No caller supplies a per-row completion function or a recursive syntax proof. -/
theorem of_profile (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (profile : StaticProfile compiled) : Nonempty (Certificate compiled) := by
  obtain ⟨catalog⟩ := SelectedCompilationCatalog.of_compiled compiled bodies
  have supported : ∀ instantiation, DirectSite profile.table.rows instantiation →
      Supported compiled.indexed.base.plan instantiation := fun _ site =>
    site.supported (profile.table.aligned catalog)
  have completed : ∀ named ∈ compiled.indexed.base.functions,
      Nonempty (RowCertificate compiled named profile.table.rows false) ∧
      CallableIndexedOwnedPreparedScopedMethodAdmission.RowCase compiled named profile.table.rows := by
    intro named member
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := profile_at profile selected
    cases row with
    | ordinary eligible excluded data =>
      exact ⟨ordinary_row selected eligible data supported bodies, .inl excluded⟩
    | method excluded range forms data =>
      exact ⟨⟨⟨.excluded excluded, no_lambdas data.lambdas⟩⟩,
        .inr (method_row selected checked bodies profile.table profile.catalog excluded range forms data)⟩
  exact ⟨{
    table := profile.table
    selection := .origins ⟨fun named member => (completed named member).2⟩ profile.catalog
    rows := fun named member => (completed named member).1
    profile := profile.callable
    diagnostics := profile.diagnostics }⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramAdmission
