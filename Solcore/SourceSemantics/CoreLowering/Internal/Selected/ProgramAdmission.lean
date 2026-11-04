import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PreparedMethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.AcceptedFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ProgramCompletion
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.SourceExecutableBinderInterfaces
import Solcore.SourceSemantics.SubstitutionCorrespondence
import Solcore.SourceSemantics.Graph
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodBodies
import Solcore.SourceSemantics.SourceInferenceSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedCheckedBodyTypingBridge
import Solcore.SourceSemantics.SourceInferenceSelectedActualSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCoercedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.OrdinaryMethodRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveSourceAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.Staging.SelectedPreservationContracts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicApplicationResults

/-!
# Selected compilations: program admission

Program admission and the support issuer: admission of named, scoped and closure bodies, selected body interfaces, registry bodies, and the certificates of older programs.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedNamed
/-! One refined accepted body supplies all actual expression actions. Closed
structure and original monomorphic bindings discharge the body boundary;
every remaining expression residual refers to a child of this same receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedNamed
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedBodyAdmission (BodyAt)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedNamedScopedAdmission (Admission)

theorem of_receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (receipt : BodyAt header)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite directRows instantiation)
    (complete : receipt.tree.complete header.function.resultType = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = [])
    (excluded : ∀ child ∈ receipt.tree.children,
      ¬ Nonempty (AcceptedNamedExpressionFlow.Residual prepared header (DirectSite directRows)
        child.fuel header.function.source child.scope child.expression child.lowered))
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    Admission prepared header directRows := by
  have children : ∀ child ∈ receipt.tree.children,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        header.function.source child.expression (DirectSite directRows) := by
    intro child member
    cases AcceptedNamedExpressionFlow.syntax_of_header prepared aligned metadata supported covered child.accepted with
    | inl grammar => exact grammar
    | inr residual => exact False.elim (excluded child member residual)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  obtain ⟨_facts, certificate⟩ := certified
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certificate.local_identity_ownership
  have bindings := AcceptedNamedBodyBindings.of_monomorphic receipt.tree
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    header.unique ownership typed monomorphic
  exact ⟨metadata, receipt.tree.scan_complete
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    complete header.unique ownership children bindings typed⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedNamed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramAdmission
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
open SelectedCompilationPreparedProgramCertificates (RootCertificate RowCertificate Certificate)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

private theorem no_lambdas {named : SourceCoreGeneralFunctions.Function}
    {rows : List SourceSpecialization.SpecializedFunction} {allowCoerced : Bool}
    (absent : ∀ node ∈ named.specialized.function.typedBody.nodes, LambdaAllowed none node) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate compiled named rows allowCoerced := by
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
  have finish : AcceptedCompilerBodyCompletion.Finish header.function.source
      header.function.resultType true header.function.body := by
    rw [source, body, _result, namedEq]
    exact profile.finish
  obtain ⟨receipt, ready⟩ := AcceptedNamedBodyRefinement.of_header prepared aligned
  obtain ⟨closed, monomorphic, children⟩ := AcceptedCompilerBodyProfile.facts receipt.tree
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) flatBody ready finish
  have admission := SelectedCompilationAcceptedNamed.of_receipt prepared aligned receipt
    expressions.metadata supported expressions.covered closed monomorphic
    (by
      intro child member residual
      obtain ⟨residual⟩ := residual
      exact residual.impossible_ordinary expressions.metadata expressions.compositeForms expressions.noInitializer
        expressions.ordinaryArguments expressions.ordinaryMetadata expressions.indexOperands expressions.constructorRanges (children child member)) certified
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

private theorem coerced_factory_of_header
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) (same : named.specialized = row)
    {rows : List SourceSpecialization.SpecializedFunction}
    (profile : CoercedFactory compiled named rows)
    (supported : ∀ instantiation, DirectSite rows instantiation → Supported compiled.indexed.base.plan instantiation)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    Nonempty (RowCertificate compiled named rows true) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  obtain ⟨source, body, _result⟩ :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned
  rw [namedEq] at source body
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
  let inner : CompilerCoercedExpressionProfile.Profile compiled prepared.named
      header.function.source rows profile.inner := by
    rw [source, namedEq]
    exact profile.innerProfile
  have innerAt : CompilerCoercedExpressionProfile.Profile compiled prepared.named
      header.function.source rows produced.certificate.returnExpression := expressionEq ▸ inner
  obtain ⟨actualClosure⟩ := SelectedCompilationAcceptedCoercedFactories.of_produced prepared aligned
    produced innerAt supported
  have closure : CallableIndexedOwnedPreparedCoercedClosureAdmission.BodyCertificate compiled named rows
      [produced.certificate.returnStatement] := namedEq ▸ actualClosure
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
        (show Nonempty (CallableIndexedOwnedPreparedClosureAdmission.BodyCertificate compiled named rows true
          [profile.statement]) from ⟨.coerced rfl closure⟩)
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
  have bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids profile.statements profile.result := by
    change AcceptedCompilerBodySubsetProfile.Profile header.function.source
      (AcceptedCompilerExpressionProfile.supportedIds header.function.source false true true) profile.statements profile.result
    rw [source]
    exact profile.body
  obtain ⟨⟨factory⟩, ⟨closure⟩⟩ := SelectedCompilationAcceptedScopedFactories.of_returning prepared aligned
    (by rw [body]; exact profile.roots) (by rw [source]; exact profile.outerFound) profile.outerForm
    (by rw [source]; exact profile.found) profile.form profile.requirements profile.coercions
    ordinary expressions bodyProfile supported certified
  obtain ⟨factory⟩ := SelectedCompilationAcceptedScopedFactories.source_of_header prepared aligned selected same factory
  obtain ⟨closure⟩ := SelectedCompilationAcceptedScopedFactories.closure_of_header prepared selected same closure
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

private theorem coerced_row {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (eligible : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible compiled named.specialized)
    {rows : List SourceSpecialization.SpecializedFunction} (profile : CoercedFactory compiled named rows)
    (supported : ∀ instantiation, DirectSite rows instantiation → Supported compiled.indexed.base.plan instantiation)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled) :
    Nonempty (RowCertificate compiled named rows true) := by
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
  exact coerced_factory_of_header prepared aligned selected rfl profile supported certified

private theorem enable_row {named : SourceCoreGeneralFunctions.Function}
    {rows : List SourceSpecialization.SpecializedFunction} (original : RowCertificate compiled named rows false) :
    Nonempty (RowCertificate compiled named rows true) := by
  refine ⟨⟨original.root, ⟨?_⟩⟩⟩
  intro node member
  have ready := original.closures.nodes node member
  cases node with
  | statement node => exact True.intro
  | expression node =>
    cases form : node.form
    case lambda parameters result body =>
      simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, form] at ready ⊢
      obtain ⟨certificate⟩ := ready
      cases certificate with
      | ordinary certificate => exact ⟨.ordinary certificate⟩
      | «scoped» certificate => exact ⟨.scoped certificate⟩
      | coerced impossible certificate => cases impossible
    all_goals simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, form]

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

private theorem primitive_row {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (profile : CompilerCoercedMethodProfile.Primitive compiled named) :
    Nonempty (CallableIndexedOwnedPreparedPrimitiveMethodAdmission.SourceCertificate compiled named) := by
  obtain ⟨method, ⟨_selection⟩, same⟩ := method_origin selected profile.noOrdinary
  obtain ⟨diagnostics, code, generated, ⟨compilation⟩⟩ :=
    CallableIndexedNamedGeneration.compiled_at compiled.indexed selected
  let cached : CallablePreparedMethodSelection.Cached compiled method.specialized :=
    ⟨index, named, diagnostics, code, selected, same, generated, compilation⟩
  obtain ⟨metadata, accepted⟩ := profile.metadataAccepted
  exact SelectedCompilationAcceptedPrimitiveMethods.of_cached cached profile.terminal profile.forms accepted

private theorem closed_methods (closed : CompilerCoercedMethodProfile.Closed compiled) :
    Nonempty (CallableIndexedOwnedPreparedPrimitiveMethodAdmission.Certificate compiled) := by
  refine ⟨⟨?_⟩⟩
  intro named member
  cases closed.methods named member with
  | inl excluded => exact .inl excluded
  | inr profiles =>
    obtain ⟨profile⟩ := profiles
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    exact .inr (primitive_row selected profile)

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
  have finish : AcceptedCompilerBodyCompletion.Finish (AcceptedMethodBodyReceipts.source cached)
      cached.named.specialized.function.inferredBodyType true cached.compilation.statements := by
    rw [← AcceptedMethodBodyAdmission.roots cached]
    exact profile.finish
  obtain ⟨closed, monomorphic, children⟩ := AcceptedCompilerBodyProfile.facts receipt.tree
    (AcceptedMethodBodyReceipts.read cached) profile.body ready finish
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

private theorem of_closed (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (profile : StaticProfile compiled) (closed : CompilerCoercedMethodProfile.Closed compiled) :
    Nonempty (Certificate compiled) := by
  obtain ⟨catalog⟩ := SelectedCompilationCatalog.of_compiled compiled bodies
  have supported : ∀ instantiation, DirectSite profile.table.rows instantiation →
      Supported compiled.indexed.base.plan instantiation := fun _ site =>
    site.supported (profile.table.aligned catalog)
  obtain ⟨methods⟩ := closed_methods closed
  have completed : ∀ named ∈ compiled.indexed.base.functions,
      Nonempty (RowCertificate compiled named profile.table.rows true) := by
    intro named member
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := profile_at profile selected
    cases row with
    | ordinary eligible excluded data =>
      obtain ⟨original⟩ := ordinary_row selected eligible data supported bodies
      exact enable_row original
    | coercedFactory eligible excluded data _ => exact coerced_row selected eligible data supported bodies
    | method excluded range forms data => exact ⟨⟨.excluded excluded, no_lambdas data.lambdas⟩⟩
    | closedMethod data _ => exact ⟨⟨.excluded data.noOrdinary, no_lambdas (primitive_lambdas data)⟩⟩
  exact ⟨{
    table := profile.table
    selection := .closed methods closed.catalog
    rows := completed
    profile := profile.callable
    diagnostics := profile.diagnostics }⟩

private def OrdinaryLane {named : SourceCoreGeneralFunctions.Function}
    {rows : List SourceSpecialization.SpecializedFunction} : Row compiled named rows → Prop
  | .ordinary .. | .method .. => True
  | .coercedFactory .. | .closedMethod .. => False

/-- The existing complete certificate is built from all actual cache positions.
The original route is retained unless a stored row uses the closed extension. -/
theorem of_profile (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (profile : StaticProfile compiled) : Nonempty (Certificate compiled) := by
  classical
  let chosen := fun index => Classical.choice (profile.rows index)
  by_cases regular : ∀ index, OrdinaryLane (chosen index)
  · obtain ⟨catalog⟩ := SelectedCompilationCatalog.of_compiled compiled bodies
    have supported : ∀ instantiation, DirectSite profile.table.rows instantiation →
        Supported compiled.indexed.base.plan instantiation := fun _ site =>
      site.supported (profile.table.aligned catalog)
    have completed : ∀ named ∈ compiled.indexed.base.functions,
        Nonempty (RowCertificate compiled named profile.table.rows false) ∧
        CallableIndexedOwnedPreparedScopedMethodAdmission.RowCase compiled named profile.table.rows := by
      intro named member
      obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp selected
      subst named
      have allowed := regular ⟨index, bound⟩
      generalize chosenEq : chosen ⟨index, bound⟩ = row at allowed
      cases row with
      | ordinary eligible excluded data =>
        exact ⟨ordinary_row selected eligible data supported bodies, .inl excluded⟩
      | method excluded range forms data =>
        exact ⟨⟨⟨.excluded excluded, no_lambdas data.lambdas⟩⟩,
          .inr (method_row selected checked bodies profile.table profile.catalog excluded range forms data)⟩
      | coercedFactory => cases allowed
      | closedMethod => cases allowed
    exact ⟨{
      table := profile.table
      selection := .origins ⟨fun named member => (completed named member).2⟩ profile.catalog
      rows := fun named member => (completed named member).1
      profile := profile.callable
      diagnostics := profile.diagnostics }⟩
  · obtain ⟨index, absent⟩ := Classical.not_forall.mp regular
    generalize chosenEq : chosen index = row at absent
    cases row with
    | ordinary => exact False.elim (absent True.intro)
    | method => exact False.elim (absent True.intro)
    | coercedFactory _ _ _ closed => exact of_closed bodies profile closed
    | closedMethod _ closed => exact of_closed bodies profile closed

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfileBinders
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfileBinders
open Frontend SourceInference TypeSystem CompilerProgramStaticProfile
open ExecutableBinderInterfaces

private theorem lambda_node {source : TypedSource} {initializer : ExpressionId}
    (direct : SourceSpecialization.isDirectLambdaInitializer source initializer = true) :
    ∃ node parameters result body, source.lookupExpression? initializer = some node ∧
      node.form = .lambda parameters result body := by
  unfold SourceSpecialization.isDirectLambdaInitializer at direct
  cases found : source.lookupExpression? initializer with
  | none => simp only [found, Bool.false_eq_true] at direct
  | some node =>
    cases node with
    | mk id span type actualForm requirements coercions start =>
      cases actualForm <;> simp only [found, Bool.false_eq_true] at direct
      case lambda parameters result body => exact ⟨_, parameters, result, body, rfl, rfl⟩

/-- A returned lambda occurrence cannot simultaneously initialize a local.
Both edges refer to the original complete occurrence graph. -/
theorem returned_lambda_not_initializer {source : TypedSource}
    (closed : OccurrenceGraphClosed source)
    {outer : StatementId} {outerNode node : StatementNode} {expression : ExpressionId}
    (outerFound : source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some expression))
    {binder : TypedBinder}
    (member : Node.statement node ∈ source.nodes)
    (form : node.form = .letDecl binder (some expression)) : False := by
  have returned : DirectChild source (.statement outer) (.expression expression) := by
    refine ⟨.statement outerNode, ?_, ?_⟩
    · exact ⟨(lookupStatement?_sound outerFound).1, by
        simpa only [Node.id] using congrArg NodeId.statement (lookupStatement?_sound outerFound).2⟩
    · simp only [nodeChildIds, Node.references, outerForm, StatementForm.references,
        Option.map_some, Option.toList_some, List.mem_singleton]
  have initialized : DirectChild source (.statement node.id) (.expression expression) := by
    refine ⟨.statement node, ⟨member, rfl⟩, ?_⟩
    simp only [nodeChildIds, Node.references, form, StatementForm.references,
      Option.map_some, Option.toList_some, List.mem_singleton]
  have sameId := NodeId.statement.inj (closed.childHasUniqueParent returned initialized)
  have nodeFound : source.lookupStatement? outer = some node :=
    lookupStatement?_complete closed.wellFormed.nodeOccurrencesUnique ⟨member, sameId.symm⟩
  have same := Option.some.inj (outerFound.symm.trans nodeFound)
  rw [← same, outerForm] at form
  cases form

private theorem mono_without_lambdas {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (lambdas : ∀ node ∈ specialized.function.typedBody.nodes, LambdaAllowed none node) :
    SourceMonomorphic specialized.function.typedBody := by
  intro binder member
  by_cases monomorphic : binder.scheme.quantified = []
  · exact monomorphic
  · obtain ⟨_, expression, _, _, direct⟩ :=
      SelectedCompilationSpecializationBinders.initialized_position accepted member monomorphic
    obtain ⟨node, parameters, result, body, found, form⟩ := lambda_node direct
    have allowed := lambdas (.expression node) (lookupExpression?_sound found).1
    simp only [LambdaAllowed, form] at allowed
    cases allowed

private theorem mono_returned_lambda {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (closed : OccurrenceGraphClosed specialized.function.typedBody)
    {outer : StatementId} {outerNode : StatementNode} {expression : ExpressionId} {allowedNode : ExpressionNode}
    (outerFound : specialized.function.typedBody.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some expression))
    (found : specialized.function.typedBody.lookupExpression? expression = some allowedNode)
    (lambdas : ∀ node ∈ specialized.function.typedBody.nodes, LambdaAllowed (some allowedNode) node) :
    SourceMonomorphic specialized.function.typedBody := by
  intro binder member
  by_cases monomorphic : binder.scheme.quantified = []
  · exact monomorphic
  · obtain ⟨statement, initializer, present, statementForm, direct⟩ :=
      SelectedCompilationSpecializationBinders.initialized_position accepted member monomorphic
    obtain ⟨node, parameters, result, body, initializerFound, form⟩ := lambda_node direct
    have allowed := lambdas (.expression node) (lookupExpression?_sound initializerFound).1
    simp only [LambdaAllowed, form, Option.some.injEq] at allowed
    subst node
    have sameId : initializer = expression :=
      (lookupExpression?_sound initializerFound).2.symm.trans (lookupExpression?_sound found).2
    subst initializer
    exact False.elim (returned_lambda_not_initializer closed outerFound outerForm present statementForm)

private theorem item_binders_apply (substitution : ParameterSubstitution) (item : ForItemForm) :
    (SourceSpecialization.applyForItemForm substitution item).initializedLetBinders =
      item.initializedLetBinders.map (SourceSpecialization.applyBinder substitution) := by
  cases item <;> try rfl
  case letDecl binder initializer => cases initializer <;> rfl

private theorem statement_binders_apply (substitution : ParameterSubstitution) (form : StatementForm) :
    (SourceSpecialization.applyStatementForm substitution form).initializedLetBinders =
      form.initializedLetBinders.map (SourceSpecialization.applyBinder substitution) := by
  cases form <;> try rfl
  case letDecl binder initializer => cases initializer <;> rfl
  case forLoop initializer condition post body =>
    simp only [SourceSpecialization.applyStatementForm, StatementForm.initializedLetBinders,
      List.flatMap_map, List.map_append, List.map_flatMap, item_binders_apply]

private theorem node_binders_apply (substitution : ParameterSubstitution) (node : Node) :
    (SourceSpecialization.applyNode substitution node).initializedLetBinders =
      node.initializedLetBinders.map (SourceSpecialization.applyBinder substitution) := by
  cases node with
  | expression _ => rfl
  | statement statement => exact statement_binders_apply substitution statement.form

/-- Rigid specialization preserves the entire initialized-binder inventory,
including loop headers and statements after returns. -/
theorem initializedLetBinders_applyParameters (substitution : ParameterSubstitution) (source : TypedSource) :
    (SourceSpecialization.applyTypedSource substitution source).initializedLetBinders =
      source.initializedLetBinders.map (SourceSpecialization.applyBinder substitution) := by
  simp only [SourceSpecialization.applyTypedSource, TypedSource.initializedLetBinders,
    List.flatMap_map, List.map_flatMap, node_binders_apply]

theorem monomorphic_beforeParameters {source : TypedSource} {substitution : ParameterSubstitution}
    (monomorphic : SourceMonomorphic (SourceSpecialization.applyTypedSource substitution source)) :
    SourceMonomorphic source := by
  intro binder member
  apply monomorphic (SourceSpecialization.applyBinder substitution binder)
  rw [initializedLetBinders_applyParameters]
  exact List.mem_map.mpr ⟨binder, member, rfl⟩

/-- Every existing profile lane excludes a polymorphic initializer throughout
the original table. Factories use occurrence uniqueness, not a tail scan. -/
theorem of_row {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {rows : List SourceSpecialization.SpecializedFunction}
    (profile : Row compiled named rows)
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (closed : OccurrenceGraphClosed generic.typedBody) : SourceMonomorphic generic.typedBody := by
  have sourceEq := congrArg CheckedFunction.typedBody
    (CallableCoercionBodyProvenance.specialization_fields accepted).1
  have specializedClosed : OccurrenceGraphClosed named.specialized.function.typedBody := by
    rw [sourceEq]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters named.specialized.parameterSubstitution closed
  have monomorphic : SourceMonomorphic named.specialized.function.typedBody := by
    cases profile with
    | method _ _ _ profile => exact mono_without_lambdas accepted profile.lambdas
    | closedMethod profile _ => exact mono_without_lambdas accepted (primitive_lambdas profile)
    | coercedFactory _ _ profile _ =>
      exact mono_returned_lambda accepted specializedClosed
        profile.outerFound profile.outerForm profile.found profile.lambdas
    | ordinary _ _ profile =>
      cases profile with
      | «scoped» profile => exact mono_without_lambdas accepted profile.lambdas
      | factory profile =>
        exact mono_returned_lambda accepted specializedClosed
          profile.outerFound profile.outerForm profile.found profile.lambdas
      | scopedFactory profile =>
        exact mono_returned_lambda accepted specializedClosed
          profile.outerFound profile.outerForm profile.found profile.lambdas
  rw [sourceEq] at monomorphic
  exact monomorphic_beforeParameters monomorphic

/-- The exact final cache position selects its stored profile. The output
concerns the complete original checker carrier, not just the emitted body. -/
theorem of_profile {compiled : SourceCoreUnifiedCompilation.Compiled}
    (profile : StaticProfile compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (closed : OccurrenceGraphClosed generic.typedBody) : SourceMonomorphic generic.typedBody := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp selected
  have actual := profile.rows ⟨index, bound⟩
  rw [same] at actual
  obtain ⟨row⟩ := actual
  exact of_row row accepted closed

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfileBinders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationSelectedBodyInterfaces
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationSelectedBodyInterfaces
open Frontend SourceInference TypeSystem
open ExecutableCoercionInterfaces ExecutableBinderInterfaces
open SelectedCompilationBodyTyping CompilerProgramStaticProfile

private theorem original_interfaces {compiled : SourceCoreUnifiedCompilation.Compiled}
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized) :
    BodyInterfaces compiled.sourceProgram.signatures generic := by
  apply SelectedCompilationCoercionInterfaces.of_applied (substitution := named.specialized.parameterSubstitution)
  rw [← (CallableCoercionBodyProvenance.specialization_fields accepted).1]
  exact SelectedCompilationCoercionInterfaces.cached compiled selected

/-- The actual selected ordinary definition receives both executable
interfaces and source-wide monomorphism from existing checker/compiler facts. -/
theorem ordinary {compiled : SourceCoreUnifiedCompilation.Compiled}
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : Frontend.checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (profile : StaticProfile compiled) {generic : CheckedFunction}
    (selected : OrdinarySource compiled generic) :
    BodyInterfaces compiled.sourceProgram.signatures generic ∧ SourceMonomorphic generic.typedBody := by
  obtain ⟨index, named, signature, supplied, cached, _, member, accepted⟩ := selected
  obtain ⟨_, _, bodyChecked⟩ := Frontend.checkProgram_success_function_body checked member
  exact ⟨original_interfaces cached accepted,
    SelectedCompilationProfileBinders.of_profile profile cached accepted
      (SourceInferenceSoundness.checkFunctionBody_success_occurrenceGraphClosed bodyChecked)⟩

/-- Methods retain their genuine selected method identity and complete
original checker carrier. No ordinary-origin or whole-program typing fact is used. -/
theorem method {compiled : SourceCoreUnifiedCompilation.Compiled}
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : Frontend.checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (profile : StaticProfile compiled) {retained : CheckedImplementationMethod}
    (selected : MethodSource compiled retained) :
    BodyInterfaces compiled.sourceProgram.signatures retained.checked ∧
      SourceMonomorphic retained.checked.typedBody := by
  obtain ⟨index, named, method, cached, same, selection, member, _, identical⟩ := selected
  have accepted : SourceSpecialization.specializeFunction
      (selection.implementation.functionSignatureOfMethodWithTrait selection.trait selection.declaration)
      retained.checked selection.supplied = .ok named.specialized := by
    simpa only [identical, same] using selection.specialized
  obtain ⟨_, _, _, _, _, _, _, bodyChecked⟩ := Frontend.checkProgram_success_method_body checked member
  exact ⟨original_interfaces cached accepted,
    SelectedCompilationProfileBinders.of_profile profile cached accepted
      (SourceInferenceSoundness.checkFunctionBody_success_occurrenceGraphClosed bodyChecked)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationSelectedBodyInterfaces
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedBodyTyping
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedBodyTyping
open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

/-- Only the selected original function uses the recursive source theorem.
Its header and original body-checking receipt come from the public checker. -/
theorem ordinary_valid
    {raw : Workspace.RawWorkspace} {fuel : Nat} {program : CheckedProgram}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {function : CheckedFunction} (member : function ∈ program.functions)
    (interfaces : ExecutableCoercionInterfaces.BodyInterfaces program.signatures function)
    (monomorphic : ExecutableBinderInterfaces.SourceMonomorphic function.typedBody)
    (recursiveSound : ActualInferStatementsFuelSoundness fuel) :
    FunctionDefinition.Valid program.signatures (FunctionDefinition.ofChecked function) := by
  apply functionDefinitionValid_ofCheckProgram checked member
  intro signature signatureMember bodySuccess
  obtain ⟨headerSignature, headerMember, header⟩ :=
    checkedFunctionHeaderWellFormed_ofCheckProgram checked member
  have signatureEq : headerSignature = signature := by
    have catalog := SignatureCatalogWellFormed.ofCheckProgram checked
    exact eq_of_mem_of_nodup_map catalog.function_ids headerMember signatureMember
      (header.declaration_eq.symm.trans (checkFunctionBody_success_declaration bodySuccess))
  subst headerSignature
  have predicatesFixed : signature.scheme.predicates.map
      (TypedTraitResolution.applySubstitution function.substitution) = signature.scheme.predicates :=
    ((Frontend.checkProgram_success_signature_formation checked).functions
      signature signatureMember).2.2.apply_eq_self function.substitution
  apply checkedBodyHasType_ofStatements bodySuccess
  exact SelectedCheckedBodyTypingBridge.checkedBodyStatementsHaveType_ofCheckProgram_function
    checked signatureMember header predicatesFixed bodySuccess interfaces monomorphic recursiveSound

/-- The selected method retains its actual implementation, trait signature
and original checker carrier throughout body typing. -/
theorem method_valid
    {raw : Workspace.RawWorkspace} {fuel : Nat} {program : CheckedProgram}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {retained : CheckedImplementationMethod} (member : retained ∈ program.methods)
    (interfaces : ExecutableCoercionInterfaces.BodyInterfaces program.signatures retained.checked)
    (monomorphic : ExecutableBinderInterfaces.SourceMonomorphic retained.checked.typedBody)
    (recursiveSound : ActualInferStatementsFuelSoundness fuel) :
    MethodDefinition.Valid program.signatures (MethodDefinition.ofChecked retained) := by
  apply methodDefinitionValid_ofCheckProgram checked member
  intro implementation method trait implementationMember methodMember traitLookup bodySuccess
  let catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have implementationWellFormed := catalog.implementations_semantic implementation implementationMember
  have methodWellFormed := implementationWellFormed.methods method methodMember
  obtain ⟨semanticTrait, traitMethod, semanticTraitMember, selectedHeadTrait,
    traitMethodMember, traitMethodId, _, _, _, _, _, _⟩ := methodWellFormed.trait_method
  have rawLookup : program.signatures.traits.find?
      (fun candidate => decide (candidate.id = method.traitMethod.trait)) = some trait := by
    simpa [ProgramSignatures.trait?] using traitLookup
  have selectedMember : trait ∈ program.signatures.traits := List.mem_of_find?_eq_some rawLookup
  have selectedId : trait.id = method.traitMethod.trait := of_decide_eq_true (List.find?_some
    (p := fun candidate : ProgramTraitSignature => decide (candidate.id = method.traitMethod.trait)) rawLookup)
  have semanticTraitWellFormed := catalog.traits_semantic semanticTrait semanticTraitMember
  have traitMethodWellFormed := semanticTraitWellFormed.methods traitMethod traitMethodMember
  have semanticId : semanticTrait.id = method.traitMethod.trait := by
    rw [← traitMethodWellFormed.owner]
    exact congrArg ProgramTraitMethodId.trait traitMethodId
  have traitEq : trait = semanticTrait := Frontend.trait_signature_eq_of_mem_of_id_eq
    catalog.trait_ids selectedMember semanticTraitMember (selectedId.trans semanticId.symm)
  subst semanticTrait
  let signature := implementation.functionSignatureOfMethodWithTrait trait method
  have header : CheckedBodyHeaderWellFormed program.signatures signature retained.checked :=
    CheckedBodyHeaderWellFormed.ofCheckImplementationMethod implementationWellFormed methodWellFormed bodySuccess
  have predicatesFixed : signature.scheme.predicates.map
      (TypedTraitResolution.applySubstitution retained.checked.substitution) = signature.scheme.predicates := by
    simpa [signature, ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
      ProgramImplementationSignature.functionSignatureOfMethod] using
      methodAssumptions_applySubstitution_eq_self catalog implementationMember methodMember
        selectedMember selectedHeadTrait retained.checked.substitution
  apply checkedBodyHasType_ofStatements bodySuccess
  exact SelectedCheckedBodyTypingBridge.checkedBodyStatementsHaveType_ofCheckProgram_method
    checked implementationMember header predicatesFixed bodySuccess interfaces monomorphic recursiveSound

/-- Actual checking, the complete selected compiler profile and recursive
inference soundness construct the body certificate for exactly the retained
compilation scope. The full original program remains unchanged. -/
theorem of_checked_profile
    {raw : Workspace.RawWorkspace} {fuel : Nat} {compiled : SourceCoreUnifiedCompilation.Compiled}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (profile : CompilerProgramStaticProfile.StaticProfile compiled)
    (recursiveSound : ActualInferStatementsFuelSoundness fuel) :
    SelectedCompilationBodyTyping.Bodies compiled := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  obtain ⟨functionIds, methodIds⟩ := Frontend.checkProgram_success_ids checked
  refine ⟨catalog, ?_, ?_, ?_, ?_⟩
  · simp only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked]
    rw [functionIds]
    exact catalog.function_ids
  · simp only [Program.ofChecked, List.map_map, Function.comp_def, MethodDefinition.ofChecked]
    rw [methodIds]
    exact catalog.implementation_method_ids
  · intro generic selected
    obtain ⟨interfaces, monomorphic⟩ :=
      SelectedCompilationSelectedBodyInterfaces.ordinary checked profile selected
    obtain ⟨index, named, signature, supplied, cached, signatureMember, member, accepted⟩ := selected
    exact ordinary_valid checked member interfaces monomorphic recursiveSound
  · intro retained selected
    obtain ⟨interfaces, monomorphic⟩ :=
      SelectedCompilationSelectedBodyInterfaces.method checked profile selected
    obtain ⟨index, named, method, cached, same, selection, member, identity, original⟩ := selected
    exact method_valid checked member interfaces monomorphic recursiveSound

/-- Successful checking and the accepted compiler profile provide typing for
all selected original bodies. Recursive checker soundness is discharged inside
this producer, using the original checking budget and complete source program. -/
theorem of_checked
    {raw : Workspace.RawWorkspace} {fuel : Nat} {compiled : SourceCoreUnifiedCompilation.Compiled}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (profile : CompilerProgramStaticProfile.StaticProfile compiled) :
    SelectedCompilationBodyTyping.Bodies compiled :=
  of_checked_profile checked profile (actualInferStatementsFuelSoundness_selected fuel)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedBodyTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedAdmission
/-! Finite original-source statement admission supplies scoped named bodies.
Independent Header typing recovers lexical contexts and loop typing through
the shared scanner. The existing physical family consumes the issued support. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedScopedAdmission (Admission)

/-- Actual Header typing and accepted body compilation close the existing
scoped static issuer. Syntax, metadata, direct support and slot callbacks are
all constructed from the certification result and inventory. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (table : TableAligned inputs directRows)
    (admission : Admission prepared header directRows)
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      SelectedCompilationPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) := by
  obtain ⟨final, facts, typed, _complete⟩ := certified.statements
  have syntaxTree := admission.body.syntax header.unique typed
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted
    aligned.accepted admission.body.shape aligned.projection
  let support := SelectedCompilationNamedPhysicalMixedScopedCollectors.of_actual_with_catalog
    prepared aligned ready diagnostic receiver bodies certified
    (fun _ site => site.supported table) admission.metadata rows
    (fun _ site _ _ target global => site.covered rows table target global)
    checked catalog methods member receipt actual syntaxTree
  let body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header := {
    row := row, prepared := prepared, instantiation := instantiation, aligned := aligned,
    layouts := aligned.layouts, compilation := .canonicalBranching receipt }
  exact ⟨body, .scoped body receipt rfl support⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedFactoryAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedFactoryAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedNamedFactoryAdmission (Certificate at_header)
/-- The terminal compiler receipt and its Point are constructed here. No
caller supplies expression syntax, metadata or a closure execution premise. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) (certificate : Certificate compiled named)
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {bodyRegistry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
    {semanticFaults : FunctionCalls.FaultRep} :
    ∃ terminal : Terminal header,
      Nonempty (SelectedCompilationPhysicalNamedFormationSupport.Support
        (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) header terminal) := by
  let source := at_header prepared aligned selected same certificate
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [aligned.policy]; rfl) source.terminal aligned.accepted
  let terminal : Terminal header := {
    row := row, prepared := prepared, instantiation := instantiation, aligned := aligned,
    layouts := aligned.layouts, expression := source.expression, receipt := receipt,
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) source.expression receipt.child,
    certifies := by
      intro child generated
      have childEq : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, childEq⟩ }
  exact ⟨terminal, SelectedCompilationPhysicalNamedFormationCollectors.of_actual terminal
    ready diagnostic certified profile member source.found source.form source.owner
    source.requirements source.coercions source.ordinary source.read source.returnFound
    source.returnForm source.returnType rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedFactoryAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactoryAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactoryAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open SelectedCompilationScopedFactorySourceCertificate (Certificate at_header)
/-- The terminal compiler receipt and its Point are constructed here. No
caller supplies expression syntax, metadata or a closure execution premise. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) (certificate : Certificate compiled named)
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {bodyRegistry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
    {semanticFaults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → semanticFaults reason token) :
    ∃ terminal : Terminal header,
      Nonempty (SelectedCompilationPhysicalNamedFormationSupport.Support
        (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) header terminal) := by
  let source := at_header prepared aligned selected same certificate
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [aligned.policy]; rfl) source.terminal aligned.accepted
  let terminal : Terminal header := {
    row := row, prepared := prepared, instantiation := instantiation, aligned := aligned,
    layouts := aligned.layouts, expression := source.expression, receipt := receipt,
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) source.expression receipt.child,
    certifies := by
      intro child generated
      have childEq : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, childEq⟩ }
  exact ⟨terminal, SelectedCompilationPhysicalNamedFormationCollectors.of_prepared_branching terminal
    ready diagnostic receiver included certified catalog profile member source.found source.form source.owner
    source.requirements source.coercions source.ordinary source.read source.scan.shape
    (fun typed => source.scan.syntax header.unique rfl typed) rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactoryAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramNamedSupport
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramNamedSupport
open Core Frontend SourceInference
open SelectedCompilationPreparedProgramCertificates (Certificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open SelectedCompilationPhysicalProgramSupport (stagePrepared stages)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {recipe : SourceCoreIndexedSession.Recipe} (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (identity : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed initial.entry
    initial.result.context.registry initial.result.extension initial.result.diagnostics)
  (registry : initial.result.context.registry = compiled.compatible.checked.staticRegistry)
  {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (entryMember : entry ∈ compiled.indexed.entries)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  (aligned : TableAligned inputs certificate.table.rows)

include certificate bodies ready checked identity issued entryMember rows aligned in
theorem named_support (input : Input compiled) (packet : Issued input) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body packet.header,
      SelectedCompilationPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := initial.result.context.registry)
        (stages := stages compiled)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
        packet.header body) := by
  obtain ⟨source⟩ := certificate.rows input.prepared.named (List.mem_of_getElem? input.prepared.selected)
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨packet.selected.diagnostics, packet.selected.found, rfl⟩
  have certified : SelectedCompilationNamedSourceTyping.Certified packet.header :=
    SelectedCompilationHeaders.certificate_at prepared bodies input.range packet.aligned
  cases source.root with
  | «scoped» admission =>
    have original := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.source_at_header
      prepared packet.aligned input.prepared.selected input.prepared.same admission
    exact SelectedCompilationNamedScopedAdmission.of_actual prepared packet.aligned rows aligned
      original ready diagnostic issued bodies certified checked identity
      certificate.selection.operatorCatalog
      entryMember (stagePrepared compiled)
  | formation admission =>
    obtain ⟨terminal, ⟨supported⟩⟩ := SelectedCompilationNamedFactoryAdmission.of_actual
      prepared packet.aligned input.prepared.selected input.prepared.same admission ready diagnostic
      certified certificate.profile entryMember
    exact ⟨⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal terminal,
      .formation terminal supported packet.aligned.globals⟩⟩
  | scopedFactory admission =>
    obtain ⟨terminal, ⟨supported⟩⟩ := SelectedCompilationScopedFactoryAdmission.of_actual
      prepared packet.aligned input.prepared.selected input.prepared.same admission ready diagnostic
      certified bodies.signatures certificate.profile entryMember issued (fun _ _ represented => represented)
    exact ⟨⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal terminal,
      .formation terminal supported packet.aligned.globals⟩⟩
  | excluded absent =>
    obtain ⟨request, signature, generic, member, _genericMember, _resolved, specialized⟩ := input.prepared.origin
    have fields := RecursiveNamedSpecializationBodyFacts.identities specialized
    have declaration : input.prepared.named.specialized.declaration = signature.id :=
      (congrArg (·.declaration) input.prepared.same).trans (fields.2.2.trans fields.1.symm)
    exact False.elim (absent signature member declaration)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramNamedSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosureAdmission
/-! Finite original-source lambda checks cover ordinary terminal roots and the
existing constrained coerced terminal roots. Catalog capability controls the
coerced branch; original bodies and metadata are retained in both branches. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedClosureAdmission (OrdinaryBodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)

include stagePrepared code support provenance receiver bodies rows aligned checked catalog methods in
theorem of_ordinary
    (certificate : OrdinaryBodyCertificate compiled support.caller.named directRows function.body) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨caller⟩ := provenance.body_caller_receipt
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies caller
  have supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation := by
    intro instantiation site
    rw [support.compilation]
    exact site.supported aligned
  have covered : ∀ instantiation, DirectSite directRows instantiation → ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro instantiation site index signature target global
    rw [support.compilation] at target global
    exact site.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact SelectedCompilationOrdinaryMethodTerminalSupport.of_actual_with_catalog
    stagePrepared code support provenance receiver bodies certified supported
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows covered checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    certificate.expression
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.terminal)
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.tree)
    _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedClosureAdmission
/-! Compiler-derived scoped body certificates use the existing branching closure
collector at the original Source frame and exact current parameter context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedScopedClosureAdmission (SourceBodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)

include stagePrepared code support provenance receiver bodies rows aligned checked catalog methods in
theorem of_actual
    (certificate : SourceBodyCertificate compiled support.caller.named directRows function.body) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody (headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨caller⟩ := provenance.body_caller_receipt
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies caller
  have supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation := by
    intro instantiation site
    rw [support.compilation]
    exact site.supported aligned
  have covered : ∀ instantiation, DirectSite directRows instantiation → ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro instantiation site index signature target global
    rw [support.compilation] at target global
    exact site.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  obtain ⟨finalContext, facts, typed, completed⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.body.frame support.body.extended
  have scan : ScopedSourceBodyAdmission.Scan function.source
      (fun id => GeneralSyntax function.source id (DirectSite directRows)) certificate.result true function.body := by
    simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.scan
  have result : function.resultType = certificate.result :=
    scan.result_eq_of_completes support.body.unique typed completed
  have syntaxTree := scan.syntax support.body.unique result typed
  rw [← result] at syntaxTree
  exact SelectedCompilationOrdinaryMethodScopedSupport.of_actual_with_catalog
    stagePrepared code support provenance receiver bodies certified supported
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows covered checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    scan.shape syntaxTree
    _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercedClosureAdmission
/-! Finite checks retain each original lambda body and its constrained direct
call. The original coercion rows and captured Source remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedCoercedClosureAdmission (BodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)

include stagePrepared code support provenance receiver bodies rows aligned checked catalog methods in
theorem of_actual
    (certificate : BodyCertificate compiled support.caller.named directRows function.body)
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
        (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
      (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
      (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
      ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
        packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
          principal packet (headers rows) (RecursiveNamedPreparedStageScopes.registry stagePrepared)
          (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨caller⟩ := provenance.body_caller_receipt
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies caller
  have supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
      code.compilation.plan certificate.instantiation := by
    rw [support.compilation]
    exact certificate.direct.supported aligned
  have covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan certificate.instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro index signature target global
    rw [support.compilation] at target global
    exact certificate.direct.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact SelectedCompilationOrdinaryCoercedTerminalSupport.of_actual
    stagePrepared code support provenance receiver bodies certified
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    methodBodies certificate.expression
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.terminal)
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.found)
    certificate.form certificate.coercions certificate.requirements
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.children)
    certificate.initializer supported covered _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercedClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramClosureSupport
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramClosureSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedProgramAdmission (Selection)
open SelectedCompilationPreparedProgramCertificates (Certificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedPreparedPhysicalProgramSupport (stagePrepared stages)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (identity : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed initial.entry
    initial.result.context.registry initial.result.extension initial.result.diagnostics)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  (aligned : TableAligned inputs certificate.table.rows)

include certificate bodies checked identity issued rows aligned in
theorem of_certificate
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association (headers rows) (keys compiled)
      initial.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result) :
    Nonempty (Σ packet : SelectedCompilationPhysicalClosureStaticSupport.PacketFor
        association (stages compiled),
      SelectedCompilationPhysicalClosureStaticSupport.SupportFor association
        (stages compiled) packet) := by
  cases association with
  | legacy original =>
    rcases original with ⟨original, _slots⟩
    cases original with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      obtain ⟨source⟩ := certificate.rows support.caller.named (List.mem_of_getElem? support.caller.selected)
      have found := code.sourceFound
      rw [support.source] at found
      obtain ⟨body⟩ := source.closures.selected found code.sourceForm
      cases body with
      | ordinary body =>
        obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationClosureAdmission.of_ordinary
          (stagePrepared compiled) code support provenance issued bodies rows aligned checked identity
          certificate.selection.operatorCatalog body
        exact ⟨⟨.terminal packet, supported⟩⟩
      | «scoped» body =>
        obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationScopedClosureAdmission.of_actual
          (stagePrepared compiled) code support provenance issued bodies rows aligned checked identity
          certificate.selection.operatorCatalog body
        exact ⟨⟨.branching packet, supported⟩⟩
      | coerced enabled body =>
        cases selectionEq : certificate.selection with
        | closed methods catalog =>
          obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationCoercedClosureAdmission.of_actual
            (stagePrepared compiled) code support provenance issued bodies rows aligned checked identity
            catalog body
            (fun principal sourceAt diagnostic certified =>
              SelectedCompilationPrimitiveMethodAdmission.support methods principal sourceAt diagnostic issued
                bodies.signatures certified (headers := headers rows) (stages compiled))
          exact ⟨⟨.terminal packet, supported⟩⟩
        | origins methods catalog =>
          simp only [selectionEq, Selection.allowCoerced, Bool.false_eq_true] at enabled
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      have found := code.sourceFound
      rw [support.source, support.principal.source_eq] at found
      cases certificate.selection with
      | closed methods _ => exact False.elim (methods.no_lambda support.principal found code.sourceForm)
      | origins methods _ => exact False.elim (methods.no_lambda support.principal found code.sourceForm)
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex typed provenance slots callerReceipt =>
    obtain ⟨caller⟩ := callerReceipt
    obtain ⟨source⟩ := certificate.rows support.caller.named (List.mem_of_getElem? support.caller.selected)
    have found := code.sourceFound
    rw [support.source] at found
    obtain ⟨body⟩ := source.closures.selected found code.sourceForm
    cases body with
    | ordinary body =>
      obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedClosureAdmission.of_ordinary
        (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.terminal packet, supported⟩⟩
    | «scoped» body =>
      obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedScopedClosureAdmission.of_actual
        (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.branching packet, supported⟩⟩
    | coerced enabled body =>
      cases selectionEq : certificate.selection with
      | closed methods catalog =>
        obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedCoercedClosureAdmission.of_actual
          (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
          catalog body
          (fun principal sourceAt diagnostic certified =>
            SelectedCompilationPrimitiveMethodAdmission.support methods principal sourceAt diagnostic issued
              bodies.signatures certified (headers := headers rows) (stages compiled))
        exact ⟨⟨.terminal packet, supported⟩⟩
      | origins methods catalog =>
        simp only [selectionEq, Selection.allowCoerced, Bool.false_eq_true] at enabled
  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex typed provenance slots callerReceipt =>
    obtain ⟨caller⟩ := callerReceipt
    obtain ⟨source⟩ := certificate.rows support.caller.named (List.mem_of_getElem? support.caller.selected)
    have found := code.sourceFound
    rw [support.source] at found
    obtain ⟨body⟩ := source.closures.selected found code.sourceForm
    cases body with
    | ordinary body =>
      obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedBranchingClosureAdmission.of_ordinary
        (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.terminal packet, supported⟩⟩
    | «scoped» body =>
      obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedBranchingScopedClosureAdmission.of_actual
        (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.branching packet, supported⟩⟩
    | coerced enabled body =>
      cases selectionEq : certificate.selection with
      | closed methods catalog =>
        obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedBranchingCoercedClosureAdmission.of_actual
          (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
          catalog body
          (fun principal sourceAt diagnostic certified =>
            SelectedCompilationPrimitiveMethodAdmission.support methods principal sourceAt diagnostic issued
              bodies.signatures certified (headers := headers rows) (stages compiled))
        exact ⟨⟨.terminal packet, supported⟩⟩
      | origins methods catalog =>
        simp only [selectionEq, Selection.allowCoerced, Bool.false_eq_true] at enabled
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramClosureSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramSupportIssuer
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramSupportIssuer
open Core Frontend SourceInference
open SelectedCompilationPreparedProgramCertificates (Certificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPhysicalProgramSupport (stagePrepared stages Support)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  {recipe : SourceCoreIndexedSession.Recipe} (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (identity : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed initial.entry
    initial.result.context.registry initial.result.extension initial.result.diagnostics)
  (registry : initial.result.context.registry = compiled.compatible.checked.staticRegistry)
  {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (entryMember : entry ∈ compiled.indexed.entries)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  (aligned : TableAligned inputs certificate.table.rows)

private theorem owners_physical (rows : Inventory inputs) :
    ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys compiled),
      CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

include certificate bodyTyping ready checked identity issued registry entryMember rows aligned in
/-- Finite raw-row alignment is the only inventory adapter. All three semantic
families are issued internally from the single original-source certificate. -/
theorem issue_for :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) := by
  have named : ∀ header, header ∈ headers rows →
      Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
        SelectedCompilationPhysicalNamedBodySupport.Support
          (headers := headers rows) (bodyRegistry := initial.result.context.registry)
          (stages := stages compiled)
          (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
          header body) := by
    intro header member
    obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers header member
    cases same
    exact SelectedCompilationProgramNamedSupport.named_support certificate bodyTyping ready checked identity issued entryMember rows aligned input packet
  let namedChoice := fun header member => Classical.choice (named header member)
  let closureChoice := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association (headers rows) (keys compiled)
      initial.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result) =>
    Classical.choice (SelectedCompilationProgramClosureSupport.of_certificate certificate bodyTyping checked identity issued rows aligned association)
  refine ⟨{
    profile := certificate.profile
    bodyTyping := bodyTyping
    certificates := SelectedCompilationCatalog.certificates bodyTyping rows
    issued := issued
    registry := registry
    diagnostics := certificate.diagnostics
    bodies := fun header member => (namedChoice header member).1
    bodySupport := fun header member => (namedChoice header member).2
    closurePackets := fun association => (closureChoice association).1
    closureSupport := fun association => (closureChoice association).2
    owners := owners_physical rows
    methods := ?_ }⟩
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port selection
  have certified := SelectedCompilationMethodBodySupport.Certified.of_typed port.principal port.sourceAt selection
  cases certificate.selection with
  | closed methods _ =>
    obtain ⟨packet, same, supported⟩ := SelectedCompilationPrimitiveMethodAdmission.support methods port.principal port.sourceAt
      ⟨port.diagnostics⟩ issued bodyTyping.signatures certified (headers := headers rows) (stages compiled)
    exact ⟨.terminal packet, same, supported⟩
  | origins methods _ =>
    exact SelectedCompilationScopedMethodAdmission.support methods port.principal port.sourceAt port.resolved ⟨port.diagnostics⟩ issued bodyTyping certified
      rows aligned ready entryMember (stages compiled)

include certificate bodyTyping ready issued registry entryMember rows aligned in
/-- The original public checker receipt retains its actual checking budget.
The separate static method receipt matches the compiler's method recheck. -/
theorem issue_for_checked_with_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (methods : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) := by
  exact issue_for certificate bodyTyping ready methods
    (CallableCoercionSelectionIdentity.Catalog.of_checked accepted) issued registry entryMember rows aligned

include certificate bodyTyping ready issued registry entryMember in
/-- The automatic catalog issuer also retains the actual whole-program budget. -/
theorem issue_with_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (methods : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) := by
  obtain ⟨catalog⟩ := SelectedCompilationCatalog.of_compiled compiled bodyTyping
  exact ⟨catalog, issue_for_checked_with_methods certificate bodyTyping ready issued registry entryMember
    catalog.rows (certificate.table.aligned catalog) methods accepted⟩

include certificate bodyTyping ready issued registry entryMember rows aligned in
/-- An empty retained method catalog needs no additional body check. The actual
original checker receipt establishes that every method target is absent. -/
theorem issue_for_without_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (empty : compiled.sourceProgram.methods = []) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) :=
  issue_for_checked_with_methods certificate bodyTyping ready issued registry entryMember rows aligned
    (CallableMethodBodyCoherence.of_empty_checked accepted empty) accepted

include certificate bodyTyping ready issued registry entryMember in
theorem issue_without_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (empty : compiled.sourceProgram.methods = []) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) :=
  issue_with_methods certificate bodyTyping ready issued registry entryMember
    (CallableMethodBodyCoherence.of_empty_checked accepted empty) accepted

include certificate bodyTyping ready issued registry entryMember rows aligned in
/-- Original checker success supplies the method receipt at its actual budget. -/
theorem issue_for_checked {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) :=
  issue_for_checked_with_methods certificate bodyTyping ready issued registry entryMember rows aligned
    (CallableMethodBodyCoherence.of_checked accepted) accepted

include certificate bodyTyping ready issued registry entryMember in
/-- Automatic catalog construction also accepts the actual original checking budget. -/
theorem issue {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) :=
  issue_with_methods certificate bodyTyping ready issued registry entryMember
    (CallableMethodBodyCoherence.of_checked accepted) accepted

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramSupportIssuer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderParameterProjections
/-! Actual named preparation and independent source signature typing determine
both ordered parameter vectors. Packed equality is proved from raw source shape
and real projection, then used only after source binder identity fixes arity.
Invocation evidence and exact source/native catalog identity remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderParameterProjections
open Core Frontend SourceInference RecursiveNamedCatalog

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- Only the outer function preparation is inverted. Its input fold is consumed
as the actual success witness and does not need to be exposed again. -/
theorem prepared_parameter {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    {parameter result : TypeSystem.Ty}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (shape : specialized.function.type = .function parameter result) :
    representation.expressions.projectType (.declaration specialized.key.declaration) parameter =
      .ok named.signature.parameterType := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (specialized.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged, shape, pure, Except.pure, bind, Except.bind] at accepted
    by_cases mismatch : result ≠ specialized.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨parameterType, projected, accepted⟩ := bind_ok accepted
      obtain ⟨resultType, _, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact mapError_ok projected

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : SourceSemantics.Program}

theorem header_type (header : Header compiled.indexed.ancestry values definitions program)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    header.instantiation.type = .function
      (TypeSystem.Ty.productMany (header.bindings.map (fun binding => binding.1.scheme.body)))
      header.function.resultType := by
  obtain ⟨_, certificate⟩ := certified
  have types : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  rw [types, header.frame.result]
  exact certificate.callable_type

private theorem project_productMany {catalog : SourceCoreCompatibleCatalog.Catalog}
    {types : List TypeSystem.Ty} {native : List Core.Ty}
    (projected : types.mapM catalog.project = .ok native) :
    catalog.project (TypeSystem.Ty.productMany types) = .ok (SourceCoreCompatibleCatalog.packTypes native) := by
  induction types generalizing native with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
    subst native
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at projected
    obtain ⟨first, projectedHead, projected⟩ := bind_ok projected
    obtain ⟨rest, projectedTail, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projectedTail
      subst rest
      exact projectedHead
    | cons next suffix =>
      have remaining := ih projectedTail
      rw [List.mapM_cons] at projectedTail
      obtain ⟨nextNative, _, projectedTail⟩ := bind_ok projectedTail
      obtain ⟨suffixNative, _, projectedTail⟩ := bind_ok projectedTail
      cases projectedTail
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [projectedHead, remaining]
      rfl

/-- The real prepared parameter projection agrees with the complete ordered
input vector, using independent source shape for the packed parameter type. -/
theorem parameter_pack (header : Header compiled.indexed.ancestry values definitions program)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    header.named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd) := by
  have binders := header.parameters.symm.trans header.agreement.parameters
  have raw : header.bindings.map (fun binding => binding.1.scheme.body) =
      header.named.inputs.map (fun binding => binding.1.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) binders
  have shape := matched.type.trans (header_type header certified)
  rw [raw] at shape
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled header.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have sourceShape := same ▸ shape
  have projected := prepared_parameter accepted sourceShape
  have realProjected := CompatibleExpressionReads.projectType_of_accepted projected
  have vector := project_productMany (RecursiveNamedPreparedParameterProjections.cached_projected compiled header.selected)
  exact Except.ok.inj (realProjected.symm.trans vector)

/-- The Header's native projection callback is now supplied by actual compiler
receipts; the source and compiler catalogs must still be the same catalog. -/
theorem projections (header : Header compiled.indexed.ancestry values definitions program)
    (sameChecked : values.checked = compiled.compatible.checked)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := by
  apply RecursiveNamedParameterPackingFacts.header_projections header (parameter_pack header certified matched)
  rw [sameChecked]
  exact RecursiveNamedPreparedParameterProjections.cached_projected compiled header.selected

/-- Complete exact plan selection supplies the metadata match without a
separate Matches assumption. A key alone is deliberately insufficient. -/
theorem projections_of_record (header : Header compiled.indexed.ancestry values definitions program)
    (sameChecked : values.checked = compiled.compatible.checked)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan header.named.signature.key =
      .ok header.named.specialized) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) :=
  projections header sameChecked certified (CallableNamedMetadata.matches_of_exact header.target record)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderParameterProjections
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryMethodCertificates
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryMethodCertificates
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

/-- The existing flat profile retains the complete raw replacement range at
all actual cache positions, including method rows. -/
def Ranges (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop :=
  ∀ (index : Nat) (named : SourceCoreGeneralFunctions.Function), compiled.indexed.base.functions[index]? = some named →
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) named.specialized.parameterSubstitution

theorem ranges_of_profile {compiled : SourceCoreUnifiedCompilation.Compiled}
    (profile : CompilerProgramStaticProfile.StaticProfile compiled) : Ranges compiled := by
  intro index named selected
  have bound : index < compiled.indexed.base.functions.length := by
    exact List.getElem?_eq_some_iff.mp selected |>.1
  obtain ⟨row⟩ := profile.rows ⟨index, bound⟩
  have same : compiled.indexed.base.functions[index] = named := by
    exact List.getElem?_eq_some_iff.mp selected |>.2
  rw [same] at row
  cases row with
  | ordinary eligible _ _ => exact eligible.range
  | method _ range _ _ => exact range
  | coercedFactory eligible _ _ _ => exact eligible.range
  | closedMethod profile _ => exact profile.range

/-- A final method origin supplies its complete original checker body. Its
retained raw range permits the same structural instance certificate used by
actual invocation, with no requirement that a body view determine a method ID. -/
theorem of_origin {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (ranges : Ranges compiled)
    {method : ExecutableImplMethods.CheckedMethod}
    (origin : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (member : method.specialized ∈ compiled.indexed.base.plan.specializations) :
    ∃ types lexical facts, BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method)
      types lexical facts := by
  obtain ⟨cached⟩ := CallablePreparedMethodSelection.cached_row compiled member
  have range := ranges cached.index cached.named cached.selected
  rw [cached.same] at range
  obtain ⟨retained, retainedMember, retainedId, complete⟩ :=
    origin.retained (CallableMethodBodyCoherence.of_checked checked)
  let receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method :=
    ⟨origin, retained, retainedMember, retainedId, complete⟩
  have valid := bodies.methods retained
    ⟨cached.index, cached.named, method, cached.selected, cached.same,
      origin, retainedMember, retainedId, complete⟩
  have owner : retained.checked.declaration = origin.implementation.id := by
    rw [← complete]
    exact checkFunctionBody_success_declaration origin.bodyChecked
  have traitMember : origin.trait ∈ compiled.sourceProgram.signatures.traits :=
    List.mem_of_find?_eq_some origin.traitLookup
  have traitOwner : origin.declaration.traitMethod.trait = origin.trait.id := by
    have found := origin.traitLookup
    unfold ProgramSignatures.trait? at found
    have same : decide (origin.trait.id = origin.declaration.traitMethod.trait) = true :=
      List.find?_some (p := fun trait : ProgramTraitSignature =>
        decide (trait.id = origin.declaration.traitMethod.trait)) found
    exact (of_decide_eq_true same).symm
  have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
      method.specialized.parameterSubstitution origin.implementation.parameters := by
    refine ⟨(bodies.signatures.implementations_semantic origin.implementation origin.implementationMember).parameters_nodup, ?_⟩
    rw [SourceSemantics.ParameterSubstitution.domain,
      SourceSpecialization.specializeFunction_parameterDomain origin.specialized]
    rfl
  have instantiates : TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      origin.implementation origin.declaration origin.trait (MethodDefinition.ofChecked retained)
      method.specialized.parameterSubstitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) := by
    apply TraitMethodInstantiates.intro origin.implementationMember origin.methodMember
      traitMember traitOwner (List.mem_map.mpr ⟨retained, retainedMember, rfl⟩)
      (retainedId.trans origin.methodId) owner exactSubstitution range
    · exact receipt.body
    · exact receipt.result.1
    · change declarationContext compiled.sourceProgram.signatures method.specialized.function.typedBody.owner []
        method.specialized.assumptions method.specialized.function.solvedRequirements = _
      rw [receipt.owner, receipt.assumptions, receipt.ledger]
      change declarationContext compiled.sourceProgram.signatures origin.implementation.id [] _ _ =
        declarationContext compiled.sourceProgram.signatures retained.checked.declaration [] _ _
      rw [owner]
      rfl
  obtain ⟨types, lexical, facts, certificate⟩ := instantiates.certificate_of_valid bodies.signatures valid
  exact ⟨types, lexical, facts, certificate.toBodyInstanceTypingCertificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryMethodCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryBodies
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryBodies
open Frontend SourceInference TypeSystem SourceCoreStageContracts
open Solcore.SourceSemantics.Dynamic
open SelectedCompilationRegistryMethodCertificates (Ranges)

private theorem function_impl_ne {program : CheckedProgram}
    (catalog : SignatureCatalogWellFormed program.signatures)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    {implementation : ProgramImplementationSignature}
    (implMember : implementation ∈ program.signatures.implementations) :
    signature.id ≠ implementation.id := by
  have unique := catalog.declaration_ids
  simp only [signatureDeclarationIds] at unique
  have separated := (List.nodup_append.mp (List.nodup_append.mp unique).1).2.2
  apply separated signature.id
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨signature, member, rfl⟩)))
    implementation.id (List.mem_map.mpr ⟨implementation, implMember, rfl⟩)

private theorem instantiated_owner {program : CheckedProgram} {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {implementation : ProgramImplementationSignature} {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : ParameterSubstitution} {body : BodyInstance}
    (instantiates : TraitMethodInstantiates (Program.ofChecked program)
      implementation method trait definition substitution body) :
    body.source.owner = implementation.id := by
  cases instantiates with
  | intro _ _ _ _ definitionMember _ owner _ _ sourceEq _ _ =>
    obtain ⟨retained, retainedMember, rfl⟩ := List.mem_map.mp definitionMember
    obtain ⟨_, _, _, _, _, _, _, header⟩ := checkedMethodHeaderWellFormed_ofCheckProgram checked retainedMember
    rw [sourceEq]
    exact header.source_owner.trans owner

private theorem row_owner {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok row) :
    row.function.typedBody.owner = signature.id := by
  rw [RecursiveNamedSpecializationBodyFacts.body accepted]
  exact (RecursiveNamedSpecializationBodyFacts.identities accepted).2.1.trans
    (RecursiveNamedSpecializationBodyFacts.identities accepted).1.symm

private theorem method_view_injective {left right : BodyInstance}
    {leftEvidence rightEvidence : EvidenceEnvironment} {leftRoots rightRoots : List StatementId}
    (same : Staging.Recursive.methodView left leftEvidence leftRoots =
      Staging.Recursive.methodView right rightEvidence rightRoots) : left = right := by
  have context := congrArg Dynamic.Closure.context same
  have source := congrArg Dynamic.Closure.source same
  have result := congrArg Dynamic.Closure.resultType same
  cases left
  cases right
  simp only [Staging.Recursive.methodView, Staging.Recursive.globalView] at context source result
  cases context
  cases source
  cases result
  rfl

/-- The exact final row is checked as a method origin. Other registry entry
kinds are excluded by the original owner catalog and occurrence forest. -/
theorem methods {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (ranges : Ranges compiled) :
    Staging.Recursive.SelectedPreservation.MethodBodiesTyped
      (Program.ofChecked compiled.sourceProgram) (RecursiveNamedPreparedStageScopes.registry actual) := by
  intro context evidence dictionary traitName methodName requirements body roots child method rootsEq selected
  have graph : OccurrenceGraphClosed body.source := by
    cases method with
    | intro _ _ _ _ _ _ _ _ _ _ _ instantiates _ _ =>
      exact SelectedCompilationRegistryLambdaExclusion.method_graph checked instantiates
  have owner : ∃ implementation ∈ compiled.sourceProgram.signatures.implementations,
      body.source.owner = implementation.id := by
    cases method with
    | intro _ _ implementationMember _ _ _ _ _ _ _ _ instantiates _ _ =>
      exact ⟨_, implementationMember, instantiated_owner checked instantiates⟩
  generalize viewEq : Staging.Recursive.methodView body dictionary roots = view at selected
  change RecursiveNamedPreparedStageScopes.Selected compiled native view child at selected
  cases selected with
  | @anonymous function scope receipt =>
    apply False.elim
    apply SelectedCompilationRegistryLambdaExclusion.anonymous_ne_whole_body receipt
    · simpa only [← viewEq, Staging.Recursive.methodView, Staging.Recursive.globalView] using graph
    · simpa only [← viewEq, Staging.Recursive.methodView, Staging.Recursive.globalView] using rootsEq
  | @named row prepared sidecar issued same =>
    obtain ⟨implementation, implMember, owner⟩ := owner
    obtain ⟨request, signature, generic, signatureMember, _, _, accepted⟩ := prepared.origin
    have sourceEq := congrArg (fun closure : Dynamic.Closure => closure.source.owner) viewEq
    change body.source.owner = prepared.named.specialized.function.typedBody.owner at sourceEq
    rw [prepared.same] at sourceEq
    exact False.elim (function_impl_ne bodies.signatures signatureMember implMember
      ((row_owner accepted).symm.trans (sourceEq.symm.trans owner)))
  | @method selectedMethod callerContext callerEvidence selectedDictionary selectedTrait selectedName selectedRequirements
      selectedRoots selection statements sidecar issued same =>
    have bodyEq := method_view_injective viewEq
    have member : selectedMethod.specialized ∈ compiled.indexed.base.plan.specializations := by
      rw [← same]
      exact SelectedCompilationRegistryGlobals.exact_member (LambdaSourceAlignment.sidecar_lookup issued)
    have origin := CallablePreparedFinalCatalogOrigins.of_default_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) selectedMethod.specialized member
    have certificate : ∃ types lexical facts, BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram selectedMethod) types lexical facts := by
      generalize rowEq : selectedMethod.specialized = row at origin member
      cases origin with
      | ordinary ordinary =>
        obtain ⟨implementation, implMember, owner⟩ := owner
        obtain ⟨request, signature, generic, signatureMember, _, _, accepted⟩ := ordinary
        have sameOwner : row.function.typedBody.owner = implementation.id := by
          rw [← rowEq]
          rw [bodyEq] at owner
          exact owner
        exact False.elim (function_impl_ne bodies.signatures signatureMember implMember
          ((row_owner accepted).symm.trans sameOwner))
      | method origin =>
        simpa only [CallableCoercionMethodInstantiation.bodyInstance, rowEq] using
          SelectedCompilationRegistryMethodCertificates.of_origin bodies checked ranges origin member
    exact SelectedCompilationMethodCertificateTransport.selected checked method (bodyEq.symm ▸ certificate)

/-- Actual checker success, selected original body typing and the existing
finite raw-range receipts certify the unchanged compiler registry. -/
theorem of_checked {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (ranges : Ranges compiled) :
    Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram) (RecursiveNamedPreparedStageScopes.registry actual) :=
  ⟨bodies.signatures, SelectedCompilationRegistryGlobals.globals actual bodies checked,
    methods actual bodies checked ranges⟩

theorem of_profile {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (profile : CompilerProgramStaticProfile.StaticProfile compiled) :
    Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram) (RecursiveNamedPreparedStageScopes.registry actual) :=
  of_checked actual bodies checked (SelectedCompilationRegistryMethodCertificates.ranges_of_profile profile)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryBodies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {program : Program} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {ids : List ExpressionId} {types : List TypeSystem.Ty} {values : List Dynamic.Value}

theorem values_at (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types) {size : Nat}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context
      environment before ids (.values values) after) :
    Dynamic.ValuesHaveTypes context after values types ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapTypesExtend before after := by
  have preserved := Staging.Recursive.SelectedPreservation.expressions selectedBodies
    runtime covers locals heap typing trace
  exact ⟨preserved.values_typed values rfl, preserved.heap_typed, preserved.heap_extends⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)
  {function : Dynamic.Closure} {parameter result : TypeSystem.Ty}

theorem closure_at (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types)
    (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : values.length = function.parameters.length)
    (admitted : Admission bridge context reached) {size : Nat}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context
      environment before ids (.values values) index.heap) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function index.heap values ∧
      Dynamic.ClosureFrame program function := by
  obtain ⟨argumentsTyped, _finalHeap, extension⟩ :=
    values_at selectedBodies runtime covers locals heap typing trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack values
  obtain ⟨raw, _rows⟩ :=
    CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
      bridge reached runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  obtain ⟨_parameters, _result, signatures, code, evidence, _captures⟩ := calleeTyped.closure_function_inv
  exact ⟨raw, signatures.trans runtime.signatures, code.owner, code,
    code.requirement_ledger.idsUnique, evidence⟩

end Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPackedNamedArguments
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPackedNamedArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
section SourceAdmission
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}

theorem arguments_at_global (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (certifiedAt : SelectedCompilationNamedArgumentRows.CertifiedAt (header := header) (function := source))
    {context : SourceSemantics.Context} {bodySource : TypedSource} {before : Dynamic.Heap}
    {arguments : List Dynamic.Value} {packed : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context bodySource)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (callableTyped : Dynamic.ValueHasType context before (.global source) (.function parameter result))
    (packing : Dynamic.ValuesPack arguments packed)
    (packedTyped : Dynamic.ValueHasType context before packed parameter)
    (arity : header.function.parameters.length = arguments.length) :
    Dynamic.HeapWellTyped header.function.context before ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  rcases callableTyped.global_inv with ordinary | staged
  · rcases ordinary with ⟨typeEq, _valid, _evidence⟩
    obtain ⟨facts, certified⟩ := certifiedAt
    have parameterEq := (TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)).1
    rw [parameterEq] at packedTyped
    have signatures := certified.signatures_eq.trans runtime.signatures.symm
    have bodyHeap := heapTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have bodyPacked := packedTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have length : arguments.length = header.types.length := arity.symm.trans
      ((congrArg List.length sourceAt.frame.parameters).trans certified.typing.inputs_extend.length_eq)
    have bodyArguments := packing.unpackTypes bodyPacked length
    exact ⟨sourceAt.frame.context.symm ▸ bodyHeap, sourceAt.frame.context.symm ▸ bodyArguments⟩
  · rcases staged with ⟨inner, impossible, innerTyped⟩
    cases impossible

end SourceAdmission

theorem global_count {program : Program} {function : Dynamic.GlobalFunction} {count : Nat}
    (arity : RecursivePublicCallableArity.Arity program (.global function) count)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    {body : Dynamic.BodyInstance}
    (actual : Dynamic.FunctionInstantiates program function.instantiation body) :
    body.source.inputs.length = count := by
  cases arity with
  | global instantiates =>
    cases BuiltinNamedCalls.instantiation_unique owners actual instantiates
    rfl

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPackedNamedArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLegacyProgramCertificates
/-! Existing program certificates retain their exact cache, table and source
receipts when used by selected prepared execution. The scoped factory case
forgets only the additional legacy shape restriction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
open Frontend

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {directRows : List Frontend.SourceSpecialization.SpecializedFunction}

/-- Every original root remains attached to the same cached function and rows. -/
def RootCertificate.to_prepared : RootCertificate compiled named directRows →
    SelectedCompilationPreparedProgramCertificates.RootCertificate compiled named directRows
  | .scoped source => .scoped source
  | .formation source => .formation source
  | .scopedFactory source => .scopedFactory (SelectedCompilationScopedFactorySourceCertificate.of_legacy source.toSourceCertificate)
  | .excluded absent => .excluded absent

/-- The conversion preserves the complete original table and its selection. -/
def Certificate.to_prepared (certificate : Certificate compiled) :
    SelectedCompilationPreparedProgramCertificates.Certificate compiled where
  table := certificate.table
  selection := certificate.selection
  rows := by
    intro named member
    obtain ⟨row⟩ := certificate.rows named member
    exact ⟨⟨row.root.to_prepared, row.closures⟩⟩
  profile := certificate.profile
  diagnostics := certificate.diagnostics

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
end
