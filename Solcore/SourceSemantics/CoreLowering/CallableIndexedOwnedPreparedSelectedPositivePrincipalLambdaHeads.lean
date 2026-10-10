import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedSiteShellReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedLambdaCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedNativeFamilyQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds

/-! One literal raw compiler lambda retains its actual compiler Receipt and
OccurrenceFactory at that same receipt's body read fuel. The static receipt is
manufactured by the selected issuer and same-Site shell producer below; the
finite occurrence factory remains an authentic static construction obligation.

The semantic leaf consumes that retained packet, captures from the original
caller pool and forms one positive closure under the selected family facet. The constructor
retains the exact selected issuer and bootstrap owner at the same pool.
No field contains a completed Tree, execution or body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedNativeSiteShellReceipts (FiniteBodyReceipts)
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (selected : SelectedReceipt compiled principal.named principal.cached.index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {context : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope}
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

/-- This positive constructor preserves exactly the raw compiler lambda
branch and its own native witness. Finite body receipts are Source authority,
not a result of native typing. The exact constructed Receipt and its static
occurrence factory are retained together before runtime formation. -/
inductive Lambdas (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | actual {childFuel id lowered node parameters result statements reported nativeType}
      (allowed : expressionSyntax (source principal.named) id)
      (found : (source principal.named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope
        id node parameters result statements reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope id rootReasonAt = .ok lowered)
      (sourceTyped : ExpressionHasType (source principal.named) context id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source principal.named) id node lowered.type)
      (raw : HasType (SourceCoreLocalCell.coreContext scope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
          (compiled := compiled) principal.named) lowered.expression nativeType compiled.indexed.layouts.definitions)
      (finite : FiniteBodyReceipts (source principal.named) (expressionSyntax (source principal.named))
        context parameters result statements)
      (receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := principal.dictionary))
      (sameIssuer : receipt.shell.issued =
        CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site)
      (factory : CallableIndexedOwnedPreparedNativeFamilyStaticQualification.OccurrenceFactory
        root expressionSyntax (some principal.dictionary) headers receipt.body.readFuel) :
      Lambdas children scope id lowered

/-- The same positive compiler lambda is included into the original raw
head. Only its own native witness is retained, with no used child slots. -/
theorem Lambdas.to_native_heads
    (callerEvidence : Option Dynamic.EvidenceEnvironment)
    {children : GenericExpressionMeaning.Certificate} {childScope id lowered}
    (head : Lambdas principal selected root expressionSyntax headers (context := context) (scope := scope) children childScope id lowered) :
    CallableIndexedOwnedPreparedRawCompilerHeads.Head root expressionSyntax callerEvidence headers
      (sourceContext := context) (scope := scope) children childScope id lowered ∧
      CallableIndexedOwnedPreparedNativeAssignmentChildren.RawTyped
        (SourceCoreLocalCell.coreContext childScope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
          (compiled := compiled) principal.named) lowered.expression compiled.indexed.layouts.definitions := by
  cases head with
  | actual allowed found form certificate accepted typed metadata raw finite receipt sameIssuer factory =>
      exact ⟨.lambda allowed found form certificate accepted typed metadata, ⟨_, raw⟩⟩

variable
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source principal.named))
  (covers : principal.dictionary.Covers context)
  (ownership : LocalIdentityOwnership (source principal.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source principal.named) scope context)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed principal.named).solvedRequirements)

include profile runtime covers ownership declarations sameLedger in
/-- The only shell callback is manufactured by the actual selected static
producer. It preserves the Site generated once by the original compiler. -/
theorem compiler_receipt
    {childFuel id lowered node parameters result statements reported nativeType}
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope
      id node parameters result statements reported rootReasonAt lowered)
    (found : (source principal.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (sourceTyped : ExpressionHasType (source principal.named) context id node.type)
    (coercions : node.coercions = [])
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope id rootReasonAt = .ok lowered)
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
      (compiled := compiled) principal.named) lowered.expression nativeType compiled.indexed.layouts.definitions)
    (finite : FiniteBodyReceipts (source principal.named) (expressionSyntax (source principal.named))
      context parameters result statements) :
    ∃ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := principal.dictionary),
      receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site := by
  apply CallableIndexedOwnedPreparedNativeTaggedLambdaCompilerReceipts.of_certificate_with_shell_property
    root expressionSyntax certificate
    (fun site shell => shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected site)
    profile runtime covers found form sourceTyped coercions accepted raw
  intro site identifier emitted policy body fuel view reason frame
  have sourceFound : (source principal.named).lookupExpression? id = some site.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, identifier] using site.code.sourceFound
  have sameNode := Option.some.inj (sourceFound.symm.trans found)
  have typedAt : ExpressionHasType (source principal.named) context site.code.id site.code.sourceNode.type := by
    rw [identifier, sameNode]
    exact sourceTyped
  have coercionsAt : site.code.sourceNode.coercions = [] := by
    rw [sameNode]
    exact coercions
  exact CallableIndexedOwnedPreparedNativeTaggedSiteShellReceipts.of_selected_with_issuer selected root expressionSyntax site
    policy view typedAt coercionsAt runtime covers ownership declarations sameLedger finite 0

section Semantics
variable
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {children : GenericExpressionMeaning.Certificate}

variable (owners : CallableIndexedOwnedPreparedPositiveFunctionOrigins.OwnerCover headers keys bodyRegistry profile)

local notation "nativeFacet" => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.facet (compiled := compiled) headers
local notation "bridge" => CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner principal.named
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
  (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions nativeFacet headers keys bodyRegistry faults profile)

include profile owners complete wellFormed runtime covers in
/-- Actual admitted caller capture and one original formation prove the
selected Principal lambda leaf at its unchanged canonical packet. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context principal.dictionary (source principal.named)
      (Lambdas principal selected root expressionSyntax headers (context := context) (scope := scope) children) faults size := by
  intro childScope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  cases certified with
  | @actual childFuel id lowered actualNode parameters sourceResult statements reported nativeType allowed actualFound form certificate accepted parentTyped metadata raw finite receipt sameIssuer factory =>
    let captured := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.captured
      principal.named owner complete environments agrees typed initial.1 initial.2
    have sameEmbedding : captured.embedding = ξ := rfl
    let code := RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment
    let support := (CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
      (SelectedReceipt.principal principal selected) receipt.site
      expressionSyntax (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        (CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) principal.named))
      receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment
    have qualified : (nativeFacet).principal code support :=
      CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Principal.actual
        principal selected root expressionSyntax certificate receipt sameIssuer factory environment
    have identifier : code.id = id := receipt.identifier
    have emitted : code.lowered = lowered := receipt.emitted
    have sameNode : code.sourceNode = node :=
      receipt.sourceNodeEq.trans (Option.some.inj (actualFound.symm.trans found))
    have codeTyped : ExpressionHasType (source principal.named) context code.id code.sourceNode.type := by
      rw [identifier, sameNode]
      exact sourceTyped
    have sourceType := receipt.sourceFacts.sourceType
    rw [← receipt.sourceNodeEq] at sourceType
    have ordinary := receipt.sourceFacts.ordinary
    rw [← receipt.sourceNodeEq] at ordinary
    have coercions := receipt.sourceFacts.coercions
    rw [← receipt.sourceNodeEq] at coercions
    cases trace.sound with
    | value valueTrace =>
      rename_i actualValue
      have codeTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
          context principal.dictionary (source principal.named) environment before code.id actualValue after := by
        simpa only [identifier, closure] using valueTrace
      obtain ⟨valueEq, heapEq⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions codeTrace
      subst actualValue
      subst after
      let packet := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.packet_at_capture
        principal.named owner complete environments agrees typed initial.1 initial.2
      have admittedCapture := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.admission_at_capture
        principal.named owner complete environments agrees typed initial.1 initial.2 context admitted
      obtain ⟨sourceTrace, nativeTrace, member, post, determined⟩ :=
        CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts.formation_post
          (compiled := compiled) (headers := headers) (keys := keys)
          (function := closure principal.named parameters sourceResult statements context principal.dictionary environment)
          (scope := scope) (actual := actual) (mapping := mapping) (world := world) (heap := before) (store := store)
          (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (captured := captured) (code := code) (owner := owner)
          (qualification := nativeFacet) (profile := profile)
          (models := CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions
            (compiled := compiled) nativeFacet headers keys bodyRegistry faults profile)
          (lift := fun member => .closure
            (CallableIndexedOwnedPreparedPositiveFunctionOrigins.closure_of_direct owners member))
          (support := support) (qualified := qualified)
          (prepared := CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.principal_prepared qualified)
          (initial := initial.1) (packet := packet)
          (cells := heaps) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := codeTyped) (sourceType := sourceType) (admitted := admittedCapture) ordinary coercions
      let formedValue := CallableIndexedLambdaValues.value (prepared := compiled.indexed)
        (function := closure principal.named parameters sourceResult statements context principal.dictionary environment)
        (scope := scope) (administrative := captured.administrative) code captured.embedding
        (initial.1.rows owner.position).authority.current actual
      refine ⟨.inRight .word formedValue, store, mapping, world, ?_, ?_, post.cells, .refl _, .refl _, .refl _ _, .refl _,
        initial, Relates.refl initial.1, ?_⟩
      · simpa only [emitted, sameEmbedding, formedValue,
          CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.history_at, History.native] using nativeTrace
      · simpa only [sameNode, emitted, closure, formedValue,
          CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.history_at, History.native] using post.result
      · refine ⟨post.admission.rows, ?_⟩
        intro value same
        simpa only [sameNode, closure] using post.admission.successful value same
    | fault failed =>
      rename_i actualReason
      have codeFailed : Dynamic.ExpressionFaults (Program.ofChecked compiled.sourceProgram)
          context principal.dictionary (source principal.named) environment before code.id actualReason after := by
        simpa only [identifier, closure] using failed
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions codeFailed)

include profile owners complete wellFormed runtime covers in
/-- Independent native completion uses one actual formation and its own
Source grade. The same qualified post stays in the caller's reached packet. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context principal.dictionary (source principal.named)
      (Lambdas principal selected root expressionSyntax headers (context := context) (scope := scope) children) faults size := by
  intro childScope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ result finalStore environments heaps locals agrees typed initial admitted completed
  cases certified with
  | @actual childFuel id lowered actualNode parameters sourceResult statements reported nativeType allowed actualFound form certificate accepted parentTyped metadata raw finite receipt sameIssuer factory =>
    let captured := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.captured
      principal.named owner complete environments agrees typed initial.1 initial.2
    have sameEmbedding : captured.embedding = ξ := rfl
    let code := RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment
    let support := (CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
      (SelectedReceipt.principal principal selected) receipt.site
      expressionSyntax (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        (CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) principal.named))
      receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment
    have qualified : (nativeFacet).principal code support :=
      CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Principal.actual
        principal selected root expressionSyntax certificate receipt sameIssuer factory environment
    have identifier : code.id = id := receipt.identifier
    have emitted : code.lowered = lowered := receipt.emitted
    have sameNode : code.sourceNode = node :=
      receipt.sourceNodeEq.trans (Option.some.inj (actualFound.symm.trans found))
    have codeTyped : ExpressionHasType (source principal.named) context code.id code.sourceNode.type := by
      rw [identifier, sameNode]
      exact sourceTyped
    have sourceType := receipt.sourceFacts.sourceType
    rw [← receipt.sourceNodeEq] at sourceType
    have ordinary := receipt.sourceFacts.ordinary
    rw [← receipt.sourceNodeEq] at ordinary
    have coercions := receipt.sourceFacts.coercions
    rw [← receipt.sourceNodeEq] at coercions
    let packet := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.packet_at_capture
      principal.named owner complete environments agrees typed initial.1 initial.2
    have admittedCapture := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.admission_at_capture
      principal.named owner complete environments agrees typed initial.1 initial.2 context admitted
    obtain ⟨sourceTrace, nativeTrace, member, post, determined⟩ :=
      CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts.formation_post
        (compiled := compiled) (headers := headers) (keys := keys)
        (function := closure principal.named parameters sourceResult statements context principal.dictionary environment)
        (scope := scope) (actual := actual) (mapping := mapping) (world := world) (heap := before) (store := store)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (captured := captured) (code := code) (owner := owner)
        (qualification := nativeFacet) (profile := profile)
          (models := CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions
            (compiled := compiled) nativeFacet headers keys bodyRegistry faults profile)
          (lift := fun member => .closure
            (CallableIndexedOwnedPreparedPositiveFunctionOrigins.closure_of_direct owners member))
          (support := support) (qualified := qualified)
        (prepared := CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.principal_prepared qualified)
        (initial := initial.1) (packet := packet)
        (cells := heaps) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
        (typed := codeTyped) (sourceType := sourceType) (admitted := admittedCapture) ordinary coercions
    have codeCompleted : Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore := by
      simpa only [emitted, sameEmbedding] using completed.sound
    obtain ⟨rfl, rfl⟩ := determined result finalStore codeCompleted
    obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
    refine ⟨sourceSize, .value (.closure (closure principal.named parameters sourceResult statements context principal.dictionary environment)),
      before, mapping, world, ?_, ?_, post.cells, .refl _, .refl _, .refl _ _, .refl _,
      initial, Relates.refl initial.1, ?_⟩
    · simpa only [identifier, closure] using sized
    · simpa only [sameNode, emitted] using post.result
    · refine ⟨post.admission.rows, ?_⟩
      intro value same
      simpa only [sameNode, closure] using post.admission.successful value same

end Semantics
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads
