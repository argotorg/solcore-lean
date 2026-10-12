import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedSiteShellReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedLambdaCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedNativeFamilyQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelFormationBounds
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
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads
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
  {caller : Header compiled (Program.ofChecked compiled.sourceProgram)} {index : Nat}
  (selected : SelectedReceipt compiled caller.named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope}
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

/-- This positive constructor preserves exactly the raw compiler lambda
branch and its own native witness. Finite body receipts are Source authority,
not a result of native typing. The exact constructed Receipt and its static
occurrence factory are retained together before runtime formation. -/
inductive Lambdas (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | actual {childFuel id lowered node parameters result statements reported nativeType}
      (allowed : expressionSyntax (source caller.named) id)
      (found : (source caller.named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope
        id node parameters result statements reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered)
      (sourceTyped : ExpressionHasType (source caller.named) context id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type)
      (raw : HasType (SourceCoreLocalCell.coreContext scope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
          (compiled := compiled) caller.named) lowered.expression nativeType compiled.indexed.layouts.definitions)
      (finite : FiniteBodyReceipts (source caller.named) (expressionSyntax (source caller.named))
        context parameters result statements)
      (receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := evidence))
      (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons receipt.site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
      (sameIssuer : receipt.shell.issued =
        CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site)
      (factory : CallableIndexedOwnedPreparedNativeFamilyStaticQualification.OccurrenceFactory
        root expressionSyntax (some evidence) headers receipt.body.readFuel) :
      Lambdas children scope id lowered

/-- The same positive compiler lambda is included into the original raw
head. Only its own native witness is retained, with no used child slots. -/
theorem Lambdas.to_native_heads
    (callerEvidence : Option Dynamic.EvidenceEnvironment)
    {children : GenericExpressionMeaning.Certificate} {childScope id lowered}
    (head : Lambdas selected root expressionSyntax headers (context := context) (evidence := evidence) (scope := scope) children childScope id lowered) :
    CallableIndexedOwnedPreparedRawCompilerHeads.Head root expressionSyntax callerEvidence headers
      (sourceContext := context) (scope := scope) children childScope id lowered ∧
      CallableIndexedOwnedPreparedNativeAssignmentChildren.RawTyped
        (SourceCoreLocalCell.coreContext childScope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
          (compiled := compiled) caller.named) lowered.expression compiled.indexed.layouts.definitions := by
  cases head with
  | actual allowed found form certificate accepted typed metadata raw finite receipt bodyReasons sourceDeclarations sameIssuer factory =>
      exact ⟨.lambda allowed found form certificate accepted typed metadata, ⟨_, raw⟩⟩

variable
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
  (covers : evidence.Covers context)
  (ownership : LocalIdentityOwnership (source caller.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements)

include profile runtime covers ownership declarations sameLedger in
/-- The only shell callback is manufactured by the actual selected static
producer. It preserves the Site generated once by the original compiler. -/
theorem compiler_receipt
    {childFuel id lowered node parameters result statements reported nativeType}
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope
      id node parameters result statements reported rootReasonAt lowered)
    (found : (source caller.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (sourceTyped : ExpressionHasType (source caller.named) context id node.type)
    (coercions : node.coercions = [])
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered)
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
      (compiled := compiled) caller.named) lowered.expression nativeType compiled.indexed.layouts.definitions)
    (finite : FiniteBodyReceipts (source caller.named) (expressionSyntax (source caller.named))
      context parameters result statements) :
    ∃ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := evidence),
      receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site := by
  apply CallableIndexedOwnedPreparedNativeTaggedLambdaCompilerReceipts.of_certificate_with_shell_property
    root expressionSyntax certificate
    (fun site shell => shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected site)
    profile runtime covers found form sourceTyped coercions accepted raw
  intro site identifier emitted policy body fuel view reason frame
  have sourceFound : (source caller.named).lookupExpression? id = some site.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, identifier] using site.code.sourceFound
  have sameNode := Option.some.inj (sourceFound.symm.trans found)
  have typedAt : ExpressionHasType (source caller.named) context site.code.id site.code.sourceNode.type := by
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
  (member : caller ∈ headers)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {children : GenericExpressionMeaning.Certificate}

variable (owners : CallableIndexedOwnedPreparedPositiveFunctionOrigins.OwnerCover headers keys bodyRegistry profile)

local notation "nativeFacet" => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.facet (compiled := compiled) headers
local notation "bridge" => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
  (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions nativeFacet headers keys bodyRegistry faults profile)

include profile owners member complete wellFormed runtime covers in
/-- Actual admitted caller capture and one original formation prove the
ordinary native-qualified lambda leaf at its unchanged canonical packet. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence (source caller.named)
      (Lambdas selected root expressionSyntax headers (context := context) (evidence := evidence) (scope := scope) children) faults size := by
  intro childScope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  cases certified with
  | @actual childFuel id lowered actualNode parameters sourceResult statements reported nativeType allowed actualFound form certificate accepted parentTyped metadata raw finite receipt bodyReasons sourceDeclarations sameIssuer factory =>
    let captured := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Ordinary.captured
      owner complete environments agrees typed caller initial.1 initial.2
    have sameEmbedding : captured.embedding = ξ := rfl
    let code := RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment
    let support := (CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site caller selected.compilation receipt.site
      expressionSyntax (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        (CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) caller.named))
      receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment
    have qualified : (nativeFacet).ordinary code support :=
      CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Ordinary.actual (compiled := compiled) member selected root expressionSyntax certificate receipt bodyReasons sourceDeclarations sameIssuer factory environment
    have identifier : code.id = id := receipt.identifier
    have emitted : code.lowered = lowered := receipt.emitted
    have sameNode : code.sourceNode = node :=
      receipt.sourceNodeEq.trans (Option.some.inj (actualFound.symm.trans found))
    have codeTyped : ExpressionHasType (source caller.named) context code.id code.sourceNode.type := by
      rw [identifier, sameNode]
      exact sourceTyped
    have sourceType := receipt.sourceFacts.sourceType
    rw [← receipt.sourceNodeEq] at sourceType
    have ordinary := receipt.sourceFacts.ordinary
    rw [← receipt.sourceNodeEq] at ordinary
    have coercions := receipt.sourceFacts.coercions
    rw [← receipt.sourceNodeEq] at coercions
    have codeTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
        context evidence (source caller.named) environment before code.id outcome after := by
      rw [identifier]
      exact trace
    obtain ⟨result, finalStore, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post, _member⟩ :=
      CallableIndexedOwnedPreparedFunctionModelFormationBounds.Ordinary.preserves_at
        (compiled := compiled) (headers := headers) (keys := keys)
        (function := closure caller.named parameters sourceResult statements context evidence environment)
        (scope := scope) (actual := actual) (mapping := mapping) (world := world) (heap := before) (store := store)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (captured := captured) (code := code) (owner := owner)
        (qualification := nativeFacet) (profile := profile)
        (models := CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions
          (compiled := compiled) nativeFacet headers keys bodyRegistry faults profile)
        (lift := fun member => .closure
          (CallableIndexedOwnedPreparedPositiveFunctionOrigins.closure_of_direct owners member))
        (support := support) (qualified := qualified)
        (prepared := CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.ordinary_prepared (compiled := compiled) (headers := headers) (code := code) (support := support) qualified)
        (initial := initial.1) (packet := initial.2)
        (prefixContext := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Ordinary.captured_prefix
          owner complete environments agrees typed caller initial.1 initial.2)
        (observed := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.capture_globals caller.named owner complete
          initial.2.observed initial.2.bundle environments agrees typed)
        (cells := heaps) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
        (typed := codeTyped) (sourceType := sourceType) (ordinary := ordinary) (coercions := coercions)
        (admitted := admitted) codeTrace
    refine ⟨result, finalStore, mapping, world, ?_, ?_, finalHeaps, maps, worlds, frame, metadata,
      reached, related, ?_⟩
    · simpa only [emitted, sameEmbedding] using evaluated
    · simpa only [sameNode, emitted] using represented
    · refine ⟨post.admission.rows, ?_⟩
      intro value same
      simpa only [sameNode, closure] using post.admission.successful value same

include profile owners member complete wellFormed runtime covers in
/-- Independent native completion uses one actual formation and its own
Source grade. The same qualified post stays in the caller's reached packet. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence (source caller.named)
      (Lambdas selected root expressionSyntax headers (context := context) (evidence := evidence) (scope := scope) children) faults size := by
  intro childScope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ result finalStore environments heaps locals agrees typed initial admitted completed
  cases certified with
  | @actual childFuel id lowered actualNode parameters sourceResult statements reported nativeType allowed actualFound form certificate accepted parentTyped metadata raw finite receipt bodyReasons sourceDeclarations sameIssuer factory =>
    let captured := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Ordinary.captured
      owner complete environments agrees typed caller initial.1 initial.2
    have sameEmbedding : captured.embedding = ξ := rfl
    let code := RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment
    let support := (CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site caller selected.compilation receipt.site
      expressionSyntax (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        (CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) caller.named))
      receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment
    have qualified : (nativeFacet).ordinary code support :=
      CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Ordinary.actual (compiled := compiled) member selected root expressionSyntax certificate receipt bodyReasons sourceDeclarations sameIssuer factory environment
    have identifier : code.id = id := receipt.identifier
    have emitted : code.lowered = lowered := receipt.emitted
    have sameNode : code.sourceNode = node :=
      receipt.sourceNodeEq.trans (Option.some.inj (actualFound.symm.trans found))
    have codeTyped : ExpressionHasType (source caller.named) context code.id code.sourceNode.type := by
      rw [identifier, sameNode]
      exact sourceTyped
    have sourceType := receipt.sourceFacts.sourceType
    rw [← receipt.sourceNodeEq] at sourceType
    have ordinary := receipt.sourceFacts.ordinary
    rw [← receipt.sourceNodeEq] at ordinary
    have coercions := receipt.sourceFacts.coercions
    rw [← receipt.sourceNodeEq] at coercions
    have codeCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore := by
      simpa only [emitted, sameEmbedding] using completed
    obtain ⟨sourceSize, outcome, after, sourceTrace, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post, _member⟩ :=
      CallableIndexedOwnedPreparedFunctionModelFormationBounds.Ordinary.reflects_at
        (compiled := compiled) (headers := headers) (keys := keys)
        (function := closure caller.named parameters sourceResult statements context evidence environment)
        (scope := scope) (actual := actual) (mapping := mapping) (world := world) (heap := before) (store := store)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (captured := captured) (code := code) (owner := owner)
        (qualification := nativeFacet) (profile := profile)
        (models := CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions
          (compiled := compiled) nativeFacet headers keys bodyRegistry faults profile)
        (lift := fun member => .closure
          (CallableIndexedOwnedPreparedPositiveFunctionOrigins.closure_of_direct owners member))
        (support := support) (qualified := qualified)
        (prepared := CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.ordinary_prepared (compiled := compiled) (headers := headers) (code := code) (support := support) qualified)
        (initial := initial.1) (packet := initial.2)
        (prefixContext := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Ordinary.captured_prefix
          owner complete environments agrees typed caller initial.1 initial.2)
        (observed := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.capture_globals caller.named owner complete
          initial.2.observed initial.2.bundle environments agrees typed)
        (cells := heaps) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
        (typed := codeTyped) (sourceType := sourceType) (ordinary := ordinary) (coercions := coercions)
        (admitted := admitted) codeCompleted
    refine ⟨sourceSize, outcome, after, mapping, world, ?_, ?_, finalHeaps, maps, worlds, frame, metadata,
      reached, related, ?_⟩
    · simpa only [identifier, closure] using sourceTrace
    · simpa only [sameNode, emitted] using represented
    · refine ⟨post.admission.rows, ?_⟩
      intro value same
      simpa only [sameNode, closure] using post.admission.successful value same

end Semantics
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads
