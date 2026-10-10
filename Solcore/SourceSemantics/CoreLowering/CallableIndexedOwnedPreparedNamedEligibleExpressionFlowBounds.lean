import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedHeaderRootPolicyReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNamedProfileExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedFlowStep

/-! The finite issued Header retains the same selected compiler packet used by
each child action. The actual paired collector constructs the finite child
Tree, both raw typings and the rich profile. The shared graded E hypothesis
then supplies child meaning to the original named flow producer once.

Occurrence-specific raw compiler Domain and Source syntax remain static
inputs. Neither a finished Tree nor an expression or body law is a static
construction input; arbitrary older profiles are not identified with issuers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEligibleExpressionFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Header)
open CallableIndexedOwnedPreparedNamedDiagnosticSources
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (Validity FlowPreserves FlowReflects bridge)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (packet : Issued input)
  {headers : List (Header compiled)}
  (expressionSyntax : Header compiled → ExpressionId → Prop)
  (administrative : Core.Context)

/-- One literal child root, at the selected issuer, with its same finite Tree
and the actual and fixed native contexts supplied by the body collector. -/
def Certificate (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => ∃ predecessor,
    ∃ root : RootPolicyReceipt (compiled := compiled) input.prepared.named
      (CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.lowered compiled packet.selected.diagnostics)
      packet.selected.code packet.selected.compilation predecessor packet.header.function.source
      scope id packet.header.reasonAt lowered,
    CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := sourceContext) (compilerScope := scope) (fuel := packet.header.readFuel)
      (solved := (context compiled.indexed input.prepared.named).solvedRequirements)
      root (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence)
      headers (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
      («prefix» (compiled := compiled) input.prepared.named) scope id lowered

/-- The receiving certificate family is fixed to this actual issued Header.
The flow theorem below is only about that same Header. -/
def certificates : Header compiled → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ sourceContext => Certificate (headers := headers) packet expressionSyntax administrative sourceContext

/-- The raw Domain supplies genuine finite Source/compiler conditions at the
actual context and selected root. It contains no native or semantic child law. -/
structure Static where
  domain : ∀ sourceContext scope predecessor id lowered,
    ∀ root : RootPolicyReceipt (compiled := compiled) input.prepared.named
      (CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.lowered compiled packet.selected.diagnostics)
      packet.selected.code packet.selected.compilation predecessor packet.header.function.source
      scope id packet.header.reasonAt lowered,
    CallableIndexedOwnedPreparedRawCompilerHeads.Domain
      (sourceContext := sourceContext) (scope := scope) (readFuel := packet.header.readFuel)
      root (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence) headers
  syntaxTree : GenericImperativeMatch.Syntax packet.header.function.source
    (expressionSyntax packet.header) packet.header.context
    (.statements true packet.header.function.body) packet.header.function.resultType

/-- Actual child acceptance manufactures its exact contextual root. One raw
compiler induction supplies its Tree; both native witnesses are forwarded. -/
theorem children (static : Static (headers := headers) packet expressionSyntax) :
    CallableIndexedOwnedPreparedPairedNamedProfileExtraction.Children
      (certificates := certificates (headers := headers) packet expressionSyntax administrative)
      (expressionSyntax := expressionSyntax) (header := packet.header) (administrative := administrative) where
  syntaxTree := static.syntaxTree
  expressions := by
    intro sourceContext closed residual signatures scope fuel id node lowered declarations allowed found typed accepted
      nativeType fixedNativeType nativeTyped fixedTyped
    obtain ⟨predecessor, _fuel, ⟨root⟩⟩ :=
      CallableIndexedOwnedPreparedHeaderRootPolicyReceipts.at_accepted (prepared packet) packet.aligned accepted
    have actual : CallableIndexedOwnedPreparedPrincipalCompilerChildren.AcceptedAt
        root (fun _ id => expressionSyntax packet.header id) packet.header.readFuel
        (source input.prepared.named) sourceContext scope id lowered := by
      rw [← source packet]
      exact .intro found typed allowed declarations closed residual signatures root.selected.accepted
    have unique : NodeOccurrencesUnique (source input.prepared.named) := by
      rw [← source packet]
      exact packet.header.unique
    have tree := CallableIndexedOwnedPreparedRawCompilerHeads.tree_of_accepted
      (sourceContext := sourceContext) (scope := scope) (readFuel := packet.header.readFuel)
      root (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence) headers
      (static.domain sourceContext scope predecessor id lowered root) unique actual
    refine ⟨predecessor, root, tree, ⟨nativeType, nativeTyped⟩, ⟨fixedNativeType, ?_⟩⟩
    simpa only [packet.aligned.named, CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued] using fixedTyped

/-- The paired extraction's genuine coupled output constructs the rich
profile, retaining this child certificate family and the selected issuer. -/
def of_collected
    (extraction : CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Receipt
      (certificates := certificates (headers := headers) packet expressionSyntax administrative)
      (expressionSyntax := expressionSyntax) (administrative := administrative)
      (prepared packet) (issuer packet).typing.2 (assignments_prepared packet)) :
    CallableIndexedOwnedPreparedCatalogNamedProfiles.Profile
      (certificates := certificates (headers := headers) packet expressionSyntax administrative)
      (expressionSyntax := expressionSyntax) packet.header administrative :=
  CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles.of_collected packet extraction

private theorem eligible_at
    {caller : Header compiled} {named : Named} {index : Nat}
    (member : caller ∈ headers) (same : caller.named = named)
    (selected : CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.SelectedReceipt compiled named index) :
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.Eligible (headers := headers)
      selected (.ordinary caller) (some caller.function.evidence) caller.function.evidence := by
  cases same
  exact .ordinary member selected (some caller.function.evidence) rfl

section Meaning
variable {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (member : packet.header ∈ headers)

include member in
/-- The semantic E hypothesis is consumed at the same literal root and actual
administrative context. It is separate from every static certificate. -/
theorem preserves_children (budget : Nat)
    (expressions : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    ∀ sourceContext, Validity packet.header sourceContext →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (bridge (headers := headers) owner packet.header)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          sourceContext packet.header.function.evidence packet.header.function.source
          (Certificate (headers := headers) packet expressionSyntax administrative sourceContext) faults size) := by
  intro sourceContext valid size within scope id lowered certified
  obtain ⟨predecessor, root, tree⟩ := certified
  have actualValid : CompatibleRuntimeContextValidity.Valid
      (context compiled.indexed input.prepared.named).solvedRequirements sourceContext packet.header.function.evidence := by
    change CompatibleRuntimeContextValidity.Valid
      input.prepared.named.specialized.function.solvedRequirements sourceContext packet.header.function.evidence
    have actual := valid.1
    change CompatibleRuntimeContextValidity.Valid packet.header.solved sourceContext packet.header.function.evidence at actual
    rw [packet.aligned.solved] at actual
    exact actual
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      sourceContext (source input.prepared.named) := by
    rw [← source packet]
    exact valid.2
  have meaning : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionPreserves
      (headers := headers) (registry := registry) (faults := faults) functions packet.selected root
      (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence)
      packet.header.readFuel
      (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
      (.ordinary packet.header) owner sourceContext packet.header.function.evidence size :=
    expressions packet.selected root (fun _ id => expressionSyntax packet.header id)
    (some packet.header.function.evidence) packet.header.readFuel
    (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
    (.ordinary packet.header) owner sourceContext packet.header.function.evidence
    (eligible_at member packet.aligned.named packet.selected) actualValid runtime size within
  unfold CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionPreserves at meaning
  rw [← source packet] at meaning
  intro node
  exact meaning scope tree (node := node)

include member in
/-- Reflection consumes the independent strict native E grade at this same
child and preserves its returned Source grade and reached caller. -/
theorem reflects_children (budget : Nat)
    (expressions : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionsReflects
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    ∀ sourceContext, Validity packet.header sourceContext →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (bridge (headers := headers) owner packet.header)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          sourceContext packet.header.function.evidence packet.header.function.source
          (Certificate (headers := headers) packet expressionSyntax administrative sourceContext) faults size) := by
  intro sourceContext valid size within scope id lowered certified
  obtain ⟨predecessor, root, tree⟩ := certified
  have actualValid : CompatibleRuntimeContextValidity.Valid
      (context compiled.indexed input.prepared.named).solvedRequirements sourceContext packet.header.function.evidence := by
    change CompatibleRuntimeContextValidity.Valid
      input.prepared.named.specialized.function.solvedRequirements sourceContext packet.header.function.evidence
    have actual := valid.1
    change CompatibleRuntimeContextValidity.Valid packet.header.solved sourceContext packet.header.function.evidence at actual
    rw [packet.aligned.solved] at actual
    exact actual
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      sourceContext (source input.prepared.named) := by
    rw [← source packet]
    exact valid.2
  have meaning : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionReflects
      (headers := headers) (registry := registry) (faults := faults) functions packet.selected root
      (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence)
      packet.header.readFuel
      (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
      (.ordinary packet.header) owner sourceContext packet.header.function.evidence size :=
    expressions packet.selected root (fun _ id => expressionSyntax packet.header id)
    (some packet.header.function.evidence) packet.header.readFuel
    (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
    (.ordinary packet.header) owner sourceContext packet.header.function.evidence
    (eligible_at member packet.aligned.named packet.selected) actualValid runtime size within
  unfold CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionReflects at meaning
  rw [← source packet] at meaning
  intro node
  exact meaning scope tree (node := node)
end Meaning

section Flows
variable {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : CallableIndexedOwnedPreparedCatalogNamedProfiles.Profile
    (certificates := certificates (headers := headers) packet expressionSyntax administrative)
    (expressionSyntax := expressionSyntax) packet.header administrative)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (member : packet.header ∈ headers)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : profile.receiving.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep profile.receiving.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token,
    EmittedDiagnosticTokenPlan.UnaryRep profile.receiving.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity packet.header context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context)
      (certificates := certificates (headers := headers) packet expressionSyntax administrative packet.header)
      (administrative := SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
      (factory := profile.factory) (faults := faults) (registry := registry) profile.receiving
      (bridge (headers := headers) owner packet.header) functions table)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets member in
/-- The original named preservation producer is invoked once with child
meaning derived from the shared E induction at this selected packet. -/
theorem preserves_flow (budget : Nat)
    (expressions : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves (headers := headers) (registry := registry) (faults := faults) functions owner profile) :=
  CallableIndexedOwnedPreparedCatalogNamedFlowStep.preserves_flow profile owner functions extension
    faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (preserves_children packet expressionSyntax administrative functions owner member budget expressions)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets member in
/-- Reflection invokes the same original producer once, retaining its strict
native budget and independent Source grade. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (expressions : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionsReflects
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    Below budget
      (FlowReflects (headers := headers) (registry := registry) (faults := faults) functions owner profile) :=
  CallableIndexedOwnedPreparedCatalogNamedFlowStep.reflects_flow profile owner functions extension
    faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget functionTypes
    (reflects_children packet expressionSyntax administrative functions owner member budget expressions)
end Flows

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEligibleExpressionFlowBounds
