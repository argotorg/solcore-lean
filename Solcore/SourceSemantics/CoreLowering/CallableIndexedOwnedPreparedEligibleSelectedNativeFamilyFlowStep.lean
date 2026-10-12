import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedNativeFamilyQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyFlowStep
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds

/-! The closure F step asks E only for a literal selected ordinary Header
or the literal selected Principal and dictionary retained at formation. It
never asks for an unrelated Origin or caller evidence. The same fixed-prefix
raw occurrence witness supplies both views of the paired expression Tree.

The authentic occurrence factory constructs the finite Tree internally.
Receiving table/token/reached-interpretation facts stay static inputs; graded
E is the mutual induction hypothesis. The original prepared F producer runs
once with the same body, protocol, owner and independent reflection grade. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedSelectedNativeFamilyQualification (facet)
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open CallableIndexedOwnedTypedLambdaProtocolContinuations (FlowPreserves FlowReflects)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (trackedFactory)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- The root is attached positively to the actual caller domain. Methods
retain their complete selector and literal dictionary; no Header is synthesized. -/
inductive Eligible : {named : Named} → {index : Nat} →
    SelectedReceipt compiled named index → Origin compiled →
    Option Dynamic.EvidenceEnvironment → Dynamic.EvidenceEnvironment → Prop where
  | ordinary {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers) {index : Nat}
      (selected : SelectedReceipt compiled caller.named index)
      (callerEvidence : Option Dynamic.EvidenceEnvironment)
      {evidence : Dynamic.EvidenceEnvironment}
      (sameEvidence : CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.CallerEvidence
        callerEvidence evidence) :
      Eligible selected (.ordinary caller) callerEvidence evidence
  | principal {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (selected : SelectedReceipt compiled principal.named principal.cached.index) :
      Eligible selected (.principal principal.named) (some principal.dictionary) principal.dictionary

section Expressions
variable {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
  (origin : Origin compiled) (owner : OwnedKey keys)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- E is measured at the actual selected-root RuntimeTree. Its meaning is an
induction hypothesis, separate from every static receipt. -/
def ExpressionPreserves (size : Nat) : Prop :=
  ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
    (Origin.bridge (headers := headers) origin owner)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context evidence (source named)
    (CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := context) (compilerScope := compilerScope) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers («prefix» (compiled := compiled) named)
      («prefix» (compiled := compiled) named)) faults size

def ExpressionReflects (size : Nat) : Prop :=
  ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
    (Origin.bridge (headers := headers) origin owner)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context evidence (source named)
    (CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := context) (compilerScope := compilerScope) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers («prefix» (compiled := compiled) named)
      («prefix» (compiled := compiled) named)) faults size
end Expressions

/-- This is the numeric E family over authentic selected compiler roots.
Its RuntimeTree argument is built from the same accepted child and raw native
witness. It is a semantic induction hypothesis, never a static packet field. -/
def ExpressionsPreserves (budget : Nat) : Prop :=
  ∀ {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
    (origin : Origin compiled) (owner : OwnedKey keys)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment),
    Eligible (headers := headers) selected origin callerEvidence evidence →
    CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements
      context evidence → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named) →
    RecursiveNamedHeaderContracts.AtMost budget (ExpressionPreserves (headers := headers) (registry := registry) (faults := faults)
      functions selected root expressionSyntax callerEvidence readFuel origin owner context evidence)

def ExpressionsReflects (budget : Nat) : Prop :=
  ∀ {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (readFuel : Nat)
    (origin : Origin compiled) (owner : OwnedKey keys)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment),
    Eligible (headers := headers) selected origin callerEvidence evidence →
    CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements
      context evidence → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named) →
    Below budget (ExpressionReflects (headers := headers) (registry := registry) (faults := faults)
      functions selected root expressionSyntax callerEvidence readFuel origin owner context evidence)

section Closure
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

namespace Ordinary
variable (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (qualified : CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Ordinary headers code support)

/-- Only the actual issuer's rebuilt table, token inclusions and static
readiness at reached valid contexts are retained. -/
def Receiving : Prop :=
  ∃ table : SourceCoreFaultSites.Table,
    support.issued.diagnostics.tableForRegistry registry extension = .ok table ∧
    (∀ reason token, GenericAssignmentDiagnostics.OperandRep support.issued.assignments reason token → faults reason token) ∧
    (∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep support.issued.assignments reason token → faults reason token) ∧
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
        (context := context) (certificates := support.certificates support.body.readFuel function.source)
        (administrative := captured.administrative)
        (factory := trackedFactory support.diagnosticPolicy function.source support.issued.invalidOperand)
        (faults := faults) (registry := registry) support.issued
        (Origin.bridge (headers := headers) (.ordinary support.caller) owner) functions table

include qualified faithful observations wellFormed in
/-- The actual selected occurrence factory builds the same Tree before one
original F producer is invoked. Reflection keeps an independent Source grade. -/
theorem preserves_flow (budget : Nat)
    (receiving : Receiving (headers := headers) (registry := registry) (faults := faults) functions captured code owner extension support)

    (expressionIH : ExpressionsPreserves (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code support.body.toBody functions
        (Origin.bridge (headers := headers) (.ordinary support.caller) owner)
        (registry := registry) (faults := faults)) := by
  cases captured with
  | mk administrative canonical actualContext embedding represented agrees respects typed =>
    cases qualified with
    | @actual caller member index selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered root expressionSyntax sourceContext evidence scope id lowered node parameters result statements reported childFuel certificate receipt bodyReasons declarations sameIssuer factory environment =>
        obtain ⟨table, rebuilt, operands, unaries, interprets⟩ := receiving
        apply CallableIndexedOwnedPreparedNativeFamilyFlowStep.preserves_flow
          selected.compilation root expressionSyntax (some evidence)
          ⟨_, canonical, actualContext, embedding, represented, agrees, respects, typed⟩ (RecursiveNamedLambdaFormationHeads.recaptureCode
            (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
          rfl receipt.shell.issued
          ((CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site
            caller selected.compilation receipt.site expressionSyntax
            (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
              («prefix» (compiled := compiled) caller.named)) receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment).body
          factory (.ordinary caller) owner functions
          extension faithful observations wellFormed rebuilt operands unaries interprets budget

        intro context valid child within compilerScope currentScope expression lowered accepted node
        have eligible : Eligible (headers := headers) selected (.ordinary caller) (some evidence) evidence :=
          .ordinary member selected (some evidence) rfl
        have currentValid : CompatibleRuntimeContextValidity.Valid
            (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements context evidence := by
          simpa only [Validity, RecursiveNamedLambdaFormationHeads.recaptureCode, receipt.site.compilation,
            CallableIndexedLambdaGeneration.closure] using valid.1
        exact expressionIH selected root expressionSyntax (some evidence) receipt.body.readFuel
          (.ordinary caller) owner context evidence eligible currentValid valid.2
          child within compilerScope ⟨accepted.1, accepted.2, accepted.2⟩ (node := node)

include qualified faithful observations wellFormed in
/-- The actual selected occurrence factory builds the same Tree before one
original F producer is invoked. Reflection keeps an independent Source grade. -/
theorem reflects_flow (budget : Nat)
    (receiving : Receiving (headers := headers) (registry := registry) (faults := faults) functions captured code owner extension support)
    (functionTypes : FunctionRuntimeViews functions)
    (expressionIH : ExpressionsReflects (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    Below budget
      (FlowReflects captured code support.body.toBody functions
        (Origin.bridge (headers := headers) (.ordinary support.caller) owner)
        (registry := registry) (faults := faults)) := by
  cases captured with
  | mk administrative canonical actualContext embedding represented agrees respects typed =>
    cases qualified with
    | @actual caller member index selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered root expressionSyntax sourceContext evidence scope id lowered node parameters result statements reported childFuel certificate receipt bodyReasons declarations sameIssuer factory environment =>
        obtain ⟨table, rebuilt, operands, unaries, interprets⟩ := receiving
        apply CallableIndexedOwnedPreparedNativeFamilyFlowStep.reflects_flow
          selected.compilation root expressionSyntax (some evidence)
          ⟨_, canonical, actualContext, embedding, represented, agrees, respects, typed⟩ (RecursiveNamedLambdaFormationHeads.recaptureCode
            (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
          rfl receipt.shell.issued
          ((CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site
            caller selected.compilation receipt.site expressionSyntax
            (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
              («prefix» (compiled := compiled) caller.named)) receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment).body
          factory (.ordinary caller) owner functions
          extension faithful observations wellFormed rebuilt operands unaries interprets budget
          functionTypes
        intro context valid child within compilerScope currentScope expression lowered accepted node
        have eligible : Eligible (headers := headers) selected (.ordinary caller) (some evidence) evidence :=
          .ordinary member selected (some evidence) rfl
        have currentValid : CompatibleRuntimeContextValidity.Valid
            (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements context evidence := by
          simpa only [Validity, RecursiveNamedLambdaFormationHeads.recaptureCode, receipt.site.compilation,
            CallableIndexedLambdaGeneration.closure] using valid.1
        exact expressionIH selected root expressionSyntax (some evidence) receipt.body.readFuel
          (.ordinary caller) owner context evidence eligible currentValid valid.2
          child within compilerScope ⟨accepted.1, accepted.2, accepted.2⟩ (node := node)

end Ordinary

namespace Principal
variable (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Principal headers code support)

/-- Only the actual issuer's rebuilt table, token inclusions and static
readiness at reached valid contexts are retained. -/
def Receiving : Prop :=
  ∃ table : SourceCoreFaultSites.Table,
    support.issued.diagnostics.tableForRegistry registry extension = .ok table ∧
    (∀ reason token, GenericAssignmentDiagnostics.OperandRep support.issued.assignments reason token → faults reason token) ∧
    (∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep support.issued.assignments reason token → faults reason token) ∧
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
        (context := context) (certificates := support.certificates support.body.readFuel function.source)
        (administrative := captured.administrative)
        (factory := trackedFactory support.diagnosticPolicy function.source support.issued.invalidOperand)
        (faults := faults) (registry := registry) support.issued
        (Origin.bridge (headers := headers) (.principal support.principal.named) owner) functions table

include qualified faithful observations wellFormed in
/-- The actual selected occurrence factory builds the same Tree before one
original F producer is invoked. Reflection keeps an independent Source grade. -/
theorem preserves_flow (budget : Nat)
    (receiving : Receiving (headers := headers) (registry := registry) (faults := faults) functions captured code owner extension support)

    (expressionIH : ExpressionsPreserves (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code support.body.toBody functions
        (Origin.bridge (headers := headers) (.principal support.principal.named) owner)
        (registry := registry) (faults := faults)) := by
  cases captured with
  | mk administrative canonical actualContext embedding represented agrees respects typed =>
    cases qualified with
    | @actual method principal selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered root expressionSyntax sourceContext scope id lowered node parameters result statements reported childFuel certificate receipt sameIssuer factory environment =>
        obtain ⟨table, rebuilt, operands, unaries, interprets⟩ := receiving
        apply CallableIndexedOwnedPreparedNativeFamilyFlowStep.preserves_flow
          selected.compilation root expressionSyntax (some principal.dictionary)
          ⟨_, canonical, actualContext, embedding, represented, agrees, respects, typed⟩ (RecursiveNamedLambdaFormationHeads.recaptureCode
            (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
          rfl receipt.shell.issued
          ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
            (SelectedReceipt.principal principal selected) receipt.site expressionSyntax
            (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
              («prefix» (compiled := compiled) principal.named)) receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment).body
          factory (.principal principal.named) owner functions
          extension faithful observations wellFormed rebuilt operands unaries interprets budget

        intro context valid child within compilerScope currentScope expression lowered accepted node
        have eligible : Eligible (headers := headers) selected (.principal principal.named)
            (some principal.dictionary) principal.dictionary := .principal principal selected
        have currentValid : CompatibleRuntimeContextValidity.Valid
            (CallableIndexedNamedGeneration.context compiled.indexed principal.named).solvedRequirements
            context principal.dictionary := by
          simpa only [Validity, RecursiveNamedLambdaFormationHeads.recaptureCode, receipt.site.compilation,
            CallableIndexedLambdaGeneration.closure] using valid.1
        exact expressionIH selected root expressionSyntax (some principal.dictionary) receipt.body.readFuel
          (.principal principal.named) owner context principal.dictionary eligible currentValid valid.2
          child within compilerScope ⟨accepted.1, accepted.2, accepted.2⟩ (node := node)

include qualified faithful observations wellFormed in
/-- The actual selected occurrence factory builds the same Tree before one
original F producer is invoked. Reflection keeps an independent Source grade. -/
theorem reflects_flow (budget : Nat)
    (receiving : Receiving (headers := headers) (registry := registry) (faults := faults) functions captured code owner extension support)
    (functionTypes : FunctionRuntimeViews functions)
    (expressionIH : ExpressionsReflects (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    Below budget
      (FlowReflects captured code support.body.toBody functions
        (Origin.bridge (headers := headers) (.principal support.principal.named) owner)
        (registry := registry) (faults := faults)) := by
  cases captured with
  | mk administrative canonical actualContext embedding represented agrees respects typed =>
    cases qualified with
    | @actual method principal selected rootFuel rootSource rootScope rootId rootReasonAt rootLowered root expressionSyntax sourceContext scope id lowered node parameters result statements reported childFuel certificate receipt sameIssuer factory environment =>
        obtain ⟨table, rebuilt, operands, unaries, interprets⟩ := receiving
        apply CallableIndexedOwnedPreparedNativeFamilyFlowStep.reflects_flow
          selected.compilation root expressionSyntax (some principal.dictionary)
          ⟨_, canonical, actualContext, embedding, represented, agrees, respects, typed⟩ (RecursiveNamedLambdaFormationHeads.recaptureCode
            (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
          rfl receipt.shell.issued
          ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
            (SelectedReceipt.principal principal selected) receipt.site expressionSyntax
            (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
              («prefix» (compiled := compiled) principal.named)) receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment).body
          factory (.principal principal.named) owner functions
          extension faithful observations wellFormed rebuilt operands unaries interprets budget
          functionTypes
        intro context valid child within compilerScope currentScope expression lowered accepted node
        have eligible : Eligible (headers := headers) selected (.principal principal.named)
            (some principal.dictionary) principal.dictionary := .principal principal selected
        have currentValid : CompatibleRuntimeContextValidity.Valid
            (CallableIndexedNamedGeneration.context compiled.indexed principal.named).solvedRequirements
            context principal.dictionary := by
          simpa only [Validity, RecursiveNamedLambdaFormationHeads.recaptureCode, receipt.site.compilation,
            CallableIndexedLambdaGeneration.closure] using valid.1
        exact expressionIH selected root expressionSyntax (some principal.dictionary) receipt.body.readFuel
          (.principal principal.named) owner context principal.dictionary eligible currentValid valid.2
          child within compilerScope ⟨accepted.1, accepted.2, accepted.2⟩ (node := node)

end Principal

end Closure
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep
