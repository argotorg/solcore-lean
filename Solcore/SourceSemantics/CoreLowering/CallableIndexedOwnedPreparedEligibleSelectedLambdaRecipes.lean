import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets

/-! The final call domain retains a positive static packet factory at each
literal raw lambda occurrence. Its output is the authentic selected compiler
Receipt, same issuer tag and finite OccurrenceFactory already retained by the
positive Lambdas constructor. The producer125 can manufacture that output from
original compiler/static inputs. No semantic expression/body law is a field.
Runtime formation consumes the same packet once at the actual Origin bridge.
The universal construction of these static factories remains explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedLambdaRecipes
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedPreparedNativeAssignmentChildren (RawTyped)
open CallableIndexedOwnedPreparedNativeSiteShellReceipts (FiniteBodyReceipts)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedNativeFamilyStaticQualification (OccurrenceFactory)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {named : Named} {index : Nat} (selected : SelectedReceipt compiled named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {context : SourceSemantics.Context} {compilerScope : SourceCoreLocalCell.Scope}

/-- The literal compiler action and its genuine fixed-prefix witness contain
no child meaning, runtime Tree or execution result. -/
inductive RawLambda : GenericExpressionMeaning.Certificate where
  | actual {childFuel id lowered node parameters result statements reported}
      (allowed : expressionSyntax (source named) id)
      (found : (source named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (CallableIndexedNamedGeneration.context compiled.indexed named) (source named) compilerScope
        id node parameters result statements reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (CallableIndexedNamedGeneration.context compiled.indexed named) (source named) compilerScope id rootReasonAt = .ok lowered)
      (sourceTyped : ExpressionHasType (source named) context id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named) id node lowered.type)
      (fixed : RawTyped (SourceCoreLocalCell.coreContext compilerScope ++ «prefix» (compiled := compiled) named)
        lowered.expression compiled.indexed.layouts.definitions) :
      RawLambda compilerScope id lowered

/-- These are original compiler and Source inputs at this actual occurrence.
The occurrence factory is requested only for the one tagged Receipt constructed
from them. No completed expression, body or application is retained. -/
inductive CompilerInputs (evidence : Dynamic.EvidenceEnvironment) : GenericExpressionMeaning.Certificate where
  | actual {childFuel id lowered node parameters result statements reported nativeType}
      (allowed : expressionSyntax (source named) id)
      (found : (source named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (CallableIndexedNamedGeneration.context compiled.indexed named) (source named) compilerScope
        id node parameters result statements reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (CallableIndexedNamedGeneration.context compiled.indexed named) (source named) compilerScope id rootReasonAt = .ok lowered)
      (sourceTyped : ExpressionHasType (source named) context id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named) id node lowered.type)
      (coercions : node.coercions = [])
      (raw : HasType (SourceCoreLocalCell.coreContext compilerScope ++ «prefix» (compiled := compiled) named)
        lowered.expression nativeType compiled.indexed.layouts.definitions)
      (finite : FiniteBodyReceipts (source named) (expressionSyntax (source named)) context parameters result statements)
      (ownership : LocalIdentityOwnership (source named))
      (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) compilerScope context)
      (sameLedger : context.solvedRequirements =
        (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
      (occurrences : ∀ receipt : Receipt root expressionSyntax certificate
          (sourceContext := context) (evidence := evidence),
        receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site →
        OccurrenceFactory root expressionSyntax (some evidence) headers receipt.body.readFuel) :
      CompilerInputs evidence compilerScope id lowered

namespace CompilerInputs

/-- One original tagged compiler producer constructs the ordinary packet. -/
theorem ordinary {caller : Header compiled (Program.ofChecked compiled.sourceProgram)} {index : Nat}
    (selected : SelectedReceipt compiled caller.named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilerScope scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
    (covers : evidence.Covers context)
    (inputs : CompilerInputs (headers := headers) selected root expressionSyntax evidence
      (context := context) (compilerScope := compilerScope) scope id lowered)
    (children : GenericExpressionMeaning.Certificate) :
    CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.Lambdas selected root expressionSyntax headers
      (context := context) (evidence := evidence) (scope := compilerScope) children scope id lowered := by
  cases inputs with
  | actual allowed found form certificate accepted sourceTyped metadata coercions raw finite ownership declarations sameLedger occurrences =>
    exact CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets.Ordinary.of_compiler
      selected root expressionSyntax headers profile runtime covers ownership declarations sameLedger
      allowed found form certificate accepted sourceTyped metadata coercions raw finite occurrences

/-- The principal producer retains the complete literal method dictionary. -/
theorem principal {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (selected : SelectedReceipt compiled principal.named principal.cached.index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    {context : SourceSemantics.Context} {compilerScope scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source principal.named))
    (covers : principal.dictionary.Covers context)
    (inputs : CompilerInputs (headers := headers) selected root expressionSyntax principal.dictionary
      (context := context) (compilerScope := compilerScope) scope id lowered)
    (children : GenericExpressionMeaning.Certificate) :
    CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.Lambdas principal selected root expressionSyntax headers
      (context := context) (scope := compilerScope) children scope id lowered := by
  cases inputs with
  | actual allowed found form certificate accepted sourceTyped metadata coercions raw finite ownership declarations sameLedger occurrences =>
    exact CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets.Principal.of_compiler
      principal selected root expressionSyntax headers profile runtime covers ownership declarations sameLedger
      allowed found form certificate accepted sourceTyped metadata coercions raw finite occurrences
end CompilerInputs

/-- The finite positive call packet is a static output. Its actual selected
Receipt and OccurrenceFactory are retained by Lambdas.actual; no execution law
is accepted and no old raw Domain is inverted to manufacture this factory. -/
inductive Recipes : {named : Named} → {index : Nat} →
    (selected : SelectedReceipt compiled named index) →
    {rootFuel : Nat} → {rootSource : TypedSource} → {rootScope : SourceCoreLocalCell.Scope} →
    {rootId : ExpressionId} → {rootReasonAt : ExpressionId → Word} → {rootLowered : SourceCoreBasic.LoweredExpr} →
    RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered →
    (TypedSource → ExpressionId → Prop) → SourceSemantics.Context →
    Option Dynamic.EvidenceEnvironment → Dynamic.EvidenceEnvironment → Origin compiled → Prop where
  | ordinary {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers) {index : Nat}
      (selected : SelectedReceipt compiled caller.named index)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
        selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop) (context : SourceSemantics.Context)
      (callerEvidence : Option Dynamic.EvidenceEnvironment) (evidence : Dynamic.EvidenceEnvironment)
      (sameEvidence : CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.CallerEvidence callerEvidence evidence)
      (build : ∀ {compilerScope scope id lowered},
        RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope) scope id lowered →
        CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.Lambdas selected root expressionSyntax headers
          (context := context) (evidence := evidence) (scope := compilerScope) (fun _ _ _ => False) scope id lowered) :
      Recipes selected root expressionSyntax context callerEvidence evidence (.ordinary caller)
  | principal {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (selected : SelectedReceipt compiled principal.named principal.cached.index)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
        selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop) (context : SourceSemantics.Context)
      (build : ∀ {compilerScope scope id lowered},
        RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope) scope id lowered →
        CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.Lambdas principal selected root expressionSyntax headers
          (context := context) (scope := compilerScope) (fun _ _ _ => False) scope id lowered) :
      Recipes selected root expressionSyntax context (some principal.dictionary) principal.dictionary (.principal principal.named)

namespace Recipes

/-- Genuine per-occurrence compiler inputs supply the ordinary static recipe.
The tagged Receipt is constructed once when that exact occurrence is selected. -/
theorem of_ordinary_inputs {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (member : caller ∈ headers) {index : Nat}
    (selected : SelectedReceipt compiled caller.named index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop) (context : SourceSemantics.Context)
    (callerEvidence : Option Dynamic.EvidenceEnvironment) (evidence : Dynamic.EvidenceEnvironment)
    (sameEvidence : CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.CallerEvidence callerEvidence evidence)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
    (covers : evidence.Covers context)
    (inputs : ∀ {compilerScope scope id lowered},
      RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope) scope id lowered →
      CompilerInputs (headers := headers) selected root expressionSyntax evidence
        (context := context) (compilerScope := compilerScope) scope id lowered) :
    Recipes (headers := headers) selected root expressionSyntax context callerEvidence evidence (.ordinary caller) := by
  apply Recipes.ordinary member selected root expressionSyntax context callerEvidence evidence sameEvidence
  intro compilerScope scope id lowered raw
  exact CompilerInputs.ordinary selected root expressionSyntax profile runtime covers (inputs raw) (fun _ _ _ => False)

/-- The selected principal and full dictionary are retained by the same static
compiler-input producer; no earlier weak qualification is inverted. -/
theorem of_principal_inputs {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (selected : SelectedReceipt compiled principal.named principal.cached.index)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
      selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop) (context : SourceSemantics.Context)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source principal.named))
    (covers : principal.dictionary.Covers context)
    (inputs : ∀ {compilerScope scope id lowered},
      RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope) scope id lowered →
      CompilerInputs (headers := headers) selected root expressionSyntax principal.dictionary
        (context := context) (compilerScope := compilerScope) scope id lowered) :
    Recipes (headers := headers) selected root expressionSyntax context (some principal.dictionary)
      principal.dictionary (.principal principal.named) := by
  apply Recipes.principal principal selected root expressionSyntax context
  intro compilerScope scope id lowered raw
  exact CompilerInputs.principal principal selected root expressionSyntax profile runtime covers (inputs raw) (fun _ _ _ => False)
end Recipes

section Semantics
variable {callerEvidence : Option Dynamic.EvidenceEnvironment} {evidence : Dynamic.EvidenceEnvironment}
  {origin : Origin compiled}
  (recipes : Recipes (headers := headers) selected root expressionSyntax context callerEvidence evidence origin)
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : OwnedKey keys) (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owners : CallableIndexedOwnedPreparedPositiveFunctionOrigins.OwnerCover headers keys bodyRegistry profile)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source named))
  (covers : evidence.Covers context)

local notation "nativeFacet" => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.facet (compiled := compiled) headers
local notation "functions" => CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions nativeFacet headers keys bodyRegistry faults profile
local notation "bridge" => Origin.bridge (headers := headers) origin owner
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include recipes profile owners complete wellFormed runtime covers in
/-- Original positive runtime formation runs once at this same raw occurrence. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence (source named)
      (RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope)) faults size := by
  intro scope id lowered raw
  cases recipes with
  | ordinary member selected root expressionSyntax context callerEvidence evidence sameEvidence build =>
    exact CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.preserves_at
      (profile := profile) (owners := owners) (member := member) (complete := complete)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      selected root expressionSyntax headers owner size (build raw)
  | principal principal selected root expressionSyntax context build =>
    exact CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.preserves_at
      (profile := profile) (owners := owners) (complete := complete)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      principal selected root expressionSyntax headers owner size (build raw)

include recipes profile owners complete wellFormed runtime covers in
/-- Reflection retains its own native grade and reconstructed Source grade. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence (source named)
      (RawLambda selected root expressionSyntax (context := context) (compilerScope := compilerScope)) faults size := by
  intro scope id lowered raw
  cases recipes with
  | ordinary member selected root expressionSyntax context callerEvidence evidence sameEvidence build =>
    exact CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.reflects_at
      (profile := profile) (owners := owners) (member := member) (complete := complete)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      selected root expressionSyntax headers owner size (build raw)
  | principal principal selected root expressionSyntax context build =>
    exact CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.reflects_at
      (profile := profile) (owners := owners) (complete := complete)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      principal selected root expressionSyntax headers owner size (build raw)
end Semantics

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedLambdaRecipes
