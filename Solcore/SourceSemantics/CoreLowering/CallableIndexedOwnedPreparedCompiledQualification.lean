import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalCompilerChildren

/-! A concrete compiler qualification selects actual ordinary compiler factories
from the finite Header inventory, or actual selected method factories from their
Principal authority. Each constructor retains the chosen root policy and same
recaptured body. It does not quantify arbitrary Support certificates. This one
facet plugs into the generic qualified function/payload/heap model. The ordinary
collector has an existing actual Tree producer; the method accepted-child packet
still needs its genuine finite method Tree/head producer before family closure.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompiledQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet QualifiedAssociation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Only the actual named inventory can authorize the ordinary branch. The
selected compiler receipt is retained through the Collected constructor. -/
inductive Ordinary
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) :
    {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code → Prop where
  | actual {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers)
      {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
      {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
        rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      {code : Code compiled.indexed function scope administrative}
      {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
      (collected : CallableIndexedOwnedPreparedCompilerChildCollector.Collected root expressionSyntax code support) :
      Ordinary headers code support

/-- The Principal carries the selected implementation, full dictionary and
cached compiler row. There is no ordinary Header in this constructor. -/
inductive Principal : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop where
  | actual {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) principal.named principal.cached.diagnostics principal.cached.code
        principal.cached.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : Site compiled.indexed principal.named parameters result statements sourceContext principal.dictionary [] scope administrative)
      {function : Dynamic.Closure} {currentScope : SourceCoreLocalCell.Scope} {currentAdministrative : Core.Context}
      {code : Code compiled.indexed function currentScope currentAdministrative}
      {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
      (collected : CallableIndexedOwnedPreparedPrincipalCompilerChildren.Collected
        principal root expressionSyntax site code support) :
      Principal code support

/-- Both facets are actual positive compiler constructors. Payload/heap
operations need only this one FunctionModel instantiation. -/
def facet (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : Facet compiled where
  ordinary := fun code support => Ordinary headers code support
  principal := fun code support => Principal code support

section Positive
variable
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)

/-- Formation can register the exact compiled ordinary packet immediately.
No inverse on an arbitrary existing positive payload or heap is involved. -/
def ordinary_association
    (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
    (collected : Ordinary headers code support)
    (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
      .reachable bodyRegistry faults)
    (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
    (origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin support history)
    (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial compiled.compatible.checked) support.caller)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (typed : RuntimeValueHasType world (value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    QualifiedAssociation (facet headers) headers keys bodyRegistry faults mapping world function
      (value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual) code.receipt.loweredParameters
      code.receipt.parameterCore code.receipt.resultCore :=
  ⟨.ordinary (.ordinary owner captured code history support actualSites sites origin prepared
    prefixContext globals referenceIndex typed), collected⟩

/-- The corresponding actual Principal packet keeps its real dictionary and
leading method bundle, at the same body and carrier. -/
def principal_association
    (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
    (collected : Principal code support)
    (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
      .reachable bodyRegistry faults)
    (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
    (origin : CallableIndexedOwnedPreparedPrincipalLambdaSupport.SourceOrigin support history)
    (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
    (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (typed : RuntimeValueHasType world (value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    QualifiedAssociation (facet headers) headers keys bodyRegistry faults mapping world function
      (value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual) code.receipt.loweredParameters
      code.receipt.parameterCore code.receipt.resultCore :=
  ⟨.principal (.principal owner captured code history support actualSites sites origin prepared
    globals leading referenceIndex typed), collected⟩

end Positive
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompiledQualification
