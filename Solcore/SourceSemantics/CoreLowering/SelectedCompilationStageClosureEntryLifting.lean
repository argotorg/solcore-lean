import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureBodyLifting

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationStageBodyLiftBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)

private abbrev parameterScope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
local notation "physicalBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix)

/-- The actual closure parameter entry supplies this physical state. Its
complete capture environment and real frame stay in the original closure. -/
def EntryLiftsBelow (budget : Nat) : Prop :=
  ∀ {mapping world environment canonical actual actualContext before store ξ contextLocation native},
    DataHeap.EnvRepresents catalog mapping world administrative (parameterScope code) environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before inputs.context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
    canonical[(parameterScope code).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation) →
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) →
    contextLocation ∉ mapping →
    CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native →
  ∀ initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix).State
      ⟨(parameterScope code), mapping, world, before, store, canonical⟩,
    Admission physicalBridge inputs.context initial →
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function →
  ∀ {size finalContext outcome after},
    RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked compiled.sourceProgram) size inputs.context
      child.evidence child.source environment before function.body finalContext outcome after →
    size ≤ budget →
    BodyLift (Program.ofChecked compiled.sourceProgram) stages true child inputs.context environment before
      function.body finalContext outcome after

theorem of_general {budget : Nat}
    (lifted : SelectedCompilationStageClosureBodyLifting.ClosureLiftsBelow
      (headers := headers) (keys := keys) code inputs model stages child budget) :
    EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages child budget := by
  intro mapping world environment canonical actual actualContext before store ξ contextLocation native
    environments heaps locals agrees typed reference read unmapped conditioned initial admitted valid
    size finalContext outcome after trace within
  exact lifted environments heaps locals agrees typed reference read unmapped conditioned initial admitted valid trace within

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryLifting
