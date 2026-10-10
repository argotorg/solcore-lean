import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds

/-! The shared paired E family supplies the actual retained closure F.
Only the literal prefix specialization is passed to the original association
producer. Strict Source and native grades stay independent; no arbitrary
call-leaf semantics or completed body law is added to a static receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedSelectedAssociationFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (Association)
open CallableIndexedOwnedPreparedSelectedNativeFamilyQualification (facet)
open CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (receiving : CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds.Receivings
    (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
    (registry := registry) (faults := faults) functions extension)

include faithful observations wellFormed receiving in
/-- Paired E through n constructs the same selected closure F through n. -/
theorem preserves_at_most (budget : Nat)
    (expressions : ExpressionsPreserves (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    ∀ {mapping world function native bindings parameter result}
      (member : Association (facet headers) headers keys bodyRegistry faults
        mapping world function native bindings parameter result),
      RecursiveNamedHeaderContracts.AtMost budget
        (CallableIndexedOwnedPreparedDirectLambdaInvocationBounds.FlowPreserves
          functions member (registry := registry)) :=
  CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds.preserves_at_most
    functions extension faithful observations wellFormed receiving budget
    (preserves_at_prefix functions expressions)

include faithful observations wellFormed receiving in
/-- The dispatcher receives only strict F from smaller shared E budgets. -/
theorem preserves_below (budget : Nat)
    (expressions : ∀ child, child < budget → ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions child) :
    ClosurePreservesBelow (qualification := facet headers) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      functions budget :=
  CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds.preserves_below
    functions extension faithful observations wellFormed receiving budget
    (fun child smaller => preserves_at_prefix functions (expressions child smaller))

include faithful observations wellFormed receiving in
/-- Strict native E constructs strict F with its own recovered Source grade. -/
theorem reflects_below (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (expressions : ExpressionsReflects (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    ClosureReflectsBelow (qualification := facet headers) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      functions budget :=
  CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds.reflects_below
    functions extension faithful observations wellFormed receiving budget functionTypes
    (reflects_at_prefix functions expressions)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedSelectedAssociationFlowBounds
