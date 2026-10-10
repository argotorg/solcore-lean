import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher

/-! Every dispatcher closure keeps the actual selected qualification and body.
The receiving facts belong to that literal association. Eligible selected-root graded E induction is
forwarded through its actual ordinary or principal F step, retaining the same
protocol, owner and body; no static field contains a completed execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (Association)
open CallableIndexedOwnedPreparedSelectedNativeFamilyQualification (facet)
open CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)

/-- Pointwise receiving authority is indexed by the actual retained member. -/
def Receiving {mapping world function native bindings parameter result}
    (member : Association (facet headers) headers keys bodyRegistry faults
      mapping world function native bindings parameter result) : Prop :=
  match member with
  | .ordinary owner captured code _history support _origin _prepared _qualified _prefix _globals _reference _typed =>
      Ordinary.Receiving (headers := headers) (registry := registry) (faults := faults)
        functions captured code owner extension support
  | .principal owner captured code _history support _origin _prepared _qualified _globals _leading _reference _typed =>
      Principal.Receiving (headers := headers) (registry := registry) (faults := faults)
        functions captured code owner extension support

/-- All facts here are static table/token/reached-interpretation receipts. -/
def Receivings : Prop :=
  ∀ {mapping world function native bindings parameter result}
    (member : Association (facet headers) headers keys bodyRegistry faults
      mapping world function native bindings parameter result),
    Receiving (registry := registry) functions extension member

variable {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (receiving : Receivings (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
    (registry := registry) (faults := faults) functions extension)

include faithful observations wellFormed receiving in
/-- E through n produces the actual closure F through n. -/
theorem preserves_at_most (budget : Nat)
    (expressionIH : ExpressionsPreserves (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    ∀ {mapping world function native bindings parameter result}
      (member : Association (facet headers) headers keys bodyRegistry faults
        mapping world function native bindings parameter result),
      RecursiveNamedHeaderContracts.AtMost budget
        (CallableIndexedOwnedPreparedDirectLambdaInvocationBounds.FlowPreserves
          functions member (registry := registry)) := by
  intro mapping world function native bindings parameter result member
  have ready := receiving member
  cases member with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals reference typed =>
      exact Ordinary.preserves_flow functions captured code owner extension faithful observations wellFormed
        support qualified budget ready expressionIH
  | principal owner captured code history support origin prepared qualified globals leading reference typed =>
      exact Principal.preserves_flow functions captured code owner extension faithful observations wellFormed
        support qualified budget ready expressionIH

include faithful observations wellFormed receiving in
/-- The application dispatcher consumes strictly smaller F grades. -/
theorem preserves_below (budget : Nat)
    (expressionIH : ∀ child, child < budget → ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions child) :
    ClosurePreservesBelow (qualification := facet headers) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      functions budget := by
  intro mapping world function native bindings parameter result member child smaller
  exact preserves_at_most functions extension faithful observations wellFormed receiving
    child (expressionIH child smaller) member child (Nat.le_refl child)

include faithful observations wellFormed receiving in
/-- Native strict E builds strict F with an independent reconstructed Source grade. -/
theorem reflects_below (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (expressionIH : ExpressionsReflects (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    ClosureReflectsBelow (qualification := facet headers) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      functions budget := by
  intro mapping world function native bindings parameter result member
  have ready := receiving member
  cases member with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals reference typed =>
      exact Ordinary.reflects_flow functions captured code owner extension faithful observations wellFormed
        support qualified budget ready functionTypes expressionIH
  | principal owner captured code history support origin prepared qualified globals leading reference typed =>
      exact Principal.reflects_flow functions captured code owner extension faithful observations wellFormed
        support qualified budget ready functionTypes expressionIH

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds
