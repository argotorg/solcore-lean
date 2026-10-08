import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaInvocation

/-! Actual prepared ordinary indices and finite strict-child extraction.
The family records admitted expression members at their literal support
factory. Its two grades are used independently by the existing invocation
and typed-finish adapters. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRuntimeFamilyMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open RecursiveNamedCatalogInvocationBounds (Below)

/-- This index contains the actual captured environment and the static support
chosen for the same Code. Current caller state remains an invocation input. -/
structure OrdinaryIndex (compiled : SourceCoreUnifiedCompilation.Compiled) where
  function : Dynamic.Closure
  mapping : LocationMap
  world : StoreTyping
  scope : SourceCoreLocalCell.Scope
  capturedActual : Environment
  captured : Captures compiled.indexed mapping world scope function.captured capturedActual
  code : Code compiled.indexed function scope captured.administrative
  support : Support code
  prepared : PreparedAt code support

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- The certificate is the retained factory at the actual body read fuel. -/
def OrdinaryIndex.certificate (i : OrdinaryIndex compiled) (context : SourceSemantics.Context) :
    GenericExpressionMeaning.Certificate :=
  i.support.certificates i.support.body.readFuel i.function.source context

def PreservesAt (i : OrdinaryIndex compiled) (context : SourceSemantics.Context) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
    (bridge (headers := headers) (keys := keys))
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context i.function.evidence i.function.source (i.certificate context) faults size

def ReflectsAt (i : OrdinaryIndex compiled) (context : SourceSemantics.Context) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
    (bridge (headers := headers) (keys := keys))
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    context i.function.evidence i.function.source (i.certificate context) faults size

/-- Each conjunct applies to its own actual Source or native run. -/
def Family (i : OrdinaryIndex compiled) (size : Nat) : Prop :=
  ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
    PreservesAt (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i context size ∧
    ReflectsAt (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions i context size

/-- A real strict family child remains strict below the outer grade, including
when the head itself uses that outer grade. -/
theorem preserves_below (outer headBudget : Nat) (within : headBudget ≤ outer)
    (ih : ∀ i, Below outer (Family (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions i)) (i : OrdinaryIndex compiled) :
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
      Below headBudget (PreservesAt (headers := headers) (keys := keys)
        (registry := registry) (faults := faults) functions i context) := by
  intro context valid child strict
  exact (ih i child (Nat.lt_of_lt_of_le strict within) context valid).1

/-- Reflection selects the independent native conjunct at the same actual
support and context; it preserves the child's original strict grade. -/
theorem reflects_below (outer headBudget : Nat) (within : headBudget ≤ outer)
    (ih : ∀ i, Below outer (Family (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions i)) (i : OrdinaryIndex compiled) :
    ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) i.captured i.code context →
      Below headBudget (ReflectsAt (headers := headers) (keys := keys)
        (registry := registry) (faults := faults) functions i context) := by
  intro context valid child strict
  exact (ih i child (Nat.lt_of_lt_of_le strict within) context valid).2

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRuntimeFamilyMembers
