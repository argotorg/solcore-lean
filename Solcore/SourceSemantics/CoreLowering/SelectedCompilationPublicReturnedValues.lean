import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates

/-! A successful public payload retains the actual semantic result and the
returned owned pool. The Source heap, closure captures and stable history come
from the preceding execution; exporting a handle does not construct them. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  {owner : OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : NamedCapture headers owner.key header mapping world}
  {payloads : List Value} {context : SourceSemantics.Context}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
  {native payload : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

/-- Real instantiated headers share the program catalog and have closed rigid
and lexical variable scopes. Both the declaration and its parameter context
therefore support the next declaration's actual runtime type context. -/
theorem header_context_supports
    (first next : Header compiled (Program.ofChecked compiled.sourceProgram))
    (bodies : SelectedCompilationBodyTyping.Bodies compiled) :
    Dynamic.TypeContextSupports first.function.context next.function.context ∧
      Dynamic.TypeContextSupports first.context next.function.context := by
  obtain ⟨_firstFacts, firstTyped⟩ := SelectedCompilationHeaderCertificates.certified bodies first
  obtain ⟨_nextFacts, nextTyped⟩ := SelectedCompilationHeaderCertificates.certified bodies next
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields first.extended
  have signatures : first.function.context.signatures = (Program.ofChecked compiled.sourceProgram).signatures :=
    (congrArg (fun context : SourceSemantics.Context => context.signatures) first.frame.context).trans
      firstTyped.signatures_eq
  have closed : first.function.context.typeParameters = [] :=
    (congrArg (fun context : SourceSemantics.Context => context.typeParameters) first.frame.context).trans
      firstTyped.type_parameters_empty
  have variables : first.function.context.typeVariables = [] :=
    (congrArg (fun context : SourceSemantics.Context => context.typeVariables) first.frame.context).trans
      firstTyped.type_variables_empty
  rw [next.frame.context]
  exact ⟨Dynamic.TypeContextSupports.ofClosed (nextTyped.signatures_eq.trans signatures.symm)
      closed nextTyped.type_parameters_empty variables nextTyped.residual_type_variables_open,
    Dynamic.TypeContextSupports.ofClosed (nextTyped.signatures_eq.trans (fields.signatures.trans signatures).symm)
      (fields.typeParameters.trans closed) nextTyped.type_parameters_empty
      (fields.typeVariables.trans variables) nextTyped.residual_type_variables_open⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
