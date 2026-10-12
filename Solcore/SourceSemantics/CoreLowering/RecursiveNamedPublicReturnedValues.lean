import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping

/-! A successful public payload retains the actual semantic result and the
returned owned pool. The Source heap, closure captures and stable history come
from the preceding execution; exporting a handle does not construct them. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedValues
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

/-- The successful result keeps its original Source value and physical caller
state. Its heap typing fixes the returned native world exactly. -/
theorem returned_value
    (result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := registry) (payloads := payloads) functions owner caller header capture
      context outcome after native finalStore finalMap finalWorld faults)
    (decoded : LanguageResult.decode? native = some (.succeeded payload)) :
    ∃ source, outcome = .value source ∧
      ValueRep compiled.compatible.checked registry functions finalMap finalWorld
        header.function.resultType source payload header.output ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      finalWorld = finalStore.map Value.type ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧ StableRows returned ∧
        Dynamic.HeapWellTyped context after ∧
        Dynamic.ValueHasType context after source header.function.resultType := by
  obtain ⟨_evaluated, represented, heaps, _maps, _worlds, _administrative, _metadata,
    returned, related, post⟩ := result
  cases represented with
  | value represented =>
      simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
      subst payload
      have admission := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value post
      exact ⟨_, rfl, represented, heaps, heaps.runtime_hasTypes.world_eq,
        returned, related, admission.2.rows, admission.2.heap, admission.1⟩
  | fault represented => cases decoded

/-- Real instantiated headers share the program catalog and have closed rigid
and lexical variable scopes. Both the declaration and its parameter context
therefore support the next declaration's actual runtime type context. -/
theorem header_context_supports
    (first next : Header compiled (Program.ofChecked compiled.sourceProgram))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Dynamic.TypeContextSupports first.function.context next.function.context ∧
      Dynamic.TypeContextSupports first.context next.function.context := by
  obtain ⟨_firstFacts, firstTyped⟩ := RecursiveNamedHeaderSourceTyping.certificate first wellFormed
  obtain ⟨_nextFacts, nextTyped⟩ := RecursiveNamedHeaderSourceTyping.certificate next wellFormed
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

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedValues
