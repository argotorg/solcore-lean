import Solcore.SourceSemantics.Staging.SelectedPreservationComposition
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem body_all {size : Nat}
    (statementsIH : StatementsAt program registry size)
    {context : Context} {source : TypedSource} {child : Scope}
    {bodyInstance : BodyInstance} {dictionary : EvidenceEnvironment}
    {before bound after : Heap} {arguments : List Dynamic.Value}
    {inputTypes parameterTypes : List Ty}
    {lexicalContext bodyContext finalContext : Context} {facts : BodyFacts}
    {roots : List StatementId} {environment : Dynamic.Environment}
    {outcome : BodyOutcome} {result : Outcome}
    (runtime : SourceRuntimeValid program context source)
    (certificate : BodyInstanceTypingCertificate program bodyInstance inputTypes lexicalContext facts)
    (covers : dictionary.Covers bodyInstance.context)
    (beforeTyped : HeapWellTyped context before)
    (argumentsTyped : ValuesHaveTypes context before arguments inputTypes)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : registry.Closure (globalView bodyInstance dictionary roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context
      bodyInstance.source.inputs parameterTypes bodyContext)
    (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
    (body : Size.StatementsIn program registry true size child bodyContext environment bound
      roots finalContext outcome after)
    (resultRule : BodyResult bodyInstance.resultType outcome result) :
    OutcomePreserved context before after bodyInstance.resultType result := by
  cases result with
  | value value =>
    have post := body_success (StatementsAt.bodySuccess statementsIH) runtime certificate covers
      beforeTyped argumentsTyped rootsEq selected parameters allocate body resultRule
    exact ⟨post.heap_typed, post.heap_extends, by intro actual equal; cases equal; exact post.value_typed⟩
  | fault failure =>
    have post := SelectedFaultPreservation.method_body_fault (StatementsAt.fault statementsIH)
      runtime certificate covers beforeTyped argumentsTyped rootsEq selected parameters allocate body resultRule
    exact ⟨post.1, post.2, by intro value equal; cases equal⟩

 theorem coercion_step_step (selectedBodies : SelectedBodies program registry) (size : Nat)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    CoercionStepAt program registry size := by
  intro scope context before after step input outcome runtime heap typed valid trace
  cases trace with
  | coercionPrimitive noMethod applies =>
    obtain ⟨outputTyped, heapTyped, extended⟩ := CoercionStepExecutes.primitivePreserves heap typed applies
    exact ⟨heapTyped, extended, by intro value equal; cases equal; exact outputTyped⟩
  | coercionRequirement _ | coercionPrimitiveInput _ _ _ =>
    exact ⟨heap, .refl _, by intro value equal; cases equal⟩
  | @coercionMethod bodySize scope context before bound after step input bodyInstance dictionary roots child
      parameterTypes bodyContext finalContext bodyEnvironment outcome result method rootsEq selected parameters allocate body resultRule =>
    cases valid with
    | intro profile requirementsProve =>
      have selectedTyped := selectedBodies.methods method rootsEq selected
      obtain ⟨lexicalContext, facts, certificate, resultEq⟩ :=
        selectedTyped.coercionCertificateOfProfile selectedBodies.signatures runtime.signatures
          runtime.requirements.idsUnique profile requirementsProve
      have covers : dictionary.Covers bodyInstance.context := by cases method; assumption
      have post := body_all (statementsIH bodySize (Size.child_lt_stepSize (by simp)))
        runtime certificate covers heap (.cons typed .nil) rootsEq selected parameters allocate body resultRule
      exact ⟨post.heap_typed, post.heap_extends, by
        intro value equal
        exact resultEq ▸ post.value_typed value equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
