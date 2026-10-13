import Solcore.SourceSemantics.Staging.RecursiveBodyErasure

/-! Ordinary callable outcomes retain their exact independent Dynamic
application, including argument allocation, nested bodies and final heap.
The invocation dictionary is the one stored by the actual callable. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

/-- Builtins carry no dictionary; named and anonymous functions retain theirs. -/
def callableEvidence : Value → EvidenceEnvironment
  | .closure function => function.evidence
  | .global function => function.evidence
  | _ => []

theorem Applies.value_plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Heap} {callable : Value} {arguments : List Value} {value : Value}
    (trace : Applies program registry scope context before callable arguments (.value value) after) :
    CallableApplies program context scope.evidence (callableEvidence callable)
      before callable arguments value after := by
  cases trace with
  | builtin primitive => exact .builtin primitive
  | @global _ _ _ _ _ function _ _ _ _ _ bodyInstance _ child _ _
      instantiates covers roots selected parameters allocate body resultRule =>
    have source : child.source = bodyInstance.source := registry.source selected
    have evidence : child.evidence = function.evidence := registry.evidence selected
    generalize typeEq : bodyInstance.resultType = type at resultRule
    cases resultRule with
    | returned =>
      exact .global instantiates rfl covers
        (.returned covers roots parameters allocate
          (by simpa only [source, evidence, callableEvidence] using Statements.returned_plain body) rfl)
    | unit =>
      exact .global instantiates rfl covers
        (.unit covers typeEq roots parameters allocate
          (by simpa only [source, evidence, callableEvidence] using Statements.fallthrough_plain body) ⟨_, rfl⟩)
  | @closure _ _ _ _ _ function _ _ _ _ _ child _ _
      selected valid parameters allocate body resultRule =>
    have source : child.source = function.source := registry.source selected
    have evidence : child.evidence = function.evidence := registry.evidence selected
    generalize typeEq : function.resultType = type at resultRule
    cases resultRule with
    | returned =>
      exact .closure rfl valid parameters allocate
        (by simpa only [source, evidence, callableEvidence] using Statements.returned_plain body) rfl
    | unit =>
      exact .closureUnit rfl valid typeEq parameters allocate
        (by simpa only [source, evidence, callableEvidence] using Statements.fallthrough_plain body) ⟨_, rfl⟩

theorem Applies.semanticFault_plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Heap} {callable : Value} {arguments : List Value} {reason : SemanticFault}
    (trace : Applies program registry scope context before callable arguments (.fault (.semantic reason)) after) :
    CallableFaults program context scope.evidence (callableEvidence callable)
      before callable arguments reason after := by
  cases trace with
  | builtinArity mismatch => exact .builtinArity mismatch
  | builtinType arity mismatch => exact .builtinArgumentType arity mismatch
  | closureArity mismatch => exact .closureArity mismatch
  | globalArity instantiates mismatch => exact .globalArity instantiates mismatch
  | @global _ _ _ _ _ function _ _ _ _ _ bodyInstance _ child _ _
      instantiates _covers roots selected parameters allocate body resultRule =>
    have source : child.source = bodyInstance.source := registry.source selected
    have evidence : child.evidence = function.evidence := registry.evidence selected
    generalize typeEq : bodyInstance.resultType = type at resultRule
    cases resultRule with
    | fault =>
      exact .globalBody instantiates rfl
        (.statements roots parameters allocate
          (by simpa only [source, evidence, callableEvidence] using Statements.semanticFault_plain body))
  | @closure _ _ _ _ _ function _ _ _ _ _ child _ _
      selected valid parameters allocate body resultRule =>
    have source : child.source = function.source := registry.source selected
    have evidence : child.evidence = function.evidence := registry.evidence selected
    generalize typeEq : function.resultType = type at resultRule
    cases resultRule with
    | fault =>
      exact .closureBody rfl valid parameters allocate
        (by simpa only [source, evidence, callableEvidence] using Statements.semanticFault_plain body)

end Solcore.SourceSemantics.Staging.Recursive
