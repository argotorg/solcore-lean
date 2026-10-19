import Solcore.Test.SourceCoreSelectedFaultingLocalSource
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.Dynamic.Fault

/-! Independent Source execution of the original identity body after a genuine
local-scheme instance has been selected. No target execution is a premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Frontend SourceInference SourceSemantics

/-- The exact materialized body reads its newly allocated parameter and returns
it. The supplied frame is static Source code/evidence validity. -/
theorem Shape.identity_applies {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument : Dynamic.Value)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] argument
      ⟨before.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨before.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates before parameter.scheme.body (some argument)
      ⟨before.cells.length⟩ after := .append
  have read : Dynamic.ExpressionEvaluates program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨before.cells.length⟩) :: captured)
      after shape.parameterRead.node.id argument after := by
    apply Dynamic.ExpressionEvaluates.intro
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution
        (lookupExpression?_sound shape.parameterRead.found))
    · simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        shape.parameterRead.form, shape.parameterRead.requirements, shape.parameterRead.coercions]
      exact .local rfl .head allocation.reads_new rfl rfl
    · simp only [ExpressionNode.applySubstitution, shape.parameterRead.coercions, List.map_nil]
      exact .nil
  have returned : Dynamic.StatementExecutes program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨before.cells.length⟩) :: captured)
      after shape.identityReturn.id
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      (.returned argument) after := by
    exact .returnValue
      (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
        (lookupStatement?_sound shape.identityFound))
      (by simp only [StatementNode.applySubstitution, shape.identityForm,
        StatementForm.applySubstitution]) read
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id, node, _contains, form, _raw, typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
      function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_, _, parameters⟩
  obtain ⟨types, callContext, parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      apply Dynamic.CallableApplies.closure rfl frame
        (parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _))
      · exact .cons allocation (.nil _ _)
      · apply Dynamic.FunctionStatementsExecute.singleton
          (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
            (lookupStatement?_sound shape.identityFound))
        · intro expression impossible
          simp only [StatementNode.applySubstitution, shape.identityForm,
            StatementForm.applySubstitution] at impossible
          cases impossible
        · exact returned
      · rfl

/-- A read selects the actual instance before the ordered argument evaluation.
The call allocates the identity parameter only after that argument finishes. -/
theorem Shape.invoke {source : TypedSource} (shape : Shape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence produced : Dynamic.EvidenceEnvironment)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type type) [] substitution produced)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution)))
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      argument ⟨argumentsHeap.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  have callee : Dynamic.ExpressionEvaluates program context evidence source environment before
      call.callee.node.id
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution))) before := by
    apply Dynamic.ExpressionEvaluates.generalizedLocal (owned := [])
      (lookupExpression?_sound call.callee.found) call.callee.form
      (by rw [call.callee.requirements, call.callee.coercions]; rfl)
      lookup read descriptor fields
    · rw [call.callee.raw]; exact instantiation
    · rw [call.callee.coercions]; exact .nil
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound call.found)
  · rw [call.form]
    exact .indirectCall
      (by rw [call.requirements, call.argumentCoercions, call.coercions]; rfl)
      callee (.cons argumentTrace .nil) (.singleton argument)
      (by rw [call.argumentCoercions]; exact .nil) (.singleton argument)
      (by rw [call.arity]; rfl) (by rw [call.arity]; rfl)
      (shape.identity_applies captured substitution _ evidence argumentsHeap argument frame)
  · rw [call.coercions]; exact .nil

/-- The two runtime instances use an exact singleton substitution. Original
scheme validity and the requested ground type are the only typing inputs. -/
theorem Shape.instance {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    {type : TypeSystem.Ty} (wellformed : SchemeWellFormed context shape.binder.scheme)
    (ground : TypeWellFormed context type) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type type) [] [(shape.typeVariable, type)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.scheme]; exact ExactSubstitution.singleton _ _
  · intro typeVariable replacement member
    have same := List.mem_singleton.mp member
    cases same
    exact ground
  · simp [shape.scheme, TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates, shape.schemeRequirements]
    exact .nil

/-- Deep typing of the actual captured descriptor supplies the static invocation
frame for each instance, independently of executing either call. -/
theorem Shape.frame {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (evidence : Dynamic.EvidenceEnvironment) {type : TypeSystem.Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : Dynamic.GeneralizedClosureWellTyped nextContext heap (shape.descriptor context environment))
    (fields : Dynamic.RuntimeContextFields context nextContext)
    (signatures : nextContext.signatures = program.signatures)
    (covers : evidence.Covers nextContext)
    (wellformed : SchemeWellFormed nextContext shape.binder.scheme)
    (ground : TypeWellFormed nextContext type) :
    Dynamic.ClosureFrame program
      ((shape.descriptor context environment).instantiate [(shape.typeVariable, type)]
        (evidence.applySubstitution [(shape.typeVariable, type)])) := by
  have materialized := Dynamic.GeneralizedClosureWellTyped.instantiateHasType
    catalog typed fields covers (shape.instance evidence wellformed ground)
  obtain ⟨_parameter, _result, same, code, closed, _captured⟩ := materialized.closure_function_inv
  exact ⟨same.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, closed⟩

def Shape.wordHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(shape.allocatedHeap context environment before).cells ++
    [{type := (shape.parameter.applySubstitution [(shape.typeVariable, .word)]).scheme.body, value := some (.word (Core.Word.ofNatModulo 11))}]⟩

def Shape.valueHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(shape.wordHeap context environment before).cells ++
    [{type := shape.valueBinder.scheme.body, value := some (.word (Core.Word.ofNatModulo 11))}]⟩

def Shape.finalHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(shape.valueHeap context environment before).cells ++
    [{type := shape.absentBinder.scheme.body, value := none}]⟩

def Shape.failure {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.SemanticFault :=
  .uninitializedLocation ⟨(shape.valueHeap context environment before).cells.length⟩

/-- The Word call and ordinary allocation occur before the absent read. The
later Bool call is not evaluated after the first tuple element fails. -/
theorem Shape.body_trace {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext valueContext finalContext : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (before : Dynamic.Heap)
    (unique : NodeOccurrencesUnique source)
    (extended : BinderExtends source.owner context shape.binder nextContext)
    (valueExtended : BinderExtends source.owner nextContext shape.valueBinder valueContext)
    (absentExtended : BinderExtends source.owner valueContext shape.absentBinder finalContext)
    (fields : Dynamic.RuntimeContextFields context nextContext)
    (wellformed : SchemeWellFormed nextContext shape.binder.scheme)
    (word : TypeWellFormed nextContext .word)
    {literalType : TypeSystem.Ty}
    (literal : ExpressionHasType source nextContext shape.literal.node.id literalType)
    (wordFrame : Dynamic.ClosureFrame program
      ((shape.descriptor context environment).instantiate [(shape.typeVariable, .word)]
        (evidence.applySubstitution [(shape.typeVariable, .word)]))) :
    Dynamic.FunctionStatementsFault program context evidence source environment before
      [shape.initialized.id, shape.valueInitialized.id, shape.absentDeclared.id, shape.returned.id] finalContext
      (shape.failure context environment before) (shape.finalHeap context environment before) := by
  let allocated := shape.allocatedHeap context environment before
  let first := shape.wordHeap context environment before
  let bound := shape.valueHeap context environment before
  let after := shape.finalHeap context environment before
  let locals := (shape.binder.id, ⟨before.cells.length⟩) :: environment
  have allocation : Dynamic.Heap.AllocatesGeneralized before (shape.descriptor context environment)
      ⟨before.cells.length⟩ allocated := .append
  have literalTrace : Dynamic.ExpressionEvaluates program nextContext evidence source locals
      allocated shape.literal.node.id (.word (Core.Word.ofNatModulo 11)) allocated := by
    simpa only [shape.literalValue] using shape.literal.evaluates evidence locals allocated unique literal
  have firstTrace := shape.invoke shape.wordCall environment locals [(shape.typeVariable, .word)] evidence []
    Dynamic.Environment.LooksUp.head allocation.reads_new rfl fields
    (shape.instance evidence wellformed word) wordFrame literalTrace
  have valueAllocation : Dynamic.Heap.Allocates first shape.valueBinder.scheme.body
      (some (.word (Core.Word.ofNatModulo 11))) ⟨first.cells.length⟩ bound := .append
  let valueLocals := (shape.valueBinder.id, ⟨first.cells.length⟩) :: locals
  have initialized : Dynamic.StatementExecutes program nextContext evidence source locals allocated shape.valueInitialized.id
      valueContext (.fallthrough valueLocals) bound :=
    .letInitialized (lookupStatement?_sound shape.valueFound) shape.valueForm firstTrace
      (by rw [shape.valueScheme]; rfl) valueExtended valueAllocation
  have absentAllocation : Dynamic.Heap.Allocates bound shape.absentBinder.scheme.body none
      ⟨bound.cells.length⟩ after := .append
  let absentLocals := (shape.absentBinder.id, ⟨bound.cells.length⟩) :: valueLocals
  have absent : Dynamic.StatementExecutes program valueContext evidence source valueLocals bound
      shape.absentDeclared.id finalContext (.fallthrough absentLocals) after :=
    .letUninitialized (lookupStatement?_sound shape.absentFound) shape.absentForm
      (by rw [shape.absentScheme]; rfl) absentExtended absentAllocation
  have absentFault : Dynamic.ExpressionFaults program finalContext evidence source absentLocals after
      shape.absentRead.node.id (shape.failure context environment before) after := by
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound shape.absentRead.found)
    rw [shape.absentRead.form]
    exact .localUninitialized (owned := []) (by rw [shape.absentRead.requirements, shape.absentRead.coercions]; rfl)
      .head absentAllocation.reads_new rfl rfl (by simp [shape.absentScheme, TypeSystem.Scheme.mono, TypeSystem.Ty.word ])
  have tupleFault : Dynamic.ExpressionFaults program finalContext evidence source absentLocals after
      shape.tuple.id (shape.failure context environment before) after := by
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound shape.tupleFound)
    rw [shape.tupleForm]
    exact .tuple (by rw [shape.tupleRequirements, shape.tupleCoercions]; rfl) (.head absentFault)
  exact .tail (shape.initializes evidence environment before extended)
    (.tail initialized (.tail absent (.singleton
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleFault))))

end Tests.SourceCoreSelectedFaultingLocal
