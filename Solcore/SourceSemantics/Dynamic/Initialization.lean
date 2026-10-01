import Solcore.SourceSemantics.Dynamic.Evaluation

/-! Successful declarative source execution never clears an initialized cell.
Allocations preserve existing cells; all source writes install a value. This
property needs no source typing or executable evaluator assumption. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Dynamic
open Frontend Frontend.SourceInference TypeSystem

def HeapInitializationExtend (before after : Heap) : Prop :=
  ∀ location cell, Heap.Reads before location cell → cell.value ≠ none →
    ∃ current, Heap.Reads after location current ∧ current.value ≠ none

namespace HeapInitializationExtend

theorem refl (heap : Heap) : HeapInitializationExtend heap heap := by
  intro location cell read initialized
  exact ⟨cell, read, initialized⟩

theorem trans {first middle last : Heap}
    (left : HeapInitializationExtend first middle)
    (right : HeapInitializationExtend middle last) :
    HeapInitializationExtend first last := by
  intro location cell read initialized
  obtain ⟨current, read, initialized⟩ := left location cell read initialized
  exact right location current read initialized

theorem of_allocation {before after : Heap} {type : Ty} {value : Option Value}
    {location : Location} (allocation : Heap.Allocates before type value location after) :
    HeapInitializationExtend before after := by
  intro oldLocation cell read initialized
  exact ⟨cell, allocation.preserves_read read, initialized⟩

theorem of_generalized_allocation {before after : Heap} {function : GeneralizedClosure}
    {location : Location} (allocation : Heap.AllocatesGeneralized before function location after) :
    HeapInitializationExtend before after := by
  intro oldLocation cell read initialized
  exact ⟨cell, allocation.preserves_read read, initialized⟩

theorem of_write {before after : Heap} {written : Location} {value : Value}
    (write : Heap.Writes before written (some value) after) :
    HeapInitializationExtend before after := by
  intro location cell read initialized
  by_cases same : location = written
  · subst location
    obtain ⟨previous, _, updatedRead⟩ := write.reads_updated
    exact ⟨{previous with value := some value}, updatedRead, by simp⟩
  · exact ⟨cell, write.preserves_other same read, initialized⟩

end HeapInitializationExtend

theorem BindersAllocate.initialization_extends
    {environment finalEnvironment : Environment} {before after : Heap}
    {binders : List TypedBinder} {values : List Value}
    (trace : BindersAllocate environment before binders values finalEnvironment after) :
    HeapInitializationExtend before after := by
  induction trace with
  | nil => exact .refl _
  | cons allocation _ ih => exact (HeapInitializationExtend.of_allocation allocation).trans ih

theorem ResolvedPlaceWrites.initialization_extends
    {modify : Option Value → Value → Prop} {before after : Heap}
    {place : ResolvedPlace} {value : Value}
    (trace : ResolvedPlaceWrites modify before place value after) :
    HeapInitializationExtend before after := by
  cases trace with
  | intro _ _ _ _ write => exact .of_write write

set_option maxHeartbeats 1000000 in
mutual

  theorem ExpressionEvaluates.initialization_extends {program : Program}
      {context : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {id : ExpressionId}
      {value : Value}
      {before after : Heap}
      (trace : ExpressionEvaluates program
        context evidence source environment before id value after) :
      HeapInitializationExtend before after :=
    match trace with
    | .intro _ form coercions => (form.initialization_extends).trans coercions.initialization_extends
    | .generalizedLocal _ _ _ _ _ _ _ _ coercions => coercions.initialization_extends

  theorem ExpressionFormEvaluates.initialization_extends {program : Program}
      {context : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {form : ExpressionForm}
      {requirements : List RequirementId}
      {coercions : List CoercionStep}
      {value : Value}
      {before after : Heap}
      (trace : ExpressionFormEvaluates program
        context evidence source environment before form requirements coercions value after) :
      HeapInitializationExtend before after :=
    match trace with
    | .literal _ _ => .refl _
    | .integerLiteral _ _ => .refl _
    | .«local» _ _ _ _ _ => .refl _
    | .localEmptyMapping _ _ _ _ _ _ write => (HeapInitializationExtend.of_write write)
    | .declaration _ _ _ => .refl _
    | .builtinFunction _ => .refl _
    | .builtinBoolean _ => .refl _
    | .group _ inner_evaluates => inner_evaluates.initialization_extends
    | .tuple _ elements_evaluate _ => elements_evaluate.initialization_extends
    | .unary _ operand_evaluates applies =>
        (operand_evaluates.initialization_extends).trans applies.initialization_extends
    | .binaryShortCircuit _ left_evaluates _ _ => left_evaluates.initialization_extends
    | .binaryEvaluateRight _ left_evaluates _ right_evaluates applies =>
        ((left_evaluates.initialization_extends).trans right_evaluates.initialization_extends).trans applies.initialization_extends
    | .conditionalTrue _ condition_evaluates branch_evaluates =>
        (condition_evaluates.initialization_extends).trans branch_evaluates.initialization_extends
    | .conditionalFalse _ condition_evaluates branch_evaluates =>
        (condition_evaluates.initialization_extends).trans branch_evaluates.initialization_extends
    | .lambda _ => .refl _
    | .directCall _ _ _ _ _ arguments_evaluate _ applies =>
        (arguments_evaluate.initialization_extends).trans applies.initialization_extends
    | .builtinCall _ arguments_evaluate applies =>
        (arguments_evaluate.initialization_extends).trans applies.initialization_extends
    | .indirectCall _ callee_evaluates arguments_evaluate _ argument_coercions _ _ _ applies =>
        (((callee_evaluates.initialization_extends).trans arguments_evaluate.initialization_extends).trans argument_coercions.initialization_extends).trans applies.initialization_extends
    | .constructor _ _ arguments_evaluate => arguments_evaluate.initialization_extends
    | .member _ base_evaluates _ => base_evaluates.initialization_extends
    | .proxy _ => .refl _
    | .indexFound _ base_evaluates index_evaluates _ =>
        (base_evaluates.initialization_extends).trans index_evaluates.initialization_extends
    | .indexDefault _ base_evaluates index_evaluates _ _ =>
        (base_evaluates.initialization_extends).trans index_evaluates.initialization_extends

  theorem ExpressionsEvaluate.initialization_extends {program : Program}
      {context : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {ids : List ExpressionId}
      {values : List Value}
      {before after : Heap}
      (trace : ExpressionsEvaluate program
        context evidence source environment before ids values after) :
      HeapInitializationExtend before after :=
    match trace with
    | .nil => .refl _
    | .cons head tail => (head.initialization_extends).trans tail.initialization_extends

  theorem SourceProjectionsEvaluate.initialization_extends {program : Program}
      {context : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {projections : List PlaceProjection}
      {evaluated : List EvaluatedProjection}
      {before after : Heap}
      (trace : SourceProjectionsEvaluate program
        context evidence source environment before projections evaluated after) :
      HeapInitializationExtend before after :=
    match trace with
    | .nil => .refl _
    | .member tail => tail.initialization_extends
    | .index head tail => (head.initialization_extends).trans tail.initialization_extends

  theorem SourcePlaceResolves.initialization_extends {program : Program}
      {context : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {place : PlaceResolution}
      {target : ResolvedPlace}
      {before after : Heap}
      (trace : SourcePlaceResolves program
        context evidence source environment before place target after) :
      HeapInitializationExtend before after :=
    match trace with
    | .intro _ _ evaluate _ _ _ => evaluate.initialization_extends

  theorem SourcePlaceAssignment.initialization_extends {program : Program}
      {context : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {combine : Option Value → Value → Value → Prop}
      {place : PlaceResolution}
      {id : ExpressionId}
      {value : Value}
      {before after : Heap}
      (trace : SourcePlaceAssignment program
        context evidence source combine environment before place id value after) :
      HeapInitializationExtend before after :=
    match trace with
    | .intro resolve evaluate_right write =>
        ((resolve.initialization_extends).trans evaluate_right.initialization_extends).trans write.initialization_extends

  theorem SourcePlaceSnapshotUpdate.initialization_extends {program : Program}
      {context : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {modify : Option Value → Value → Prop}
      {place : PlaceResolution}
      {value : Value}
      {before after : Heap}
      (trace : SourcePlaceSnapshotUpdate program
        context evidence source modify environment before place value after) :
      HeapInitializationExtend before after :=
    match trace with
    | .intro resolve write => (resolve.initialization_extends).trans write.initialization_extends

  theorem UnaryOperationApplies.initialization_extends {program : Program}
      {context : Context}
      {evidence : EvidenceEnvironment}
      {operator : Syntax.UnaryOp}
      {requirements : List RequirementId}
      {input output : Value}
      {before after : Heap}
      (trace : UnaryOperationApplies program
        context evidence before operator requirements input output after) :
      HeapInitializationExtend before after :=
    match trace with
    | .primitive _ => .refl _
    | .method _ _ invokes => invokes.initialization_extends

  theorem BinaryOperationApplies.initialization_extends {program : Program}
      {context : Context}
      {evidence : EvidenceEnvironment}
      {operator : Syntax.BinaryOp}
      {requirements : List RequirementId}
      {left right output : Value}
      {before after : Heap}
      (trace : BinaryOperationApplies program
        context evidence before operator requirements left right output after) :
      HeapInitializationExtend before after :=
    match trace with
    | .primitive _ => .refl _
    | .method _ _ invokes => invokes.initialization_extends

  theorem CoercionStepExecutes.initialization_extends {program : Program}
      {context : Context} {evidence : EvidenceEnvironment} {step : CoercionStep} {input output : Value}
      {before after : Heap}
      (trace : CoercionStepExecutes program
        context evidence before step input output after) :
      HeapInitializationExtend before after :=
    match trace with
    | .primitive _ _ => .refl _
    | .method _ invokes => invokes.initialization_extends

  theorem CoercionPathExecutes.initialization_extends {program : Program}
      {context : Context} {evidence : EvidenceEnvironment} {steps : List CoercionStep} {input output : Value}
      {before after : Heap}
      (trace : CoercionPathExecutes program
        context evidence before steps input output after) :
      HeapInitializationExtend before after :=
    match trace with
    | .nil => .refl _
    | .cons head tail => (head.initialization_extends).trans tail.initialization_extends

  theorem CallableApplies.initialization_extends {program : Program}
      {context : Context}
      {callerEvidence invocationEvidence : EvidenceEnvironment}
      {callable : Value}
      {arguments : List Value}
      {value : Value}
      {before after : Heap}
      (trace : CallableApplies program
        context callerEvidence invocationEvidence before callable arguments value after) :
      HeapInitializationExtend before after :=
    match trace with
    | .builtin _ => .refl _
    | .global _ _ _ invokes => invokes.initialization_extends
    | .closure _ _ _ allocate execute _ =>
        (allocate.initialization_extends).trans execute.initialization_extends
    | .closureUnit _ _ _ _ allocate execute _ =>
        (allocate.initialization_extends).trans execute.initialization_extends

  theorem BodyInvokes.initialization_extends {program : Program}
      {bodyInstance : BodyInstance} {evidence : EvidenceEnvironment} {arguments : List Value} {value : Value}
      {before after : Heap}
      (trace : BodyInvokes program
        bodyInstance evidence before arguments value after) :
      HeapInitializationExtend before after :=
    match trace with
    | .returned _ _ _ allocate execute _ =>
        (allocate.initialization_extends).trans execute.initialization_extends
    | .unit _ _ _ _ allocate execute _ =>
        (allocate.initialization_extends).trans execute.initialization_extends

  theorem StatementExecutes.initialization_extends {program : Program}
      {context finalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {id : StatementId}
      {outcome : ControlOutcome}
      {before after : Heap}
      (trace : StatementExecutes program
        context evidence source environment before id finalContext outcome after) :
      HeapInitializationExtend before after :=
    match trace with
    | .letUninitialized _ _ _ _ allocate => (HeapInitializationExtend.of_allocation allocate)
    | .letInitialized _ _ evaluate _ _ allocate =>
        (evaluate.initialization_extends).trans (HeapInitializationExtend.of_allocation allocate)
    | .letInitializedGeneralized _ _ _ _ _ allocate =>
        (HeapInitializationExtend.of_generalized_allocation allocate)
    | .returnUnit _ _ => .refl _
    | .returnValue _ _ evaluate => evaluate.initialization_extends
    | .expression _ _ evaluate => evaluate.initialization_extends
    | .assignValue _ _ assignment_executes => assignment_executes.initialization_extends
    | .assignBitNot _ _ assignment_executes => assignment_executes.initialization_extends
    | .ifTrue _ _ condition_evaluates body_executes =>
        (condition_evaluates.initialization_extends).trans body_executes.initialization_extends
    | .ifFalseWithoutElse _ _ condition_evaluates => condition_evaluates.initialization_extends
    | .ifFalseWithElse _ _ condition_evaluates body_executes =>
        (condition_evaluates.initialization_extends).trans body_executes.initialization_extends
    | .block _ _ body_executes => body_executes.initialization_extends
    | .matchArm _ _ _ scrutinee_evaluates allocate_hidden _ _ _ _ allocate_bindings execute =>
        (((scrutinee_evaluates.initialization_extends).trans (HeapInitializationExtend.of_allocation allocate_hidden)).trans allocate_bindings.initialization_extends).trans execute.initialization_extends
    | .matchDefault _ _ _ scrutinee_evaluates allocate_hidden _ execute =>
        ((scrutinee_evaluates.initialization_extends).trans (HeapInitializationExtend.of_allocation allocate_hidden)).trans execute.initialization_extends
    | .matchNoBranch _ _ _ scrutinee_evaluates allocate_hidden _ =>
        (scrutinee_evaluates.initialization_extends).trans (HeapInitializationExtend.of_allocation allocate_hidden)
    | .forLoop _ _ initializer_executes iterate =>
        (initializer_executes.initialization_extends).trans iterate.initialization_extends
    | .whileLoop _ _ iterate => iterate.initialization_extends
    | .breakStmt _ _ => .refl _
    | .continueStmt _ _ => .refl _

  theorem StatementsExecute.initialization_extends {program : Program}
      {context finalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {ids : List StatementId}
      {outcome : ControlOutcome}
      {before after : Heap}
      (trace : StatementsExecute program
        context evidence source environment before ids finalContext outcome after) :
      HeapInitializationExtend before after :=
    match trace with
    | .nil => .refl _
    | .cons head tail => (head.initialization_extends).trans tail.initialization_extends
    | .terminal head _ => head.initialization_extends

  theorem FunctionStatementsExecute.initialization_extends {program : Program}
      {context finalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {ids : List StatementId}
      {outcome : ControlOutcome}
      {before after : Heap}
      (trace : FunctionStatementsExecute program
        context evidence source environment before ids finalContext outcome after) :
      HeapInitializationExtend before after :=
    match trace with
    | .nil => .refl _
    | .tailExpression _ _ evaluate => evaluate.initialization_extends
    | .singleton _ _ execute => execute.initialization_extends
    | .cons head tail => (head.initialization_extends).trans tail.initialization_extends
    | .terminal head _ => head.initialization_extends

  theorem ForItemExecutes.initialization_extends {program : Program}
      {context finalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment finalEnvironment : Environment}
      {item : ForItemForm}
      {before after : Heap}
      (trace : ForItemExecutes program
        context evidence source environment before item finalContext finalEnvironment after) :
      HeapInitializationExtend before after :=
    match trace with
    | .letUninitialized _ _ allocate => (HeapInitializationExtend.of_allocation allocate)
    | .letInitialized evaluate _ _ allocate =>
        (evaluate.initialization_extends).trans (HeapInitializationExtend.of_allocation allocate)
    | .letInitializedGeneralized _ _ _ allocate =>
        (HeapInitializationExtend.of_generalized_allocation allocate)
    | .expression evaluate => evaluate.initialization_extends
    | .assignValue execute => execute.initialization_extends
    | .assignBitNot execute => execute.initialization_extends

  theorem ForItemsExecute.initialization_extends {program : Program}
      {context finalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment finalEnvironment : Environment}
      {items : List ForItemForm}
      {before after : Heap}
      (trace : ForItemsExecute program
        context evidence source environment before items finalContext finalEnvironment after) :
      HeapInitializationExtend before after :=
    match trace with
    | .nil => .refl _
    | .cons head tail => (head.initialization_extends).trans tail.initialization_extends

  theorem WhileExecutes.initialization_extends {program : Program}
      {context finalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {condition : ExpressionId}
      {body : List StatementId}
      {outcome : ControlOutcome}
      {before after : Heap}
      (trace : WhileExecutes program
        context evidence source environment before condition body finalContext outcome after) :
      HeapInitializationExtend before after :=
    match trace with
    | .done condition_evaluates => condition_evaluates.initialization_extends
    | .nextFallthrough condition_evaluates body_executes next =>
        ((condition_evaluates.initialization_extends).trans body_executes.initialization_extends).trans next.initialization_extends
    | .nextContinue condition_evaluates body_executes next =>
        ((condition_evaluates.initialization_extends).trans body_executes.initialization_extends).trans next.initialization_extends
    | .breaks condition_evaluates body_executes =>
        (condition_evaluates.initialization_extends).trans body_executes.initialization_extends
    | .returns condition_evaluates body_executes =>
        (condition_evaluates.initialization_extends).trans body_executes.initialization_extends

  theorem ForLoopExecutes.initialization_extends {program : Program}
      {context finalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource}
      {environment : Environment}
      {condition : ExpressionId}
      {post : List ForItemForm}
      {body : List StatementId}
      {outcome : ControlOutcome}
      {before after : Heap}
      (trace : ForLoopExecutes program
        context evidence source environment before condition post body finalContext outcome after) :
      HeapInitializationExtend before after :=
    match trace with
    | .done condition_evaluates => condition_evaluates.initialization_extends
    | .nextFallthrough condition_evaluates body_executes post_executes next =>
        (((condition_evaluates.initialization_extends).trans body_executes.initialization_extends).trans post_executes.initialization_extends).trans next.initialization_extends
    | .nextContinue condition_evaluates body_executes post_executes next =>
        (((condition_evaluates.initialization_extends).trans body_executes.initialization_extends).trans post_executes.initialization_extends).trans next.initialization_extends
    | .breaks condition_evaluates body_executes =>
        (condition_evaluates.initialization_extends).trans body_executes.initialization_extends
    | .returns condition_evaluates body_executes =>
        (condition_evaluates.initialization_extends).trans body_executes.initialization_extends

end

end Solcore.SourceSemantics.Dynamic
